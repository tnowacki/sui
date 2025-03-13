// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    references::{self, Node, Ref},
    regex,
};
use anyhow::{anyhow, bail};
use std::collections::{BTreeMap, BTreeSet};

//**************************************************************************************************
// Definitions
//**************************************************************************************************

#[derive(Clone, Debug)]
pub struct Path<Loc, Lbl> {
    pub loc: Loc,
    pub labels: Vec<Lbl>,
    pub ends_in_dot_star: bool,
}

pub type Paths<Loc, Lbl> = Vec<Path<Loc, Lbl>>;

pub struct Graph<Loc, Lbl: Ord> {
    fresh_id: usize,
    abstract_size: usize,
    nodes: BTreeMap<Ref, Node<Loc, Lbl>>,
}

//**************************************************************************************************
// impls
//**************************************************************************************************

// impl<Loc, Lbl: Ord> Conflicts<Loc, Lbl> {
//     pub fn is_empty(&self) -> bool {
//         let Conflicts {
//             equal,
//             existential,
//             labeled,
//         } = self;
//         equal.is_empty() && existential.is_empty() && labeled.is_empty()
//     }
// }

// impl<Loc, Lbl: Ord> Parents<Loc, Lbl> {
//     pub fn is_empty(&self) -> bool {
//         let Parents {
//             equal,
//             existential,
//             labeled,
//         } = self;
//         equal.is_empty() && existential.is_empty() && labeled.is_empty()
//     }
// }

impl<Loc: Copy, Lbl: Ord> Graph<Loc, Lbl> {
    pub fn new<K: Ord>(initial_refs: impl IntoIterator<Item = K>) -> (Self, BTreeMap<K, Ref>) {
        let mut map = BTreeMap::new();
        let mut graph = Self {
            fresh_id: 0,
            abstract_size: 0,
            nodes: BTreeMap::new(),
        };
        for k in initial_refs {
            let r = graph.add_ref();
            map.insert(k, r);
        }
        (graph, map)
    }

    fn node(&self, r: &Ref) -> anyhow::Result<&Node<Loc, Lbl>> {
        self.nodes.get(r).ok_or_else(|| anyhow!("missing ref"))
    }

    fn node_mut(&mut self, r: &Ref) -> anyhow::Result<&mut Node<Loc, Lbl>> {
        self.nodes.get_mut(r).ok_or_else(|| anyhow!("missing ref"))
    }

    fn add_ref(&mut self) -> Ref {
        let id = self.fresh_id;
        self.fresh_id += 1;
        let r = Ref::fresh(id);
        self.nodes.insert(r, Node::new());
        self.abstract_size += 1;
        r
    }

    pub fn alias_ref(&mut self, r: Ref, loc: Loc) -> Ref {
        todo!()
    }

    /// Creates a new reference whose paths are an extension of all specified sources.
    /// If sources is empty, the reference will have a single path rooted at the specified label
    pub fn extend_by_label(
        &mut self,
        sources: impl IntoIterator<Item = Ref>,
        loc: Loc,
        extension: Lbl,
    ) -> Ref
    where
        Lbl: Clone,
    {
        self.extend_by_regex(sources, loc, regex::Regex::label(extension))
            .unwrap()
    }

    pub fn extend_by_dot_star(&mut self, sources: impl IntoIterator<Item = Ref>, loc: Loc) -> Ref
    where
        Lbl: Clone,
    {
        self.extend_by_regex(sources, loc, regex::Regex::dot_star())
            .unwrap()
    }

    fn extend_by_regex(
        &mut self,
        sources: impl IntoIterator<Item = Ref>,
        loc: Loc,
        regex: regex::Regex<Lbl>,
    ) -> anyhow::Result<Ref>
    where
        Lbl: Clone,
    {
        let new_ref = self.add_ref();
        let mut edges_to_add = vec![];
        for x in sources {
            for y in self.node(&x)?.predecessors() {
                for y_to_x in self.node(&y)?.edge(&x)?.regexes() {
                    edges_to_add.push((y, y_to_x.extend(&regex), new_ref))
                }
            }
            for y in self.node(&x)?.successors() {
                for x_to_y in self.node(&x)?.edge(&y)?.regexes() {
                    if let Some(suffix) = x_to_y.remove_prefix(&regex) {
                        edges_to_add.push((new_ref, suffix, y))
                    }
                }
            }
        }
        for (p, r, s) in edges_to_add {
            self.add_edge(p, loc, r, s);
        }
        Ok(new_ref)
    }

    fn add_edge(
        &mut self,
        predecessor: Ref,
        loc: Loc,
        regex: regex::Regex<Lbl>,
        successor: Ref,
    ) -> anyhow::Result<()> {
        let is_epsilon = regex.is_epsilon();
        self.add_edge_impl(predecessor, loc, regex, successor)?;
        if is_epsilon {
            self.add_edge_impl(successor, loc, regex::Regex::epsilon(), predecessor)?;
        }
        Ok(())
    }

    fn add_edge_impl(
        &mut self,
        predecessor: Ref,
        loc: Loc,
        regex: regex::Regex<Lbl>,
        successor: Ref,
    ) -> anyhow::Result<()> {
        let predecessor_node = self.node_mut(&predecessor)?;
        self.abstract_size += predecessor_node.add_regex(loc, regex, successor);
        let successor_node = self.node_mut(&successor)?;
        successor_node.add_predecessor(predecessor);
        Ok(())
    }

    pub fn abstract_size(&self) -> usize {
        self.abstract_size
    }

    pub fn reference_size(&self, id: Ref) -> usize {
        self.nodes[&id].abstract_size()
    }

    //**********************************************************************************************
    // Ref API
    //**********************************************************************************************

    pub fn release(&mut self, id: Ref) -> anyhow::Result<()> {
        let Some(node) = self.nodes.remove(&id) else {
            bail!("missing ref")
        };
        for r in node.successors().chain(node.predecessors()) {
            self.abstract_size
                .saturating_sub(self.node_mut(&r)?.remove_neighbor(id));
        }
        Ok(())
    }

    pub fn release_all(&mut self) {
        self.nodes.clear();
        self.fresh_id = 0
    }

    //**********************************************************************************************
    // Query API
    //**********************************************************************************************

    // returns successors
    pub fn borrowed_by(&self, r: Ref) -> anyhow::Result<BTreeMap<Ref, Paths<Loc, Lbl>>> {
        let node = self.node(r)?;
        node.successors()
            .map(|s| {
                let paths = node.edge(&s)?.paths();
                Ok((s, paths))
            })
            .collect()
    }

    // returns predecessors
    pub fn borrows_from(&self, id: Ref) -> anyhow::Result<BTreeMap<Ref, Paths<Loc, Lbl>>> {
        todo!()
    }

    //**********************************************************************************************
    // Joining
    //**********************************************************************************************

    /// Returns true if self changed
    pub fn join(&mut self, other: &Self) -> bool {
        todo!()
    }

    pub fn refresh_refs(&mut self) -> anyhow::Result<()> {
        let nodes = std::mem::take(&mut self.nodes);
        self.nodes = nodes
            .into_iter()
            .map(|(r, node)| Ok((r.refresh()?, node.refresh_refs()?)))
            .collect::<anyhow::Result<_>>()?;
        self.fresh_id = 0;
        Ok(())
    }

    pub fn canonicalize(&mut self, remapping: &mut BTreeMap<Ref, usize>) -> anyhow::Result<()> {
        let nodes = std::mem::take(&mut self.nodes);
        self.nodes = nodes
            .into_iter()
            .map(|(r, node)| Ok((r.canonicalize(remapping)?, node.canonicalize(remapping)?)))
            .collect::<anyhow::Result<_>>()?;
        self.fresh_id = 0;
        Ok(())
    }

    //**********************************************************************************************
    // Invariants
    //**********************************************************************************************

    pub fn check_invariant(&self) {
        #[cfg(debug_assertions)]
        {
            let mut calculated_size = 0;
            for (r, node) in &self.nodes {
                node.check_invariant();
                calculated_size += node.abstract_size();
                for s in node.successors() {
                    debug_assert!(self.nodes[&s].is_predecessor(r));
                }
                for p in node.predecessors() {
                    debug_assert!(self.nodes[&p].is_successor(r));
                }
            }
            debug_assert_eq!(calculated_size, self.abstract_size);
        }
    }

    //**********************************************************************************************
    // Util
    //**********************************************************************************************

    pub fn keys(&self) -> impl Iterator<Item = RefID> + '_ {
        self.map.keys().copied()
    }

    #[allow(dead_code)]
    pub fn display(&self)
    where
        Lbl: std::fmt::Display,
    {
        for (id, ref_) in &self.map {
            let mut_ = if ref_.is_mutable() { "mut " } else { "imm " };
            println!("    {}{}: {{", mut_, id.0);
            for path in ref_.paths() {
                println!("        {},", path.path);
            }
            println!("    }},")
        }
    }
}
