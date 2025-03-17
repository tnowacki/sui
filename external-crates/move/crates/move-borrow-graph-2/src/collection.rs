// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    references::{Node, Ref},
    regex::Regex,
};
use anyhow::{anyhow, bail};
use core::fmt;
use std::collections::BTreeMap;

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

impl<Loc: Copy, Lbl: Ord + Clone> Graph<Loc, Lbl> {
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
        graph.check_invariant();
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
        self.nodes.insert(r, Node::new(r));
        self.abstract_size = self.abstract_size.saturating_add(1);
        r
    }

    pub fn alias_ref(&mut self, r: Ref, loc: Loc) -> anyhow::Result<Ref> {
        self.extend_by_regex(std::iter::once(r), loc, Regex::epsilon())
    }

    /// Creates a new reference whose paths are an extension of all specified sources.
    /// If sources is empty, the reference will have a single path rooted at the specified label
    pub fn extend_by_label(
        &mut self,
        sources: impl IntoIterator<Item = Ref>,
        loc: Loc,
        extension: Lbl,
    ) -> anyhow::Result<Ref> {
        self.extend_by_regex(sources, loc, Regex::label(extension))
    }

    pub fn extend_by_dot_star(
        &mut self,
        sources: impl IntoIterator<Item = Ref>,
        loc: Loc,
    ) -> anyhow::Result<Ref> {
        self.extend_by_regex(sources, loc, Regex::dot_star())
    }

    fn extend_by_regex(
        &mut self,
        sources: impl IntoIterator<Item = Ref>,
        loc: Loc,
        regex: Regex<Lbl>,
    ) -> anyhow::Result<Ref> {
        self.check_invariant();
        let new_ref = self.add_ref();
        let mut edges_to_add = vec![];
        for x in sources {
            for y in self.node(&x)?.predecessors() {
                for y_to_x in self.node(&y)?.regexes(&x)? {
                    edges_to_add.push((y, y_to_x.extend(&regex), new_ref))
                }
            }
            for y in self.node(&x)?.successors() {
                for x_to_y in self.node(&x)?.regexes(&y)? {
                    // For the edge x --> y, we adding a new edge x --> new_ref
                    // In cases of a label extension, we might need to add an edge new_ref --> y
                    // if the extension is a prefix of x_to_y.
                    // However! In cases where an epsilon or dot-star is involved,
                    // we might also have the case that we can remove x --> y as a prefix of
                    // x --> new_ref
                    // In the case where we have `e.remove_prefix(p)` and `e` is a list of labels
                    // `fgh` and `p` is `.*`, we will consider all possible suffixes of `e`,
                    // `[fgh, gh, h, epsilon]`. This could grow rather quickly, so we might
                    // want to optimize this representation
                    for x_to_y_suffix in x_to_y.remove_prefix(&regex) {
                        edges_to_add.push((new_ref, x_to_y_suffix, y))
                    }
                    for regex_suffix in regex.remove_prefix(&x_to_y) {
                        edges_to_add.push((y, regex_suffix, new_ref));
                    }
                }
            }
        }
        for (p, r, s) in edges_to_add {
            self.add_edge(p, loc, r, s)?;
        }
        self.check_invariant();
        Ok(new_ref)
    }

    fn add_edge(
        &mut self,
        predecessor: Ref,
        loc: Loc,
        regex: Regex<Lbl>,
        successor: Ref,
    ) -> anyhow::Result<()> {
        let predecessor_node = self.node_mut(&predecessor)?;
        let size_increase = predecessor_node.add_regex(loc, regex, successor);
        self.abstract_size = self.abstract_size.saturating_add(size_increase);
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
            self.abstract_size = self
                .abstract_size
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
        let node = self.node(&r)?;
        let mut paths = BTreeMap::new();
        for s in node.successors() {
            if r == s {
                // skip self epsilon
                continue;
            }
            let _prev = paths.insert(s, node.paths(&s)?);
            debug_assert!(_prev.is_none());
        }
        Ok(paths)
    }

    // returns predecessors
    pub fn borrows_from(&self, id: Ref) -> anyhow::Result<BTreeMap<Ref, Paths<Loc, Lbl>>> {
        let node = self.node(&id)?;
        let mut paths = BTreeMap::new();
        for p in node.predecessors() {
            if id == p {
                // skip self epsilon
                continue;
            }
            let _prev = paths.insert(p, self.node(&p)?.paths(&id)?);
            debug_assert!(_prev.is_none());
        }
        Ok(paths)
    }

    //**********************************************************************************************
    // Joining
    //**********************************************************************************************

    /// Returns true if self changed
    pub fn join(&mut self, other: &Self) -> anyhow::Result<bool> {
        self.check_join_invariants(other);
        let mut size_increase = 0usize;
        for (r, other_node) in &other.nodes {
            let self_node = self.node_mut(r)?;
            size_increase = size_increase.saturating_add(self_node.join(other_node));
        }
        self.abstract_size = self.abstract_size.saturating_add(size_increase);
        self.check_invariant();
        Ok(size_increase > 0)
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

    // checks:
    // - both graphs satisfy their invariants
    // - all nodes are canonical
    // - the graphs have the same set of nodes
    fn check_join_invariants(&self, other: &Self) {
        #[cfg(debug_assertions)]
        {
            self.check_invariant();
            other.check_invariant();
            for self_r in self.keys() {
                debug_assert!(self_r.is_canonical());
                debug_assert!(other.nodes.contains_key(&self_r));
            }
            for other_r in other.keys() {
                debug_assert!(other_r.is_canonical());
                debug_assert!(self.nodes.contains_key(&other_r));
            }
        }
    }

    // checks:
    // - ref --> node has ref == node.ref()
    // - successor/predecessor relationship is correctly maintained
    // - the abstract size is correct
    pub fn check_invariant(&self) {
        #[cfg(debug_assertions)]
        {
            for (id, node) in &self.nodes {
                debug_assert_eq!(id, &node.ref_());
            }
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

    pub fn keys(&self) -> impl Iterator<Item = Ref> + '_ {
        self.nodes.keys().copied()
    }

    #[allow(dead_code)]
    pub fn print(&self)
    where
        Lbl: std::fmt::Display,
    {
        println!("{self}");
    }
}

impl<Loc, Lbl: Ord> fmt::Display for Graph<Loc, Lbl>
where
    Lbl: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (r, node) in &self.nodes {
            write!(f, "    {}: {{\n", r)?;
            write!(f, "        {}", node)?;
            write!(f, "    }},\n")?;
        }
        Ok(())
    }
}
