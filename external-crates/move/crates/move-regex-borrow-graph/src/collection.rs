// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    bail, error,
    references::{Node, Ref},
    regex::{Extension, Regex},
    Result,
};
use core::fmt;
use std::collections::{BTreeMap, BTreeSet};

//**************************************************************************************************
// Definitions
//**************************************************************************************************

#[derive(Clone, Debug)]
pub struct Path<Loc, Lbl> {
    pub loc: Loc,
    pub(crate) labels: Vec<Lbl>,
    pub(crate) ends_in_dot_star: bool,
}

pub type Paths<Loc, Lbl> = Vec<Path<Loc, Lbl>>;

#[derive(Clone, Debug)]
pub struct Graph<Loc, Lbl: Ord> {
    fresh_id: usize,
    abstract_size: usize,
    nodes: BTreeMap<Ref, Node<Loc, Lbl>>,
}

//**************************************************************************************************
// impls
//**************************************************************************************************

impl<Loc, Lbl> Path<Loc, Lbl> {
    /// An empty path
    pub fn is_epsilon(&self) -> bool {
        self.labels.is_empty() && !self.ends_in_dot_star
    }

    /// A path with a single label (and not dot-star)
    pub fn is_label(&self, lbl: &Lbl) -> bool
    where
        Lbl: Eq,
    {
        !self.ends_in_dot_star && self.labels.len() == 1 && &self.labels[0] == lbl
    }

    /// A path that starts with the specified label
    pub fn starts_with(&self, lbl: &Lbl) -> bool
    where
        Lbl: Eq,
    {
        self.ends_in_dot_star || self.labels.first().is_some_and(|l| l == lbl)
    }

    /// A path with no labels and ends with dot-star
    pub fn is_dot_star(&self) -> bool {
        self.labels.is_empty() && self.ends_in_dot_star
    }

    pub fn abstract_size(&self) -> usize {
        1 + self.labels.len() + (self.ends_in_dot_star as usize)
    }
}

impl<Loc: Copy, Lbl: Ord + Clone> Graph<Loc, Lbl> {
    pub fn new<K: Ord>(
        initial_refs: impl IntoIterator<Item = (K, /* is_mut */ bool)>,
    ) -> (Self, BTreeMap<K, Ref>) {
        let mut map = BTreeMap::new();
        let mut graph = Self {
            fresh_id: 0,
            abstract_size: 0,
            nodes: BTreeMap::new(),
        };
        for (k, is_mut) in initial_refs {
            let r = graph.add_ref(is_mut);
            map.insert(k, r);
        }
        graph.check_invariant();
        (graph, map)
    }

    pub fn is_mutable(&self, r: Ref) -> Result<bool> {
        self.node(&r).map(|n| n.is_mutable())
    }

    fn node(&self, r: &Ref) -> Result<&Node<Loc, Lbl>> {
        self.nodes.get(r).ok_or_else(|| error!("missing ref"))
    }

    fn node_mut(&mut self, r: &Ref) -> Result<&mut Node<Loc, Lbl>> {
        self.nodes.get_mut(r).ok_or_else(|| error!("missing ref"))
    }

    fn add_ref(&mut self, is_mut: bool) -> Ref {
        let id = self.fresh_id;
        self.fresh_id += 1;
        let r = Ref::fresh(id);
        self.nodes.insert(r, Node::new(r, is_mut));
        self.abstract_size = self.abstract_size.saturating_add(1);
        r
    }

    pub fn extend_by_epsilon(
        &mut self,
        loc: Loc,
        sources: impl IntoIterator<Item = Ref>,
        is_mut: bool,
    ) -> Result<Ref> {
        self.extend_by_extension(loc, sources, is_mut, Extension::Epsilon)
    }

    /// Creates a new reference whose paths are an extension of all specified sources.
    /// If sources is empty, the reference will have a single path rooted at the specified label
    pub fn extend_by_label(
        &mut self,
        loc: Loc,
        sources: impl IntoIterator<Item = Ref>,
        is_mut: bool,
        extension: Lbl,
    ) -> Result<Ref> {
        self.extend_by_extension(loc, sources, is_mut, Extension::Label(extension))
    }

    pub fn extend_by_dot_star(
        &mut self,
        loc: Loc,
        sources: impl IntoIterator<Item = Ref>,
        is_mut: bool,
    ) -> Result<Ref> {
        self.extend_by_extension(loc, sources, is_mut, Extension::DotStar)
    }

    fn extend_by_extension(
        &mut self,
        loc: Loc,
        sources: impl IntoIterator<Item = Ref>,
        is_mut: bool,
        ext: Extension<Lbl>,
    ) -> Result<Ref> {
        self.check_invariant();
        let new_ref = self.add_ref(is_mut);
        let mut edges_to_add = vec![];
        for x in sources {
            for y in self.node(&x)?.predecessors() {
                for y_to_x in self.node(&y)?.regexes(&x)? {
                    edges_to_add.push((y, y_to_x.clone().extend(&ext), new_ref))
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
                    for x_to_y_suffix in x_to_y.remove_prefix(&ext) {
                        edges_to_add.push((new_ref, x_to_y_suffix, y))
                    }
                    for regex_suffix in ext.remove_prefix(x_to_y) {
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
    ) -> Result<()> {
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

    pub fn reference_size(&self, id: Ref) -> Result<usize> {
        self.node(&id).map(|n| n.abstract_size())
    }

    //**********************************************************************************************
    // Ref API
    //**********************************************************************************************

    pub fn release(&mut self, id: Ref) -> Result<()> {
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
    pub fn borrowed_by(&self, r: Ref) -> Result<BTreeMap<Ref, Paths<Loc, Lbl>>> {
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
    pub fn borrows_from(&self, id: Ref) -> Result<BTreeMap<Ref, Paths<Loc, Lbl>>> {
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
    pub fn join(&mut self, other: &Self) -> Result<bool> {
        self.check_join_invariants(other);
        let mut size_increase = 0usize;
        let self_keys = self.keys().collect::<BTreeSet<_>>();
        for (r, other_node) in other.nodes.iter().filter(|(r, _)| self_keys.contains(r)) {
            let self_node = self.node_mut(r)?;
            size_increase = size_increase.saturating_add(self_node.join(&self_keys, other_node));
        }
        self.abstract_size = self.abstract_size.saturating_add(size_increase);
        self.check_invariant();
        Ok(size_increase > 0)
    }

    pub fn refresh_refs(&mut self) -> Result<()> {
        let nodes = std::mem::take(&mut self.nodes);
        self.nodes = nodes
            .into_iter()
            .map(|(r, node)| Ok((r.refresh()?, node.refresh_refs()?)))
            .collect::<Result<_>>()?;
        self.fresh_id = 0;
        Ok(())
    }

    pub fn canonicalize(&mut self, remapping: &BTreeMap<Ref, usize>) -> Result<()> {
        let nodes = std::mem::take(&mut self.nodes);
        self.nodes = nodes
            .into_iter()
            .map(|(r, node)| Ok((r.canonicalize(remapping)?, node.canonicalize(remapping)?)))
            .collect::<Result<_>>()?;
        self.fresh_id = 0;
        Ok(())
    }

    pub fn is_canonical(&self) -> bool {
        self.nodes.keys().all(|r| r.is_canonical())
    }

    //**********************************************************************************************
    // Invariants
    //**********************************************************************************************

    // checks:
    // - both graphs satisfy their invariants
    // - all nodes are canonical
    // - all nodes in self are also in other
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
                // there can be nodes in other that are not in self
            }
            for (self_r, self_node) in &self.nodes {
                let other_node = other.node(self_r).unwrap();
                debug_assert_eq!(self_node.ref_(), other_node.ref_());
                debug_assert_eq!(self_node.is_mutable(), other_node.is_mutable());
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
            writeln!(f, "    {}: {{", r)?;
            writeln!(f, "        {}", node)?;
            writeln!(f, "    }},")?;
        }
        Ok(())
    }
}
