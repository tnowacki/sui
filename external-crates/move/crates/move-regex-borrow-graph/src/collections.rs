// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::graph::{GraphMap, NodeIndex};
use crate::{
    MeterResult, Result, bail, ensure, error,
    meter::Meter,
    references::{Edge, Node, Ref},
    regex::{Extension, Regex},
};
use core::fmt;
use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
};

//**************************************************************************************************
// Definitions
//**************************************************************************************************

#[derive(Clone, Debug)]
/// Returned from the public query APIs of `borrowed_by` and `borrows_from`.
// Note this is not to be used internally and is not
pub struct Path<Loc, Lbl> {
    pub loc: Loc,
    pub(crate) labels: Vec<Lbl>,
    pub(crate) ends_in_dot_star: bool,
}

pub type Paths<Loc, Lbl> = Vec<Path<Loc, Lbl>>;

#[derive(Clone, Debug)]
pub struct Graph<Loc, Lbl: Ord> {
    fresh_id: usize,
    nodes: BTreeMap<Ref, Node>,
    pub(crate) graph: GraphMap<Ref, Edge<Loc, Lbl>>,
}

//**************************************************************************************************
// impls
//**************************************************************************************************

impl<Loc, Lbl> Path<Loc, Lbl> {
    /// An empty path
    pub fn is_epsilon(&self) -> bool {
        self.labels.is_empty() && !self.is_dot_star()
    }

    /// A path with a single label (and not dot-star)
    pub fn is_label(&self, lbl: &Lbl) -> bool
    where
        Lbl: Eq,
    {
        !self.is_dot_star() && self.labels.len() == 1 && &self.labels[0] == lbl
    }

    /// A path that starts with the specified label
    pub fn starts_with(&self, lbl: &Lbl) -> bool
    where
        Lbl: Eq,
    {
        self.is_dot_star() || self.labels.first().is_some_and(|l| l == lbl)
    }

    /// A path with no labels and ends with dot-star
    pub fn is_dot_star(&self) -> bool {
        self.labels.is_empty() && self.ends_in_dot_star
    }

    pub fn abstract_size(&self) -> usize {
        1 + self.labels.len() + (self.ends_in_dot_star as usize)
    }
}

impl<Loc: Copy, Lbl: Ord + Clone + fmt::Display> Graph<Loc, Lbl> {
    pub fn new<K: fmt::Debug + Ord>(
        initial_refs: impl IntoIterator<Item = (K, Loc, /* is_mut */ bool)>,
    ) -> Result<(Self, BTreeMap<K, Ref>)> {
        let mut map = BTreeMap::new();
        let mut graph = Self {
            fresh_id: 0,
            nodes: BTreeMap::new(),
            graph: GraphMap::new(),
        };
        for (k, loc, is_mut) in initial_refs {
            let r = graph.add_ref(loc, is_mut)?;
            ensure!(!map.contains_key(&k), "key {:?} already exists", k);
            map.insert(k, r);
        }
        graph.check_invariants();
        Ok((graph, map))
    }

    pub fn is_empty(&self) -> bool {
        debug_assert_eq!(self.nodes.len(), self.graph.node_count());
        self.nodes.is_empty()
    }

    pub fn is_mutable(&self, r: Ref) -> Result<bool> {
        self.node(&r).map(|n| n.is_mutable())
    }

    fn node(&self, r: &Ref) -> Result<&Node> {
        self.nodes
            .get(r)
            .ok_or_else(|| error!("missing ref {:?}", r))
    }

    /// Returns the direct successors of the specified reference
    fn successors(&self, r: Ref) -> Result<impl Iterator<Item = (&Edge<Loc, Lbl>, Ref)> + '_> {
        let r_idx = self.node(&r)?.node_index();
        Ok(self.successors_idx(r_idx)?.map(move |(e, s_idx)| {
            let s = *self.graph.node_weight(s_idx).unwrap();
            (e, s)
        }))
    }

    /// Returns the direct successors of the specified reference by NodeIndex
    fn successors_idx(
        &self,
        r: NodeIndex,
    ) -> Result<impl Iterator<Item = (&Edge<Loc, Lbl>, NodeIndex)> + '_> {
        ensure!(self.graph.contains_node(r), "missing ref {:?} in graph", r);
        Ok(self.graph.outgoing_edges(r))
    }

    /// Returns the direct predecessors of the specified reference
    fn predecessors(&self, r: Ref) -> Result<impl Iterator<Item = (Ref, &Edge<Loc, Lbl>)> + '_> {
        let r_idx = self.node(&r)?.node_index();
        Ok(self.predecessors_idx(r_idx)?.map(move |(p_idx, e)| {
            let p = *self.graph.node_weight(p_idx).unwrap();
            (p, e)
        }))
    }

    /// Returns the direct predecessors of the specified reference by NodeIndex
    fn predecessors_idx(
        &self,
        r: NodeIndex,
    ) -> Result<impl Iterator<Item = (NodeIndex, &Edge<Loc, Lbl>)> + '_> {
        ensure!(self.graph.contains_node(r), "missing ref {:?} in graph", r);
        Ok(self.graph.incoming_edges(r))
    }

    fn add_ref(&mut self, loc: Loc, is_mut: bool) -> Result<Ref> {
        self.check_invariants();
        let id = self.fresh_id;
        self.fresh_id += 1;
        let r = Ref::fresh(id);

        let r_idx = self.graph.add_node(r);
        let mut edge = Edge::<Loc, Lbl>::new();
        edge.insert(loc, Cow::Owned(Regex::epsilon()));
        self.graph.add_edge(r_idx, r_idx, edge);

        let node = Node::new(is_mut, r_idx);
        let prev = self.nodes.insert(r, node);
        ensure!(prev.is_none(), "ref {:?} already exists", r);
        self.check_invariants();
        Ok(r)
    }

    pub fn extend_by_epsilon<M: Meter>(
        &mut self,
        loc: Loc,
        sources: impl IntoIterator<Item = Ref>,
        is_mut: bool,
        meter: &mut M,
    ) -> MeterResult<Ref, M::Error> {
        let new_ref = self.add_ref(loc, is_mut)?;
        let source_idxs = sources
            .into_iter()
            .map(|r| self.node(&r).map(|n| n.node_index()))
            .collect::<Result<BTreeSet<_>>>()?;
        let ext = Extension::Epsilon;
        let new_ref_idx = self.node(&new_ref)?.node_index();
        self.extend_by_extension(loc, &source_idxs, ext, new_ref_idx, &BTreeSet::new(), meter)?;
        Ok(new_ref)
    }

    /// Creates a new reference whose paths are an extension of all specified sources.
    /// If sources is empty, the reference will have a single path rooted at the specified label
    pub fn extend_by_label<M: Meter>(
        &mut self,
        loc: Loc,
        sources: impl IntoIterator<Item = Ref>,
        is_mut: bool,
        extension: Lbl,
        meter: &mut M,
    ) -> MeterResult<Ref, M::Error> {
        let new_ref = self.add_ref(loc, is_mut)?;
        let source_idxs = sources
            .into_iter()
            .map(|r| self.node(&r).map(|n| n.node_index()))
            .collect::<Result<BTreeSet<_>>>()?;
        let ext = Extension::Label(extension);
        let new_ref_idx = self.node(&new_ref)?.node_index();
        self.extend_by_extension(loc, &source_idxs, ext, new_ref_idx, &BTreeSet::new(), meter)?;
        Ok(new_ref)
    }

    /// Creates new references based on the mutability specified. Immutable references will extend
    /// from all sources and mutable references will extends only from mutable sources.
    /// Additionally, all mutable references will be disjoint from all other references created
    pub fn extend_by_dot_star_for_call<M: Meter>(
        &mut self,
        loc: Loc,
        all_sources: impl IntoIterator<Item = Ref>,
        mutabilities: Vec<bool>,
        meter: &mut M,
    ) -> MeterResult<Vec<Ref>, M::Error> {
        let all_sources = all_sources.into_iter().collect::<BTreeSet<_>>();
        let all_source_idxs = all_sources
            .iter()
            .map(|r| self.node(r).map(|n| n.node_index()))
            .collect::<Result<BTreeSet<_>>>()?;
        let mut_source_idxs = all_sources
            .iter()
            .copied()
            .filter_map(|r| match self.is_mutable(r) {
                Err(e) => Some(Err(e)),
                Ok(false) => None,
                Ok(true) => {
                    let node = match self.node(&r) {
                        Err(e) => return Some(Err(e)),
                        Ok(n) => n,
                    };
                    let r_idx = node.node_index();
                    Some(Ok(r_idx))
                }
            })
            .collect::<Result<BTreeSet<_>>>()?;
        let new_refs = mutabilities
            .iter()
            .map(|is_mut| self.add_ref(loc, *is_mut))
            .collect::<Result<Vec<_>>>()?;
        let mut all_new_refs = BTreeSet::new();
        let mut mut_new_refs = BTreeSet::new();
        let mut imm_new_refs = BTreeSet::new();
        for &new_ref in &new_refs {
            let new_ref_idx = self.node(&new_ref)?.node_index();
            all_new_refs.insert(new_ref_idx);
            if self.is_mutable(new_ref).unwrap() {
                mut_new_refs.insert(new_ref_idx);
            } else {
                imm_new_refs.insert(new_ref_idx);
            }
        }
        for &mut_new_ref in &mut_new_refs {
            self.extend_by_extension(
                loc,
                &mut_source_idxs,
                Extension::DotStar,
                mut_new_ref,
                &all_new_refs,
                meter,
            )?;
        }
        for &imm_new_ref in &imm_new_refs {
            self.extend_by_extension(
                loc,
                &all_source_idxs,
                Extension::DotStar,
                imm_new_ref,
                &mut_new_refs,
                meter,
            )?;
        }
        #[cfg(debug_assertions)]
        {
            for &mut_new_ref in &mut_new_refs {
                for (_, s) in self
                    .successors_idx(mut_new_ref)
                    .unwrap()
                    .filter(|&(_, s)| s != mut_new_ref)
                {
                    debug_assert!(!imm_new_refs.contains(&s));
                    debug_assert!(!mut_new_refs.contains(&s));
                }
            }
            for &imm_new_ref in &imm_new_refs {
                for (_, s) in self
                    .successors_idx(imm_new_ref)
                    .unwrap()
                    .filter(|&(_, s)| s != imm_new_ref)
                {
                    // s is new ==> s is imm
                    debug_assert!(!all_new_refs.contains(&s) || imm_new_refs.contains(&s));
                    debug_assert!(!mut_new_refs.contains(&s));
                }
            }
        }
        Ok(new_refs)
    }

    fn extend_by_extension<M: Meter>(
        &mut self,
        loc: Loc,
        sources: &BTreeSet<NodeIndex>,
        ext: Extension<Lbl>,
        new_ref: NodeIndex,
        exclude: &BTreeSet<NodeIndex>,
        meter: &mut M,
    ) -> MeterResult<(), M::Error> {
        self.check_invariants();
        let mut edges_to_add = vec![];
        let mut nodes_visited = 0usize;
        let mut total_edge_size = 0usize;
        for &x in sources {
            debug_assert!(!exclude.contains(&x));
            let (neighborhood_size, edge_size) =
                self.determine_new_edges(&mut edges_to_add, x, &ext, new_ref, exclude)?;
            // we will count x itself via the self loop
            nodes_visited = nodes_visited.saturating_add(neighborhood_size);
            total_edge_size = total_edge_size.saturating_add(edge_size);
        }
        meter.visit_nodes(nodes_visited)?;
        meter.visit_edges(total_edge_size)?;
        for (p, r, s) in edges_to_add {
            debug_assert!(p == new_ref || s == new_ref);
            self.add_edge(p, loc, r, s)?;
        }
        self.check_invariants();
        Ok(())
    }

    fn determine_new_edges(
        &self,
        edges_to_add: &mut Vec<(NodeIndex, Regex<Lbl>, NodeIndex)>,
        x: NodeIndex,
        ext: &Extension<Lbl>,
        new_ref: NodeIndex,
        exclude: &BTreeSet<NodeIndex>,
    ) -> Result<(/* neighborhood */ usize, /* edge size */ usize)> {
        let mut neighborhood_size = 0usize;
        let mut edge_size = 0usize;
        for (y, edge) in self
            .predecessors_idx(x)?
            .filter(|(y, _)| !exclude.contains(y))
        {
            neighborhood_size = neighborhood_size.saturating_add(1);
            for y_to_x in edge.regexes() {
                let extended = y_to_x.clone().extend(ext);
                edge_size = edge_size.saturating_add(extended.abstract_size());
                edges_to_add.push((y, extended, new_ref))
            }
        }
        for (edge, y) in self
            .successors_idx(x)?
            .filter(|(_, y)| !exclude.contains(y))
        {
            neighborhood_size = neighborhood_size.saturating_add(1);
            for x_to_y in edge.regexes() {
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
                for x_to_y_suffix in x_to_y.remove_prefix(ext) {
                    edge_size = edge_size.saturating_add(x_to_y_suffix.abstract_size());
                    edges_to_add.push((new_ref, x_to_y_suffix, y))
                }
                for regex_suffix in ext.remove_prefix(x_to_y) {
                    edge_size = edge_size.saturating_add(regex_suffix.abstract_size());
                    edges_to_add.push((y, regex_suffix, new_ref));
                }
            }
        }
        Ok((neighborhood_size, edge_size))
    }

    pub(crate) fn add_edge(
        &mut self,
        source: NodeIndex,
        loc: Loc,
        regex: Regex<Lbl>,
        target: NodeIndex,
    ) -> Result<()> {
        if source == target {
            ensure!(
                regex.is_epsilon(),
                "self edge must be epsilon {:?} --{}--> {:?}",
                source,
                regex,
                target
            );
            self.check_self_epsilon_invariant(source);
            return Ok(());
        }
        if let Some(edge) = self.graph.edge_weight_mut(source, target) {
            edge.insert(loc, Cow::Owned(regex));
        } else {
            let mut edge = Edge::new();
            edge.insert(loc, Cow::Owned(regex));
            self.graph.add_edge(source, target, edge);
        }
        Ok(())
    }

    //**********************************************************************************************
    // Ref API
    //**********************************************************************************************

    pub fn release<M: Meter>(&mut self, r: Ref, meter: &mut M) -> MeterResult<(), M::Error> {
        self.check_invariants();
        meter.visit_nodes(self.nodes.len())?;
        let Some(node) = self.nodes.remove(&r) else {
            bail!("missing ref {:?}", r);
        };
        ensure!(
            self.graph.contains_node(node.node_index()),
            "missing ref {:?} in graph",
            r
        );
        self.graph.remove_node(node.node_index());
        self.check_invariants();
        Ok(())
    }

    pub fn release_all(&mut self) {
        self.nodes.clear();
        self.graph.clear();
        self.fresh_id = 0
    }

    //**********************************************************************************************
    // Query API
    //**********************************************************************************************

    /// Returns the references that extend the specified reference and the path(s) for the extension
    pub fn borrowed_by<M: Meter>(
        &self,
        r: Ref,
        meter: &mut M,
    ) -> MeterResult<BTreeMap<Ref, Paths<Loc, Lbl>>, M::Error> {
        let mut paths = BTreeMap::new();
        let mut nodes_visited = 0usize;
        let mut total_edge_size = 0usize;
        for (edge, s) in self.successors(r)? {
            nodes_visited = nodes_visited.saturating_add(1);
            if r == s {
                // skip self epsilon
                continue;
            }
            total_edge_size = total_edge_size.saturating_add(edge.abstract_size());
            let _prev = paths.insert(s, edge.paths());
            debug_assert!(_prev.is_none());
        }
        meter.visit_nodes(nodes_visited)?;
        meter.visit_edges(total_edge_size)?;
        Ok(paths)
    }

    /// Returns the references that are extended by the specified reference and the path(s) for the
    /// extension
    pub fn borrows_from<M: Meter>(
        &self,
        r: Ref,
        meter: &mut M,
    ) -> MeterResult<BTreeMap<Ref, Paths<Loc, Lbl>>, M::Error> {
        let mut paths = BTreeMap::new();
        let mut nodes_visited = 0usize;
        let mut total_edge_size = 0usize;
        for (p, edge) in self.predecessors(r)? {
            nodes_visited = nodes_visited.saturating_add(1);
            if r == p {
                // skip self epsilon
                continue;
            }
            total_edge_size = total_edge_size.saturating_add(edge.abstract_size());
            let _prev = paths.insert(p, edge.paths());
            debug_assert!(_prev.is_none());
        }
        meter.visit_nodes(nodes_visited)?;
        meter.visit_edges(total_edge_size)?;
        Ok(paths)
    }

    //**********************************************************************************************
    // Joining
    //**********************************************************************************************

    /// Returns true if self changed
    pub fn join<M: Meter>(&mut self, other: &Self, meter: &mut M) -> MeterResult<bool, M::Error> {
        self.check_join_invariants(other);
        let mut total_edge_size_increase = 0usize;
        let self_keys = self.keys().collect::<BTreeSet<_>>();
        let other_all_edges = other
            .graph
            .all_edges()
            .map(|(p_other_idx, e, s_other_idx)| {
                let p = *other.graph.node_weight(p_other_idx).unwrap();
                let s = *other.graph.node_weight(s_other_idx).unwrap();
                (p, e, s)
            });
        for (p, other_edge, s) in
            other_all_edges.filter(|(p, _, s)| self_keys.contains(p) && self_keys.contains(s))
        {
            let p_self_idx = self.node(&p)?.node_index();
            let s_self_idx = self.node(&s)?.node_index();
            let self_edge_size_increase =
                if let Some(self_edge) = self.graph.edge_weight_mut(p_self_idx, s_self_idx) {
                    self_edge.join(other_edge)
                } else {
                    let edge = other_edge.clone();
                    let size = edge.abstract_size();
                    debug_assert!(size > 0);
                    self.graph.add_edge(p_self_idx, s_self_idx, edge);
                    size
                };
            total_edge_size_increase =
                total_edge_size_increase.saturating_add(self_edge_size_increase);
        }
        meter.visit_nodes(self.nodes.len())?;
        meter.visit_edges(total_edge_size_increase)?;
        self.check_invariants();
        Ok(total_edge_size_increase > 0)
    }

    /// Refresh all references (making them no longer canonical)
    pub fn refresh_refs(&mut self) -> Result<()> {
        let nodes = std::mem::take(&mut self.nodes);
        self.fresh_id = 0;
        self.nodes = nodes
            .into_iter()
            .map(|(r, node)| {
                let Some(node_weight_mut) = self.graph.node_weight_mut(node.node_index()) else {
                    bail!("missing ref {:?} in graph", r);
                };
                debug_assert_eq!(r, *node_weight_mut);
                let r_fresh = r.refresh()?;
                *node_weight_mut = r_fresh;
                self.fresh_id = std::cmp::max(self.fresh_id, r_fresh.fresh_id()? + 1);
                Ok((r_fresh, node))
            })
            .collect::<Result<_>>()?;
        debug_assert!(self.is_fresh());
        self.check_invariants();
        Ok(())
    }

    /// Canonicalize all references according to the remapping. This allows graphs to have the same
    /// set of references before being joined.
    pub fn canonicalize(&mut self, remapping: &BTreeMap<Ref, usize>) -> Result<()> {
        let nodes = std::mem::take(&mut self.nodes);
        self.nodes = nodes
            .into_iter()
            .map(|(r, node)| {
                let Some(node_weight_mut) = self.graph.node_weight_mut(node.node_index()) else {
                    bail!("missing ref {:?} in graph", r);
                };
                debug_assert_eq!(r, *node_weight_mut);
                let r_canon = r.canonicalize(remapping)?;
                *node_weight_mut = r_canon;
                Ok((r_canon, node))
            })
            .collect::<Result<_>>()?;
        self.fresh_id = 0;
        debug_assert!(self.is_canonical());
        self.check_invariants();
        Ok(())
    }

    /// Are all references canonical?
    pub fn is_canonical(&self) -> bool {
        self.nodes.keys().all(|r| r.is_canonical())
    }

    /// Are all references fresh?
    pub fn is_fresh(&self) -> bool {
        self.nodes.keys().all(|r| r.is_fresh())
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
            self.check_invariants();
            other.check_invariants();
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
                debug_assert_eq!(self_node.is_mutable(), other_node.is_mutable());
            }
        }
    }

    // checks:
    // - all nodes are canonical or all nodes are fresh
    // - all nodes are present in map and graph
    // - all nodes have a self epsilon
    // - the abstract size is correct
    pub fn check_invariants(&self) {
        #[cfg(debug_assertions)]
        {
            debug_assert_eq!(self.nodes.len(), self.graph.node_count());
            self.graph.check_invariants();
            let mut is_canonical_opt = None;
            let mut node_indices = BTreeSet::new();
            for (&r, node) in &self.nodes {
                match is_canonical_opt {
                    None => is_canonical_opt = Some(r.is_canonical()),
                    Some(is_canonical) => debug_assert_eq!(is_canonical, r.is_canonical()),
                }
                let is_new = node_indices.insert(node.node_index());
                debug_assert!(is_new, "duplicate node index");
            }
            for (p_idx, e, s_idx) in self.graph.all_edges() {
                let p = *self.graph.node_weight(p_idx).unwrap();
                let s = *self.graph.node_weight(s_idx).unwrap();
                debug_assert!(self.nodes.contains_key(&p));
                debug_assert!(self.nodes.contains_key(&s));
                e.check_invariants();
            }
            for node in self.nodes.values() {
                self.check_self_epsilon_invariant(node.node_index());
            }
        }
    }

    pub fn check_self_epsilon_invariant(&self, r: NodeIndex) {
        #[cfg(debug_assertions)]
        {
            let edge_opt = self.graph.edge_weight(r, r);
            debug_assert!(edge_opt.is_some());
            let rs = edge_opt.unwrap().regexes().collect::<Vec<_>>();
            debug_assert_eq!(rs.len(), 1);
            debug_assert!(rs[0].is_epsilon());
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

impl<Loc: Copy, Lbl: Ord + Clone + fmt::Display> fmt::Display for Graph<Loc, Lbl>
where
    Lbl: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct DisplaySuccessors<'a, Loc, Lbl: Ord>(&'a Graph<Loc, Lbl>, Ref);

        impl<Loc: Copy, Lbl: Ord + Clone + fmt::Display> fmt::Display for DisplaySuccessors<'_, Loc, Lbl>
        where
            Lbl: fmt::Display,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let graph = self.0;
                let r = self.1;
                let successors = match graph.successors(r) {
                    Ok(s) => s,
                    Err(e) => return write!(f, "ERROR {r} {:?}", e),
                };
                for (edge, s) in successors {
                    writeln!(f, "\n    {}: {{", s)?;
                    for regex in edge.regexes() {
                        writeln!(f, "        {},", regex)?;
                    }
                    write!(f, "}},")?;
                }
                writeln!(f)?;
                Ok(())
            }
        }

        for (&r, node) in &self.nodes {
            let is_mut = if node.is_mutable() { "mut " } else { "" };
            writeln!(f, "{is_mut}{r}: {{{}}}", DisplaySuccessors(self, r))?;
        }
        Ok(())
    }
}
