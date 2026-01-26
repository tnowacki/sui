// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use indexmap::IndexMap;
use petgraph::graphmap::DiGraphMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeIndex(u32);

#[derive(Debug, Clone)]
pub struct GraphMap<N, E> {
    next: u32,
    node_weights: IndexMap<NodeIndex, N>,
    inner: DiGraphMap<NodeIndex, E>,
}

impl<N, E> GraphMap<N, E> {
    pub fn new(canonical_reference_capacity: usize) -> Self {
        debug_assert!(canonical_reference_capacity < 512);
        Self {
            next: 0,
            node_weights: IndexMap::with_capacity(canonical_reference_capacity),
            inner: DiGraphMap::with_capacity(
                canonical_reference_capacity,
                canonical_reference_capacity * ((canonical_reference_capacity / 2) + 1),
            ),
        }
    }

    pub fn clear(&mut self) {
        self.next = 0;
        self.node_weights.clear();
        self.inner.clear();
    }

    pub fn minimize(&mut self) {
        let mut max_next = 0;
        for index in self.node_weights.keys() {
            max_next = max_next.max(index.0.saturating_add(1));
        }
        self.next = max_next;
    }

    pub fn node_count(&self) -> usize {
        self.node_weights.len()
    }

    pub fn add_node(&mut self, weight: N) -> NodeIndex {
        let index = NodeIndex(self.next);
        self.next = self.next.checked_add(1).expect("NodeIndex overflow");
        self.node_weights.insert(index, weight);
        self.inner.add_node(index);
        index
    }

    pub fn add_edge(&mut self, from: NodeIndex, weight: E, to: NodeIndex) {
        let prev = self.inner.add_edge(from, to, weight);
        assert!(
            prev.is_none(),
            "Edge from {:?} to {:?} already exists",
            from,
            to
        );
    }

    pub fn contains_node(&self, index: NodeIndex) -> bool {
        self.node_weights.contains_key(&index)
    }

    pub fn node_weight(&self, index: NodeIndex) -> Option<&N> {
        self.node_weights.get(&index)
    }

    pub fn node_weight_mut(&mut self, index: NodeIndex) -> Option<&mut N> {
        self.node_weights.get_mut(&index)
    }

    pub fn contains_edge(&self, from: NodeIndex, to: NodeIndex) -> bool {
        self.inner.contains_edge(from, to)
    }

    pub fn edge_weight(&self, from: NodeIndex, to: NodeIndex) -> Option<&E> {
        self.inner.edge_weight(from, to)
    }

    pub fn edge_weight_mut(&mut self, from: NodeIndex, to: NodeIndex) -> Option<&mut E> {
        self.inner.edge_weight_mut(from, to)
    }

    pub fn remove_node(&mut self, index: NodeIndex) {
        self.node_weights.swap_remove(&index).expect("node missing");
        self.inner.remove_node(index);
    }

    pub fn outgoing_edges(&self, index: NodeIndex) -> impl Iterator<Item = (&E, NodeIndex)> + '_ {
        self.inner
            .edges_directed(index, petgraph::Direction::Outgoing)
            .map(move |(p, s, e)| {
                debug_assert_eq!(index, p);
                (e, s)
            })
    }

    pub fn incoming_edges(&self, index: NodeIndex) -> impl Iterator<Item = (NodeIndex, &E)> + '_ {
        self.inner
            .edges_directed(index, petgraph::Direction::Incoming)
            .map(move |(p, s, e)| {
                debug_assert_eq!(index, s);
                (p, e)
            })
    }

    pub fn all_edges(&self) -> impl Iterator<Item = (NodeIndex, &E, NodeIndex)> + '_ {
        self.inner
            .all_edges()
            .map(|(from, to, weight)| (from, weight, to))
    }

    pub(crate) fn check_invariants(&self) {
        #[cfg(debug_assertions)]
        {
            for (from, _weight, to) in self.all_edges() {
                debug_assert!(
                    self.contains_node(from),
                    "Edge from non-existent node: {:?}",
                    from
                );
                debug_assert!(
                    self.contains_node(to),
                    "Edge to non-existent node: {:?}",
                    to
                );
            }
            for index in self.node_weights.keys() {
                debug_assert!(
                    index.0 < self.next,
                    "NodeIndex {:?} out of bounds (next: {:?})",
                    index,
                    self.next
                );
                debug_assert!(
                    self.inner.contains_node(*index),
                    "NodeIndex {:?} missing from inner graph",
                    index
                );
            }
        }
    }
}
