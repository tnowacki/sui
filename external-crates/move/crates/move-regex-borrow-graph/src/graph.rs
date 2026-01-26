// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct NodeIndex(u32);

#[derive(Debug, Clone)]
pub struct GraphMap<N, E> {
    next: u32,
    node_weights: BTreeMap<NodeIndex, N>,
    edge_weights: Vec<Option<(NodeIndex, E, NodeIndex)>>,
}

impl<N, E> GraphMap<N, E> {
    pub fn new() -> Self {
        Self {
            next: 0,
            node_weights: BTreeMap::new(),
            edge_weights: Vec::new(),
        }
    }

    pub fn clear(&mut self) {
        self.next = 0;
        self.node_weights.clear();
        self.edge_weights.clear();
    }

    pub fn minimize(&mut self) {
        let mut max_next = 0;
        for index in self.node_weights.keys() {
            max_next = max_next.max(index.0.saturating_add(1));
        }
        self.next = max_next;
        self.edge_weights.retain(|e| e.is_some());
    }

    pub fn node_count(&self) -> usize {
        self.node_weights.len()
    }

    pub fn add_node(&mut self, weight: N) -> NodeIndex {
        let index = NodeIndex(self.next);
        self.next = self.next.checked_add(1).expect("NodeIndex overflow");
        self.node_weights.insert(index, weight);
        index
    }

    pub fn add_edge(&mut self, from: NodeIndex, weight: E, to: NodeIndex) {
        assert!(self.contains_node(from), "From node does not exist");
        assert!(self.contains_node(to), "To node does not exist");
        assert!(!self.contains_edge(from, to), "Edge already exists");
        self.edge_weights.push(Some((from, weight, to)));
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
        self.all_edges().any(|(f, _, t)| f == from && t == to)
    }

    pub fn edge_weight(&self, from: NodeIndex, to: NodeIndex) -> Option<&E> {
        self.all_edges()
            .find(|(f, _, t)| *f == from && *t == to)
            .map(|(_, e, _)| e)
    }

    pub fn edge_weight_mut(&mut self, from: NodeIndex, to: NodeIndex) -> Option<&mut E> {
        self.all_edges_mut()
            .find(|(f, _, t)| *f == from && *t == to)
            .map(|(_, e, _)| e)
    }

    pub fn remove_node(&mut self, index: NodeIndex) {
        self.node_weights.remove(&index).expect("node missing");
        // Remove all edges with this node
        for edge in &mut self.edge_weights {
            if let Some((from, _, to)) = edge {
                if *from == index || *to == index {
                    *edge = None;
                }
            }
        }
    }

    pub fn outgoing_edges(&self, index: NodeIndex) -> impl Iterator<Item = (&E, NodeIndex)> + '_ {
        self.all_edges()
            .filter(move |(from, _, _)| *from == index)
            .map(|(_, e, to)| (e, to))
    }

    pub fn incoming_edges(&self, index: NodeIndex) -> impl Iterator<Item = (NodeIndex, &E)> + '_ {
        self.all_edges()
            .filter(move |(_, _, to)| *to == index)
            .map(|(from, e, _)| (from, e))
    }

    pub fn all_edges(&self) -> impl Iterator<Item = (NodeIndex, &E, NodeIndex)> + '_ {
        self.edge_weights
            .iter()
            .filter_map(|e| e.as_ref().map(|(from, weight, to)| (*from, weight, *to)))
    }

    fn all_edges_mut(&mut self) -> impl Iterator<Item = (NodeIndex, &mut E, NodeIndex)> + '_ {
        self.edge_weights
            .iter_mut()
            .filter_map(|e| e.as_mut().map(|(from, weight, to)| (*from, weight, *to)))
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
            }
        }
    }
}
