// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct NodeIndex(usize);

#[derive(Debug, Clone)]
pub struct GraphMap<N, E> {
    next: usize,
    outgoing: BTreeMap<NodeIndex, Node<N, E>>,
    incoming: BTreeMap<NodeIndex, BTreeSet<NodeIndex>>,
}

#[derive(Debug, Clone)]
pub struct Node<N, E> {
    weight: N,
    outgoing: BTreeMap<NodeIndex, E>,
}

impl<N, E> GraphMap<N, E> {
    pub fn new() -> Self {
        Self {
            next: 0,
            outgoing: BTreeMap::new(),
            incoming: BTreeMap::new(),
        }
    }

    pub fn clear(&mut self) {
        self.next = 0;
        self.outgoing.clear();
        self.incoming.clear();
    }

    pub fn minimize_next(&mut self) {
        let mut max_next = 0;
        for index in self.outgoing.keys() {
            max_next = max_next.max(index.0.saturating_add(1));
        }
        self.next = max_next;
    }

    pub fn node_count(&self) -> usize {
        self.outgoing.len()
    }

    pub fn add_node(&mut self, weight: N) -> NodeIndex {
        let index = NodeIndex(self.next);
        self.next = self.next.checked_add(1).expect("NodeIndex overflow");
        self.outgoing.insert(
            index,
            Node {
                weight,
                outgoing: BTreeMap::new(),
            },
        );
        self.incoming.insert(index, BTreeSet::new());
        index
    }

    pub fn add_edge(&mut self, from: NodeIndex, to: NodeIndex, weight: E) {
        let from_node = self.outgoing.get_mut(&from).expect("from node missing");
        let prev = from_node.outgoing.insert(to, weight);
        assert!(
            prev.is_none(),
            "Edge from {:?} to {:?} already exists",
            from,
            to
        );
        let to_incoming = self.incoming.get_mut(&to).expect("to incoming missing");
        let was_new = to_incoming.insert(from);
        assert!(
            was_new,
            "Incoming marker from {:?} to {:?} already exists",
            from, to
        );
    }

    pub fn contains_node(&self, index: NodeIndex) -> bool {
        self.outgoing.contains_key(&index)
    }

    pub fn node_weight(&self, index: NodeIndex) -> Option<&N> {
        self.outgoing.get(&index).map(|node| &node.weight)
    }

    pub fn node_weight_mut(&mut self, index: NodeIndex) -> Option<&mut N> {
        self.outgoing.get_mut(&index).map(|node| &mut node.weight)
    }

    pub fn contains_edge(&self, from: NodeIndex, to: NodeIndex) -> bool {
        self.outgoing
            .get(&from)
            .map_or(false, |node| node.outgoing.contains_key(&to))
    }

    pub fn edge_weight(&self, from: NodeIndex, to: NodeIndex) -> Option<&E> {
        self.outgoing
            .get(&from)
            .and_then(|node| node.outgoing.get(&to))
    }

    pub fn edge_weight_mut(&mut self, from: NodeIndex, to: NodeIndex) -> Option<&mut E> {
        self.outgoing
            .get_mut(&from)
            .and_then(|node| node.outgoing.get_mut(&to))
    }

    pub fn remove_node(&mut self, index: NodeIndex) {
        let node = self.outgoing.remove(&index).expect("node missing");
        // Remove all outgoing edges from this node
        for to in node.outgoing.keys() {
            let to_incoming = self.incoming.get_mut(to).expect("to incoming missing");
            let was_present = to_incoming.remove(&index);
            assert!(was_present, "incoming edge missing");
        }
        // Remove all incoming edges to this node
        let incoming = self.incoming.remove(&index).expect("incoming missing");
        for from in incoming {
            let from_node = self.outgoing.get_mut(&from).expect("from node missing");
            let prev = from_node.outgoing.remove(&index);
            assert!(prev.is_some(), "edge missing");
        }
    }

    pub fn outgoing_edges(&self, index: NodeIndex) -> impl Iterator<Item = (&E, NodeIndex)> + '_ {
        self.outgoing
            .get(&index)
            .unwrap()
            .outgoing
            .iter()
            .map(|(to, e)| (e, *to))
    }

    pub fn incoming_edges(&self, index: NodeIndex) -> impl Iterator<Item = (NodeIndex, &E)> + '_ {
        self.incoming
            .get(&index)
            .unwrap()
            .iter()
            .copied()
            .map(move |from| {
                let from_node = self.outgoing.get(&from).unwrap();
                let e = from_node.outgoing.get(&index).unwrap();
                (from, e)
            })
    }

    pub fn all_edges(&self) -> impl Iterator<Item = (NodeIndex, &E, NodeIndex)> + '_ {
        self.outgoing
            .iter()
            .flat_map(|(from, node)| node.outgoing.iter().map(move |(to, e)| (*from, e, *to)))
    }

    pub(crate) fn check_invariants(&self) {
        #[cfg(debug_assertions)]
        {
            for index in self.outgoing.keys() {
                debug_assert!(
                    self.incoming.contains_key(index),
                    "incoming entry missing for node {:?}",
                    index
                );
            }
            for index in self.incoming.keys() {
                debug_assert!(
                    self.outgoing.contains_key(index),
                    "outgoing entry missing for node {:?}",
                    index
                );
            }
            for (node_index, node) in &self.outgoing {
                for (to_index, _) in &node.outgoing {
                    let to_incoming = self.incoming.get(to_index).unwrap();
                    debug_assert!(
                        to_incoming.contains(node_index),
                        "incoming edge missing from {:?} to {:?}",
                        node_index,
                        to_index
                    );
                }
            }
            for (node_index, incoming) in &self.incoming {
                for from_index in incoming {
                    let from_node = self.outgoing.get(from_index).unwrap();
                    debug_assert!(
                        from_node.outgoing.contains_key(node_index),
                        "outgoing edge missing from {:?} to {:?}",
                        from_index,
                        node_index
                    );
                }
            }

            for index in self.outgoing.keys().copied() {
                debug_assert!(
                    index.0 < self.next,
                    "node index {:?} exceeds next index {:?}",
                    index,
                    self.next
                );
            }
        }
    }
}
