// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::regex;
use anyhow::{anyhow, bail};
use std::{
    cmp,
    collections::{BTreeMap, BTreeSet},
    fmt::{self, Debug},
};

//**************************************************************************************************
// Definitions
//**************************************************************************************************

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Ref(Ref_);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Ref_ {
    Canonical(usize),
    Fresh(usize),
}

pub struct Regex<Loc, Lbl> {
    loc: Loc,
    regex: regex::Regex<Lbl>,
}

pub struct Edge<Loc, Lbl: Ord> {
    abstract_size: usize,
    regexes: BTreeSet<Regex<Loc, Lbl>>,
}

pub struct Node<Loc, Lbl: Ord> {
    abstract_size: usize,
    successors: BTreeMap<Ref, Edge<Loc, Lbl>>,
    predecessors: BTreeSet<Ref>,
}

//**************************************************************************************************
// impls
//**************************************************************************************************

impl Ref {
    pub fn fresh(id: usize) -> Self {
        Self(Ref_::Fresh(id))
    }
}

impl<Loc, Lbl: Ord> Edge<Loc, Lbl> {
    pub fn new() -> Self {
        Self {
            abstract_size: 0,
            regexes: BTreeSet::new(),
        }
    }

    pub fn abstract_size(&self) -> usize {
        self.abstract_size
    }

    pub fn regexes(&self) -> impl Iterator<Item = &regex::Regex<Lbl>> {
        self.regexes.iter().map(|r| &r.regex)
    }

    pub fn insert(&mut self, r: Regex<Loc, Lbl>) -> usize {
        let size = r.regex.abstract_size();
        let was_new = self.regexes.insert(r);
        if was_new {
            self.abstract_size += size;
            size
        } else {
            0
        }
    }

    pub fn check_invariant(&self) {
        #[cfg(debug_assertions)]
        {
            let mut calculated_size = 0;
            for r in &self.regexes {
                calculated_size += r.regex.abstract_size();
            }
            debug_assert_eq!(calculated_size, self.abstract_size);
            debug_assert!(!self.regexes.is_empty());
        }
    }
}

impl<Loc, Lbl: Ord> Node<Loc, Lbl> {
    pub fn new() -> Self {
        Self {
            abstract_size: 1,
            successors: BTreeMap::new(),
            predecessors: BTreeSet::new(),
        }
    }

    pub fn abstract_size(&self) -> usize {
        self.abstract_size
    }

    pub fn successors(&self) -> impl Iterator<Item = Ref> + '_ {
        self.successors.keys().copied()
    }

    pub fn predecessors(&self) -> impl Iterator<Item = Ref> + '_ {
        self.predecessors.iter().copied()
    }

    pub fn is_successor(&self, r: &Ref) -> bool {
        self.successors.contains_key(r)
    }

    pub fn is_predecessor(&self, r: &Ref) -> bool {
        self.predecessors.contains(r)
    }

    pub fn remove_neighbor(&mut self, neighbor: Ref) -> usize {
        let successor_edge_opt = self.successors.remove(&neighbor);
        self.predecessors.remove(&neighbor);
        // size_decrease
        successor_edge_opt.map(|e| e.abstract_size).unwrap_or(0)
    }

    pub fn edge(&self, successor: &Ref) -> anyhow::Result<&Edge<Loc, Lbl>> {
        self.successors
            .get(successor)
            .ok_or_else(|| anyhow!("Missing edge"))
    }
}

//**************************************************************************************************
// extension
//**************************************************************************************************

impl<Loc, Lbl: Ord> Node<Loc, Lbl> {
    // Returns factored edges
    pub fn add_regex(&mut self, loc: Loc, regex: regex::Regex<Lbl>, successor: Ref) -> usize {
        let r = Regex { loc, regex };
        let size_increase = self
            .successors
            .entry(successor)
            .or_insert_with(|| Edge::new())
            .insert(r);
        self.abstract_size += size_increase;
        size_increase
    }

    pub fn add_predecessor(&mut self, predecessor: Ref) {
        self.predecessors.insert(predecessor);
    }
}

//**************************************************************************************************
// canonicalization
//**************************************************************************************************

impl Ref {
    pub fn refresh(self) -> anyhow::Result<Self> {
        match self.0 {
            Ref_::Canonical(id) => Ok(Self(Ref_::Fresh(id))),
            Ref_::Fresh(_) => {
                bail!("should never refresh a fresh ref. it should have been canonicalized")
            }
        }
    }

    pub fn canonicalize(self, remapping: &mut BTreeMap<Ref, usize>) -> anyhow::Result<Self> {
        match self.0 {
            Ref_::Canonical(_) => bail!("should never canonicalize a cnonical ref"),
            Ref_::Fresh(_) => {
                let Some(id) = remapping.get(&self).copied() else {
                    bail!("missing remapping for ref {:?}", self)
                };
                Ok(Self(Ref_::Canonical(id)))
            }
        }
    }
}

impl<Loc, Lbl: Ord> Node<Loc, Lbl> {
    pub fn refresh_refs(self) -> anyhow::Result<Self> {
        let Self {
            abstract_size,
            successors,
            predecessors,
        } = self;
        let successors = successors
            .into_iter()
            .map(|(r, es)| Ok((r.refresh()?, es)))
            .collect::<anyhow::Result<_>>()?;
        let predecessors = predecessors
            .into_iter()
            .map(|r| r.refresh())
            .collect::<anyhow::Result<_>>()?;
        Ok(Self {
            abstract_size,
            successors,
            predecessors,
        })
    }

    pub fn canonicalize(self, remapping: &mut BTreeMap<Ref, usize>) -> anyhow::Result<Self> {
        let Self {
            abstract_size,
            successors,
            predecessors,
        } = self;
        let successors = successors
            .into_iter()
            .map(|(r, es)| Ok((r.canonicalize(remapping)?, es)))
            .collect::<anyhow::Result<_>>()?;
        let predecessors = predecessors
            .into_iter()
            .map(|r| r.canonicalize(remapping))
            .collect::<anyhow::Result<_>>()?;
        Ok(Self {
            abstract_size,
            successors,
            predecessors,
        })
    }
}

//**************************************************************************************************
// traits
//**************************************************************************************************

impl<Loc, Lbl: PartialEq> PartialEq for Regex<Loc, Lbl> {
    fn eq(&self, other: &Regex<Loc, Lbl>) -> bool {
        self.regex == other.regex
    }
}
impl<Loc, Lbl: Eq> Eq for Regex<Loc, Lbl> {}

impl<Loc, Lbl: PartialOrd> PartialOrd for Regex<Loc, Lbl> {
    fn partial_cmp(&self, other: &Regex<Loc, Lbl>) -> Option<cmp::Ordering> {
        self.regex.partial_cmp(&other.regex)
    }
}

impl<Loc, Lbl: Ord> Ord for Regex<Loc, Lbl> {
    fn cmp(&self, other: &Regex<Loc, Lbl>) -> cmp::Ordering {
        self.regex.cmp(&other.regex)
    }
}

impl<Loc, Lbl: Debug> Debug for Regex<Loc, Lbl> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.regex.fmt(f)
    }
}
