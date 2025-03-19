// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    bail,
    collection::{Path, Paths},
    error,
    regex::Regex,
    Result,
};
use itertools::Either;
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

#[derive(Clone)]
struct LocRegex<Loc, Lbl> {
    loc: Loc,
    regex: Regex<Lbl>,
}

#[derive(Clone, Debug)]
struct Edge<Loc, Lbl: Ord> {
    abstract_size: usize,
    regexes: BTreeSet<LocRegex<Loc, Lbl>>,
}

#[derive(Clone, Debug)]
pub struct Node<Loc, Lbl: Ord> {
    ref_: Ref,
    is_mutable: bool,
    abstract_size: usize,
    self_epsilon: Regex<Lbl>,
    successors: BTreeMap<Ref, Edge<Loc, Lbl>>,
    predecessors: BTreeSet<Ref>,
}

//**************************************************************************************************
// impls
//**************************************************************************************************

impl Ref {
    pub(crate) fn fresh(id: usize) -> Self {
        Self(Ref_::Fresh(id))
    }
}

impl<Loc, Lbl: Ord> Edge<Loc, Lbl> {
    fn new() -> Self {
        Self {
            abstract_size: 0,
            regexes: BTreeSet::new(),
        }
    }

    fn abstract_size(&self) -> usize {
        self.abstract_size
    }

    fn regexes(&self) -> impl Iterator<Item = &Regex<Lbl>> {
        self.regexes.iter().map(|r| &r.regex)
    }
}

impl<Loc, Lbl: Ord> Node<Loc, Lbl> {
    pub fn new(r: Ref, is_mutable: bool) -> Self {
        Self {
            ref_: r,
            is_mutable,
            abstract_size: 1,
            self_epsilon: Regex::epsilon(),
            successors: BTreeMap::new(),
            predecessors: BTreeSet::new(),
        }
    }

    pub fn ref_(&self) -> Ref {
        self.ref_
    }

    pub fn is_mutable(&self) -> bool {
        self.is_mutable
    }

    pub fn abstract_size(&self) -> usize {
        self.abstract_size
    }
}

//**************************************************************************************************
// extension
//**************************************************************************************************

impl<Loc, Lbl: Ord> Edge<Loc, Lbl> {
    fn insert(&mut self, r: LocRegex<Loc, Lbl>) -> usize {
        let size = r.regex.abstract_size();
        let was_new = self.regexes.insert(r);
        if was_new {
            self.abstract_size += size;
            size
        } else {
            0
        }
    }
}

impl<Loc, Lbl: Ord> Node<Loc, Lbl> {
    // Returns factored edges
    pub fn add_regex(&mut self, loc: Loc, regex: Regex<Lbl>, successor: Ref) -> usize {
        let r = LocRegex { loc, regex };
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

    pub fn remove_neighbor(&mut self, neighbor: Ref) -> usize {
        let successor_edge_opt = self.successors.remove(&neighbor);
        self.predecessors.remove(&neighbor);
        // size_decrease
        successor_edge_opt.map(|e| e.abstract_size).unwrap_or(0)
    }
}

//**************************************************************************************************
// query
//**************************************************************************************************

impl<Loc: Copy, Lbl: Ord + Clone> Edge<Loc, Lbl> {
    fn paths(&self) -> Paths<Loc, Lbl> {
        self.regexes
            .iter()
            .map(|r| {
                let (labels, ends_in_dot_star) = r.regex.pub_path();
                Path {
                    loc: r.loc,
                    labels,
                    ends_in_dot_star,
                }
            })
            .collect()
    }
}

impl<Loc, Lbl: Ord> Node<Loc, Lbl> {
    pub fn successors(&self) -> impl Iterator<Item = Ref> + '_ {
        std::iter::once(self.ref_).chain(self.successors.keys().copied())
    }

    pub fn predecessors(&self) -> impl Iterator<Item = Ref> + '_ {
        std::iter::once(self.ref_).chain(self.predecessors.iter().copied())
    }

    pub fn is_successor(&self, r: &Ref) -> bool {
        self.successors.contains_key(r)
    }

    pub fn is_predecessor(&self, r: &Ref) -> bool {
        self.predecessors.contains(r)
    }

    pub fn regexes(&self, successor: &Ref) -> Result<impl Iterator<Item = &Regex<Lbl>>> {
        Ok(if successor == &self.ref_ {
            Either::Left(std::iter::once(&self.self_epsilon))
        } else {
            Either::Right(
                self.successors
                    .get(successor)
                    .ok_or_else(|| error!("Missing edge"))?
                    .regexes(),
            )
        })
    }

    pub fn paths(&self, successor: &Ref) -> Result<Paths<Loc, Lbl>>
    where
        Loc: Copy,
        Lbl: Clone,
    {
        Ok(self
            .successors
            .get(successor)
            .ok_or_else(|| error!("Missing edge"))?
            .paths())
    }
}

//**************************************************************************************************
// canonicalization
//**************************************************************************************************

impl Ref {
    pub fn refresh(self) -> Result<Self> {
        match self.0 {
            Ref_::Canonical(id) => Ok(Self(Ref_::Fresh(id))),
            Ref_::Fresh(_) => {
                bail!("should never refresh a fresh ref. it should have been canonicalized")
            }
        }
    }

    pub fn canonicalize(self, remapping: &BTreeMap<Ref, usize>) -> Result<Self> {
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
    pub fn refresh_refs(self) -> Result<Self> {
        let Self {
            ref_,
            is_mutable,
            abstract_size,
            self_epsilon,
            successors,
            predecessors,
        } = self;
        let ref_ = ref_.refresh()?;
        let successors = successors
            .into_iter()
            .map(|(r, es)| Ok((r.refresh()?, es)))
            .collect::<Result<_>>()?;
        let predecessors = predecessors
            .into_iter()
            .map(|r| r.refresh())
            .collect::<Result<_>>()?;
        Ok(Self {
            ref_,
            is_mutable,
            self_epsilon,
            abstract_size,
            successors,
            predecessors,
        })
    }

    pub fn canonicalize(self, remapping: &BTreeMap<Ref, usize>) -> Result<Self> {
        let Self {
            ref_,
            is_mutable,
            abstract_size,
            self_epsilon,
            successors,
            predecessors,
        } = self;
        let ref_ = ref_.canonicalize(remapping)?;
        let successors = successors
            .into_iter()
            .map(|(r, es)| Ok((r.canonicalize(remapping)?, es)))
            .collect::<Result<_>>()?;
        let predecessors = predecessors
            .into_iter()
            .map(|r| r.canonicalize(remapping))
            .collect::<Result<_>>()?;
        Ok(Self {
            ref_,
            is_mutable,
            abstract_size,
            self_epsilon,
            successors,
            predecessors,
        })
    }
}

//**************************************************************************************************
// joining
//**************************************************************************************************

impl<Loc: Copy, Lbl: Ord + Clone> Node<Loc, Lbl> {
    pub fn join(&mut self, other: &Self) -> usize {
        debug_assert_eq!(self.ref_, other.ref_);
        let mut size_increase = 0usize;
        for (s, edge) in &other.successors {
            for LocRegex { loc, regex } in &edge.regexes {
                size_increase =
                    size_increase.saturating_add(self.add_regex(*loc, regex.clone(), *s));
            }
        }
        for p in &other.predecessors {
            self.add_predecessor(*p);
        }
        size_increase
    }
}

//**************************************************************************************************
// invariants
//**************************************************************************************************

impl Ref {
    pub fn is_canonical(&self) -> bool {
        matches!(self.0, Ref_::Canonical(_))
    }
}

impl<Loc, Lbl: Ord> Edge<Loc, Lbl> {
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
    pub fn check_invariant(&self) {
        #[cfg(debug_assertions)]
        {
            let is_canonical = self.ref_.is_canonical();
            for s in self.successors.keys() {
                debug_assert_eq!(is_canonical, s.is_canonical());
            }
            for p in &self.predecessors {
                debug_assert_eq!(is_canonical, p.is_canonical());
            }
            debug_assert!(self.self_epsilon.is_epsilon());
            debug_assert!(!self.successors.contains_key(&self.ref_));
            debug_assert!(!self.predecessors.contains(&self.ref_));
            let mut calculated_size = 1;
            for edge in self.successors.values() {
                edge.check_invariant();
                calculated_size += edge.abstract_size();
            }
            debug_assert_eq!(calculated_size, self.abstract_size);
        }
    }
}

//**************************************************************************************************
// traits
//**************************************************************************************************

impl<Loc, Lbl: PartialEq> PartialEq for LocRegex<Loc, Lbl> {
    fn eq(&self, other: &LocRegex<Loc, Lbl>) -> bool {
        self.regex == other.regex
    }
}
impl<Loc, Lbl: Eq> Eq for LocRegex<Loc, Lbl> {}

impl<Loc, Lbl: PartialOrd> PartialOrd for LocRegex<Loc, Lbl> {
    fn partial_cmp(&self, other: &LocRegex<Loc, Lbl>) -> Option<cmp::Ordering> {
        self.regex.partial_cmp(&other.regex)
    }
}

impl<Loc, Lbl: Ord> Ord for LocRegex<Loc, Lbl> {
    fn cmp(&self, other: &LocRegex<Loc, Lbl>) -> cmp::Ordering {
        self.regex.cmp(&other.regex)
    }
}

impl<Loc, Lbl: Debug> Debug for LocRegex<Loc, Lbl> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.regex.fmt(f)
    }
}

impl fmt::Display for Ref {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Ref_::Canonical(id) => write!(f, "l#{}", id),
            Ref_::Fresh(id) => write!(f, "{}", id),
        }
    }
}

impl<Loc, Lbl: Ord> fmt::Display for Node<Loc, Lbl>
where
    Lbl: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (s, edge) in &self.successors {
            writeln!(f, "    {}: {{", s)?;
            for regex in edge.regexes() {
                writeln!(f, "        {},", regex)?;
            }
            writeln!(f, "    }},")?;
        }
        Ok(())
    }
}
