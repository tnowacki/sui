// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::paths::Path;
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
    Canonical(u16),
    Fresh(u16),
}

pub struct Edge<Loc, Lbl> {
    loc: Loc,
    path: Path<Lbl>,
}

pub struct Edges<Loc, Lbl: Ord> {
    edges: BTreeSet<Edge<Loc, Lbl>>,
}

pub struct Node<Loc, Lbl: Ord> {
    successors: BTreeMap<Ref, Edges<Loc, Lbl>>,
    predecessors: BTreeSet<Ref>,
}

//**************************************************************************************************
// impls
//**************************************************************************************************

impl Ref {
    pub fn fresh(id: u16) -> Self {
        Self(Ref_::Fresh(id))
    }
}

impl<Loc, Lbl: Ord> Edges<Loc, Lbl> {
    pub fn new() -> Self {
        Self {
            edges: BTreeSet::new(),
        }
    }
}

impl<Loc, Lbl: Ord> Node<Loc, Lbl> {
    pub fn new() -> Self {
        Self {
            successors: BTreeMap::new(),
            predecessors: BTreeSet::new(),
        }
    }

    pub fn iter_successors(&self) -> impl Iterator<Item = (&Edge<Loc, Lbl>, Ref)> {
        self.successors
            .iter()
            .flat_map(|(r, es)| es.edges.iter().map(|e| (e, *r)))
    }
}

//**************************************************************************************************
// extension
//**************************************************************************************************

impl<Loc, Lbl: Ord> Node<Loc, Lbl> {
    // Returns factored edges
    pub fn add_edge(&mut self, edge: Edge<Loc, Lbl>, target: Ref) -> Vec<(Edge<Loc, Lbl>, Ref)> {
        for (edge, successor) in self.iter_successors() {
            match edge.path.factor(&edge.path) {}
        }
    }
}

//**************************************************************************************************
// canonicalization
//**************************************************************************************************

impl Ref {
    pub fn refresh(&mut self) -> anyhow::Result<()> {
        match self.0 {
            Ref_::Canonical(id) => {
                *self = Self(Ref_::Fresh(id));
                Ok(())
            }
            Ref_::Fresh(_) => {
                anyhow!("should never refresh a fresh ref. it should have been canonicalized")
            }
        }
    }

    pub fn canonicalize(&mut self, remapping: &mut BTreeMap<Ref, u16>) -> anyhow::Result<()> {
        match self.0 {
            Ref_::Canonical(_) => anyhow!("should never canonicalize a cnonical ref"),
            Ref_::Fresh(_) => {
                let Some(id) = remapping.get(self).copied() else {
                    anyhow::bail!("missing remapping for ref {:?}", self)
                };
                *self = Self(Ref_::Canonical(id));
                Ok(())
            }
        }
    }
}

impl<Loc, Lbl: Ord> Edges<Loc, Lbl> {
    pub fn refresh_refs(&mut self) -> anyhow::Result<()> {
        for edge in &mut self.edges {
            edge.refresh_refs()?;
        }
        Ok(())
    }

    pub fn canonicalize_refs(&mut self, remapping: &mut BTreeMap<Ref, u16>) -> anyhow::Result<()> {
        for edge in &mut self.edges {
            edge.canonicalize_refs(remapping)?;
        }
        Ok(())
    }
}

impl<Loc, Lbl: Ord> Node<Loc, Lbl> {
    pub fn refresh_refs(&mut self) -> anyhow::Result<()> {
        let Self {
            successors,
            predecessors,
        } = self;
        *successors = std::mem::take(successors)
            .into_iter()
            .map(|(mut r, mut es)| Ok((r.refresh()?, es.refresh_refs()?)))
            .collect::<anyhow::Result<_>>()?;
        *predecessors = predecessors
            .iter()
            .map(|r| r.refresh())
            .collect::<anyhow::Result<_>>()?;
        Ok(())
    }
}

//**************************************************************************************************
// traits
//**************************************************************************************************

impl<Loc, Lbl: Clone + Ord> PartialEq for Edge<Loc, Lbl> {
    fn eq(&self, other: &Edge<Loc, Lbl>) -> bool {
        self.path == other.path
    }
}
impl<Loc, Lbl: Clone + Ord> Eq for Edge<Loc, Lbl> {}

impl<Loc, Lbl: Clone + Ord> PartialOrd for Edge<Loc, Lbl> {
    fn partial_cmp(&self, other: &Edge<Loc, Lbl>) -> Option<cmp::Ordering> {
        Some(self.path.cmp(&other.path))
    }
}

impl<Loc, Lbl: Clone + Ord> Ord for Edge<Loc, Lbl> {
    fn cmp(&self, other: &Edge<Loc, Lbl>) -> cmp::Ordering {
        self.path.cmp(&other.path)
    }
}

impl<Loc, Lbl: Clone + Ord + Debug> Debug for Edge<Loc, Lbl> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.path.fmt(f)
    }
}
