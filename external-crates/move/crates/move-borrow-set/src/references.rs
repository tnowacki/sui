// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::paths::*;
use std::{
    cmp,
    collections::BTreeSet,
    fmt::{self, Debug},
    iter,
};

//**************************************************************************************************
// Definitions
//**************************************************************************************************

/// Unique identifier for the reference.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct RefID(pub(crate) usize);

/// Represents the borrow paths and state for a single reference
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Ref<Loc: Copy, Lbl: Clone + Ord, Delta: Clone + Ord> {
    /// true if mutable, false otherwise
    mutable: bool,
    /// Set of paths defining possible locations for this reference
    pub(crate) paths: BorrowPaths<Loc, Lbl, Delta>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// A path + a location where it was added
pub(crate) struct BorrowPaths<Loc, Lbl: Clone + Ord, Delta: Clone + Ord>(
    BTreeSet<BorrowPath<Loc, Lbl, Delta>>,
);

#[derive(Clone)]
/// A path + a location where it was added
pub(crate) struct BorrowPath<Loc, Lbl, Delta> {
    /// The location
    pub(crate) loc: Loc,
    /// The actual path data
    pub(crate) path: Path<Lbl, Delta>,
}

//**************************************************************************************************
// Impls
//**************************************************************************************************

impl RefID {
    pub fn new(id: usize) -> Self {
        Self(id)
    }

    pub fn value(self) -> usize {
        self.0
    }
}

impl<Loc: Copy, Lbl: Clone + Ord, Delta: Clone + Ord> Ref<Loc, Lbl, Delta> {
    pub(crate) fn new(
        mutable: bool,
        paths: impl IntoIterator<Item = BorrowPath<Loc, Lbl, Delta>>,
    ) -> Result<Self, ()> {
        Ok(Self {
            mutable,
            paths: BorrowPaths::new(paths)?,
        })
    }

    pub(crate) fn make_copy(&self, loc: Loc, mutable: bool) -> Self {
        let paths = self.paths.copy_paths(loc);
        Self { mutable, paths }
    }

    pub(crate) fn is_mutable(&self) -> bool {
        self.mutable
    }

    pub(crate) fn paths(&self) -> &BTreeSet<BorrowPath<Loc, Lbl, Delta>> {
        debug_assert!(self.satisfies_invariant());
        &self.paths.0
    }

    #[allow(unused)]
    pub(crate) fn add_path(&mut self, path: BorrowPath<Loc, Lbl, Delta>) {
        debug_assert!(self.satisfies_invariant());
        self.paths.add_path(path);
        debug_assert!(self.satisfies_invariant());
    }

    pub(crate) fn add_paths(
        &mut self,
        paths: impl IntoIterator<Item = BorrowPath<Loc, Lbl, Delta>>,
    ) -> bool {
        debug_assert!(self.satisfies_invariant());
        let changed = self.paths.add_paths(paths);
        debug_assert!(self.satisfies_invariant());
        changed
    }

    pub(crate) fn satisfies_invariant(&self) -> bool {
        !self.paths.is_empty() &&
        // mut ==> no star
        (!self.mutable || !self.paths.0.iter().any(|p| p.path.ends_with_star())) &&
        self.paths.satisfies_invariant()
    }

    pub(crate) fn abstract_size(&self) -> usize {
        self.paths.abstract_size()
    }
}

impl<Loc: Copy, Lbl: Clone + Ord, Delta: Clone + Ord> BorrowPaths<Loc, Lbl, Delta> {
    // // // { p.delta_i.q'.q, p.delta_i.q } = { p.delta_i.q }
    // if let Some(delta_prefix) = path.delta_prefix {
    //     if let Some(other_path) = self.paths
    // }
    // self.paths.insert(path);
    pub(crate) fn new(
        paths: impl IntoIterator<Item = BorrowPath<Loc, Lbl, Delta>>,
    ) -> Result<Self, ()> {
        let mut s = Self(BTreeSet::new());
        s.add_paths(paths);
        if s.is_empty() {
            Err(())
        } else {
            Ok(s)
        }
    }

    pub(crate) fn copy_paths(&self, loc: Loc) -> Self {
        let s = self
            .0
            .iter()
            .map(|path| {
                let mut new_path: BorrowPath<Loc, Lbl, Delta> = path.clone();
                new_path.loc = loc;
                new_path
            })
            .collect();
        Self(s)
    }

    pub(crate) fn add_path(&mut self, path: BorrowPath<Loc, Lbl, Delta>) -> bool {
        // TODO I'm not sure delta reduction is necessary with the rule in extends
        // let contains_delta = path.contains_delta();
        // // { p.delta_i.q'.q, p.delta_i.q } = { p.delta_i.q }
        // if !contains_delta || !self.0.iter().any(|other| other.delta_reduces(&path)) {
        //     // if no delta reduction exists, add the path
        //     self.0.insert(path);
        // }
        self.0.insert(path)
    }

    pub(crate) fn add_paths(
        &mut self,
        paths: impl IntoIterator<Item = BorrowPath<Loc, Lbl, Delta>>,
    ) -> bool {
        let mut changed = false;
        for path in paths {
            let new_path_added = self.add_path(path);
            changed = changed || new_path_added;
        }
        changed
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn satisfies_invariant(&self) -> bool {
        self.0.iter().all(|p| {
            p.satisfies_invariant()
                && self.0.iter().all(|q| {
                    // p != q ==> !p.delta_reduces(q)
                    p == q || !p.delta_reduces(q)
                })
        })
    }

    fn abstract_size(&self) -> usize {
        self.0.iter().map(|p| p.abstract_size()).sum()
    }
}

impl<Loc, Lbl: Clone + Ord, Delta: Clone + Ord> BorrowPath<Loc, Lbl, Delta> {
    pub(crate) fn initial(loc: Loc, lbl: Lbl) -> Self {
        Self {
            loc,
            path: Path::initial(lbl),
        }
    }

    pub(crate) fn extend(&self, loc: Loc, extension: Extension<Lbl, Delta>) -> Self
    where
        Lbl: Clone,
    {
        Self {
            loc,
            path: self.path.extend(extension),
        }
    }

    pub(crate) fn compare<'a>(&self, other: &'a Self) -> Ordering<&'a Lbl, &'a Delta> {
        self.path.compare(&other.path)
    }

    fn contains_delta(&self) -> bool {
        self.path.contains_delta()
    }

    ///  Are we in this reduction situation, { p.delta_i.q'.q, p.delta_i.q } = { p.delta_i.q }?
    /// Where self = p.delta_i.q
    /// And other = p.delta_i.q'.q
    fn delta_reduces(&self, other: &Self) -> bool {
        let reduces = self.path.delta_reduces(&other.path);
        // reduces ==> selfcontains_delta() && other.contains_delta()
        debug_assert!(!reduces || self.contains_delta());
        debug_assert!(!reduces || other.contains_delta());
        reduces
    }

    fn satisfies_invariant(&self) -> bool {
        self.path.satisfies_invariant()
    }

    fn abstract_size(&self) -> usize {
        self.path.abstract_size()
    }
}

//**************************************************************************************************
// traits
//**************************************************************************************************

impl IntoIterator for RefID {
    type Item = RefID;
    type IntoIter = iter::Once<RefID>;
    fn into_iter(self) -> Self::IntoIter {
        iter::once(self)
    }
}

impl<Loc, Lbl: Clone + Ord, Delta: Clone + Ord> PartialEq for BorrowPath<Loc, Lbl, Delta> {
    fn eq(&self, other: &BorrowPath<Loc, Lbl, Delta>) -> bool {
        self.path == other.path
    }
}

impl<Loc, Lbl: Clone + Ord, Delta: Clone + Ord> Eq for BorrowPath<Loc, Lbl, Delta> {}

impl<Loc, Lbl: Clone + Ord, Delta: Clone + Ord> PartialOrd for BorrowPath<Loc, Lbl, Delta> {
    fn partial_cmp(&self, other: &BorrowPath<Loc, Lbl, Delta>) -> Option<cmp::Ordering> {
        self.path.partial_cmp(&other.path)
    }
}

impl<Loc, Lbl: Clone + Ord, Delta: Clone + Ord> Ord for BorrowPath<Loc, Lbl, Delta> {
    fn cmp(&self, other: &BorrowPath<Loc, Lbl, Delta>) -> cmp::Ordering {
        self.path.cmp(&other.path)
    }
}

impl<Loc, Lbl: Clone + Ord + Debug, Delta: Clone + Ord + Debug> Debug
    for BorrowPath<Loc, Lbl, Delta>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.path.fmt(f)
    }
}
