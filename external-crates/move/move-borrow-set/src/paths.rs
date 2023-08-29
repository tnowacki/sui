// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use std::{collections::BTreeSet, fmt::Display};

#[derive(Debug)]
pub enum Ordering<Lbl, Delta> {
    /// Could be dissimilar, e.g. x.f and x.g
    Dissimilar,
    /// lhs is an extension of rhs
    LeftExtendsRight,
    /// Exactly equal
    Equal,
    /// rhs is an extension of lhs
    /// Note if lhs is an extension of rhs AND rhs is an extension of lhs, `RightExtendsLeft` is
    /// given by convention
    RightExtendsLeft(Extension<Lbl, Delta>),
}

/// A path extension:
/// - A label, indexed by `Lbl`.
/// - A delta, representing an abstract extension (representing 0 or more label extensions).
///   Deltas are indexed by `Delta` and comparable only if the indexes match. Extensions are
///   tracked past the delta.
/// - A star, representing 0 or more label extensions, but not indexed. No extensions are tracked
///   past the star
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Extension<Lbl, Delta> {
    Label(Lbl),
    Delta(Delta, DisjointSet),
    Star,
}

/// An extension, excluding star
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Ext<Lbl, Delta> {
    Label(Lbl),
    Delta(Delta, DisjointSet),
}

/// Used to represent the disjoint set of values within a given delta
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum DisjointSet {
    Immutable,
    Mutable(/* return index */ usize),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Path<Lbl, Delta> {
    path: Vec<Ext<Lbl, Delta>>,
    ends_in_star: bool,
}

impl<Lbl, Delta> Path<Lbl, Delta>
where
    Delta: Ord,
{
    pub fn initial(lbl: Lbl) -> Self {
        Self {
            path: vec![Ext::Label(lbl)],
            ends_in_star: false,
        }
    }

    /// Extend the path by the specified extension. If the extension is `delta_i` and the path
    /// already contains `delta_i`, we truncate to that first `delta_i`. For example:
    /// extend(p.delta_i.q, delta_i) ==> p.delta_i
    pub fn extend(&self, extension: Extension<Lbl, Delta>) -> Self
    where
        Lbl: Clone,
        Delta: Clone,
    {
        debug_assert!(self.satisfies_invariant());
        let mut new_path = self.clone();

        match extension {
            _ if new_path.ends_in_star => (),
            Extension::Label(lbl) => new_path.path.push(Ext::Label(lbl)),
            Extension::Delta(i, o) => {
                if let Some(index) = self.find_delta(&i) {
                    new_path.path.truncate(index + 1);
                    if let Some(Ext::Delta(i2, o2)) = new_path.path.last_mut() {
                        debug_assert!(&i == i2);
                        *o2 = o;
                    } else {
                        debug_assert!(false)
                    }
                } else {
                    new_path.path.push(Ext::Delta(i, o))
                }
            }
            Extension::Star => new_path.ends_in_star = true,
        }
        debug_assert!(new_path.satisfies_invariant());
        new_path
    }

    fn find_delta(&self, delta: &Delta) -> Option<usize> {
        self.path.iter().enumerate().find_map(|(index, ext)| {
            if matches!(ext, Ext::Delta(i, _) if i == delta) {
                Some(index)
            } else {
                None
            }
        })
    }

    // does `self` send `other`
    pub fn compare<'a>(&self /* lhs */, other: &'a Self) -> Ordering<&'a Lbl, &'a Delta>
    where
        Lbl: Eq,
        Delta: Eq,
    {
        debug_assert!(self.satisfies_invariant());
        debug_assert!(other.satisfies_invariant());

        let mut l_iter = self.extensions();
        let mut r_iter = other.extensions();
        let mut cur_l = l_iter.next();
        let mut cur_r = r_iter.next();
        while cur_l.is_some() || cur_r.is_some() {
            use Extension as E;
            match (cur_l, cur_r) {
                (None, None) => return Ordering::Equal,
                (None, Some(e)) => return Ordering::RightExtendsLeft(e),
                (Some(_), None) => return Ordering::LeftExtendsRight,
                // star extends anything
                (_, Some(E::Star)) => return Ordering::RightExtendsLeft(E::Star),
                (Some(E::Star), _) => return Ordering::LeftExtendsRight,
                // deltas overlap with any specified label
                (Some(E::Label(_)), Some(e @ E::Delta(_, _))) => {
                    return Ordering::RightExtendsLeft(e)
                }
                (Some(E::Delta(_, _)), Some(E::Label(_))) => return Ordering::LeftExtendsRight,
                (Some(E::Delta(i, x)), Some(E::Delta(j, y))) => {
                    if i != j {
                        // different deltas, so each path extends each other. As convention
                        // we pick right extends left
                        return Ordering::RightExtendsLeft(E::Delta(j, y));
                    } else if x != y {
                        // same delta, but different offsets, so it is as if we have two
                        // distinct labels
                        return Ordering::Dissimilar;
                    }
                }
                (Some(E::Label(l1)), Some(E::Label(l2))) => {
                    if l1 != l2 {
                        return Ordering::Dissimilar;
                    }
                }
            };
            cur_l = l_iter.next();
            cur_r = r_iter.next();
        }
        assert!(cur_l.is_none());
        assert!(cur_r.is_none());
        Ordering::Equal
    }

    pub(crate) fn first(&self) -> Option<&Ext<Lbl, Delta>> {
        debug_assert!(self.satisfies_invariant());
        let first = self.path.first();
        debug_assert!(first.is_some());
        first
    }

    pub(crate) fn satisfies_invariant(&self) -> bool {
        let mut unique_deltas = true;
        let mut deltas: BTreeSet<&Delta> = BTreeSet::new();
        for ext in &self.path {
            match ext {
                Ext::Label(_) => (),
                Ext::Delta(i, _) => {
                    let is_new = deltas.insert(i);
                    if !is_new {
                        unique_deltas = false;
                        break;
                    }
                }
            }
        }

        !self.path.is_empty() && unique_deltas
    }

    fn extensions<'a>(&'a self) -> impl Iterator<Item = Extension<&'a Lbl, &'a Delta>> {
        let extensions = self.path.iter().map(|e| match e {
            Ext::Label(l) => Extension::Label(l),
            Ext::Delta(i, o) => Extension::Delta(i, *o),
        });
        let star = if self.ends_in_star {
            Some(Extension::Star)
        } else {
            None
        };
        extensions.chain(star)
    }

    pub(crate) fn contains_delta(&self) -> bool {
        self.path.iter().any(|e| matches!(e, Ext::Delta(_, _)))
    }

    ///  Are we in this reduction situation, { p.delta_i.q'.q, p.delta_i.q } = { p.delta_i.q }?
    /// Where self = p.delta_i.q
    /// And other = p.delta_i.q'.q
    pub(crate) fn delta_reduces(&self, other: &Self) -> bool
    where
        Lbl: Eq,
        Delta: Eq,
    {
        let mut l_iter = self.extensions();
        let mut r_iter = other.extensions();
        let mut cur_l = l_iter.next();
        let mut cur_r = r_iter.next();
        let mut hit_eq_delta = false;
        // walk through p.delta_i
        while let (Some(ext1), Some(ext2)) = (&cur_l, &cur_r) {
            if ext1 != ext2 {
                break;
            }
            if matches!(
                (ext1, ext2),
                (Extension::Delta(_, _), Extension::Delta(_, _))
            ) {
                hit_eq_delta = true
            }
            cur_l = l_iter.next();
            cur_r = r_iter.next();
        }
        // no eq delta hit, not a delta reduction
        if !hit_eq_delta {
            return false;
        }
        // walk through q'
        while cur_l != cur_r && cur_r.is_some() {
            cur_r = r_iter.next()
        }
        // walk through q
        loop {
            // if both are none, we have walked through q
            if cur_l.is_none() && cur_r.is_none() {
                break true;
            }
            // if not equal, not a delta reduction
            if cur_l != cur_r {
                break false;
            }
            cur_l = l_iter.next();
            cur_r = r_iter.next();
        }
    }

    pub(crate) fn ends_with_star(&self) -> bool {
        self.ends_in_star
    }

    pub(crate) fn abstract_size(&self) -> usize {
        let star = if self.ends_in_star { 1 } else { 0 };
        self.path.len() + star
    }
}

impl<Lbl, Delta> Display for Ext<Lbl, Delta>
where
    Lbl: Display,
    Delta: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ext::Label(l) => l.fmt(f),
            Ext::Delta(i, o) => {
                write!(f, "delta_{i}_{o}")?;
                Ok(())
            }
        }
    }
}

impl<Lbl, Delta> Display for Path<Lbl, Delta>
where
    Lbl: Display,
    Delta: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut exts = self.path.iter().peekable();
        while let Some(ext) = exts.peek() {
            // display the element
            ext.fmt(f)?;
            // advance the iterator
            exts.next();
            // if there is a next element, add a separator
            if exts.peek().is_some() {
                write!(f, ".")?;
            }
        }
        if self.ends_in_star {
            write!(f, "*")?;
        }
        Ok(())
    }
}

impl Display for DisjointSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DisjointSet::Immutable => write!(f, "imm"),
            DisjointSet::Mutable(i) => write!(f, "{i}"),
        }
    }
}
