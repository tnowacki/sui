// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{paths::*, references::*};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Debug, Display},
};

//**************************************************************************************************
// Definitions
//**************************************************************************************************

#[derive(Debug)]
pub struct Conflicts<Loc, Lbl: Ord> {
    /// These refs share a path
    pub equal: BTreeSet<RefID>,
    /// These refs extend the source ref by an unknown offset/lbl
    pub existential: BTreeMap<RefID, Loc>,
    /// These refs extend the source ref by a specified offset/lbl
    pub labeled: BTreeMap<Lbl, BTreeMap<RefID, Loc>>,
}

pub struct Parents<Loc, Lbl: Ord> {
    /// Not quite parents, but exactly equal
    pub equal: BTreeSet<RefID>,
    /// The ref in question extends these refs at an existential
    pub existential: BTreeMap<RefID, Loc>,
    /// The ref in question extends these refs at this label
    pub labeled: BTreeMap<Lbl, BTreeMap<RefID, Loc>>,
}

/// Map of references from their abstract ID to their set of paths.
/// We keep all of the references in this collection to avoid having to walk the stack and locals
/// when performing checks
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RefMap<Loc: Copy, Lbl: Clone + Ord, Delta: Clone + Ord> {
    map: BTreeMap<RefID, Ref<Loc, Lbl, Delta>>,
    next_id: usize,
}

//**************************************************************************************************
// impls
//**************************************************************************************************

impl<Loc, Lbl: Ord> Conflicts<Loc, Lbl> {
    pub fn is_empty(&self) -> bool {
        let Conflicts {
            equal,
            existential,
            labeled,
        } = self;
        equal.is_empty() && existential.is_empty() && labeled.is_empty()
    }
}

impl<Loc, Lbl: Ord> Parents<Loc, Lbl> {
    pub fn is_empty(&self) -> bool {
        let Parents {
            equal,
            existential,
            labeled,
        } = self;
        equal.is_empty() && existential.is_empty() && labeled.is_empty()
    }
}

impl<Loc: Copy, Lbl: Clone + Ord + Display, Delta: Clone + Ord + Display> RefMap<Loc, Lbl, Delta> {
    pub fn new<K: Ord>(
        initial_refs: impl IntoIterator<Item = (K, bool, Loc, Lbl)>,
    ) -> (Self, BTreeMap<K, RefID>) {
        let mut s = Self {
            map: BTreeMap::new(),
            next_id: 0,
        };
        let ref_ids = initial_refs
            .into_iter()
            .map(|(k, mutable, loc, lbl)| {
                let path = BorrowPath::initial(loc, lbl);
                let paths = std::iter::once(path);
                // only errors when the paths are empty, and we have specified a path
                (k, s.add_ref(Ref::new(mutable, paths).unwrap()))
            })
            .collect();
        debug_assert!((0..s.next_id).all(|i| s.map.contains_key(&RefID(i))));
        (s, ref_ids)
    }

    fn add_ref(&mut self, ref_: Ref<Loc, Lbl, Delta>) -> RefID {
        let id = RefID(self.next_id);
        self.next_id += 1;
        let old_value = self.map.insert(id, ref_);
        debug_assert!(old_value.is_none());
        id
    }

    /// Creates a new reference whose paths are an extension of all specified sources.
    /// If sources is empty, the reference will have a single path rooted at the specified label
    pub fn extend_by_label(
        &mut self,
        sources: impl IntoIterator<Item = RefID>,
        loc: Loc,
        mutable: bool,
        extension: Lbl,
    ) -> RefID {
        let mut paths = vec![];
        for source in sources {
            for path in self.map[&source].paths() {
                paths.push(path.extend(loc.clone(), Extension::Label(extension.clone())))
            }
        }
        if paths.is_empty() {
            paths.push(BorrowPath::initial(loc, extension))
        }

        // Only errors when paths is empty, and we just ensured that it is not
        self.add_ref(Ref::new(mutable, paths).unwrap())
    }

    /// Creates a new reference whose paths are an extension of all specified sources. If the source
    /// is an immutable reference, Extension::Star is used instead of the specified delta.
    /// Errors if sources is empty
    pub fn extend_by_delta<'a>(
        &mut self,
        sources: impl IntoIterator<Item = RefID>,
        loc: Loc,
        mutable: bool,
        delta: Delta,
        return_index: usize,
    ) -> Result<RefID, ()> {
        let mut paths = vec![];
        for source in sources {
            let ref_ = &self.map[&source];
            let extension = if ref_.is_mutable() {
                Extension::Delta(delta.clone(), return_index)
            } else {
                Extension::Star
            };
            for path in ref_.paths() {
                paths.push(path.extend(loc.clone(), extension.clone()))
            }
        }
        Ok(self.add_ref(Ref::new(mutable, paths)?))
    }

    pub fn abstract_size(&self) -> usize {
        self.map.values().map(|r| r.abstract_size()).sum()
    }

    //**********************************************************************************************
    // Ref API
    //**********************************************************************************************

    /// checks if the given reference is mutable or not
    pub fn is_mutable(&self, id: RefID) -> bool {
        self.map.get(&id).map(|r| r.is_mutable()).unwrap_or(false)
    }

    pub fn make_copy(&mut self, loc: Loc, id: RefID, mutable: bool) -> RefID {
        let ref_ = self.map[&id].make_copy(loc, mutable);
        self.add_ref(ref_)
    }

    pub fn release(&mut self, id: RefID) {
        self.map.remove(&id);
    }

    //**********************************************************************************************
    // Query API
    //**********************************************************************************************

    pub fn borrowed_by(&self, id: &RefID) -> Conflicts<Loc, Lbl> {
        let mut equal = BTreeSet::new();
        let mut existential = BTreeMap::new();
        let mut labeled = BTreeMap::new();
        for path in self.map[&id].paths() {
            let filtered = self.map.iter().filter(|(other_id, _)| id != *other_id);
            for (other_id, other_ref) in filtered {
                for other_path in other_ref.paths() {
                    match path.compare(other_path) {
                        Ordering::Dissimilar | Ordering::LeftExtendsRight => (),
                        Ordering::Equal => {
                            equal.insert(*other_id);
                        }
                        Ordering::RightExtendsLeft(Extension::Delta(_, _) | Extension::Star) => {
                            existential.insert(*other_id, other_path.loc.clone());
                        }
                        Ordering::RightExtendsLeft(Extension::Label(lbl)) => {
                            labeled
                                .entry(lbl.clone())
                                .or_insert_with(BTreeMap::new)
                                .insert(*other_id, other_path.loc.clone());
                        }
                    }
                }
            }
        }

        debug_assert!(labeled.values().all(|refs| !refs.is_empty()));
        Conflicts {
            equal,
            existential,
            labeled,
        }
    }

    pub fn borrows_from(&self, id: RefID) -> Parents<Loc, Lbl> {
        let mut equal = BTreeSet::new();
        let mut existential = BTreeMap::new();
        let mut labeled = BTreeMap::new();
        for path in self.map[&id].paths() {
            let filtered = self.map.iter().filter(|(other_id, _)| id != **other_id);
            for (other_id, other_ref) in filtered {
                for other_path in other_ref.paths() {
                    match other_path.compare(path) {
                        Ordering::Dissimilar | Ordering::LeftExtendsRight => (),
                        Ordering::Equal => {
                            equal.insert(*other_id);
                        }
                        Ordering::RightExtendsLeft(Extension::Delta(_, _) | Extension::Star) => {
                            existential.insert(*other_id, path.loc);
                        }
                        Ordering::RightExtendsLeft(Extension::Label(lbl)) => {
                            labeled
                                .entry(lbl.clone())
                                .or_insert_with(BTreeMap::new)
                                .insert(*other_id, path.loc);
                        }
                    }
                }
            }
        }

        debug_assert!(labeled.values().all(|refs| !refs.is_empty()));
        Parents {
            equal,
            existential,
            labeled,
        }
    }

    pub fn all_starting_with_label(&self, lbl: &Lbl) -> BTreeMap<RefID, Loc> {
        self.all_starting_with_predicate(|l| l == lbl)
    }

    pub fn all_starting_with_predicate(
        &self,
        mut p: impl FnMut(&Lbl) -> bool,
    ) -> BTreeMap<RefID, Loc> {
        let mut map = BTreeMap::new();
        for (id, ref_) in &self.map {
            for path in ref_.paths() {
                match path.path.first() {
                    Some(Ext::Label(lbl)) if p(lbl) => {
                        map.insert(*id, path.loc);
                    }
                    _ => (),
                }
            }
        }
        map
    }

    //**********************************************************************************************
    // Joining
    //**********************************************************************************************

    /// Returns true if self changed
    pub fn join(&mut self, other: &Self) -> bool {
        debug_assert!(self.satisfies_invariant());
        debug_assert!(other.satisfies_invariant());
        debug_assert!(self.consistent_with(other));
        let mut changed = false;
        for (id, other_ref) in &other.map {
            // this should always be some
            if let Some(r) = self.map.get_mut(&id) {
                let r_changed = r.add_paths(other_ref.paths().iter().cloned());
                changed = changed || r_changed;
            }
        }
        self.reset_next_id();
        debug_assert!(self.satisfies_invariant());
        changed
    }

    pub fn rekey(&mut self, old_to_new: &BTreeMap<RefID, RefID>) {
        let map = std::mem::take(&mut self.map);
        self.map = map
            .into_iter()
            .map(|(id, r)| (*old_to_new.get(&id).unwrap(), r))
            .collect();
        self.reset_next_id()
    }

    fn reset_next_id(&mut self) {
        self.next_id = self.map.keys().map(|id| id.value()).max().unwrap_or(0);
    }

    //**********************************************************************************************
    // Invariants
    //**********************************************************************************************

    pub(crate) fn satisfies_invariant(&self) -> bool {
        self.map.keys().all(|id| id.0 < self.next_id)
            && self.map.values().all(|r| r.satisfies_invariant())
    }

    pub(crate) fn consistent_with(&self, other: &Self) -> bool {
        self.map.keys().all(|id| other.map.contains_key(id))
            && other.map.keys().all(|id| self.map.contains_key(id))
    }

    //**********************************************************************************************
    // Util
    //**********************************************************************************************

    #[allow(dead_code)]
    pub fn display(&self)
    where
        Lbl: std::fmt::Display,
    {
        for (id, ref_) in &self.map {
            let mut_ = if ref_.is_mutable() { "mut " } else { "imm " };
            println!("    {}{}: {{", mut_, id.0);
            for path in ref_.paths() {
                println!("        {},", path.path.to_string());
            }
            println!("    }},")
        }
    }
}

// // Copyright (c) The Diem Core Contributors
// // SPDX-License-Identifier: Apache-2.0

// use crate::{
//     map::{merge_btree_map, BorrowMap},
//     references::*,
// };
// use mirai_annotations::{
//     debug_checked_postcondition, debug_checked_precondition, debug_checked_verify,
// };
// use std::collections::BTreeMap;

// //**************************************************************************************************
// // Definitions
// //**************************************************************************************************

// pub use crate::map::{Conflicts, Parents, QueryFilter};

// #[derive(Clone, Debug, Default)]
// pub struct BorrowSet<Loc: Copy, Instr: Copy + Ord, Lbl: Clone + Ord> {
//     worlds: Vec<BorrowMap<Loc, Instr, Lbl>>,
// }

// //**************************************************************************************************
// // impls
// //**************************************************************************************************

// impl<Loc: Copy, Instr: Copy + Ord + std::fmt::Display, Lbl: Clone + Ord + std::fmt::Display>
//     BorrowSet<Loc, Instr, Lbl>
// {
//     pub fn new<K: Ord>(
//         pinned_initial_refs: impl IntoIterator<Item = (K, bool, Option<(Loc, Lbl)>)>,
//     ) -> (Self, BTreeMap<K, RefID>) {
//         let (map, ids) = BorrowMap::new(pinned_initial_refs);
//         (Self { worlds: vec![map] }, ids)
//     }

//     //**********************************************************************************************
//     // Ref API
//     //**********************************************************************************************

//     /// checks if the given reference is mutable or not
//     pub fn is_mutable(&self, id: RefID) -> bool {
//         debug_checked_precondition!(self.satisfies_invariant());
//         self.worlds[0].is_mutable(id)
//     }

//     pub fn make_copy(&mut self, loc: Loc, id: RefID, mutable: bool) -> RefID {
//         debug_checked_precondition!(self.satisfies_invariant());
//         let mut worlds = self.worlds.iter_mut();
//         let new_id = worlds.next().unwrap().make_copy(loc, id, mutable);
//         for world in worlds {
//             let other_id = world.make_copy(loc, id, mutable);
//             debug_checked_verify!(new_id == other_id)
//         }
//         new_id
//     }

//     pub fn extend_by_label(
//         &mut self,
//         sources: impl IntoIterator<Item = RefID>,
//         loc: Loc,
//         mutable: bool,
//         lbl: Lbl,
//     ) -> RefID {
//         debug_checked_precondition!(self.satisfies_invariant());
//         let sources = sources.into_iter().collect::<Vec<_>>();
//         let mut worlds = self.worlds.iter_mut();
//         let new_id =
//             worlds
//                 .next()
//                 .unwrap()
//                 .extend_by_label(sources.clone(), loc, mutable, lbl.clone());
//         for world in worlds {
//             let other_id = world.extend_by_label(sources.clone(), loc, mutable, lbl.clone());
//             debug_checked_verify!(new_id == other_id)
//         }
//         new_id
//     }

//     pub fn extend_by_unknown(
//         &mut self,
//         sources: impl IntoIterator<Item = RefID>,
//         loc: Loc,
//         mutable: bool,
//         instr: Instr,
//         ref_created_at_instr: usize,
//     ) -> RefID {
//         debug_checked_precondition!(self.satisfies_invariant());
//         let sources = sources.into_iter().collect::<Vec<_>>();
//         let mut worlds = self.worlds.iter_mut();
//         let new_id = worlds.next().unwrap().extend_by_unknown(
//             sources.clone(),
//             loc,
//             mutable,
//             instr,
//             ref_created_at_instr,
//         );
//         for world in worlds {
//             let other_id =
//                 world.extend_by_unknown(sources.clone(), loc, mutable, instr, ref_created_at_instr);
//             debug_checked_verify!(new_id == other_id)
//         }
//         new_id
//     }

//     pub fn move_into_pinned(&mut self, loc: Loc, pinned: RefID, other: RefID) {
//         debug_checked_precondition!(self.satisfies_invariant());
//         for world in &mut self.worlds {
//             world.move_into_pinned(loc, pinned, other)
//         }
//     }

//     pub fn release(&mut self, id: RefID) {
//         debug_checked_precondition!(self.satisfies_invariant());
//         for world in &mut self.worlds {
//             world.release(id)
//         }
//     }

//     //**********************************************************************************************
//     // Query API
//     //**********************************************************************************************

//     pub fn borrowed_by(&self, id: RefID, filter: QueryFilter) -> Conflicts<Loc, Lbl> {
//         debug_checked_precondition!(self.satisfies_invariant());
//         self.worlds
//             .iter()
//             .map(|world| world.borrowed_by(id, filter.clone()))
//             .reduce(|conflicts1, conflicts2| conflicts1.merge(conflicts2))
//             .unwrap()
//     }

//     pub fn borrows_from(&self, id: RefID, filter: QueryFilter) -> Parents<Loc, Lbl> {
//         debug_checked_precondition!(self.satisfies_invariant());
//         self.worlds
//             .iter()
//             .map(|world| world.borrows_from(id, filter.clone()))
//             .reduce(|parents1, parents2| parents1.merge(parents2))
//             .unwrap()
//     }

//     pub fn all_starting_with_label(&self, lbl: &Lbl) -> BTreeMap<RefID, Loc> {
//         debug_checked_precondition!(self.satisfies_invariant());
//         self.worlds
//             .iter()
//             .map(|world| world.all_starting_with_label(lbl))
//             .reduce(|refs1, refs2| merge_btree_map(refs1, refs2))
//             .unwrap()
//     }

//     pub fn all_starting_with_predicate(
//         &self,
//         mut p: impl FnMut(&Lbl) -> bool,
//     ) -> BTreeMap<RefID, Loc> {
//         debug_checked_precondition!(self.satisfies_invariant());
//         self.worlds
//             .iter()
//             .map(|world| world.all_starting_with_predicate(&mut p))
//             .reduce(|refs1, refs2| merge_btree_map(refs1, refs2))
//             .unwrap()
//     }

//     /// Returns true iff a pinned id has no borrows
//     pub fn is_pinned_released(&self, id: RefID) -> bool {
//         debug_checked_precondition!(self.satisfies_invariant());
//         self.worlds[0].is_pinned_released(id)
//     }

//     //**********************************************************************************************
//     // Joining
//     //**********************************************************************************************

//     pub fn covers(&self, other: &Self) -> bool {
//         other.worlds.iter().all(|other_world| {
//             self.worlds
//                 .iter()
//                 .any(|self_world| self_world.covers(other_world))
//         })
//     }

//     pub fn join(&self, other: &Self) -> Self {
//         debug_checked_precondition!(self.satisfies_invariant());
//         debug_checked_precondition!(other.satisfies_invariant());
//         let mut joined = self.clone();
//         let not_covered_worlds = other
//             .worlds
//             .iter()
//             .filter(|other_world| {
//                 !self
//                     .worlds
//                     .iter()
//                     .any(|self_world| self_world.covers(other_world))
//             })
//             .cloned();
//         joined.worlds.extend(not_covered_worlds);
//         for world in &mut joined.worlds {
//             world.set_next_id_after_join()
//         }
//         debug_checked_postcondition!(joined.satisfies_invariant());
//         joined
//     }

//     //**********************************************************************************************
//     // Invariants
//     //**********************************************************************************************

//     pub fn satisfies_invariant(&self) -> bool {
//         if self.worlds.is_empty() {
//             return false;
//         }
//         let world_0 = &self.worlds[0];
//         let mut other_worlds = self.worlds.iter().skip(1);
//         other_worlds.all(|other| world_0.consistent_world(other))
//     }

//     //**********************************************************************************************
//     // Util
//     //**********************************************************************************************

//     #[allow(dead_code)]
//     pub fn display(&self)
//     where
//         Instr: std::fmt::Display,
//         Lbl: std::fmt::Display,
//     {
//         for world in &self.worlds {
//             println!("{{");
//             world.display();
//             println!("}},");
//         }
//     }
// }
