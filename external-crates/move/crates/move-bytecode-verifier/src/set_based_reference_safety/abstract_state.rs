// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

//! This module defines the abstract state for the type and memory safety analysis.
use move_abstract_interpreter::absint::{AbstractDomain, FunctionContext, JoinResult};
use move_binary_format::{
    errors::{PartialVMError, PartialVMResult},
    file_format::{
        CodeOffset, FieldHandleIndex, FunctionDefinitionIndex, LocalIndex, Signature,
        SignatureToken,
    },
    safe_unwrap,
};
use move_borrow_set::{collection::Conflicts, references::RefID};
use move_bytecode_verifier_meter::{Meter, Scope};
use move_core_types::vm_status::StatusCode;
use std::{
    cmp::max,
    collections::{BTreeMap, BTreeSet},
};

type RefMap = move_borrow_set::collection::RefMap<(), Label, Delta>;

/// AbstractValue represents a reference or a non reference value, both on the stack and stored
/// in a local
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum AbstractValue {
    Reference(RefID),
    NonReference,
}

/// ValueKind is used for specifying the type of value expected to be returned
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ValueKind {
    Reference(/* is_mut */ bool),
    NonReference,
}

impl AbstractValue {
    /// checks if self is a reference
    pub fn is_reference(&self) -> bool {
        match self {
            AbstractValue::Reference(_) => true,
            AbstractValue::NonReference => false,
        }
    }

    /// checks if self is a value
    pub fn is_value(&self) -> bool {
        !self.is_reference()
    }

    /// possibly extracts id from self
    pub fn ref_id(&self) -> Option<RefID> {
        match self {
            AbstractValue::Reference(id) => Some(*id),
            AbstractValue::NonReference => None,
        }
    }
}

impl ValueKind {
    pub fn for_signature(s: &Signature) -> Vec<Self> {
        s.0.iter().map(Self::for_type).collect()
    }

    pub fn for_type(s: &SignatureToken) -> Self {
        match s {
            SignatureToken::Reference(_) => Self::Reference(false),
            SignatureToken::MutableReference(_) => Self::Reference(true),
            SignatureToken::Bool
            | SignatureToken::U8
            | SignatureToken::U64
            | SignatureToken::U128
            | SignatureToken::Address
            | SignatureToken::Signer
            | SignatureToken::Vector(_)
            | SignatureToken::Datatype(_)
            | SignatureToken::DatatypeInstantiation(_)
            | SignatureToken::TypeParameter(_)
            | SignatureToken::U16
            | SignatureToken::U32
            | SignatureToken::U256 => Self::NonReference,
        }
    }
}

/// Label is used to specify path extensions
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Label {
    /// A reference that came in as an argument to the function
    Parameter(LocalIndex),
    /// A reference created by borrowing a local variable
    Local(LocalIndex),
    /// A reference that is the field extension of another reference
    Field(FieldHandleIndex),
    /// A reference that was created from a function that had no reference inputs
    /// Either:
    /// - This reference is the result of a native function call, if so it is largely up
    ///   to the native function implmentation to maintain safety
    /// - This is the result of a function that is divergent, if so who cares
    Ethereal(CodeOffset, usize),
}

// Needed for debugging with the borrow graph
impl std::fmt::Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Label::Parameter(i) => write!(f, "parameter#{i}"),
            Label::Local(i) => write!(f, "local#{i}"),
            Label::Field(i) => write!(f, "field#{i}"),
            Label::Ethereal(i, o) => write!(f, "ethereal#{i}_{o}"),
        }
    }
}

/// Delta is used as an abstract set of Labels, containing zero or more labels
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Delta {
    /// Generated via a FunctionCall
    Call(CodeOffset),
}

impl std::fmt::Display for Delta {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Delta::Call(i) => write!(f, "{i}"),
        }
    }
}

pub(crate) const STEP_BASE_COST: u128 = 1;
pub(crate) const JOIN_BASE_COST: u128 = 10;

pub(crate) const PER_SET_ITEM_COST: u128 = 4;

pub(crate) const JOIN_ITEM_COST: u128 = 4;

pub(crate) const ADD_BORROW_COST: u128 = 3;

/// AbstractState is the analysis state over which abstract interpretation is performed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AbstractState {
    current_function: Option<FunctionDefinitionIndex>,
    locals: BTreeMap<LocalIndex, RefID>,
    references: RefMap,
}

impl AbstractState {
    /// create a new abstract state
    pub fn new(simple_calls: bool, function_context: &FunctionContext) -> Self {
        let param_refs = function_context
            .parameters()
            .0
            .iter()
            .enumerate()
            .filter_map(|(idx, ty)| {
                let mutable = match ty {
                    SignatureToken::MutableReference(_) => true,
                    SignatureToken::Reference(_) => false,
                    _ => return None,
                };
                let idx = idx as LocalIndex;
                Some((idx, mutable, (), Label::Parameter(idx)))
            });
        let delta_is_star = simple_calls;
        let (references, locals) = RefMap::new(delta_is_star, param_refs);

        let mut state = AbstractState {
            current_function: function_context.index(),
            locals,
            references,
        };
        state.canonicalize();
        state
    }

    pub(crate) fn local_count(&self) -> usize {
        self.locals.len()
    }

    pub(crate) fn total_reference_size(&self) -> usize {
        self.references.abstract_size()
    }

    pub(crate) fn reference_size(&self, id: RefID) -> usize {
        self.references.reference_size(id)
    }

    fn error(&self, status: StatusCode, offset: CodeOffset) -> PartialVMError {
        PartialVMError::new(status).at_code_offset(
            self.current_function.unwrap_or(FunctionDefinitionIndex(0)),
            offset,
        )
    }

    #[allow(dead_code)]
    pub(crate) fn display(&self) {
        self.references.display();
        println!()
    }

    //**********************************************************************************************
    // Core Predicates
    //**********************************************************************************************

    // Writable if
    // No imm equal
    // No extensions
    fn is_writable(&self, id: RefID, meter: &mut (impl Meter + ?Sized)) -> PartialVMResult<bool> {
        debug_assert!(self.references.is_mutable(id));
        charge_set_size(self.total_reference_size(), meter)?;
        let Conflicts {
            equal: _,
            existential: ext_conflicts,
            labeled: lbl_conflicts,
        } = self.references.borrowed_by(id);
        Ok(ext_conflicts.is_empty() && lbl_conflicts.is_empty())
    }

    // are the references able to be used in a call or return
    fn are_transferrable(
        &self,
        ids: &BTreeSet<RefID>,
        meter: &mut (impl Meter + ?Sized),
    ) -> PartialVMResult<bool> {
        charge_set_size(self.total_reference_size(), meter)?;
        Ok(ids.iter().copied().all(|id| {
            if !self.references.is_mutable(id) {
                return true;
            }
            let Conflicts {
                equal: alias_conflicts,
                existential: ext_conflicts,
                labeled: lbl_conflicts,
            } = self.references.borrowed_by(id);
            ext_conflicts.is_empty()
                && lbl_conflicts.is_empty()
                && alias_conflicts.iter().all(|other| !ids.contains(other))
        }))
    }

    fn is_initial_label_borrowed(
        &self,
        lbl: Label,
        allow_alias: bool,
        meter: &mut (impl Meter + ?Sized),
    ) -> PartialVMResult<bool> {
        charge_set_size(self.total_reference_size(), meter)?;
        let Conflicts {
            equal: alias_conflicts,
            existential: ext_conflicts,
            labeled: lbl_conflicts,
        } = self.references.conflicts_with_initial_lbl(lbl);
        let not_borrowed = ext_conflicts.is_empty()
            && lbl_conflicts.is_empty()
            && (allow_alias || alias_conflicts.is_empty());
        Ok(!not_borrowed)
    }

    /// checks if local#idx is borrowed
    fn is_local_borrowed(
        &self,
        idx: LocalIndex,
        allow_alias: bool,
        meter: &mut (impl Meter + ?Sized),
    ) -> PartialVMResult<bool> {
        self.is_initial_label_borrowed(Label::Local(idx), allow_alias, meter)
    }

    /// checks if any local#_ is borrowed
    fn is_local_local_borrowed(&self, meter: &mut (impl Meter + ?Sized)) -> PartialVMResult<bool> {
        charge_set_size(self.total_reference_size(), meter)?;
        let local_or_global_rooted_refs = self
            .references
            .all_starting_with_predicate(|lbl| matches!(lbl, Label::Local(_)));
        Ok(local_or_global_rooted_refs.is_empty())
    }

    //**********************************************************************************************
    // Instruction Entry Points
    //**********************************************************************************************

    /// destroys local@idx
    pub fn release_value(&mut self, value: AbstractValue) {
        match value {
            AbstractValue::Reference(id) => self.references.release(id),
            AbstractValue::NonReference => (),
        }
    }

    pub fn copy_loc(
        &mut self,
        _offset: CodeOffset,
        local: LocalIndex,
        meter: &mut (impl Meter + ?Sized),
    ) -> PartialVMResult<AbstractValue> {
        match self.locals.get(&local) {
            Some(id) => {
                let id = *id;
                charge_set_size(self.reference_size(id), meter)?;
                let new_id = self
                    .references
                    .make_copy((), id, self.references.is_mutable(id));
                Ok(AbstractValue::Reference(new_id))
            }
            None => Ok(AbstractValue::NonReference),
        }
    }

    pub fn move_loc(
        &mut self,
        offset: CodeOffset,
        local: LocalIndex,
        meter: &mut (impl Meter + ?Sized),
    ) -> PartialVMResult<AbstractValue> {
        match self.locals.remove(&local) {
            Some(id) => Ok(AbstractValue::Reference(id)),
            None if self.is_local_borrowed(local, /* allow alias */ false, meter)? => {
                Err(self.error(StatusCode::MOVELOC_EXISTS_BORROW_ERROR, offset))
            }
            None => Ok(AbstractValue::NonReference),
        }
    }

    pub fn st_loc(
        &mut self,
        offset: CodeOffset,
        local: LocalIndex,
        new_value: AbstractValue,
        meter: &mut (impl Meter + ?Sized),
    ) -> PartialVMResult<()> {
        if self.is_local_borrowed(local, /* allow alias */ true, meter)? {
            return Err(self.error(StatusCode::STLOC_UNSAFE_TO_DESTROY_ERROR, offset));
        }

        if let Some(old_id) = self.locals.remove(&local) {
            self.references.release(old_id);
        }
        if let Some(new_id) = new_value.ref_id() {
            let old = self.locals.insert(local, new_id);
            debug_assert!(old.is_none());
        }
        Ok(())
    }

    pub fn freeze_ref(
        &mut self,
        _offset: CodeOffset,
        id: RefID,
        meter: &mut (impl Meter + ?Sized),
    ) -> PartialVMResult<AbstractValue> {
        charge_set_size(self.reference_size(id), meter)?;
        let frozen_id = self.references.make_copy((), id, false);
        self.references.release(id);
        Ok(AbstractValue::Reference(frozen_id))
    }

    pub fn comparison(
        &mut self,
        _offset: CodeOffset,
        v1: AbstractValue,
        v2: AbstractValue,
    ) -> PartialVMResult<AbstractValue> {
        self.release_value(v1);
        self.release_value(v2);
        Ok(AbstractValue::NonReference)
    }

    pub fn read_ref(&mut self, _offset: CodeOffset, id: RefID) -> PartialVMResult<AbstractValue> {
        self.references.release(id);
        Ok(AbstractValue::NonReference)
    }

    pub fn write_ref(
        &mut self,
        offset: CodeOffset,
        id: RefID,
        meter: &mut (impl Meter + ?Sized),
    ) -> PartialVMResult<()> {
        if !self.is_writable(id, meter)? {
            return Err(self.error(StatusCode::WRITEREF_EXISTS_BORROW_ERROR, offset));
        }

        self.references.release(id);
        Ok(())
    }

    pub fn borrow_loc(
        &mut self,
        _offset: CodeOffset,
        mut_: bool,
        local: LocalIndex,
    ) -> PartialVMResult<AbstractValue> {
        let new_id =
            self.references
                .extend_by_label(std::iter::empty(), (), mut_, Label::Local(local));
        Ok(AbstractValue::Reference(new_id))
    }

    pub fn borrow_field(
        &mut self,
        _offset: CodeOffset,
        mut_: bool,
        id: RefID,
        field: FieldHandleIndex,
        meter: &mut (impl Meter + ?Sized),
    ) -> PartialVMResult<AbstractValue> {
        charge_set_size(self.reference_size(id), meter)?;
        let new_id =
            self.references
                .extend_by_label(std::iter::once(id), (), mut_, Label::Field(field));
        self.references.release(id);
        Ok(AbstractValue::Reference(new_id))
    }

    pub fn vector_op(
        &mut self,
        offset: CodeOffset,
        vector: AbstractValue,
        mut_: bool,
        meter: &mut (impl Meter + ?Sized),
    ) -> PartialVMResult<()> {
        let id = safe_unwrap!(vector.ref_id());
        if mut_ && !self.is_writable(id, meter)? {
            return Err(self.error(StatusCode::VEC_UPDATE_EXISTS_MUTABLE_BORROW_ERROR, offset));
        }
        self.references.release(id);
        Ok(())
    }

    pub fn call(
        &mut self,
        offset: CodeOffset,
        arguments: Vec<AbstractValue>,
        return_: &[ValueKind],
        meter: &mut (impl Meter + ?Sized),
        code: StatusCode,
    ) -> PartialVMResult<Vec<AbstractValue>> {
        // Check mutable references can be transferred
        let all_references_to_borrow_from = arguments
            .iter()
            .filter_map(|v| v.ref_id())
            .collect::<BTreeSet<_>>();
        let mutable_references_to_borrow_from = all_references_to_borrow_from
            .iter()
            .filter(|id| self.references.is_mutable(**id))
            .copied()
            .collect::<BTreeSet<_>>();

        if !self.are_transferrable(&all_references_to_borrow_from, meter)? {
            return Err(self.error(code, offset));
        }
        let return_values: Vec<_> = return_
            .iter()
            .enumerate()
            .map(|(return_index, return_kind)| {
                let (sources, is_mut) = match return_kind {
                    ValueKind::Reference(true) => (&mutable_references_to_borrow_from, true),
                    ValueKind::Reference(false) => (&all_references_to_borrow_from, false),
                    ValueKind::NonReference => return AbstractValue::NonReference,
                };
                let id = if sources.is_empty() {
                    self.references.extend_by_label(
                        std::iter::empty(),
                        (),
                        is_mut,
                        Label::Ethereal(offset, return_index),
                    )
                } else {
                    // only errs when sources is empty, and we just checked for it
                    self.references
                        .extend_by_delta(
                            sources.iter().copied(),
                            (),
                            is_mut,
                            Delta::Call(offset),
                            return_index,
                        )
                        .unwrap()
                };
                AbstractValue::Reference(id)
            })
            .collect();

        // Meter usage of input references
        let total_input_size = all_references_to_borrow_from
            .iter()
            .map(|id| self.reference_size(*id))
            .sum();
        charge_set_size(total_input_size, meter)?;

        // Release input references
        for id in all_references_to_borrow_from {
            self.references.release(id)
        }
        Ok(return_values)
    }

    pub fn ret(
        &mut self,
        offset: CodeOffset,
        values: Vec<AbstractValue>,
        meter: &mut (impl Meter + ?Sized),
    ) -> PartialVMResult<()> {
        // release all local variables
        for (_, id) in std::mem::take(&mut self.locals) {
            self.references.release(id)
        }

        // Check that no local or global is borrowed
        if !self.is_local_local_borrowed(meter)? {
            return Err(self.error(
                StatusCode::UNSAFE_RET_LOCAL_OR_RESOURCE_STILL_BORROWED,
                offset,
            ));
        }

        // Check mutable references can be transferred
        let returned_refs: BTreeSet<RefID> = values.iter().filter_map(|v| v.ref_id()).collect();
        if !self.are_transferrable(&returned_refs, meter)? {
            return Err(self.error(StatusCode::RET_BORROWED_MUTABLE_REFERENCE_ERROR, offset));
        }
        for id in returned_refs {
            self.references.release(id)
        }

        Ok(())
    }

    pub fn abort(&mut self) {
        // release all references
        self.locals.clear();
        self.references.release_all()
    }

    //**********************************************************************************************
    // Abstract Interpreter Entry Points
    //**********************************************************************************************

    pub fn canonicalize(&mut self) {
        self.check_invariant();
        let mut old_to_new = BTreeMap::new();
        for (local, old_id) in &self.locals {
            let new_id = RefID::new(*local as usize);
            let old_value = old_to_new.insert(*old_id, new_id);
            assert!(old_value.is_none());
        }
        self.references.rekey(&old_to_new);
        for old in self.locals.values_mut() {
            *old = old_to_new[old];
        }
    }

    pub fn is_canonical(&self) -> bool {
        let references_ids: BTreeSet<_> = self.references.keys().collect();
        let mut locals_ids = BTreeSet::new();
        self.locals
            .iter()
            .all(|(l, id)| (*l as usize) == id.value())
            && self.locals.values().all(|id| locals_ids.insert(*id))
            && locals_ids == references_ids
    }

    pub fn check_invariant(&self) {
        #[cfg(debug_assertions)]
        {
            let references_ids: BTreeSet<_> = self.references.keys().collect();
            let mut locals_ids = BTreeSet::new();
            debug_assert!(self.locals.values().all(|id| locals_ids.insert(id)));
            debug_assert!(self.locals.values().all(|id| references_ids.contains(id)));
            self.references.check_invariant()
        }
    }

    pub fn join_(&self, other: &Self) -> (Self, /* changed */ bool) {
        assert_eq!(self.current_function, other.current_function);
        self.check_invariant();
        other.check_invariant();
        assert!(self.is_canonical());
        assert!(other.is_canonical());
        let mut self_references = self.references.clone();
        let mut other_references = other.references.clone();
        let mut joined_locals = BTreeMap::new();
        for (local, id) in &self.locals {
            let id = *id;
            if !other.locals.contains_key(local) {
                self_references.release(id);
            } else {
                assert_eq!(id, *other.locals.get(local).unwrap());
                joined_locals.insert(*local, id);
            }
        }
        for (local, id) in &other.locals {
            let id = *id;
            if !self.locals.contains_key(&local) {
                other_references.release(id)
            } else {
                assert_eq!(id, *joined_locals.get(&local).unwrap())
            }
        }

        let (joined_references, changed) = {
            let changed = self_references.join(&other_references);
            (self_references, changed)
        };
        let current_function = self.current_function;

        let joined = Self {
            current_function,
            locals: joined_locals,
            references: joined_references,
        };
        assert!(joined.is_canonical());
        (joined, changed)
    }
}

impl AbstractDomain for AbstractState {
    /// attempts to join state to self and returns the result
    fn join(
        &mut self,
        state: &AbstractState,
        meter: &mut (impl Meter + ?Sized),
    ) -> PartialVMResult<JoinResult> {
        meter.add(Scope::Function, JOIN_BASE_COST)?;
        let self_size = self.total_reference_size();
        let state_size = state.total_reference_size();
        let (joined, join_changed) = Self::join_(self, state);
        meter.add(Scope::Function, JOIN_BASE_COST)?;
        let max_size = max(max(self_size, state_size), joined.total_reference_size());
        charge_join(self_size, state_size, meter)?;
        charge_set_size(max_size, meter)?;
        let locals_changed = self.locals.len() != joined.locals.len();
        if locals_changed || join_changed {
            *self = joined;
            Ok(JoinResult::Changed)
        } else {
            Ok(JoinResult::Unchanged)
        }
    }
}

fn charge_set_size(size: usize, meter: &mut (impl Meter + ?Sized)) -> PartialVMResult<()> {
    let size = max(size, 1);
    meter.add_items(Scope::Function, PER_SET_ITEM_COST, size)
}

fn charge_join(
    size1: usize,
    size2: usize,
    meter: &mut (impl Meter + ?Sized),
) -> PartialVMResult<()> {
    let size1 = max(size1, 1);
    let size2 = max(size2, 1);
    let size = size1.saturating_add(size2);
    meter.add_items(Scope::Function, JOIN_ITEM_COST, size)
}
