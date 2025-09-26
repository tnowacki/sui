// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::rc::Rc;

use crate::execution_mode::ExecutionMode;
use crate::programmable_transactions::execution::check_private_generics;
use crate::sp;
use crate::static_programmable_transactions::{env::Env, loading::ast::Type, typing::ast as T};
use move_binary_format::{CompiledModule, file_format::Visibility};
use sui_types::{
    error::{ExecutionError, ExecutionErrorKind, command_argument_error},
    execution_status::CommandArgumentError,
};

/// Is hot for entry verifier rules. A non-public entry function cannot take in any hot arguments.
#[derive(Clone, Copy)]
enum Temperature {
    AlwaysHot,
    Count(usize),
}

#[derive(Clone)]
struct Clique_ {
    id: usize,
    temp: Rc<RefCell<Temperature>>,
}

type CliqueID = usize;

#[derive(Clone)]
struct Clique(Rc<RefCell<Clique_>>);

#[must_use]
enum Value {
    // We don't want to entangle the TxContext with cliques
    TxContext,
    Normal {
        clique: Clique,
        /// If the value contributes to the hot-value count in its clique
        heats: bool,
    },
}

struct Cliques(usize);

struct Context {
    cliques: Cliques,
    tx_context: Option<Value>,
    gas_coin: Option<Value>,
    objects: Vec<Option<Value>>,
    pure: Vec<Option<Value>>,
    receiving: Vec<Option<Value>>,
    results: Vec<Vec<Option<Value>>>,
}

impl Temperature {
    fn add(self, other: Temperature) -> Result<Temperature, ExecutionError> {
        Ok(match (self, other) {
            (Temperature::AlwaysHot, _) | (_, Temperature::AlwaysHot) => Temperature::AlwaysHot,
            (Temperature::Count(a), Temperature::Count(b)) => Temperature::Count(
                a.checked_add(b)
                    .ok_or_else(|| make_invariant_violation!("Hot count overflow"))?,
            ),
        })
    }

    fn sub(self, b: usize) -> Result<Temperature, ExecutionError> {
        Ok(match self {
            Temperature::AlwaysHot => Temperature::AlwaysHot,
            Temperature::Count(a) => Temperature::Count(
                a.checked_sub(b)
                    .ok_or_else(|| make_invariant_violation!("Hot count cannot go negative"))?,
            ),
        })
    }

    fn is_hot(&self) -> bool {
        match self {
            Temperature::AlwaysHot => true,
            Temperature::Count(c) => *c > 0,
        }
    }
}

impl Clique_ {
    fn temp(&self) -> Temperature {
        *self.temp.borrow()
    }
}

impl Clique {
    fn id(&self) -> CliqueID {
        self.0.borrow().id
    }

    fn temp(&self) -> Temperature {
        self.0.borrow().temp()
    }

    fn modify_temp(
        &self,
        f: impl FnOnce(Temperature) -> Result<Temperature, ExecutionError>,
    ) -> Result<(), ExecutionError> {
        let cur = self.temp();
        let new = f(cur)?;
        *self.0.borrow_mut().temp.borrow_mut() = new;
        Ok(())
    }

    fn forward(self, to: &Clique) -> Result<(), ExecutionError> {
        // add temperature into `to`
        to.modify_temp(|to_temp| to_temp.add(self.temp()))?;
        // point `self` to `to`
        *self.0.borrow_mut() = to.0.borrow().clone();
        Ok(())
    }

    fn is_hot(&self) -> bool {
        self.temp().is_hot()
    }

    fn mark_always_hot(&self) -> Result<(), ExecutionError> {
        self.modify_temp(|_| Ok(Temperature::AlwaysHot))
    }
}

impl Cliques {
    fn new() -> Self {
        Self(0)
    }

    fn next(&mut self) -> Clique {
        let id = self.0;
        self.0 += 1;
        let data = Clique_ {
            id,
            temp: Rc::new(RefCell::new(Temperature::Count(0))),
        };
        Clique(Rc::new(RefCell::new(data)))
    }

    fn merge(&mut self, cliques: Vec<Clique>) -> Result<Clique, ExecutionError> {
        let mut unique = {
            let mut seen = BTreeSet::new();
            let mut unique = vec![];
            for c in cliques {
                let is_new = seen.insert(c.id());
                if is_new {
                    unique.push(c);
                }
            }
            unique
        };
        Ok(match unique.len() {
            0 => self.next(),
            1 => unique.pop().unwrap(),
            _ => {
                let merged = self.next();
                for c in unique {
                    c.forward(&merged)?;
                }
                merged
            }
        })
    }

    fn input_value(&mut self) -> Value {
        let clique = self.next();
        Value::Normal {
            clique,
            heats: false,
        }
    }

    fn new_value(&mut self, clique: Clique, heats: bool) -> Result<Value, ExecutionError> {
        if heats {
            clique.modify_temp(|t| t.add(Temperature::Count(1)))?;
        }
        Ok(Value::Normal { clique, heats })
    }

    fn release_value(&mut self, value: Value) -> Result<Option<Clique>, ExecutionError> {
        let (clique, heats) = match value {
            Value::TxContext => return Ok(None),
            Value::Normal { clique, heats } => (clique, heats),
        };
        if heats {
            clique.modify_temp(|t| t.sub(1))?;
        }
        Ok(Some(clique))
    }
}

impl Context {
    fn new(txn: &T::Transaction) -> Self {
        let mut cliques = Cliques::new();
        let tx_context = Some(Value::TxContext);
        let gas_coin = Some(cliques.input_value());
        let objects = (0..txn.objects.len())
            .map(|_| Some(cliques.input_value()))
            .collect();
        let pure = (0..txn.pure.len())
            .map(|_| Some(cliques.input_value()))
            .collect();
        let receiving = (0..txn.receiving.len())
            .map(|_| Some(cliques.input_value()))
            .collect();
        Self {
            tx_context,
            cliques,
            gas_coin,
            objects,
            pure,
            receiving,
            results: vec![],
        }
    }

    fn location(&mut self, location: &T::Location) -> &mut Option<Value> {
        match location {
            T::Location::GasCoin => &mut self.gas_coin,
            T::Location::ObjectInput(i) => &mut self.objects[*i as usize],
            T::Location::PureInput(i) => &mut self.pure[*i as usize],
            T::Location::ReceivingInput(i) => &mut self.receiving[*i as usize],
            T::Location::Result(i, j) => &mut self.results[*i as usize][*j as usize],
            T::Location::TxContext => &mut self.tx_context,
        }
    }

    fn usage(&mut self, usage: &T::Usage) -> Result<Value, ExecutionError> {
        match usage {
            T::Usage::Move(location) => {
                let Some(value) = self.location(location).take() else {
                    invariant_violation!("Move of moved value");
                };
                Ok(value)
            }
            T::Usage::Copy { location, .. } => {
                let Some(location) = self.location(location).as_ref() else {
                    invariant_violation!("Copy of moved value");
                };
                let (clique, heats) = match location {
                    Value::TxContext => {
                        invariant_violation!("Cannot copy TxContext");
                    }
                    Value::Normal { clique, heats } => (clique.clone(), *heats),
                };
                self.cliques.new_value(clique, heats)
            }
        }
    }

    fn argument(&mut self, sp!(_, (arg, _ty)): &T::Argument) -> Result<Value, ExecutionError> {
        Ok(match arg {
            T::Argument__::Use(usage) => self.usage(usage)?,
            T::Argument__::Read(usage) | T::Argument__::Freeze(usage) => {
                // This is equivalent to just the `usage` but we go through the steps of
                // creating a new value and releasing the old one for "correctness" and clarity
                let value = self.usage(usage)?;
                let (clique, heats) = match &value {
                    Value::TxContext => {
                        invariant_violation!("Cannot read or freeze TxContext");
                    }
                    Value::Normal { clique, heats } => (clique.clone(), *heats),
                };
                let new_value = self.cliques.new_value(clique, heats)?;
                self.cliques.release_value(value)?;
                new_value
            }
            T::Argument__::Borrow(_, location) => {
                let Some(location) = self.location(location).as_ref() else {
                    invariant_violation!("Borrow of moved value");
                };
                let (clique, heats) = match location {
                    Value::TxContext => {
                        // no clique/heat for TxContext
                        return Ok(Value::TxContext);
                    }
                    Value::Normal { clique, heats } => (clique.clone(), *heats),
                };
                // Create a new value (representing the reference to this value)
                // that is in the same clique and has the same heat
                self.cliques.new_value(clique, heats)?
            }
        })
    }
}

/// Checks the following
/// - entry function taint rules
///   - `entry` function cannot have "hot" arguments
///   - All commands propagate "hotness"
///   - Move calls "heat" their "outputs" (mutable arguments and return values) if
///     - they return a hot potato (no `drop` and no `store`)
/// - valid visibility for move function calls
///   - Can be disabled under certain execution modes
/// - private generics rules for move function calls
/// - no references returned from move calls
///    - Can be disabled under certain execution modes
pub fn verify<Mode: ExecutionMode>(env: &Env, txn: &T::Transaction) -> Result<(), ExecutionError> {
    let mut context = Context::new(txn);
    for c in &txn.commands {
        dbg!(c);
        let result_values = command::<Mode>(env, &mut context, c)
            .map_err(|e| e.with_command_index(c.idx as usize))?;
        assert_invariant!(
            result_values.len() == c.value.result_type.len(),
            "result length mismatch"
        );
        context
            .results
            .push(result_values.into_iter().map(Some).collect());
    }
    Ok(())
}

fn command<Mode: ExecutionMode>(
    env: &Env,
    context: &mut Context,
    sp!(_, c): &T::Command,
) -> Result<Vec<Value>, ExecutionError> {
    let T::Command_ {
        command,
        result_type,
        drop_values: _,
        consumed_shared_objects,
    } = c;
    let argument_cliques = arguments(env, context, command.arguments())?;
    match command {
        T::Command__::MoveCall(call) => move_call::<Mode>(env, context, call, &argument_cliques)?,
        T::Command__::TransferObjects(_, _)
        | T::Command__::SplitCoins(_, _, _)
        | T::Command__::MergeCoins(_, _, _)
        | T::Command__::MakeMoveVec(_, _)
        | T::Command__::Publish(_, _, _)
        | T::Command__::Upgrade(_, _, _, _, _) => (),
    }
    let merged_clique = context
        .cliques
        .merge(argument_cliques.into_iter().map(|(_, c)| c).collect())?;

    let consumes_shared_objects = !consumed_shared_objects.is_empty();
    if consumes_shared_objects {
        merged_clique.mark_always_hot()?;
    }
    result_type
        .iter()
        .map(|ty| {
            let heats = is_hot_potato_return_type(ty);
            context.cliques.new_value(merged_clique.clone(), heats)
        })
        .collect()
}

/// Returns the index of the first hot argument, if any
fn arguments<'a>(
    env: &Env,
    context: &mut Context,
    args: impl IntoIterator<Item = &'a T::Argument>,
) -> Result<Vec<(u16, Clique)>, ExecutionError> {
    let mut arguments = vec![];
    for arg in args {
        if let Some(clique) = argument(env, context, arg)? {
            arguments.push((arg.idx, clique));
        }
    }
    Ok(arguments)
}

fn argument(
    _env: &Env,
    context: &mut Context,
    arg: &T::Argument,
) -> Result<Option<Clique>, ExecutionError> {
    let value = context.argument(arg)?;
    context.cliques.release_value(value)
}

/// Checks a move call for
/// - valid signature (no references in return type)
/// - valid visibility
/// - private generics rules
/// - if entry, no hot arguments
///
/// Returns true iff any return type is a hot potato
fn move_call<Mode: ExecutionMode>(
    env: &Env,
    _context: &mut Context,
    call: &T::MoveCall,
    argument_cliques: &[(u16, Clique)],
) -> Result<(), ExecutionError> {
    let T::MoveCall {
        function,
        arguments: _,
    } = call;
    check_signature::<Mode>(function)?;
    check_private_generics(&function.runtime_id, function.name.as_ident_str())?;
    let (vis, is_entry) = check_visibility::<Mode>(env, function)?;
    // check rules around hot arguments and entry functions
    if is_entry && matches!(vis, Visibility::Private) && !Mode::allow_arbitrary_values() {
        if let Some((idx, _)) = argument_cliques.iter().find(|(_, c)| c.is_hot()) {
            return Err(command_argument_error(
                CommandArgumentError::InvalidArgumentToPrivateEntryFunction,
                *idx as usize,
            ));
        }
    }
    Ok(())
}

fn check_signature<Mode: ExecutionMode>(
    function: &T::LoadedFunction,
) -> Result<(), ExecutionError> {
    fn check_return_type<Mode: ExecutionMode>(
        idx: usize,
        return_type: &T::Type,
    ) -> Result<(), ExecutionError> {
        if let Type::Reference(_, _) = return_type {
            if !Mode::allow_arbitrary_values() {
                return Err(ExecutionError::from_kind(
                    ExecutionErrorKind::InvalidPublicFunctionReturnType { idx: idx as u16 },
                ));
            }
        }
        Ok(())
    }
    for (idx, ty) in function.signature.return_.iter().enumerate() {
        check_return_type::<Mode>(idx, ty)?;
    }
    Ok(())
}

fn check_visibility<Mode: ExecutionMode>(
    env: &Env,
    function: &T::LoadedFunction,
) -> Result<(Visibility, /* is_entry */ bool), ExecutionError> {
    let module = env.module_definition(&function.runtime_id, &function.linkage)?;
    let module: &CompiledModule = module.as_ref();
    let Some((_index, fdef)) = module.find_function_def_by_name(function.name.as_str()) else {
        invariant_violation!(
            "Could not resolve function '{}' in module {}. \
            This should have been checked when linking",
            &function.name,
            module.self_id(),
        );
    };
    let visibility = fdef.visibility;
    let is_entry = fdef.is_entry;
    match (visibility, is_entry) {
        // can call entry
        (Visibility::Private | Visibility::Friend, true) => (),
        // can call public entry
        (Visibility::Public, true) => (),
        // can call public
        (Visibility::Public, false) => (),
        // cannot call private or friend if not entry
        (Visibility::Private | Visibility::Friend, false) => {
            if !Mode::allow_arbitrary_function_calls() {
                return Err(ExecutionError::new_with_source(
                    ExecutionErrorKind::NonEntryFunctionInvoked,
                    "Can only call `entry` or `public` functions",
                ));
            }
        }
    };
    Ok((visibility, is_entry))
}

// is missing both drop and store
fn is_hot_potato_return_type(ty: &T::Type) -> bool {
    let abilities = ty.abilities();
    !abilities.has_drop() && !abilities.has_store()
}
