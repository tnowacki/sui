// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use crate::execution_mode::ExecutionMode;
use crate::programmable_transactions::execution::check_private_generics;
use crate::sp;
use crate::static_programmable_transactions::{env::Env, loading::ast::Type, typing::ast as T};
use move_binary_format::{CompiledModule, file_format::Visibility};
use sui_types::{
    error::{ExecutionError, ExecutionErrorKind, command_argument_error},
    execution_status::CommandArgumentError,
};

struct Context {
    gas_coin: IsHot,
    objects: Vec<IsHot>,
    pure: Vec<IsHot>,
    receiving: Vec<IsHot>,
    results: Vec<Vec<IsHot>>,
}

/// Is hot for entry verifier rules. A non-public entry function cannot take in any hot arguments.
type IsHot = bool;

impl Context {
    fn new(txn: &T::Transaction) -> Self {
        Self {
            gas_coin: false,
            objects: txn.objects.iter().map(|_| false).collect(),
            pure: txn.pure.iter().map(|_| false).collect(),
            receiving: txn.receiving.iter().map(|_| false).collect(),
            results: vec![],
        }
    }

    // check if hot, and mark it as fixed if mutably borrowing a pure input
    fn is_hot(&self, arg: &T::Argument) -> bool {
        self.is_loc_hot(arg.value.0.location())
    }

    fn is_loc_hot(&self, location: T::Location) -> bool {
        match location {
            T::Location::TxContext => false, // TxContext is never hot
            T::Location::GasCoin => self.gas_coin,
            T::Location::ObjectInput(i) => self.objects[i as usize],
            T::Location::PureInput(i) => self.pure[i as usize],
            T::Location::ReceivingInput(i) => self.receiving[i as usize],
            T::Location::Result(i, j) => self.results[i as usize][j as usize],
        }
    }

    /// Marks mutable usages as hot. We don't care about `Move` since the value will be moved
    /// and that location is no longer accessible.
    fn mark_hot(&mut self, arg: &T::Argument) {
        match &arg.value.0 {
            T::Argument__::Borrow(/* mut */ true, loc) => self.mark_loc_hot(*loc),
            T::Argument__::Borrow(/* mut */ false, _)
            | T::Argument__::Use(_)
            | T::Argument__::Read(_)
            | &T::Argument__::Freeze(_) => (),
        }
    }

    fn mark_loc_hot(&mut self, location: T::Location) {
        match location {
            T::Location::TxContext => (), // TxContext is never hot, so nothing to do
            T::Location::GasCoin => self.gas_coin = true,
            T::Location::ObjectInput(i) => self.objects[i as usize] = true,
            T::Location::PureInput(i) => self.pure[i as usize] = true,
            T::Location::ReceivingInput(i) => self.receiving[i as usize] = true,
            T::Location::Result(i, j) => self.results[i as usize][j as usize] = true,
        }
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
        let results_hot = command::<Mode>(env, &mut context, c)
            .map_err(|e| e.with_command_index(c.idx as usize))?;
        assert_invariant!(
            results_hot.len() == c.value.result_type.len(),
            "result length mismatch"
        );
        context.results.push(results_hot);
    }
    Ok(())
}

fn command<Mode: ExecutionMode>(
    env: &Env,
    context: &mut Context,
    sp!(_, c): &T::Command,
) -> Result<Vec<IsHot>, ExecutionError> {
    let result = &c.result_type;
    Ok(match &c.command {
        T::Command__::MoveCall(call) => move_call::<Mode>(env, context, call, result)?,
        T::Command__::TransferObjects(objs, recipient) => {
            arguments(env, context, objs);
            argument(env, context, recipient);
            vec![]
        }
        T::Command__::SplitCoins(_, coin, amounts) => {
            let amounts_are_hot = arguments(env, context, amounts);
            let coin_is_hot = argument(env, context, coin);
            let is_hot = amounts_are_hot || coin_is_hot;
            if is_hot {
                context.mark_hot(coin);
            }
            vec![is_hot; result.len()]
        }
        T::Command__::MergeCoins(_, target, coins) => {
            let is_hot = arguments(env, context, coins);
            argument(env, context, target);
            if is_hot {
                context.mark_hot(target);
            }
            vec![]
        }
        T::Command__::MakeMoveVec(_, args) => {
            let is_hot = arguments(env, context, args);
            debug_assert_eq!(result.len(), 1);
            vec![is_hot]
        }
        T::Command__::Publish(_, _, _) => {
            debug_assert_eq!(Mode::packages_are_predefined(), result.is_empty());
            debug_assert_eq!(!Mode::packages_are_predefined(), result.len() == 1);
            result.iter().map(|_| false).collect::<Vec<_>>()
        }
        T::Command__::Upgrade(_, _, _, ticket, _) => {
            debug_assert_eq!(result.len(), 1);
            let result = vec![false];
            argument(env, context, ticket);
            result
        }
    })
}

fn arguments(env: &Env, context: &Context, args: &[T::Argument]) -> bool {
    args.iter().any(|arg| argument(env, context, arg))
}

fn argument(_env: &Env, context: &Context, arg: &T::Argument) -> bool {
    context.is_hot(arg)
}

fn move_call<Mode: ExecutionMode>(
    env: &Env,
    context: &mut Context,
    call: &T::MoveCall,
    result: &T::ResultType,
) -> Result<Vec<IsHot>, ExecutionError> {
    let T::MoveCall {
        function,
        arguments: args,
    } = call;
    check_signature::<Mode>(function)?;
    check_private_generics(&function.runtime_id, function.name.as_ident_str())?;
    let (vis, is_entry) = check_visibility::<Mode>(env, function)?;
    // check rules around hot arguments and entry functions
    let returns_hot_potato = has_hot_potato_return_type::<Mode>(function);
    let args_hot = args
        .iter()
        .map(|arg| argument(env, context, arg))
        .collect::<Vec<_>>();
    let is_hot = returns_hot_potato || args_hot.iter().any(|&is_hot| is_hot);
    if is_entry && matches!(vis, Visibility::Private) {
        for (idx, &arg_is_hot) in args_hot.iter().enumerate() {
            if arg_is_hot && !Mode::allow_arbitrary_values() {
                return Err(command_argument_error(
                    CommandArgumentError::InvalidArgumentToPrivateEntryFunction,
                    idx,
                ));
            }
        }
    }
    if is_hot {
        for arg in args {
            context.mark_hot(arg);
        }
    }
    Ok(vec![is_hot; result.len()])
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

// Checks if any return type is a hot potato (ignoring it if arbitrary values are allowed)
fn has_hot_potato_return_type<Mode: ExecutionMode>(function: &T::LoadedFunction) -> bool {
    if Mode::allow_arbitrary_values() {
        // If arbitrary values are allowed, we don't care about hot args
        return false;
    }
    function
        .signature
        .return_
        .iter()
        .any(|ty| is_hot_potato_return_type(ty))
}

// is missing both drop and store
fn is_hot_potato_return_type(ty: &T::Type) -> bool {
    let abilities = ty.abilities();
    !abilities.has_drop() && !abilities.has_store()
}
