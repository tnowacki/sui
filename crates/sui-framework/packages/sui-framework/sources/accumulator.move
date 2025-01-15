
module sui::accumulator;

use sui::balance::Balance;

/// Transfers the balance to the accumulator for `Balance<T>` for the `recipient`.
/// If the `recipient` is a Sui Account/Address (not an object), it can used as an input
/// object using
/// `CallArg::BalanceForSender(
///     /* sender */ address,
///     /* Balance<T> */ TypeInput,
///     amount: u64,
/// )`.
/// These produce a value `Balance<T>` in the PTB execution environment.
fun send<T>(balance: Balance<T>, recipient: address) {
    if (balance.value() == 0) balance.destroy_zero()
    else send_impl<T>(balance, recipient)
}
public native fun send_impl<T>(balance: Balance<T>, recipient: address);



////////////////////////////////////////////////////////////////////////////////////////////////////

// EXTENSION: Objects as accumulators: TTO + Balance<T>

/// Receives the balance for an the accumulator for `Balance<T>` where the accumulator is an object.
/// `ReceivingBalance<T>` is constructed with another `CallArg`
/// `CallArg::BalanceForObject(
///     /* object */ address,
///     /* Balance<T> */ TypeInput,
///     amount: u64,
/// )`.
/// These produce a value `ReceivingBalance<T>` in the PTB execution environment.
public struct ReceivingBalance<phantom T> {
    owner: ID,
    balance: Balance<T>,
}
public fun receive<T>(accumulator: &mut UID, r: ReceivingBalance<T>): Balance<T> {
    let ReceivingBalance { owner, balance } = r;
    assert!(accumulator.as_inner() == owner);
    balance
}



////////////////////////////////////////////////////////////////////////////////////////////////////

// EXTENSION: CallArg::BalanceFor*(..., amount: Option<u64>)
// Allow for taking the _full_ amount of the balance. Maybe we just make this an SDK feature?



////////////////////////////////////////////////////////////////////////////////////////////////////

// EXTENSION: Restricted transfer

// If `Balance<T> == Balance<Restricted<T'>>`, then we instead create a `RestrictedBalance<T'>` to
// force the recipient to claim the balance through the module that defines the witness `T`
// In these cases:
// ObjectArg::BalanceForSender produces a value `RestrictedBalance<T'>`
// ObjectArg::BalanceForObject produces a value `ReceivingRestrictedBalance<T'>`
use sui::balance::{restricted, RestrictedBalance, destroy_balance_for_accumulator};

public fun restricted_send<T: drop>(witness: T, amount: u64, recipient: address) {
    let balance = restricted(witness, amount);
    send(balance, recipient)
}

/// Used with CallArg::BalanceForSender
public fun restricted_claim<T: drop>(witness: T, balance: RestrictedBalance<T>): u64 {
    destroy_balance_for_accumulator(witness, balance)
}

/// Used with CallArg::BalanceForObject
public struct ReceivingRestrictedBalance<phantom T> {
    owner: ID,
    balance: RestrictedBalance<T>,
}
/// Used with CallArg::BalanceForObject
public fun restricted_receive<T: drop>(
    witness: T,
    accumulator: &mut UID,
    r: ReceivingRestrictedBalance<T>
): u64 {
    let ReceivingRestrictedBalance { owner, balance } = r;
    assert!(accumulator.as_inner() == owner);
    destroy_balance_for_accumulator(witness, balance)
}
