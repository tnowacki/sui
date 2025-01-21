
module sui::accumulator;

use sui::balance::Balance;

/// 0xA
/// hash(0xA || sui::balance::Balance<T> || address) -> Balance<T>

/// Bob, S
/// TxA, Inputs[Reservation(10)] Commands [ ..., send(5, @Bob), ...]
/// TxB, Inputs[Reservation(20)] Commands [ ..., send(15, @Bob),...]
/// Checkpoint start: S >= 30 (fork prevention check)
/// Execute
///   TxA    ||     TxB
/// Checkpoint end: S' == S - 30 + 20
///
/// Checkpoint { [Transactions] }
/// execute(Transaction) = ChangeSet

/// Transfers the balance to the accumulator for `Balance<T>` for the `recipient`.
/// If the `recipient` is a Sui Account/Address (not an object), it can used as an input
/// object using
/// `CallArg::BalanceForSender(
///     /* sender */ address,
///     /* Balance<T> */ TypeInput,
///     reservation: u64,
/// )`.
/// These produce a value `Balance<T>` in the PTB execution environment.
fun send<T>(balance: Balance<T>, recipient: address) {
    // maybe charge a fee for storage attacks
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
/// TODO reachability? existence? spam attacks on denial?
public struct ReceivingBalance<phantom T> {
    owner: ID,
    balance: Balance<T>,
}
public fun receive<T>(accumulator: &mut UID, r: ReceivingBalance<T>): Balance<T> {
    let ReceivingBalance { owner, balance } = r;
    assert!(accumulator.as_inner() == owner);
    balance
}
// TODO
// Maybe?
// Tim's suggestion
// Maybe we don't need if we have PTB change collection
public fun refund<T>(r: ReceivingBalance<T>) {
    let ReceivingBalance { owner, balance } = r;
    send(balance, owner.to_address())
}
/*
b: ReceivingBalance<SUI>;

if (is_tuesday) send(receive(&mut obj_id, b), @dario)
else refund(b)
*/



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

public struct AdditiveU8<phantom T>(u8) has store;
...
public struct AdditiveU128<phantom T>(u128) has store;

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

public struct Token has key {
    id: UID,
    value: u64,
}

public struct TokenWitness() has drop;

public struct TreasuryCap has key {
    id: UID,
}

public fun mint(_cap: &mut TreasuryCap, value: u64, ctx: &mut TxContext): Token {
    Token {
        id: object::new(ctx),
        value,
    }
}

public fun token_send(token: Token, recipient: address) {
    let Token { id, value } = token;
    object::delete(id);
    restricted_send(TokenWitness(), value, recipient)
}

public fun token_receive(b: RestrictedBalance<TokenWitness>, ctx: &mut TxContext): Token {
    let value = restricted_claim(TokenWitness(), b);
    Token { id: object::new(ctx), value }
}
