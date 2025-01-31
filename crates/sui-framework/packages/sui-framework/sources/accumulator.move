module sui::accumulator;

use sui::balance::{Self, Balance, restricted, Restricted};
use sui::config::{Self, Config};
use sui::vec_set::VecSet;

// 0xA
// hash(0xA || sui::balance::Balance<T> || address) -> Balance<T>

// Bob, S
// TxA, Inputs[Reservation(10)] Commands [ ..., send(5, @Bob), ...]
// TxB, Inputs[Reservation(20)] Commands [ ..., send(15, @Bob),...]
// Checkpoint start: S >= 30 (fork prevention check)
// Execute
//   TxA    ||     TxB
// Checkpoint end: S' == S - 30 + 20
//
// Checkpoint { [Transactions] }
// execute(Transaction) = ChangeSet

// Reasons for doing this over shared objects + Table<address, Balance>
// - You can send without taking a dependency on the recipient
// - You can withdraw in parallel

/// Transfers the balance to the accumulator for `Balance<T>` for the `recipient`.
/// If the `recipient` is a Sui Account/Address (not an object), it can used as an input
/// object using
/// `CallArg::Balance {
///     account: address, // validity checked at signing
///     balance_type: TypeInput, // Balance<T>
///     reservation: u64,
/// }`.
/// These produce a value `Balance<T>` in the PTB execution environment.
public fun send<T>(balance: Balance<T>, recipient: address) {
    // maybe charge a fee for storage attacks
    if (balance.value() == 0) balance.destroy_zero()
    else send_impl<T>(balance, recipient)
}
native fun send_impl<T>(balance: Balance<T>, recipient: address);

////////////////////////////////////////////////////////////////////////////////////////////////////

// EXTENSION: Objects as accumulators

/// The object acts as a hook for the accumulator, so we know that there are no withdrawals
/// happening in parallel. So we can just withdraw!
public fun object_withdraw<T>(accumulator: &mut UID, amount: u64): Balance<T> {
    if (amount == 0) return balance::zero();
    let address = accumulator.to_address();
    withdraw_impl(address, amount)
}
// Small details here
// - The system needs to ensure that the balance is not being increased until the end
// - We construct a `Balance<T>` natively since having even a public(package) function that
//   constructs a `Balance<T>` might make folks squeamish. Though we could totally do it if we want.
native fun withdraw_impl<T>(addr: address, amount: u64): Balance<T>;

////////////////////////////////////////////////////////////////////////////////////////////////////

// EXTENSION: CallArg::BalanceFor*(..., amount: Option<u64>)
// Allow for taking the _full_ amount of the balance. Essentially it might be nice to have a
// `object_withdraw` version for top level accounts.

////////////////////////////////////////////////////////////////////////////////////////////////////

// EXTENSION: Restricted transfer

// Goals
// - Maintain the same gains from normal Balance transfers
//   - We don't want to just force everything through a single object, that defeats the purpose of
//     doing this at all
// - Allow for arbitrary restrictions on send/withdraw of balances
// - Allow for a third party to claim the balance
// - Reusing Balance as much as possible to avoid new requirements in core
//     - We could just make a new type if we need it, but just for simplicity I am trying to
//       show what is possible without doing so
//     - Having a separate type would make it clearer to enforce the PTB argument restrictions,
//       so we should consider it

public struct RestrictedWithdrawCap<phantom T> has key {
    id: UID,
    accounts: AccountSet,
}

public enum AccountSet has copy, drop, store {
    All,
    Limited(VecSet<address>),
}

public use fun account_set_contains as AccountSet.contains;

public fun account_set_contains(set: &AccountSet, account: &address): bool {
    match (set) {
        AccountSet::All => true,
        AccountSet::Limited(accounts) => accounts.contains(account),
    }
}

public fun account_set_all(): AccountSet {
    AccountSet::All
}

public fun account_set_limited(accounts: VecSet<address>): AccountSet {
    assert!(accounts.size() > 0);
    AccountSet::Limited(accounts)
}

public fun restricted_withdraw_cap<T: drop>(
    _witness: T,
    accounts: AccountSet,
    ctx: &mut TxContext,
): RestrictedWithdrawCap<T> {
    let id = object::new(ctx);
    RestrictedWithdrawCap { id, accounts }
}

public use fun restricted_withdraw_cap_transfer as RestrictedWithdrawCap.transfer;

public fun restricted_withdraw_cap_transfer<T: drop>(
    cap: RestrictedWithdrawCap<T>,
    _witness: T,
    recipient: address,
) {
    transfer::transfer(cap, recipient)
}

// Things will get a bit swirly-wirly here.
// We have a similar call arg for restricted
// `CallArg::RestrictedReservation {
//     account: address, // checks that there is a valid RestrictedWithdrawCap as an input arg
//     balance_type: TypeInput, // Balance<Restricted<T>>
//     reservation: u64,
// }`
// This is like `CallArg::Balance` but for `Balance<Restricted<T>>`. It then produces a
// `RestrictedBalance<T>` to force the withdrawal to happen through the module that defines `T`

public struct RestrictedReservation<phantom T> has drop {
    account: address,
    value: u64,
}

// As far as goals
// - the witness `T` allows layering of custom code (restrictions) on send/withdraw
// - We can allow arbitrary minting of `RestrictedWithdrawCap` by `T` to allow for clawback
//   - If we had `T: internal` we might be able to do this without the witness
// - Not sure if we want `RestrictedWithdrawCap` to have `store` or not. Forcing it to the top level
//   at the very least makes it clear that we need this as an input object... maybe?

public fun restricted_balance<T: drop>(witness: T, amount: u64): Balance<Restricted<T>> {
    restricted(witness, amount)
}

public use fun restricted_withdraw as RestrictedReservation.withdraw;

public fun restricted_withdraw<T: drop>(
    reservation: &mut RestrictedReservation<T>,
    _witness: T,
    cap: &mut RestrictedWithdrawCap<T>,
    amount: u64,
): Balance<Restricted<T>> {
    let account = reservation.account;
    assert!(cap.accounts.contains(&account));
    assert!(amount >= reservation.value);
    reservation.value = reservation.value - amount;
    withdraw_impl(account, amount)
}
