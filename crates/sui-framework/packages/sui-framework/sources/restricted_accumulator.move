// accumulator v2 but with capabilities
module sui::restricted_accumulator;

use sui::accumulator;
use sui::vec_set::VecSet;


// `T` is a type with a single `u[8,16,32,64,128]` field. `u256` is not supported.
public struct Restricted<T: store>(T) has store;

// In some ways `WithdrawCap` opens up `accumulator` into a full blown custom accumulator table
// Instead of being bound to the behavior specified by `withdraw_from_sender` and
// `withdraw_from_object`, you can withdraw from any `address` contained in `accounts`.
// We don't have `store` to check at signing that the withdrawal is valid. This should hopefully
// make scheduling easier, but if we don't care about this, we can give it `store` and relax the
// rules for creating a `WithdrawCap`.
public struct WithdrawCap<phantom T> has key {
    id: UID,
    accounts: AccountSet,
}

public enum AccountSet has copy, drop, store {
    // used to access all accounts
    All,
    // used to access a limited set of accounts
    Limited(VecSet<address>),
}

// Same rules as `accumulator::add`
// we need to modify those rules to also allow for wrappers around the single `u*` field
public fun add<T: store>(value: T, recipient: address) {
    accumulator::add(Restricted(value), recipient)
}

// Same rules as `accumulator::add`
public fun withdraw</* internal */T: store>(
    cap: &mut WithdrawCap<T>,
    withdrawal: &mut accumulator::Withdrawal<Restricted<T>>,
    value: u128,
): T {
    assert!(cap.accounts.contains(&withdrawal.location()));
    let Restricted(inner) = accumulator::withdraw(withdrawal, value);
    inner
}

public fun withdraw_cap</* internal */ T>(
    accounts: AccountSet,
    ctx: &mut TxContext,
): WithdrawCap<T> {
    let id = object::new(ctx);
    WithdrawCap { id, accounts }
}

public use fun withdraw_cap_transfer as WithdrawCap.transfer;

public fun withdraw_cap_transfer</* internal */T>(
    cap: WithdrawCap<T>,
    recipient: address,
) {
    transfer::transfer(cap, recipient)
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
