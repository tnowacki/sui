// Example with deny-list and claw-back Token
// In `sui` since `Config` is all public(package) currently
module sui::claw_back_example;

use sui::accumulator;
use sui::balance::{Balance, Restricted};
use sui::config::{Self, Config};
use sui::vec_set;

public struct Token {
    balance: Balance<Restricted<TokenWitness>>,
}

public struct TokenWitness() has drop;

public struct MintCap has key {
    id: UID,
}

const GOD: address = @0xC0FFEE;
const DENY_LIST: address = @0xDEAD; // added after init in a v2 upgrade

fun init(ctx: &mut TxContext) {
    let claw_back = accumulator::restricted_withdraw_cap(
        TokenWitness(),
        accumulator::account_set_all(),
        ctx,
    );
    claw_back.transfer(TokenWitness(), GOD);
    transfer::transfer(MintCap { id: object::new(ctx) }, GOD);
    config::new(&mut TokenWitness(), ctx).share();
}

public fun mint(_cap: &mut MintCap, value: u64, _ctx: &mut TxContext): Token {
    Token {
        balance: accumulator::restricted_balance(TokenWitness(), value),
    }
}

// I feel like for safety you want to encourage this? Otherwise someone could sneak in a call
// to claim account cap anywhere in the code and it would be hard to track down.
public fun claim_account_cap(ctx: &mut TxContext) {
    let account = ctx.sender();
    let cap = accumulator::restricted_withdraw_cap(
        TokenWitness(),
        accumulator::account_set_limited(vec_set::from_keys(vector[account])),
        ctx,
    );
    cap.transfer(TokenWitness(), account);
}

// Similarly, we rely on TTO to avoid unauthorized RestrictedWithdrawCap creation for an object
public fun claim_object_cap(object: &mut UID, ctx: &mut TxContext) {
    let account = object.to_address();
    let cap = accumulator::restricted_withdraw_cap(
        TokenWitness(),
        accumulator::account_set_limited(vec_set::from_keys(vector[account])),
        ctx,
    );
    cap.transfer(TokenWitness(), account);
}

// Why not?
public fun restricted_withdraw_cap_transfer(
    cap: accumulator::RestrictedWithdrawCap<TokenWitness>,
    recipient: address,
) {
    cap.transfer(TokenWitness(), recipient)
}

// - If you want instantaneous denial, you take an &Config<TokenWitness> and check it
public fun send(token: Token, recipient: address, ctx: &mut TxContext) {
    let Token { balance } = token;
    assert!(!is_denied(ctx.sender(), ctx));
    assert!(!is_denied(recipient, ctx));
    accumulator::send(balance, recipient)
}

// - For claw-back, GOD has a RestrictedWithdrawCap that can take withdraw from any account
public fun receive(
    reservation: &mut accumulator::RestrictedReservation<TokenWitness>,
    cap: &mut accumulator::RestrictedWithdrawCap<TokenWitness>,
    amount: u64,
    _ctx: &mut TxContext,
): Token {
    let balance = reservation.withdraw(TokenWitness(), cap, amount);
    Token { balance }
}

public fun balance(token: &Token): &Balance<Restricted<TokenWitness>> {
    &token.balance
}

public fun is_denied(account: address, ctx: &TxContext): bool {
    let id = object::id_from_address(DENY_LIST);
    config::read_setting(
        id,
        AddressKey(account),
        ctx,
    ).destroy_or!(false) ||
    config::read_setting(
        id,
        GlobalPauseKey(),
        ctx,
    ).destroy_or!(false)
}

public struct AddressKey(address) has copy, drop, store;
public struct GlobalPauseKey() has copy, drop, store;

public fun deny(
    _cap: &mut MintCap,
    deny_list: &mut Config<TokenWitness>,
    account: address,
    ctx: &mut TxContext,
) {
    deny_list.entry!(&mut TokenWitness(), AddressKey(account), |_, _, _| true, ctx);
}

public fun undeny(
    _cap: &mut MintCap,
    deny_list: &mut Config<TokenWitness>,
    account: address,
    ctx: &mut TxContext,
) {
    deny_list.remove_for_next_epoch<_, AddressKey, bool>(
        &mut TokenWitness(),
        AddressKey(account),
        ctx,
    );
}

public fun pause(_cap: &mut MintCap, deny_list: &mut Config<TokenWitness>, ctx: &mut TxContext) {
    deny_list.entry!(&mut TokenWitness(), GlobalPauseKey(), |_, _, _| true, ctx);
}

public fun unpause(_cap: &mut MintCap, deny_list: &mut Config<TokenWitness>, ctx: &mut TxContext) {
    deny_list.remove_for_next_epoch<_, GlobalPauseKey, bool>(
        &mut TokenWitness(),
        GlobalPauseKey(),
        ctx,
    );
}
