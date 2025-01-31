// Example with deny-list and claw-back Token
// in sui for Config reasons
module sui::token_example;

use sui::accumulator;
use sui::balance::{Balance, Restricted};
use sui::config::{Self, Config};

public struct Token {
    balance: Balance<Restricted<TokenWitness>>,
}

public struct TokenWitness() has drop;

public struct MintCap has key {
    id: UID,
}

const GOD: address = @0xC0FFEE;
const DENY_LIST: address = @0xDEAD; // filled in after init

fun init(ctx: &mut TxContext) {
    let clawback = accumulator::restricted_withdraw_cap(
        TokenWitness(),
        accumulator::account_set_all(),
        ctx,
    );
    clawback.transfer(TokenWitness(), GOD);
    transfer::transfer(MintCap { id: object::new(ctx) }, GOD);
    config::new(&mut TokenWitness(), ctx).share();
}

public fun mint(_cap: &mut MintCap, value: u64, _ctx: &mut TxContext): Token {
    Token {
        balance: accumulator::restricted_balance(TokenWitness(), value),
    }
}

// - If you want instantaneous denial, you take an &Config<TokenWitness> and check it
public fun token_send(token: Token, recipient: address, ctx: &mut TxContext) {
    let Token { balance } = token;
    assert!(!is_denied(ctx.sender(), ctx));
    assert!(!is_denied(recipient, ctx));
    accumulator::send(balance, recipient)
}

// - For clawback, GOD has a RestrictedWithdrawCap that can take withdraw from any account
public fun token_receive(
    reservation: &mut accumulator::RestrictedReservation<TokenWitness>,
    cap: &mut accumulator::RestrictedWithdrawCap<TokenWitness>,
    amount: u64,
    _ctx: &mut TxContext,
): Token {
    let balance = reservation.withdraw(TokenWitness(), cap, amount);
    Token { balance }
}

public use fun token_balance as Token.balance;

public fun token_balance(token: &Token): &Balance<Restricted<TokenWitness>> {
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
