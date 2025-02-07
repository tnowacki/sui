// Example with deny-list and claw-back Token
// In `sui` since `Config` is all public(package) currently
module sui::claw_back_example;

use sui::accumulator;
use sui::balance::{Self, Balance, Supply};
use sui::config::{Self, Config};

public struct TokenPotato(Token)
public struct Token(Balance<TokenWitness>) has store;

public struct TokenWitness() has drop;

public struct MintCap has key {
    id: UID,
    supply: Supply<TokenWitness>,
}

const GOD: address = @0xC0FFEE;
const DENY_LIST: address = @0xDEAD; // added after init in a v2 upgrade

fun init(ctx: &mut TxContext) {
    let claw_back = accumulator::create_seize_cap<Token>(
        ctx,
    );
    claw_back.transfer(GOD);
    let id = object::new(ctx);
    let supply = balance::create_supply(TokenWitness());
    transfer::transfer(MintCap { id, supply }, GOD);
    config::new(&mut TokenWitness(), ctx).share();
}

public fun mint(cap: &mut MintCap, value: u64, _ctx: &mut TxContext): TokenPotato {
    TokenPotato(Token(cap.supply.increase_supply(value)))
}

// - If you want instantaneous denial, you take an &Config<TokenWitness> and check it
public fun send(token: TokenPotato, recipient: address, ctx: &mut TxContext) {
    let TokenPotato(token) = token;
    assert!(!is_denied(ctx.sender(), ctx));
    assert!(!is_denied(recipient, ctx));
    accumulator::add(token, recipient)
}

public fun withdraw_from_sender(
    withdrawal: &mut accumulator::Withdrawal<Token>,
    value: u64,
    ctx: &mut TxContext,
): Token {
    withdrawal.withdraw_from_sender(value as u128, ctx)
}

public fun withdraw_from_object(
    obj: &mut UID,
    value: u64,
): Token {
    accumulator::withdraw_from_object(obj, value as u128)
}

public fun balance(token: &TokenPotato): &Balance<TokenWitness> {
    &token.0.0
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
