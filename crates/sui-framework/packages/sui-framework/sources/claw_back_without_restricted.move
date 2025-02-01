// CLT example with deny-list and claw-back Token without using `Restricted` and related APIs
// HOWEVER this example is exceedingly less parallel as all sends incur a dependency on the
// recipient's balance
// In `sui` since `Config` is all public(package) currently
module sui::claw_back_without_restricted;

use sui::accumulator;
use sui::balance::{Self, Balance, Supply};
use sui::config::{Self, Config};
use sui::vec_set;

public struct Account has key {
    id: UID,
}

public struct Token(Balance<TokenWitness>)

public struct TokenWitness has drop()

public struct MintCap has key {
    id: UID,
    supply: Supply<TokenWitness>,
}

const GOD: address = @0xC0FFEE;
const DENY_LIST: address = @0xDEAD; // added after init in a v2 upgrade

fun init(ctx: &mut TxContext) {
    let supply = balance::create_supply(TokenWitness());
    transfer::transfer(MintCap { id: object::new(ctx), supply, }, GOD);
    config::new(&mut TokenWitness(), ctx).share();
}

public fun create_account(_cap: &mut MintCap, account: address, _ctx: &mut TxContext): Account {
    /*
    // We can use multiparty objects (or whatever we call them) so that the claw-back `GOD` address
    // can manipulate any account
    let account = Account { id: object::new(ctx) };
    let mut permissions = Permissions::new();
    permissions.set(account, Permissions::all());
    permissions.set(GOD, Permissions::all()); // claw-back
    transfer::multiparty_transfer(permissions, account);
    */
    abort
}

public fun mint(cap: &mut MintCap, value: u64, _ctx: &mut TxContext): Token {
    Token(cap.supply.increase_supply(value))
}

// - If you want instantaneous denial, you take an &Config<TokenWitness> and check it
// - &Account here is a subtle one. Without requiring proof of the object `&Account` we do not know
//   if the recipient `address` is an object or a Sui account address. If it is a Sui account, we
//   lose the "closed" part of our closed loop token, since the APIs for `accumulator` do not
//   force calling through this module without objects.
//   Additionally without objects, we cannot implement claw back in the basic `accumulator` API.
public fun send(token: Token, recipient: &Account, ctx: &mut TxContext) {
    let Token(balance) = token;
    let recipient = recipient.id.to_address();
    assert!(!is_denied(ctx.sender(), ctx));
    assert!(!is_denied(recipient, ctx));
    accumulator::send(balance, recipient)
}

// - For claw-back, GOD has all permissions on all accounts
public fun withdraw(
    account: &mut Account,
    amount: u64,
    _ctx: &mut TxContext,
): Token {
    Token(accumulator::object_withdraw(&mut account.id, amount))
}

public fun balance(token: &Token): &Balance<TokenWitness> {
    &token.0
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
