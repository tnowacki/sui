module deepbook::prediction;

use deepbook::prediction_direction as pd;
use deepbook::type_u32;
use std::type_name;
use sui::coin::Coin;
use sui::coin_registry::CoinRegistry;
use sui::coin_registry::CurrencyInitializer;
use sui::coin::TreasuryCap;

public struct Market has key {
    id: UID,
}

public struct Prediction<phantom T> has key {
    id: UID,
}

public struct Strata<phantom Coin, phantom Direction, phantom Strike, phantom Date>()
public struct StrikeU32<phantom Value>()
public struct DateU32<phantom Value>()

public fun register_prediction<
    Asset,
    Direction,
    S_N8,
    S_N7,
    S_N6,
    S_N5,
    S_N4,
    S_N3,
    S_N2,
    S_N1,
    D_N8,
    D_N7,
    D_N6,
    D_N5,
    D_N4,
    D_N3,
    D_N2,
    D_N1,
>(
    registry: &mut CoinRegistry,
    market: &mut Market,
    bet: u64,
    strike: u32,
    expiration: u32,
    ctx: &mut TxContext,
): Coin<
    Prediction<
        Strata<
            Asset,
            Direction,
            StrikeU32<type_u32::TU32<S_N8, S_N7, S_N6, S_N5, S_N4, S_N3, S_N2, S_N1>>,
            DateU32<type_u32::TU32<D_N8, D_N7, D_N6, D_N5, D_N4, D_N3, D_N2, D_N1>>,
        >,
    >,
> {
    let direction_tn = type_name::with_defining_ids<Direction>();
    assert!(
        direction_tn == type_name::with_defining_ids<pd::Up>() ||
        direction_tn == type_name::with_defining_ids<pd::Down>(),
    );
    let specified_strike = type_u32::nibbles_to_u32<S_N8, S_N7, S_N6, S_N5, S_N4, S_N3, S_N2, S_N1>();
    assert!(specified_strike == strike);
    let specified_date = type_u32::nibbles_to_u32<D_N8, D_N7, D_N6, D_N5, D_N4, D_N3, D_N2, D_N1>();
    assert!(specified_date == expiration);
    let (initializer, treasury) = registry.new_currency<
        Prediction<
            Strata<
                Asset,
                Direction,
                StrikeU32<type_u32::TU32<S_N8, S_N7, S_N6, S_N5, S_N4, S_N3, S_N2, S_N1>>,
                DateU32<type_u32::TU32<D_N8, D_N7, D_N6, D_N5, D_N4, D_N3, D_N2, D_N1>>,
            >,
        >
    >(
        /* decimals */ 10,
        "DPRED",
        "DeepBook Prediction Token",
        "Token representing a prediction position in DeepBook",
        "wow_url.com",
        ctx,
    );
    market.do_things(registry, initializer, treasury, bet, ctx)
}

public fun do_things<TStrata>(
    _market: &mut Market,
    _registry: &mut CoinRegistry,
    _initializer: CurrencyInitializer<
        Prediction<TStrata>,
    >,
    _treasury: TreasuryCap<
        Prediction<TStrata>,
    >,
    _bet: u64,
    _ctx: &mut TxContext,
): Coin<Prediction<TStrata>> {
    abort
}
