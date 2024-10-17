// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

#[allow(unused_const)]
module sui::transfer;

use sui::vec_map::{Self, VecMap};

/// This represents the ability to `receive` an object of type `T`.
/// This type is ephemeral per-transaction and cannot be stored on-chain.
/// This does not represent the obligation to receive the object that it
/// references, but simply the ability to receive the object with object ID
/// `id` at version `version` if you can prove mutable access to the parent
/// object during the transaction.
/// Internals of this struct are opaque outside this module.
public struct Receiving<phantom T: key> has drop {
    id: ID,
    version: u64,
}

/// Shared an object that was previously created. Shared objects must currently
/// be constructed in the transaction they are created.
const ESharedNonNewObject: u64 = 0;

#[allow(unused_const)]
/// Serialization of the object failed.
const EBCSSerializationFailure: u64 = 1;

#[allow(unused_const)]
/// The object being received is not of the expected type.
const EReceivingObjectTypeMismatch: u64 = 2;

#[allow(unused_const)]
/// Represents both the case where the object does not exist and the case where the object is not
/// able to be accessed through the parent that is passed-in.
const EUnableToReceiveObject: u64 = 3;

#[allow(unused_const)]
/// Shared object operations such as wrapping, freezing, and converting to owned are not allowed.
const ESharedObjectOperationNotSupported: u64 = 4;

/// Transfer ownership of `obj` to `recipient`. `obj` must have the `key` attribute,
/// which (in turn) ensures that `obj` has a globally unique ID. Note that if the recipient
/// address represents an object ID, the `obj` sent will be inaccessible after the transfer
/// (though they will be retrievable at a future date once new features are added).
/// This function has custom rules performed by the Sui Move bytecode verifier that ensures
/// that `T` is an object defined in the module where `transfer` is invoked. Use
/// `public_transfer` to transfer an object with `store` outside of its module.
public fun transfer<T: key>(obj: T, recipient: address) {
    transfer_impl(obj, recipient)
}

/// Transfer ownership of `obj` to `recipient`. `obj` must have the `key` attribute,
/// which (in turn) ensures that `obj` has a globally unique ID. Note that if the recipient
/// address represents an object ID, the `obj` sent will be inaccessible after the transfer
/// (though they will be retrievable at a future date once new features are added).
/// The object must have `store` to be transferred outside of its module.
public fun public_transfer<T: key + store>(obj: T, recipient: address) {
    transfer_impl(obj, recipient)
}

/// Freeze `obj`. After freezing `obj` becomes immutable and can no longer be transferred or
/// mutated.
/// This function has custom rules performed by the Sui Move bytecode verifier that ensures
/// that `T` is an object defined in the module where `freeze_object` is invoked. Use
/// `public_freeze_object` to freeze an object with `store` outside of its module.
public fun freeze_object<T: key>(obj: T) {
    freeze_object_impl(obj)
}

/// Freeze `obj`. After freezing `obj` becomes immutable and can no longer be transferred or
/// mutated.
/// The object must have `store` to be frozen outside of its module.
public fun public_freeze_object<T: key + store>(obj: T) {
    freeze_object_impl(obj)
}

/// Turn the given object into a mutable shared object that everyone can access and mutate.
/// This is irreversible, i.e. once an object is shared, it will stay shared forever.
/// Aborts with `ESharedNonNewObject` of the object being shared was not created in this
/// transaction. This restriction may be relaxed in the future.
/// This function has custom rules performed by the Sui Move bytecode verifier that ensures
/// that `T` is an object defined in the module where `share_object` is invoked. Use
/// `public_share_object` to share an object with `store` outside of its module.
public fun share_object<T: key>(obj: T) {
    share_object_impl(obj)
}

/// Turn the given object into a mutable shared object that everyone can access and mutate.
/// This is irreversible, i.e. once an object is shared, it will stay shared forever.
/// Aborts with `ESharedNonNewObject` of the object being shared was not created in this
/// transaction. This restriction may be relaxed in the future.
/// The object must have `store` to be shared outside of its module.
public fun public_share_object<T: key + store>(obj: T) {
    share_object_impl(obj)
}

public fun public_custom_auth<T: key + store>(obj: T, auth: Auth) {
    custom_auth(obj, auth)
}

#[allow(lint(share_owned))]
public fun custom_auth<T: key>(obj: T, auth: Auth) {
    let legacy_opt = auth_is_legacy(&auth);
    if (legacy_opt.is_none()) custom_auth_impl(obj, auth)
    else match (legacy_opt.destroy_some()) {
        LegacyAuth::Owned(recipient) => transfer(obj, recipient),
        LegacyAuth::Shared => share_object(obj),
        LegacyAuth::Frozen => freeze_object(obj),
    }
}

/// Given mutable (i.e., locked) access to the `parent` and a `Receiving` argument
/// referencing an object of type `T` owned by `parent` use the `to_receive`
/// argument to receive and return the referenced owned object of type `T`.
/// This function has custom rules performed by the Sui Move bytecode verifier that ensures
/// that `T` is an object defined in the module where `receive` is invoked. Use
/// `public_receive` to receivne an object with `store` outside of its module.
public fun receive<T: key>(parent: &mut UID, to_receive: Receiving<T>): T {
    let Receiving { id, version } = to_receive;
    receive_impl(parent.to_address(), id, version)
}

/// Given mutable (i.e., locked) access to the `parent` and a `Receiving` argument
/// referencing an object of type `T` owned by `parent` use the `to_receive`
/// argument to receive and return the referenced owned object of type `T`.
/// The object must have `store` to be received outside of its defining module.
public fun public_receive<T: key + store>(parent: &mut UID, to_receive: Receiving<T>): T {
    let Receiving { id, version } = to_receive;
    receive_impl(parent.to_address(), id, version)
}

/// Return the object ID that the given `Receiving` argument references.
public fun receiving_object_id<T: key>(receiving: &Receiving<T>): ID {
    receiving.id
}

public(package) native fun freeze_object_impl<T: key>(obj: T);

public(package) native fun share_object_impl<T: key>(obj: T);

public(package) native fun transfer_impl<T: key>(obj: T, recipient: address);

public(package) native fun custom_auth_impl<T: key>(obj: T, auth: Auth);

native fun receive_impl<T: key>(parent: address, to_receive: ID, version: u64): T;

#[test_only]
public(package) fun make_receiver<T: key>(id: ID, version: u64): Receiving<T> {
    Receiving { id, version }
}

#[test_only]
public(package) fun receiving_id<T: key>(r: &Receiving<T>): ID {
    r.id
}

public struct Auth has copy, drop, store {
    authenticators: VecMap<Authenticator, Permissions>,
    global: Permissions,
}

public struct Permissions has copy, drop, store {
    // statically checked at signing. `read` vs `write` not supported for "owned" today
    read: bool,
    // statically checked at signing. `read` vs `write` not supported for "owned" today
    write: bool,
    // checked at the end of execution. This is like our no-wrap, no-unshare rule for shared objects
    // we just check the "owner" is the same
    transfer: bool,
    // checked at the end of execution
    delete: bool,
}

public enum Authenticator has copy, drop, store {
    // fast path
    Address(address),
    // consensus (auto version) only, vector must be non-empty. We support automatically versioned,
    // address authenticated via a "club" of length 1.
    Club(vector<address>),
}

public fun auth_owned(recipient: address): Auth {
    let mut authenticators = vec_map::empty();
    authenticators.insert(authenticator_address(recipient), permissions_all());
    Auth {
        authenticators,
        global: permissions_none(),
    }
}

public fun auth_club_owned(members: vector<address>): Auth {
    let mut authenticators = vec_map::empty();
    authenticators.insert(authenticator_club(members), permissions_all());
    Auth {
        authenticators,
        global: permissions_none(),
    }
}

public fun auth_shared(): Auth {
    let authenticators = vec_map::empty();
    Auth {
        authenticators,
        global: permissions_legacy_shared(),
    }
}

public fun auth_frozen(): Auth {
    let authenticators = vec_map::empty();
    Auth {
        authenticators,
        global: perimissions_custom(
            true, // read
            false, // write
            false, // transfer
            false, // delete
        ),
    }
}

public fun permissions_all(): Permissions {
    Permissions {
        read: true,
        write: true,
        transfer: true,
        delete: true,
    }
}

public fun permissions_read_only(): Permissions {
    Permissions {
        read: true,
        write: false,
        transfer: false,
        delete: false,
    }
}

fun permissions_legacy_shared(): Permissions {
    Permissions {
        read: true,
        write: true,
        transfer: false,
        delete: true,
    }
}

public fun permissions_none(): Permissions {
    Permissions {
        read: false,
        write: false,
        transfer: false,
        delete: false,
    }
}

public fun perimissions_custom(read: bool, write: bool, transfer: bool, delete: bool): Permissions {
    Permissions {
        read,
        write,
        transfer,
        delete,
    }
}

public fun authenticator_address(address: address): Authenticator {
    Authenticator::Address(address)
}

public fun authenticator_club(members: vector<address>): Authenticator {
    assert!(!members.is_empty());
    Authenticator::Club(members)
}

public enum LegacyAuth has copy, drop {
    Owned(address),
    Shared,
    Frozen,
}

fun auth_is_legacy(auth: &Auth): Option<LegacyAuth> {
    let Auth { authenticators, global } = auth;
    match (authenticators.size()) {
        0 => {
            if (global == permissions_read_only()) option::some(LegacyAuth::Frozen)
            else if (global == permissions_legacy_shared()) option::some(LegacyAuth::Shared)
            else option::none()
        },
        1 => {
            let (authenticator, permissions) = authenticators.get_entry_by_idx(0);
            if (permissions != permissions_all()) option::none()
            else match (authenticator) {
                Authenticator::Address(a) => option::some(LegacyAuth::Owned(*a)),
                Authenticator::Club(_) => option::none(),
            }
        },
        _ => option::none(),
    }


}
