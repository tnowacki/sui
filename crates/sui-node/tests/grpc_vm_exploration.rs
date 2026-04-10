// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Exploratory test: spin up the latest VM configured for mainnet and use a
//! gRPC-backed package store to resolve a Move struct's annotated layout by
//! fetching packages from a mainnet fullnode on demand.
//!
//! This currently surfaces a bug in the latest `TypeLayoutResolver`:
//! `make_vm` fails with `MISSING_DEPENDENCY` because `type_linkage` only walks
//! packages reachable through the struct tag's type parameters, not the
//! modules' full import graph. Modules in real-world packages (like the
//! `converter` module we're querying) import things that never appear in the
//! struct's fields, so the linkage context is incomplete and bytecode loading
//! trips on a missing dep. The error is masked by `SuiErrorKind::FailObjectLayout`.
//!
//! Run with:
//!   cargo nextest run -p sui-node grpc_type_layout_resolver --run-ignored ignored-only --no-capture

use std::collections::HashMap;
use std::sync::Mutex;

use sui_protocol_config::{Chain, ProtocolConfig, ProtocolVersion};
use sui_rpc_api::client::Client;
use sui_types::base_types::ObjectID;
use sui_types::TypeTag;
use sui_types::error::{SuiError, SuiErrorKind, SuiResult};
use sui_types::storage::{BackingPackageStore, PackageObject};
use tokio::runtime::Handle;

const MAINNET_GRPC: &str = "https://fullnode.mainnet.sui.io:443";

/// A `BackingPackageStore` that fetches package objects from a mainnet fullnode
/// over gRPC on demand. Results are cached in memory so the same package is
/// only fetched once per test run.
struct GrpcPackageStore {
    client: Client,
    cache: Mutex<HashMap<ObjectID, Option<PackageObject>>>,
}

impl GrpcPackageStore {
    fn new(client: Client) -> Self {
        Self {
            client,
            cache: Mutex::new(HashMap::new()),
        }
    }
}

impl BackingPackageStore for GrpcPackageStore {
    fn get_package_object(&self, package_id: &ObjectID) -> SuiResult<Option<PackageObject>> {
        if let Some(cached) = self.cache.lock().unwrap().get(package_id) {
            return Ok(cached.clone());
        }

        // The store trait is sync but the gRPC client is async. We're running
        // inside a multi-threaded tokio runtime, so `block_in_place` lets us
        // call `block_on` without deadlocking the reactor.
        let id = *package_id;
        let mut client = self.client.clone();
        let result = tokio::task::block_in_place(|| {
            Handle::current().block_on(async move { client.get_object(id).await })
        });

        let package = match result {
            Ok(object) if object.is_package() => {
                eprintln!("fetched package {id}");
                Some(PackageObject::new(object))
            }
            Ok(_) => {
                eprintln!("fetched {id} but it is not a package");
                None
            }
            Err(e) => {
                return Err(SuiErrorKind::GenericAuthorityError {
                    error: format!("gRPC get_object({id}) failed: {e}"),
                }
                .into());
            }
        };

        self.cache
            .lock()
            .unwrap()
            .insert(*package_id, package.clone());
        Ok(package)
    }
}

#[tokio::test(flavor = "multi_thread")]
#[ignore]
async fn grpc_type_layout_resolver() {
    // Latest VM, mainnet chain id + latest protocol version.
    let protocol_config = ProtocolConfig::get_for_version(ProtocolVersion::MAX, Chain::Mainnet);
    println!(
        "protocol version: {}  execution version: {:?}",
        protocol_config.version.as_u64(),
        protocol_config.execution_version_as_option(),
    );

    let executor = sui_execution::executor(&protocol_config, true /* silent */)
        .expect("creating executor should succeed");

    let client = Client::new(MAINNET_GRPC).expect("valid gRPC URI");
    let store = GrpcPackageStore::new(client);

    let type_tag: TypeTag =
        "0xcdca58ff26abf62719b2e88b1805fc47f4f3f0669f9cde13e267dae6c38731c6::converter::Details"
            .parse()
            .unwrap();
    let struct_tag = match type_tag {
        TypeTag::Struct(s) => *s,
        other => panic!("expected struct tag, got {other:?}"),
    };

    let mut resolver = executor.type_layout_resolver(Box::new(store));
    match resolver.get_annotated_layout(&struct_tag) {
        Ok(layout) => {
            println!("\n=== annotated layout for {struct_tag} ===");
            println!("{layout:#?}");
        }
        Err(e) => {
            println!("\n=== layout resolution failed ===");
            println!("{e:#?}");
        }
    }
}
