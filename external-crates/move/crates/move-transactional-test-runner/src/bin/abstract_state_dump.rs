// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Standalone binary that compiles IR modules from a `.mvir` transactional test file
//! and prints the regex reference safety abstract state for every function.

use std::{collections::BTreeMap, fs, path::PathBuf};

use clap::Parser;
use move_binary_format::{
    CompiledModule,
    file_format::{CodeOffset, FunctionDefinitionIndex},
};
use move_bytecode_verifier::{absint::FunctionContext, regex_reference_safety};
use move_bytecode_verifier_meter::dummy::DummyMeter;
use move_core_types::account_address::AccountAddress;
use move_ir_compiler::Compiler as IRCompiler;
use move_stdlib::named_addresses as move_stdlib_named_addresses;
use move_transactional_test_runner::vm_test_harness::{
    SourceMapRegexStateSerializer, move_stdlib_compiled,
};
use move_vm_config::verifier::VerifierConfig;

#[derive(Parser)]
#[command(about = "Dump regex reference safety abstract states from a .mvir file")]
struct Args {
    /// Path to a .mvir transactional test file
    source_path: PathBuf,
}

fn main() {
    let args = Args::parse();
    let content = fs::read_to_string(&args.source_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {e}", args.source_path.display()));

    let chunks = split_on_directives(&content);

    let stdlib_named_addrs: BTreeMap<String, AccountAddress> = move_stdlib_named_addresses()
        .into_iter()
        .map(|(k, v)| (k, v.into_inner()))
        .collect();

    let stdlib_modules: Vec<CompiledModule> = move_stdlib_compiled()
        .iter()
        .map(|(m, _)| m.clone())
        .collect();
    let mut compiled_modules = vec![];

    // Compile any chunks that contain a line that starts with `module`. This is a rough heuristic
    // to avoid invoking the compiler on non-mvir chunks
    for chunk in chunks
        .iter()
        .filter(|c| c.lines().any(|l| l.starts_with("module")))
    {
        let deps: Vec<&CompiledModule> = stdlib_modules
            .iter()
            .chain(compiled_modules.iter().map(|(m, _)| m))
            .collect();
        let Ok((module, source_map)) = IRCompiler::new(deps)
            .with_named_addresses(stdlib_named_addrs.clone())
            .into_compiled_module_with_source_map(chunk)
        else {
            continue;
        };
        compiled_modules.push((module, source_map));
    }

    // Configure the verifier to run the regex safety verifier and to disable the current
    // reference safety pass.
    let mut verifier_config = VerifierConfig::default();
    verifier_config.switch_to_regex_reference_safety = true;
    verifier_config.sanity_check_with_regex_reference_safety = None;

    // module_name -> fn_name -> label -> state
    let output: BTreeMap<String, BTreeMap<String, BTreeMap<String, _>>> = compiled_modules
        .iter()
        .map(|(module, source_map)| {
            let module_id = module.self_id();
            let fns = module
                .function_defs
                .iter()
                .enumerate()
                .filter_map(|(idx, fdef)| {
                    let fdef_idx = FunctionDefinitionIndex::new(idx as u16);
                    let fhandle = module.function_handle_at(fdef.function);
                    let fname = module.identifier_at(fhandle.name).to_string();
                    let code = fdef.code.as_ref()?;

                    let function_context = FunctionContext::new(module, fdef_idx, code, fhandle);
                    let states = regex_reference_safety::verify_and_return_states(
                        &verifier_config,
                        module,
                        &function_context,
                        &mut DummyMeter,
                    )
                    .unwrap_or_else(|e| {
                        panic!("Verification failed for {module_id}::{fname}: {e:?}")
                    });

                    let function_source_map = source_map.get_function_source_map(fdef_idx).unwrap();
                    let label_for_offset: BTreeMap<CodeOffset, String> = function_source_map
                        .labels
                        .iter()
                        .map(|(label, offset)| (*offset, label.0.to_string()))
                        .collect();
                    let mut serializer =
                        SourceMapRegexStateSerializer::new(module, function_source_map);

                    let block_states: BTreeMap<String, _> = states
                        .into_iter()
                        .map(|(offset, invariant)| {
                            let key = label_for_offset
                                .get(&offset)
                                .cloned()
                                .unwrap_or_else(|| offset.to_string());
                            (key, invariant.pre.to_serializable(&mut serializer))
                        })
                        .collect();

                    Some((fname, block_states))
                })
                .collect();
            (module_id.to_string(), fns)
        })
        .collect();

    println!("{}", serde_json::to_string_pretty(&output).unwrap());
}

/// Splits on transactional test directive lines (`//# ...`), returning the text between them.
fn split_on_directives(content: &str) -> Vec<String> {
    let re = regex::Regex::new(r"(?m)^\s*//#[^\n]*\n?").unwrap();
    re.split(content)
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect()
}
