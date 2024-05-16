// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use clap::*;
use move_binary_format::file_format::{FunctionDefinitionIndex, TableIndex};
use move_bytecode_verifier::{control_flow, reference_safety, set_based_reference_safety};
use move_bytecode_verifier_meter::dummy::DummyMeter;
use move_command_line_common::files::{extension_equals, find_filenames, MOVE_COMPILED_EXTENSION};
use move_vm_config::verifier::VerifierConfig;
use std::collections::HashMap;

#[derive(Debug, Parser)]
#[clap(name = "ref-safety-analyze")]
pub struct Options {
    #[clap(
        name = "PATH_TO_MV_FILE",
        action = clap::ArgAction::Append,
    )]
    pub files: Vec<String>,
}

pub fn main() -> anyhow::Result<()> {
    let Options { files } = Options::parse();
    let files = find_filenames(&files, |path| {
        extension_equals(path, MOVE_COMPILED_EXTENSION)
    })?;
    let modules = files
        .into_iter()
        .map(|f| {
            let f = std::fs::read(f).unwrap();
            move_binary_format::file_format::CompiledModule::deserialize_with_defaults(&f)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let verifier_config = VerifierConfig::default();
    println!("module, function, graph, set-star, set-delta");
    for module in modules {
        let id = module.self_id();
        let mut name_def_map = HashMap::new();
        for (idx, func_def) in module.function_defs().iter().enumerate() {
            let fh = module.function_handle_at(func_def.function);
            name_def_map.insert(fh.name, FunctionDefinitionIndex(idx as u16));
        }
        for (idx, function_definition) in module.function_defs().iter().enumerate() {
            let fname = module
                .identifier_at(module.function_handle_at(function_definition.function).name)
                .as_str();
            let index = FunctionDefinitionIndex(idx as TableIndex);
            let code = match &function_definition.code {
                Some(code) => code,
                None => continue,
            };
            let function_context = control_flow::verify_function(
                &verifier_config,
                &module,
                index,
                function_definition,
                code,
                &mut DummyMeter,
            )?;
            let passes_graph_based = reference_safety::verify(
                &module,
                &function_context,
                &name_def_map,
                &mut DummyMeter,
            )
            .is_ok();
            let passes_set_based_star = set_based_reference_safety::verify(
                true,
                &module,
                &function_context,
                &mut DummyMeter,
            )
            .is_ok();
            let passes_set_based_delta = set_based_reference_safety::verify(
                false,
                &module,
                &function_context,
                &mut DummyMeter,
            )
            .is_ok();
            println!(
                "{}, {}, {}, {}, {}",
                id, fname, passes_graph_based, passes_set_based_star, passes_set_based_delta
            );
        }
    }
    Ok(())
}
