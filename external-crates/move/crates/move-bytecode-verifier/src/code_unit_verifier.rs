// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

//! This module implements the checker for verifying correctness of function bodies.
//! The overall verification is split between stack_usage_verifier.rs and
//! abstract_interpreter.rs. CodeUnitVerifier simply orchestrates calls into these two files.
use crate::{
    ability_cache::AbilityCache, acquires_list_verifier::AcquiresVerifier, control_flow,
    locals_safety, reference_safety, regex_reference_safety, set_based_reference_safety,
    stack_usage_verifier::StackUsageVerifier, type_safety,
};
use move_abstract_interpreter::{absint::FunctionContext, control_flow_graph::ControlFlowGraph};
use move_binary_format::{
    IndexKind,
    errors::{Location, PartialVMError, PartialVMResult, VMResult},
    file_format::{
        CompiledModule, FunctionDefinition, FunctionDefinitionIndex, IdentifierIndex, TableIndex,
    },
};
use move_bytecode_verifier_meter::{Meter, Scope};
use move_core_types::vm_status::StatusCode;
use move_vm_config::verifier::VerifierConfig;
use std::collections::HashMap;

pub struct CodeUnitVerifier<'env, 'a> {
    module: &'env CompiledModule,
    function_context: FunctionContext<'env>,
    name_def_map: &'a HashMap<IdentifierIndex, FunctionDefinitionIndex>,
}

pub fn verify_module<'env>(
    verifier_config: &VerifierConfig,
    module: &'env CompiledModule,
    ability_cache: &mut AbilityCache<'env>,
    meter: &mut (impl Meter + ?Sized),
) -> VMResult<()> {
    verify_module_impl(verifier_config, module, ability_cache, meter)
        .map_err(|e| e.finish(Location::Module(module.self_id())))
}

fn verify_module_impl<'env>(
    verifier_config: &VerifierConfig,
    module: &'env CompiledModule,
    ability_cache: &mut AbilityCache<'env>,
    meter: &mut (impl Meter + ?Sized),
) -> PartialVMResult<()> {
    let mut name_def_map = HashMap::new();
    for (idx, func_def) in module.function_defs().iter().enumerate() {
        let fh = module.function_handle_at(func_def.function);
        name_def_map.insert(fh.name, FunctionDefinitionIndex(idx as u16));
    }
    let mut total_back_edges = 0;
    for (idx, function_definition) in module.function_defs().iter().enumerate() {
        let index = FunctionDefinitionIndex(idx as TableIndex);
        let num_back_edges = verify_function(
            verifier_config,
            index,
            function_definition,
            module,
            ability_cache,
            &name_def_map,
            meter,
        )
        .map_err(|err| err.at_index(IndexKind::FunctionDefinition, index.0))?;
        total_back_edges += num_back_edges;
    }
    if let Some(limit) = verifier_config.max_back_edges_per_module {
        if total_back_edges > limit {
            return Err(PartialVMError::new(StatusCode::TOO_MANY_BACK_EDGES));
        }
    }
    Ok(())
}

pub fn verify_function<'env>(
    verifier_config: &VerifierConfig,
    index: FunctionDefinitionIndex,
    function_definition: &'env FunctionDefinition,
    module: &'env CompiledModule,
    ability_cache: &mut AbilityCache<'env>,
    name_def_map: &HashMap<IdentifierIndex, FunctionDefinitionIndex>,
    meter: &mut (impl Meter + ?Sized),
) -> PartialVMResult<usize> {
    meter.enter_scope(
        module
            .identifier_at(module.function_handle_at(function_definition.function).name)
            .as_str(),
        Scope::Function,
    );
    // nothing to verify for native function
    let code = match &function_definition.code {
        Some(code) => code,
        None => return Ok(0),
    };

    // create `FunctionContext` and `BinaryIndexedView`
    let function_context = control_flow::verify_function(
        verifier_config,
        module,
        index,
        function_definition,
        code,
        meter,
    )?;

    if let Some(limit) = verifier_config.max_basic_blocks {
        if function_context.cfg().blocks().len() > limit {
            return Err(
                PartialVMError::new(StatusCode::TOO_MANY_BASIC_BLOCKS).at_code_offset(index, 0)
            );
        }
    }

    let num_back_edges = function_context.cfg().num_back_edges();
    if let Some(limit) = verifier_config.max_back_edges_per_function {
        if num_back_edges > limit {
            return Err(
                PartialVMError::new(StatusCode::TOO_MANY_BACK_EDGES).at_code_offset(index, 0)
            );
        }
    }

    // verify
    let code_unit_verifier = CodeUnitVerifier {
        module,
        function_context,
        name_def_map,
    };
    code_unit_verifier.verify_common(verifier_config, ability_cache, meter)?;
    AcquiresVerifier::verify(module, index, function_definition, meter)?;

    meter.transfer(Scope::Function, Scope::Module, 1.0)?;

    Ok(num_back_edges)
}

impl<'env> CodeUnitVerifier<'env, '_> {
    fn verify_common(
        &self,
        verifier_config: &VerifierConfig,
        ability_cache: &mut AbilityCache<'env>,
        meter: &mut (impl Meter + ?Sized),
    ) -> PartialVMResult<()> {
        const REF_NEW_VERSION_REMOVE_ME: &str = "REF";
        let safety_option = {
            let val = std::env::var(REF_NEW_VERSION_REMOVE_ME).map(|s| s.to_ascii_lowercase());
            let val = val.as_ref().map(|s| s.as_str());
            match val {
                Ok("graph") => Safety::Graph,
                Ok("star") => Safety::Set(true),
                Ok("delta") => Safety::Set(false),
                Ok("regex") => Safety::Regex,
                _ => panic!(
                    "Please set the env '{}' to 'graph', 'star', 'delta', or 'regex'.\n\
                    'graph' for legacy, graph-based analysis.\n\
                    'star' for set-based approach where calls only use '*'.\n\
                    'delta' for set-based approach where calls use deltas for mut refs.\n\
                    'regex' for regex-based graph analysis.\n",
                    REF_NEW_VERSION_REMOVE_ME
                ),
            }
        };
        StackUsageVerifier::verify(verifier_config, self.module, &self.function_context, meter)?;
        type_safety::verify(self.module, &self.function_context, ability_cache, meter)?;
        locals_safety::verify(self.module, &self.function_context, ability_cache, meter)?;

        match safety_option {
            Safety::Graph => reference_safety::verify(
                self.module,
                &self.function_context,
                self.name_def_map,
                meter,
            ),
            Safety::Set(simple_calls) => set_based_reference_safety::verify(
                simple_calls,
                self.module,
                &self.function_context,
                meter,
            ),
            Safety::Regex => {
                regex_reference_safety::verify(self.module, &self.function_context, meter)
            }
        }
    }
}

enum Safety {
    Graph,
    Set(/* simple calls */ bool),
    Regex,
}
