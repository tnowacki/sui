// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;

use crate::compiled::{Bytecode, Code};
use move_abstract_interpreter::{
    absint::{self, AbstractInterpreter},
    control_flow_graph::{self, Instruction},
};

//**************************************************************************************************
// New traits and public APIS
//**************************************************************************************************

pub use absint::JoinResult;
use move_binary_format::file_format::CodeOffset;
pub type VMControlFlowGraph = control_flow_graph::VMControlFlowGraph<Bytecode>;

/// Wrapper around `move_abstract_interperter::absint::analyze_function`
pub fn analyze_function<A>(
    interpreter: &mut A,
    cfg: &VMControlFlowGraph,
    code: &[Bytecode],
    initial_state: A::State,
) -> Result<BTreeMap<CodeOffset, A::State>, A::Error>
where
    A: AbstractInterpreter<
        InstructionIndex = CodeOffset,
        BlockId = CodeOffset,
        Instruction = Bytecode,
    >,
{
    absint::analyze_function(interpreter, cfg, code, initial_state)
}
