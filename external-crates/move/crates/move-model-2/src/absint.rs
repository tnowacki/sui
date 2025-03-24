// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::compiled::Bytecode;
use move_abstract_interpreter::{absint, control_flow_graph};

//**************************************************************************************************
// New traits and public APIS
//**************************************************************************************************

pub use absint::JoinResult;
pub type VMControlFlowGraph<'a> = control_flow_graph::VMControlFlowGraph<'a, Bytecode>;
