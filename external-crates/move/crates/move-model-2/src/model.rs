// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use std::{collections::HashMap, rc::Rc};

use move_compiler::{
    self, compiled_unit::AnnotatedCompiledUnit, diagnostics::FilesSourceText,
    shared::program_info::TypingProgramInfo, CommentMap,
};
use move_core_types::account_address::AccountAddress;
use move_symbol_pool::Symbol;

pub struct Model {
    pub(crate) files: FilesSourceText,
    pub(crate) comments: CommentMap,
    pub(crate) info: Rc<TypingProgramInfo>,
    pub(crate) compiled_units: HashMap<AccountAddress, HashMap<Symbol, AnnotatedCompiledUnit>>,
}

impl Model {
    pub fn compiled_units(&self) -> &[AnnotatedCompiledUnit] {
        &self.compiled_units
    }
}
