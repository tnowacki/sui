// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use std::{collections::HashMap, rc::Rc};

use codespan_reporting::term::termcolor::{StandardStream, WriteColor};
use move_compiler::{
    self,
    compiled_unit::AnnotatedCompiledUnit,
    diagnostics::{env_color, output_diagnostics, Diagnostics, FilesSourceText},
    shared::{program_info::TypingProgramInfo, PackagePaths},
    CommentMap, Compiler, PASS_TYPING,
};
use move_symbol_pool::Symbol;
use vfs::VfsPath;

mod model;

pub use model::*;

// =================================================================================================
// Entry Point

/// A constructor for the `Model` that compiles the program from source
pub struct ModelCompiler {
    compiler: Option<Compiler>, // an option for in-place updates
    /// Output buffer for `Diagnostic` errors. Defaults to stderr.
    diag_buffer: Box<dyn WriteColor>,
}

/// A builder pattern for the `Model`. Used by the `ModelCompiler` but can also be used directly
pub struct ModelBuilder {
    files: Option<FilesSourceText>,
    comments: Option<CommentMap>,
    info: Option<Rc<TypingProgramInfo>>,
    compiled_units: Option<Vec<AnnotatedCompiledUnit>>,
}

impl ModelCompiler {
    pub fn from_package_paths<Paths: Into<Symbol>, NamedAddress: Into<Symbol>>(
        vfs_root: Option<VfsPath>,
        targets: Vec<PackagePaths<Paths, NamedAddress>>,
        deps: Vec<PackagePaths<Paths, NamedAddress>>,
    ) -> anyhow::Result<Self> {
        let color_choice = env_color();
        Ok(Self {
            compiler: Some(Compiler::from_package_paths(vfs_root, targets, deps)?),
            diag_buffer: Box::new(StandardStream::stderr(color_choice)),
        })
    }

    /// Modify the compiler for the builder. Useful for setting compiler flags and other settings
    pub fn modify_compiler(&mut self, f: impl FnOnce(Compiler) -> Compiler) {
        self.compiler = Some(f(self.compiler.take().unwrap()));
    }

    pub fn build(
        self,
    ) -> anyhow::Result<(FilesSourceText, Result<(Model, Diagnostics), Diagnostics>)> {
        let (files, _diag_buffer, res) = self.build_()?;
        Ok((files, res))
    }

    pub fn build_and_report(self) -> anyhow::Result<Model> {
        let (files, mut diag_buffer, res) = self.build_()?;
        let model = match res {
            Ok((model, warnings)) => {
                if !warnings.is_empty() {
                    output_diagnostics(&mut diag_buffer, &files, warnings)
                }
                model
            }
            Err(diags) => {
                output_diagnostics(&mut diag_buffer, &files, diags);
                std::process::exit(1)
            }
        };
        Ok(model)
    }

    fn build_(
        self,
    ) -> anyhow::Result<(
        FilesSourceText,
        Box<dyn WriteColor>,
        Result<(Model, Diagnostics), Diagnostics>,
    )> {
        let Self {
            compiler,
            diag_buffer,
        } = self;
        let compiler = compiler.unwrap();
        let (files, res) = compiler.run::<PASS_TYPING>()?;
        let (comments, compiler) = match res {
            Ok((comments, compiler)) => (comments, compiler),
            Err((_, diags)) => return Ok((files, diag_buffer, Err(diags))),
        };
        let (compiler, typed_prog) = compiler.into_ast();
        let info = typed_prog.info.clone();
        let (compiled_units, warnings) = match compiler.at_typing(typed_prog).build() {
            Ok((compiled_units, warnings)) => (compiled_units, warnings),
            Err((_, diags)) => return Ok((files, diag_buffer, Err(diags))),
        };
        let model = {
            let mut builder = ModelBuilder::new();
            builder.set_files(files);
            builder.set_comment_map(comments);
            builder.set_program_info(info);
            builder.set_compiled_units(compiled_units);
            builder.finish()?
        };
        Ok((files, diag_buffer, Ok((model, warnings))))
    }
}

impl ModelBuilder {
    pub fn new() -> Self {
        Self {
            files: None,
            comments: None,
            info: None,
            compiled_units: None,
        }
    }

    pub fn set_files(&mut self, files: FilesSourceText) {
        assert!(self.files.is_none(), "files already provided");
        self.files = Some(files);
    }

    pub fn set_comment_map(&mut self, comments: CommentMap) {
        assert!(self.comments.is_none(), "comment map already provided");
        self.comments = Some(comments);
    }

    pub fn set_program_info(&mut self, info: Rc<TypingProgramInfo>) {
        assert!(
            self.info.is_none(),
            "compiler program info already provided"
        );
        self.info = Some(info);
    }

    pub fn set_compiled_units(&mut self, compiled_units: Vec<AnnotatedCompiledUnit>) {
        assert!(
            self.compiled_units.is_none(),
            "compiled units already provided"
        );
        self.compiled_units = Some(compiled_units);
    }

    pub fn finish(self) -> anyhow::Result<Model> {
        let Self {
            files,
            comments,
            info,
            compiled_units,
        } = self;
        let files = files.expect("files not provided");
        let comments = comments.expect("comment map not provided");
        let info = info.expect("compiler program info not provided");
        let mut compiled_unit_map = HashMap::new();
        for unit in compiled_units.unwrap() {
            let entry = compiled_unit_map
                .entry(unit.named_module.address.into_inner())
                .or_insert_with(HashMap::new);
            let package_name = unit.package_name();
            let loc = unit.loc();
            if let Some(prev) = entry.insert(unit.named_module.name, unit) {
                anyhow::bail!(
                    "Duplicate module {}::{}. \n\
                    One in package {} in file {}. \n\
                    And one in package {} in file {}",
                    prev.named_module.address,
                    prev.named_module.name,
                    prev.package_name().map(|s| s.as_str()).unwrap_or("UNKNOWN"),
                    files[&prev.loc().file_hash()].0,
                    package_name.map(|s| s.as_str()).unwrap_or("UNKNOWN"),
                    files[&loc.file_hash()].0,
                );
            }
        }
        Ok(Model {
            files,
            comments,
            info,
            compiled_units: compiled_unit_map,
        })
    }
}
