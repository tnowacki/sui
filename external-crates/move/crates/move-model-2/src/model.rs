// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use std::{
    cell::OnceCell,
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use move_binary_format::file_format::{self, CompiledModule, SignatureToken};
use move_compiler::{
    self,
    compiled_unit::AnnotatedCompiledUnit,
    diagnostics::FilesSourceText,
    expansion::ast as E,
    expansion::ast::ModuleIdent_,
    naming::ast as N,
    shared::{
        program_info::{ConstantInfo, FunctionInfo, ModuleInfo, TypingProgramInfo},
        NumericalAddress,
    },
    CommentMap,
};
use move_core_types::{
    account_address::AccountAddress, annotated_value, language_storage::ModuleId as CoreModuleId,
};
use move_ir_types::{
    ast as ir,
    location::{Loc, Spanned},
};
use move_symbol_pool::Symbol;

//**************************************************************************************************
// Types
//**************************************************************************************************

pub struct ModelData {
    files: Arc<FilesSourceText>,
    comments: CommentMap,
    info: Arc<TypingProgramInfo>,
    compiled_units: BTreeMap<AccountAddress, BTreeMap<Symbol, AnnotatedCompiledUnit>>,
    module_deps: BTreeMap<ModuleId, BTreeMap<ModuleId, /* is immediate */ bool>>,
    // reverse mapping of module_deps
    module_used_by: BTreeMap<ModuleId, BTreeSet<ModuleId>>,
    function_immediate_deps: BTreeMap<QualifiedMemberId, BTreeSet<QualifiedMemberId>>,
    // reverse mapping of function_immediate_deps
    function_called_by: BTreeMap<QualifiedMemberId, BTreeSet<QualifiedMemberId>>,
}

pub struct Model<'a> {
    pub(crate) data: &'a ModelData,
    pub(crate) modules: BTreeMap<AccountAddress, BTreeMap<Symbol, Module<'a>>>,
}

pub trait TModuleId {
    fn module_id(&self) -> ModuleId;
}

pub type ModuleId = (AccountAddress, Symbol);
pub type QualifiedMemberId = (ModuleId, Symbol);

pub struct Module<'a> {
    id: ModuleId,
    ident: E::ModuleIdent,
    data: &'a ModelData,
    info: &'a ModuleInfo,
    compiled: &'a AnnotatedCompiledUnit,
    structs: BTreeMap<Symbol, Struct<'a>>,
    enums: BTreeMap<Symbol, Enum<'a>>,
    functions: BTreeMap<Symbol, Function<'a>>,
    constants: BTreeMap<Symbol, Constant<'a>>,
}

pub enum Member<'a> {
    Struct(&'a Struct<'a>),
    Enum(&'a Enum<'a>),
    Function(&'a Function<'a>),
    Constant(&'a Constant<'a>),
}

pub enum Datatype<'a> {
    Struct(&'a Struct<'a>),
    Enum(&'a Enum<'a>),
}

pub struct Struct<'a> {
    name: Symbol,
    data: &'a ModelData,
    module: &'a CompiledModule,
    info: &'a N::StructDefinition,
    compiled: &'a file_format::StructDefinition,
    compiled_idx: file_format::StructDefinitionIndex,
}

pub struct Enum<'a> {
    name: Symbol,
    data: &'a ModelData,
    module: &'a CompiledModule,
    info: &'a N::EnumDefinition,
    // enum_def: &'a file_format::EnumDefinition,
}

pub struct Function<'a> {
    name: Symbol,
    data: &'a ModelData,
    module: &'a CompiledModule,
    info: &'a FunctionInfo,
    compiled: &'a file_format::FunctionDefinition,
    compiled_idx: file_format::FunctionDefinitionIndex,
}

pub struct Constant<'a> {
    name: Symbol,
    data: &'a ModelData,
    module: &'a CompiledModule,
    info: &'a ConstantInfo,
    compiled: &'a file_format::Constant,
    compiled_idx: file_format::ConstantPoolIndex,
    value: OnceCell<annotated_value::MoveValue>,
}

//**************************************************************************************************
// API
//**************************************************************************************************

impl ModelData {
    /// Note that this is O(n) over the modules and should be done once per model.
    pub fn model(&self) -> Model<'_> {
        Model::new(self)
    }
}

impl<'a> Model<'a> {
    pub fn module(&self, module: impl TModuleId) -> Option<&Module> {
        let (address, name) = module.module_id();
        self.modules.get(&address)?.get(&name)
    }

    pub fn modules(&self) -> impl Iterator<Item = (ModuleId, &Module)> {
        self.modules.iter().flat_map(|(address, modules)| {
            modules
                .iter()
                .map(move |(name, module)| ((*address, *name), module))
        })
    }

    pub fn doc_at(&self, loc: Loc) -> Option<&str> {
        self.data.doc_at(loc)
    }
}

impl<'a> Module<'a> {
    pub fn struct_(&self, name: impl Into<Symbol>) -> Option<&Struct> {
        self.structs.get(&name.into())
    }

    pub fn enum_(&self, name: impl Into<Symbol>) -> Option<&Enum> {
        self.enums.get(&name.into())
    }

    pub fn function(&self, name: impl Into<Symbol>) -> Option<&Function> {
        self.functions.get(&name.into())
    }

    pub fn constant(&self, name: impl Into<Symbol>) -> Option<&Constant> {
        self.constants.get(&name.into())
    }

    pub fn member(&self, name: impl Into<Symbol>) -> Option<Member<'_>> {
        let name = name.into();
        self.structs
            .get(&name)
            .map(Member::Struct)
            .or_else(|| self.enums.get(&name).map(Member::Enum))
            .or_else(|| self.functions.get(&name).map(Member::Function))
            .or_else(|| self.constants.get(&name).map(Member::Constant))
    }

    pub fn datatype(&self, name: impl Into<Symbol>) -> Option<Datatype<'_>> {
        let name = name.into();
        self.structs
            .get(&name)
            .map(Datatype::Struct)
            .or_else(|| self.enums.get(&name).map(Datatype::Enum))
    }

    pub fn structs(&self) -> impl Iterator<Item = (Symbol, &Struct)> {
        self.structs.iter().map(|(name, s)| (*name, s))
    }

    pub fn enums(&self) -> impl Iterator<Item = (Symbol, &Enum)> {
        self.enums.iter().map(|(name, e)| (*name, e))
    }

    pub fn functions(&self) -> impl Iterator<Item = (Symbol, &Function)> {
        self.functions.iter().map(|(name, f)| (*name, f))
    }

    pub fn constants(&self) -> impl Iterator<Item = (Symbol, &Constant)> {
        self.constants.iter().map(|(name, c)| (*name, c))
    }

    pub fn info(&self) -> &ModuleInfo {
        self.info
    }

    pub fn compiled(&self) -> &AnnotatedCompiledUnit {
        self.compiled
    }

    pub fn ident(&self) -> &E::ModuleIdent {
        &self.ident
    }

    pub fn id(&self) -> ModuleId {
        self.id
    }

    pub fn source_path(&self) -> Symbol {
        self.data.files[&self.compiled.loc().file_hash()].0
    }

    pub fn loc(&self) -> Loc {
        self.info.defined_loc
    }

    pub fn doc(&self) -> &str {
        todo!()
    }

    pub fn deps(&self) -> &BTreeMap<ModuleId, /* is immediate */ bool> {
        &self.data.module_deps[&self.id()]
    }

    pub fn used_by(&self) -> &BTreeSet<ModuleId> {
        &self.data.module_used_by[&self.id()]
    }
}

impl<'a> Struct<'a> {
    pub fn name(&self) -> Symbol {
        self.name
    }

    pub fn module(&self) -> &CompiledModule {
        self.module
    }

    pub fn info(&self) -> &N::StructDefinition {
        self.info
    }

    pub fn compiled(&self) -> &file_format::StructDefinition {
        self.compiled
    }

    pub fn compiled_idx(&self) -> file_format::StructDefinitionIndex {
        self.compiled_idx
    }

    pub fn struct_handle(&self) -> &file_format::StructHandle {
        self.module.struct_handle_at(self.compiled.struct_handle)
    }

    pub fn doc(&self) -> &str {
        todo!()
    }
}

impl<'a> Enum<'a> {
    pub fn name(&self) -> Symbol {
        self.name
    }

    pub fn module(&self) -> &CompiledModule {
        self.module
    }

    pub fn info(&self) -> &N::EnumDefinition {
        self.info
    }

    // pub fn compiled(&self) -> &file_format::EnumDefinition {
    //     self.compiled
    // }

    pub fn doc(&self) -> &str {
        todo!()
    }
}

impl<'a> Function<'a> {
    pub fn name(&self) -> Symbol {
        self.name
    }

    pub fn module(&self) -> &CompiledModule {
        self.module
    }

    pub fn info(&self) -> &FunctionInfo {
        self.info
    }

    pub fn compiled(&self) -> &file_format::FunctionDefinition {
        self.compiled
    }

    pub fn compiled_idx(&self) -> file_format::FunctionDefinitionIndex {
        self.compiled_idx
    }

    pub fn doc(&self) -> &str {
        todo!()
    }

    pub fn function_handle(&self) -> &file_format::FunctionHandle {
        self.module.function_handle_at(self.compiled.function)
    }

    pub fn compiled_parameters(&self) -> &file_format::Signature {
        self.module.signature_at(self.function_handle().parameters)
    }

    pub fn compiled_return_type(&self) -> &file_format::Signature {
        self.module.signature_at(self.function_handle().return_)
    }

    /// Returns an iterator over the functions  called by this function.
    pub fn calls(&self) -> &BTreeSet<QualifiedMemberId> {
        let module_id: ModuleId = self.module.self_id().module_id();
        self.data
            .function_immediate_deps
            .get(&(module_id, self.name))
            .unwrap()
    }

    /// Returns an iterator over the functions that call this function.
    pub fn called_by(&self) -> &BTreeSet<QualifiedMemberId> {
        let module_id: ModuleId = self.module.self_id().module_id();
        self.data
            .function_called_by
            .get(&(module_id, self.name))
            .unwrap()
    }
}

impl<'a> Constant<'a> {
    pub fn name(&self) -> Symbol {
        self.name
    }

    pub fn module(&self) -> &CompiledModule {
        self.module
    }

    pub fn info(&self) -> &ConstantInfo {
        self.info
    }

    pub fn compiled(&self) -> &file_format::Constant {
        self.compiled
    }

    pub fn compiled_idx(&self) -> file_format::ConstantPoolIndex {
        self.compiled_idx
    }

    pub fn doc(&self) -> &str {
        todo!()
    }

    /// Returns the value of the constant as a `annotated_move::MoveValue`.
    /// This result will be cached and it will be deserialized only once.
    pub fn value(&self) -> &annotated_value::MoveValue {
        self.value.get_or_init(|| {
            let constant_layout = Self::annotated_constant_layout(&self.compiled.type_);
            annotated_value::MoveValue::simple_deserialize(&self.compiled.data, &constant_layout)
                .unwrap()
        })
    }

    /// If the constant is a vector<u8>, it will rendered as a UTF8 string.
    /// If it has some other type (or if the data is not a valid UTF8 string),
    /// it will will call display on the `annotated_move::MoveValue`
    pub fn display_value(&self) -> String {
        if matches!(&self.compiled.type_, SignatureToken::Vector(x) if x.as_ref() == &SignatureToken::U8)
        {
            if let Some(str) = bcs::from_bytes::<Vec<u8>>(&self.compiled.data)
                .ok()
                .and_then(|data| String::from_utf8(data).ok())
            {
                return format!("\"{str}\"");
            }
        }

        format!("{}", self.value())
    }

    fn annotated_constant_layout(ty: &SignatureToken) -> annotated_value::MoveTypeLayout {
        use annotated_value::MoveTypeLayout as L;
        use SignatureToken as ST;
        match ty {
            ST::Bool => L::Bool,
            ST::U8 => L::U8,
            ST::U16 => L::U16,
            ST::U32 => L::U16,
            ST::U64 => L::U64,
            ST::U128 => L::U128,
            ST::U256 => L::U16,
            ST::Address => L::Address,
            ST::Signer => L::Signer,
            ST::Vector(inner) => L::Vector(Box::new(Self::annotated_constant_layout(inner))),

            ST::Struct(_)
            | ST::StructInstantiation(_)
            | ST::Reference(_)
            | ST::MutableReference(_)
            | ST::TypeParameter(_) => unreachable!("{ty:?} is not supported in constants"),
        }
    }
}

//**************************************************************************************************
// Traits
//**************************************************************************************************

impl TModuleId for CoreModuleId {
    fn module_id(&self) -> ModuleId {
        (*self.address(), self.name().as_str().into())
    }
}

impl TModuleId for ModuleId {
    fn module_id(&self) -> ModuleId {
        *self
    }
}

impl TModuleId for (&AccountAddress, &Symbol) {
    fn module_id(&self) -> ModuleId {
        (*self.0, *self.1)
    }
}

impl TModuleId for (NumericalAddress, Symbol) {
    fn module_id(&self) -> ModuleId {
        (self.0.into_inner(), self.1)
    }
}

impl TModuleId for (&NumericalAddress, &Symbol) {
    fn module_id(&self) -> ModuleId {
        (self.0.clone().into_inner(), *self.1)
    }
}
impl TModuleId for ModuleIdent_ {
    fn module_id(&self) -> ModuleId {
        let address = self.address.into_addr_bytes().into_inner();
        let module = self.module.0.value;
        (address, module)
    }
}

impl<T: TModuleId> TModuleId for &T {
    fn module_id(&self) -> ModuleId {
        T::module_id(*self)
    }
}

impl<T: TModuleId> TModuleId for Spanned<T> {
    fn module_id(&self) -> ModuleId {
        T::module_id(&self.value)
    }
}

//**************************************************************************************************
// Internals
//**************************************************************************************************

impl<'a> ModelData {
    fn doc_at(&self, loc: Loc) -> Option<&str> {
        self.comments
            .get(&loc.file_hash())
            .and_then(|comments| comments.get(&loc.start()).map(|s| s.as_str()))
    }
}

//**************************************************************************************************
// Construction
//**************************************************************************************************
impl ModelData {
    pub fn new(
        files: Arc<FilesSourceText>,
        comments: CommentMap,
        info: Arc<TypingProgramInfo>,
        compiled_units: BTreeMap<AccountAddress, BTreeMap<Symbol, AnnotatedCompiledUnit>>,
    ) -> Self {
        let (module_deps, module_used_by) = Self::compute_dependencies(&compiled_units);
        let (function_immediate_deps, function_called_by) =
            Self::compute_function_dependencies(&compiled_units);
        Self {
            files,
            comments,
            info,
            compiled_units,
            module_deps,
            module_used_by,
            function_immediate_deps,
            function_called_by,
        }
    }

    fn compute_dependencies(
        compiled_units: &BTreeMap<AccountAddress, BTreeMap<Symbol, AnnotatedCompiledUnit>>,
    ) -> (
        BTreeMap<ModuleId, BTreeMap<ModuleId, /* is immediate */ bool>>,
        BTreeMap<ModuleId, BTreeSet<ModuleId>>,
    ) {
        fn visit(
            compiled_units: &BTreeMap<AccountAddress, BTreeMap<Symbol, AnnotatedCompiledUnit>>,
            acc: &mut BTreeMap<ModuleId, BTreeMap<ModuleId, bool>>,
            id: ModuleId,
            unit: &AnnotatedCompiledUnit,
        ) {
            if acc.contains_key(&id) {
                return;
            }

            let immediate_deps = unit
                .named_module
                .module
                .immediate_dependencies()
                .into_iter()
                .map(|id| (*id.address(), Symbol::from(id.name().as_str())))
                .collect::<Vec<_>>();
            for immediate_dep in &immediate_deps {
                let unit = compiled_units
                    .get(&immediate_dep.0)
                    .unwrap()
                    .get(&immediate_dep.1)
                    .unwrap();
                visit(compiled_units, acc, *immediate_dep, unit);
            }
            let mut deps = BTreeMap::new();
            for immediate_dep in immediate_deps {
                deps.insert(immediate_dep, true);
                for transitive_dep in acc.get(&immediate_dep).unwrap().keys() {
                    if !deps.contains_key(transitive_dep) {
                        deps.insert(*transitive_dep, false);
                    }
                }
            }
            acc.insert(id, deps);
        }

        let mut module_deps = BTreeMap::new();
        for (address, units) in compiled_units {
            for (name, unit) in units {
                visit(&compiled_units, &mut module_deps, (*address, *name), unit);
            }
        }
        let mut module_used_by = module_deps
            .keys()
            .map(|id| (*id, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        for (id, deps) in &module_deps {
            for dep in deps.keys() {
                module_used_by.get_mut(dep).unwrap().insert(*id);
            }
        }
        (module_deps, module_used_by)
    }

    fn compute_function_dependencies(
        compiled_units: &BTreeMap<AccountAddress, BTreeMap<Symbol, AnnotatedCompiledUnit>>,
    ) -> (
        /* calls */ BTreeMap<QualifiedMemberId, BTreeSet<QualifiedMemberId>>,
        /* called by */ BTreeMap<QualifiedMemberId, BTreeSet<QualifiedMemberId>>,
    ) {
        let function_immediate_deps: BTreeMap<_, BTreeSet<_>> = compiled_units
            .iter()
            .flat_map(|(address, units)| {
                units.iter().flat_map(|(name, unit)| {
                    let module = &unit.named_module.module;
                    let module_id = (*address, *name);
                    module.function_defs().iter().map(move |fdef| {
                        let fhandle = module.function_handle_at(fdef.function);
                        let fname = module.identifier_at(fhandle.name);
                        let qualified_id = (module_id, Symbol::from(fname.as_str()));
                        let callees = fdef
                            .code
                            .as_ref()
                            .iter()
                            .flat_map(|c| c.code.iter())
                            .filter_map(|instr| match instr {
                                file_format::Bytecode::Call(i) => Some(*i),
                                file_format::Bytecode::CallGeneric(i) => {
                                    Some(module.function_instantiation_at(*i).handle)
                                }
                                _ => None,
                            })
                            .map(|i| {
                                let callee_handle = module.function_handle_at(i);
                                let callee_module = module
                                    .module_id_for_handle(
                                        module.module_handle_at(callee_handle.module),
                                    )
                                    .module_id();
                                let callee_name = module.identifier_at(fhandle.name);
                                (callee_module, Symbol::from(callee_name.as_str()))
                            })
                            .collect();
                        (qualified_id, callees)
                    })
                })
            })
            .collect();
        // ensure the map is populated for all functions
        let mut function_called_by = function_immediate_deps
            .keys()
            .map(|caller| (*caller, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        for (caller, callees) in &function_immediate_deps {
            for callee in callees {
                function_called_by.get_mut(callee).unwrap().insert(*caller);
            }
        }
        (function_immediate_deps, function_called_by)
    }
}

impl<'a> Model<'a> {
    /// Given the data for the model, generate information about the module and its members. Note
    /// that this is O(n) over the modules and should be done once per model.
    pub fn new(data: &'a ModelData) -> Self {
        let modules = data
            .compiled_units
            .iter()
            .map(|(address, units)| {
                let modules = units
                    .iter()
                    .map(|(name, unit)| {
                        let info = data.info.modules.get(&unit.module_ident()).unwrap();
                        let module = Module::new(data, info, unit);
                        (*name, module)
                    })
                    .collect();
                (*address, modules)
            })
            .collect();
        Self { data, modules }
    }

    pub fn compiled_units(&self) -> impl Iterator<Item = &AnnotatedCompiledUnit> {
        self.data.compiled_units.values().flat_map(|m| m.values())
    }
}

impl<'a> Module<'a> {
    fn new(data: &'a ModelData, info: &'a ModuleInfo, unit: &'a AnnotatedCompiledUnit) -> Self {
        let module = &unit.named_module.module;
        let structs = info
            .structs
            .iter()
            .map(|(_loc, name, sinfo)| {
                let name = *name;
                let (idx, struct_def) = unit
                    .named_module
                    .module
                    .find_struct_def_by_name(name.as_str())
                    .unwrap();
                let struct_ = Struct::new(name, data, module, sinfo, struct_def, idx);
                (name, struct_)
            })
            .collect();
        let functions = info
            .functions
            .iter()
            .map(|(_loc, name, finfo)| {
                let name = *name;
                let (idx, function_def) = unit
                    .named_module
                    .module
                    .find_function_def_by_name(name.as_str())
                    .unwrap();
                let function = Function::new(name, data, module, finfo, function_def, idx);
                (name, function)
            })
            .collect();
        let constants = info
            .constants
            .iter()
            .map(|(_loc, name, cinfo)| {
                let name = *name;
                let cname = ir::ConstantName(name);
                let idx = *unit
                    .named_module
                    .source_map
                    .constant_map
                    .get(&cname)
                    .unwrap();
                let idx = file_format::ConstantPoolIndex(idx);
                let constant_def = unit.named_module.module.constant_at(idx);
                let constant = Constant::new(name, data, module, cinfo, constant_def, idx);
                (name, constant)
            })
            .collect();
        let ident = unit.module_ident();
        let id = (
            ident.value.address.into_addr_bytes().into_inner(),
            ident.value.module.0.value,
        );
        Self {
            id,
            ident,
            data,
            info,
            compiled: unit,
            structs,
            enums: BTreeMap::new(),
            functions,
            constants,
        }
    }
}

impl<'a> Struct<'a> {
    fn new(
        name: Symbol,
        data: &'a ModelData,
        module: &'a CompiledModule,
        info: &'a N::StructDefinition,
        compiled: &'a file_format::StructDefinition,
        compiled_idx: file_format::StructDefinitionIndex,
    ) -> Self {
        Self {
            name,
            data,
            module,
            info,
            compiled,
            compiled_idx,
        }
    }
}

impl<'a> Function<'a> {
    fn new(
        name: Symbol,
        data: &'a ModelData,
        module: &'a CompiledModule,
        info: &'a FunctionInfo,
        compiled: &'a file_format::FunctionDefinition,
        compiled_idx: file_format::FunctionDefinitionIndex,
    ) -> Self {
        Self {
            name,
            data,
            module,
            info,
            compiled,
            compiled_idx,
        }
    }
}

impl<'a> Constant<'a> {
    fn new(
        name: Symbol,

        data: &'a ModelData,
        module: &'a CompiledModule,
        info: &'a ConstantInfo,
        compiled: &'a file_format::Constant,
        compiled_idx: file_format::ConstantPoolIndex,
    ) -> Self {
        Self {
            name,
            data,
            module,
            info,
            compiled,
            value: OnceCell::new(),
            compiled_idx,
        }
    }
}
