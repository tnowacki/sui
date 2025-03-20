// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use std::{collections::BTreeMap, fmt::Display};

use move_binary_format::{CompiledModule, errors::VMError};
use move_core_types::{account_address::AccountAddress, identifier::Identifier};

pub struct Data {
    pub package_data: BTreeMap<AccountAddress, PackageData>,
}

#[derive(Default)]
pub struct PackageData {
    pub modules: BTreeMap<Identifier, ModuleData>,
    // accurate only if all modules are verified successfully
    pub ticks: u128,
}

pub struct ModuleData {
    pub name: Identifier,
    pub module: CompiledModule,
    pub result: ModuleVerificationResult,
}

pub struct ModuleVerificationResult {
    pub status: ModuleVerificationStatus,
    pub ticks: u128,
    pub function_ticks: BTreeMap<String, u128>,
}

pub enum ModuleVerificationStatus {
    Verified,
    Failed(VMError),
    FunctionsFailed(BTreeMap<String, VMError>),
}

pub struct DataDisplay<'a> {
    pub data: &'a Data,
    pub show_ticks: bool,
}

impl Data {
    pub fn display(&self, show_ticks: bool) -> DataDisplay<'_> {
        DataDisplay {
            data: self,
            show_ticks,
        }
    }
}

impl<'a> Display for DataDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let show_ticks = self.show_ticks;
        let empty_function_failures = BTreeMap::new();
        for (address, package_data) in &self.data.package_data {
            let PackageData { modules, ticks } = package_data;
            let ticks_msg = if show_ticks {
                format!(" ({ticks} ticks)")
            } else {
                String::new()
            };
            writeln!(f, "{address}{ticks_msg}")?;
            for (module_name, module_data) in modules {
                let ticks_msg = if show_ticks {
                    format!(" ({} ticks)", module_data.result.ticks)
                } else {
                    String::new()
                };
                let status_msg = match &module_data.result.status {
                    ModuleVerificationStatus::Verified => "Verified",
                    ModuleVerificationStatus::Failed(_) => "Failed",
                    ModuleVerificationStatus::FunctionsFailed(_) => "Functions Failed",
                };
                writeln!(f, "  {module_name}{ticks_msg}: {status_msg}")?;
                let function_failures = match &module_data.result.status {
                    ModuleVerificationStatus::FunctionsFailed(failures) => failures,
                    _ => &empty_function_failures,
                };
                for (fname, ticks) in &module_data.result.function_ticks {
                    if show_ticks {
                        let status = match function_failures.get(fname) {
                            Some(err) => format!("{}", err),
                            None => "Verified".to_string(),
                        };
                        writeln!(f, "    {fname} ({} ticks) {status}", ticks)?;
                    } else if let Some(err) = function_failures.get(fname) {
                        writeln!(f, "    {fname}: {}", err)?;
                    }
                }
                if !module_data.result.function_ticks.is_empty()
                    && !show_ticks
                    && function_failures.is_empty()
                {
                    writeln!(f, "    All Functions Verified")?;
                }
            }
        }
        Ok(())
    }
}
