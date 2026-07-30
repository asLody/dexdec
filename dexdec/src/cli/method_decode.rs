//! Shared method CFG decoding helpers for CFG and trace commands.

use std::path::Path;
use std::sync::Arc;

use crate::frontend::MethodNode;
use crate::ir::analysis::ClassHierarchyIndex;
use crate::ir::CFG;
use crate::DecompilerContext;

use super::error::{cli_err, CliResult};

/// Decodes a method's raw CFG without running analysis passes.
pub struct MethodCfgDecoder;

impl MethodCfgDecoder {
    pub fn decode_raw(
        dex_file: &Path,
        class_name: &str,
        method_name: &str,
        descriptor: Option<&str>,
    ) -> CliResult<CFG> {
        let mut context = DecompilerContext::from_file(dex_file)?;
        if context.load_class(class_name)?.is_none() {
            return Err(cli_err(format!("Class not found: {class_name}")));
        }
        context
            .decode_method(class_name, method_name, descriptor)?
            .cloned()
            .ok_or_else(|| {
                cli_err(format!(
                    "Method not found or has no code: {class_name}.{method_name}"
                ))
            })
    }

    pub fn decode_analysis(
        dex_file: &Path,
        class_name: &str,
        method_name: &str,
        descriptor: Option<&str>,
    ) -> CliResult<(CFG, Arc<ClassHierarchyIndex>)> {
        let mut context = DecompilerContext::from_file(dex_file)?;
        if context.load_class(class_name)?.is_none() {
            return Err(cli_err(format!("Class not found: {class_name}")));
        }
        let cfg = context
            .decode_method(class_name, method_name, descriptor)?
            .cloned()
            .ok_or_else(|| {
                cli_err(format!(
                    "Method not found or has no code: {class_name}.{method_name}"
                ))
            })?;
        let hierarchy = context.type_hierarchy()?;
        Ok((cfg, hierarchy))
    }
}

/// Match a method by name and optional JVM descriptor.
pub fn method_matches(method: &MethodNode, name: &str, descriptor: Option<&str>) -> bool {
    if method.info.name != name {
        return false;
    }
    descriptor.is_none_or(|descriptor| method.info.descriptor() == descriptor)
}
