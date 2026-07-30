//! IR dump command.

use crate::DecompilerContext;

use super::error::{cli_err, CliResult};
use super::format_insn::format_insn;
use super::method_decode::method_matches;
use super::model::IrRequest;
use super::output::CliHost;

/// Dumps a method's decoded IR blocks and successors.
pub struct IrCommand;

impl IrCommand {
    pub fn run(host: &mut impl CliHost, request: &IrRequest) -> CliResult<()> {
        let mut ctx = DecompilerContext::from_file(&request.input)?;
        ctx.load_all_classes()?;

        let (registers_size, ins_size) = {
            let class = ctx
                .get_class(&request.class)
                .ok_or_else(|| cli_err(format!("Class not found: {}", request.class)))?;
            let method = class
                .methods()
                .iter()
                .find(|m| method_matches(m, &request.method, request.descriptor.as_deref()))
                .ok_or_else(|| cli_err(format!("Method not found: {}", request.method)))?;
            let code = method
                .code
                .as_ref()
                .ok_or_else(|| cli_err("Method has no code (abstract or native)"))?;
            (code.registers_size, code.ins_size)
        };

        let ir = ctx
            .decode_method(
                &request.class,
                &request.method,
                request.descriptor.as_deref(),
            )?
            .ok_or_else(|| {
                cli_err(format!(
                    "Method not found: {}.{}",
                    request.class, request.method
                ))
            })?;

        let mut result = String::new();
        result.push_str(&format!(
            "=== IR for {}.{}{} ===\n",
            request.class,
            request.method,
            request.descriptor.as_deref().unwrap_or("")
        ));
        result.push_str(&format!(
            "Registers: {}, Ins: {}\n\n",
            registers_size, ins_size
        ));

        let mut block_ids: Vec<_> = ir.blocks.keys().copied().collect();
        block_ids.sort();

        for block_id in block_ids {
            if let Some(block) = ir.blocks.get(&block_id) {
                result.push_str(&format!("BB{}:\n", block_id));
                for insn in &block.insns {
                    result.push_str(&format!("  {}\n", format_insn(insn)));
                }

                let succs: Vec<String> = ir
                    .successors(block_id)
                    .map(|s| format!("BB{}", s))
                    .collect();
                if !succs.is_empty() {
                    result.push_str(&format!("  -> {}\n", succs.join(", ")));
                }
                result.push('\n');
            }
        }

        host.emit_or_write(request.output.as_deref(), &result)
    }
}
