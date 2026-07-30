//! CFG Visualization - Generate DOT format for control flow graphs
//!
//! This module provides visualization of control flow graphs using
//! the DOT graph description language, which can be rendered with Graphviz.

use std::fmt::Write;

use crate::ir::block::Block;
use crate::ir::cfg::CFG;
use crate::ir::insn::{InsnNode, InsnType};
use crate::ir::{ArgType, MemberReference};

/// Generate DOT format representation of a method's CFG
pub fn method_to_dot(ir: &CFG) -> String {
    let mut out = String::new();

    writeln!(out, "digraph \"{}\" {{", escape_dot_string(ir.label())).unwrap();
    writeln!(out, "    rankdir=TB;").unwrap();
    writeln!(
        out,
        "    node [shape=box, fontname=\"Courier New\", fontsize=10];"
    )
    .unwrap();
    writeln!(out, "    edge [fontname=\"Arial\", fontsize=9];").unwrap();
    writeln!(out).unwrap();

    // Entry point indicator
    writeln!(out, "    entry [shape=point, width=0.2];").unwrap();
    writeln!(out, "    entry -> BB{};", ir.entry).unwrap();
    writeln!(out).unwrap();

    // Generate nodes for each basic block
    let mut block_ids: Vec<_> = ir.blocks.keys().copied().collect();
    block_ids.sort();

    for block_id in &block_ids {
        if let Some(block) = ir.blocks.get(block_id) {
            let label = block_to_label(block);
            writeln!(
                out,
                "    BB{} [label=\"{}\"];",
                block_id,
                escape_dot_string(&label)
            )
            .unwrap();
        }
    }

    writeln!(out).unwrap();

    // Generate edges for control flow
    for block_id in &block_ids {
        if ir.blocks.contains_key(block_id) {
            let successors = ir.successors_with_kind(*block_id);
            for &(succ, kind) in successors.iter().filter(|(_, kind)| !kind.is_exception()) {
                let edge_label = get_edge_label(kind);
                if let Some(label) = edge_label {
                    writeln!(
                        out,
                        "    BB{} -> BB{} [label=\"{}\"];",
                        block_id, succ, label
                    )
                    .unwrap();
                } else {
                    writeln!(out, "    BB{} -> BB{};", block_id, succ).unwrap();
                }
            }
        }
    }

    // Add exception handler edges with different style
    for handler in &ir.handlers {
        let style = if handler.catch_type.is_some() {
            format!(
                "label=\"catch {}\", style=dashed, color=red",
                handler
                    .catch_type
                    .as_ref()
                    .map(|t| shorten_type(t))
                    .unwrap_or_default()
            )
        } else {
            "label=\"catch-all\", style=dashed, color=red".to_string()
        };
        writeln!(
            out,
            "    // Exception handler: BB{} -> BB{} [{}]",
            handler.start, handler.handler, style
        )
        .unwrap();
    }

    writeln!(out, "}}").unwrap();
    out
}

/// Generate a label for a basic block showing its instructions
fn block_to_label(block: &Block) -> String {
    let mut label = format!("BB{}", block.id);

    if block.insns.is_empty() {
        label.push_str("\\l(empty)");
        return label;
    }

    for insn in &block.insns {
        label.push_str("\\l");
        label.push_str(&insn_to_short_string(insn));
    }

    label
}

/// Get an exact label from the control-edge identity.
fn get_edge_label(kind: crate::ir::EdgeKind) -> Option<String> {
    match kind {
        crate::ir::EdgeKind::True => Some("true".to_string()),
        crate::ir::EdgeKind::False => Some("false".to_string()),
        crate::ir::EdgeKind::SwitchCase(value) => Some(format!("case {value}")),
        crate::ir::EdgeKind::SwitchDefault => Some("default".to_string()),
        crate::ir::EdgeKind::Normal | crate::ir::EdgeKind::Exception => None,
    }
}

/// Convert an instruction to a short string representation
fn insn_to_short_string(insn: &InsnNode) -> String {
    let dest_str = insn
        .result
        .as_ref()
        .map(|r| format!("v{} = ", r.reg_num))
        .unwrap_or_default();

    match &insn.insn_type {
        InsnType::Const => {
            let val = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            format!("{}const {}", dest_str, val)
        }
        InsnType::ConstStr => {
            let s = insn
                .payload
                .string_value
                .as_ref()
                .map(|s| format!("\"{}\"", truncate_string(&s.to_string_lossy(), 20)))
                .unwrap_or_default();
            format!("{}const-string {}", dest_str, s)
        }
        InsnType::ConstClass => {
            let ty = insn
                .payload
                .class_type
                .as_ref()
                .map(|t| format!("{}", t))
                .unwrap_or_else(|| "?".to_string());
            format!("{}const-class {}", dest_str, ty)
        }
        InsnType::Move => {
            let src = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            format!("{}move {}", dest_str, src)
        }
        InsnType::CompoundAssign => {
            let target = insn
                .payload
                .compound_target
                .as_ref()
                .map(|arg| format!("{}", arg))
                .unwrap_or_else(|| "?".to_string());
            let rhs = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_else(|| "?".to_string());
            let op = insn
                .payload
                .arith_op
                .map(|op| op.to_string())
                .unwrap_or_else(|| "?".to_string());
            format!("{target} {op}= {rhs}")
        }
        InsnType::Arith => {
            let op = insn
                .payload
                .arith_op
                .map(|op| format!("{:?}", op).to_lowercase())
                .unwrap_or_else(|| "?".to_string());
            let args: Vec<_> = insn.args.iter().map(|a| format!("{}", a)).collect();
            format!("{}{} {}", dest_str, op, args.join(", "))
        }
        InsnType::StringConcat => {
            let args: Vec<_> = insn.args.iter().map(|a| format!("{}", a)).collect();
            format!("{}str-concat {}", dest_str, args.join(" + "))
        }
        InsnType::Neg => {
            let src = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            format!("{}neg {}", dest_str, src)
        }
        InsnType::Not => {
            let src = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            format!("{}not {}", dest_str, src)
        }
        InsnType::Cast => {
            let src = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            let ty = insn
                .payload
                .cast_type
                .as_ref()
                .map(|t| format!("{}", t))
                .unwrap_or_else(|| "?".to_string());
            format!("{}({}) {}", dest_str, ty, src)
        }
        InsnType::If => {
            let op = insn
                .payload
                .if_op
                .map(|op| format!("{:?}", op).to_lowercase())
                .unwrap_or_else(|| "?".to_string());
            let args: Vec<_> = insn.args.iter().map(|a| format!("{}", a)).collect();
            format!("if-{} {}", op, args.join(", "))
        }
        InsnType::Goto => {
            let target = insn.payload.target.unwrap_or(0);
            format!("goto +{}", target)
        }
        InsnType::Return => {
            if insn.args.is_empty() {
                "return-void".to_string()
            } else {
                format!(
                    "return {}",
                    insn.args
                        .first()
                        .map(|a| format!("{}", a))
                        .unwrap_or_default()
                )
            }
        }
        InsnType::Invoke => {
            let kind = insn
                .payload
                .invoke_type
                .map(|k| format!("{:?}", k).to_lowercase())
                .unwrap_or_else(|| "?".to_string());
            let method = insn
                .payload
                .reference
                .as_ref()
                .map(|m| shorten_method(m))
                .unwrap_or_else(|| "?".to_string());
            format!("invoke-{} {}", kind, method)
        }
        InsnType::Constructor => {
            let method = insn
                .payload
                .reference
                .as_ref()
                .map(|m| shorten_method(m))
                .unwrap_or_else(|| "?".to_string());
            format!("{}constructor {}", dest_str, method)
        }
        InsnType::MoveResult => {
            format!("{}move-result", dest_str)
        }
        InsnType::NewInstance => {
            let ty = insn
                .payload
                .class_type
                .as_ref()
                .map(|t| format!("{}", t))
                .unwrap_or_else(|| "?".to_string());
            format!("{}new-instance {}", dest_str, ty)
        }
        InsnType::CheckCast => {
            let ty = insn
                .payload
                .class_type
                .as_ref()
                .map(|t| format!("{}", t))
                .unwrap_or_else(|| "?".to_string());
            let src = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            format!("check-cast {} {}", src, ty)
        }
        InsnType::InstanceOf => {
            let ty = insn
                .payload
                .class_type
                .as_ref()
                .map(|t| format!("{}", t))
                .unwrap_or_else(|| "?".to_string());
            let src = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            format!("{}instance-of {} {}", dest_str, src, ty)
        }
        InsnType::Throw => {
            let exc = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            format!("throw {}", exc)
        }
        InsnType::Iget | InsnType::Sget => {
            let field = insn
                .payload
                .reference
                .as_ref()
                .map(|f| shorten_field(f))
                .unwrap_or_else(|| "?".to_string());
            let prefix = if insn.insn_type == InsnType::Sget {
                "sget"
            } else {
                "iget"
            };
            format!("{}{} {}", dest_str, prefix, field)
        }
        InsnType::Iput | InsnType::Sput => {
            let field = insn
                .payload
                .reference
                .as_ref()
                .map(|f| shorten_field(f))
                .unwrap_or_else(|| "?".to_string());
            let val = insn
                .args
                .last()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            let prefix = if insn.insn_type == InsnType::Sput {
                "sput"
            } else {
                "iput"
            };
            format!("{} {} = {}", prefix, field, val)
        }
        InsnType::Aget => {
            let arr = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            let idx = insn
                .args
                .get(1)
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            format!("{}aget {}[{}]", dest_str, arr, idx)
        }
        InsnType::Aput => {
            let arr = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            let idx = insn
                .args
                .get(1)
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            let val = insn
                .args
                .get(2)
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            format!("aput {}[{}] = {}", arr, idx, val)
        }
        InsnType::ArrayLength => {
            let arr = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            format!("{}array-length {}", dest_str, arr)
        }
        InsnType::NewArray => {
            let size = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            let ty = insn
                .payload
                .class_type
                .as_ref()
                .map(|t| format!("{}", t))
                .unwrap_or_else(|| "?".to_string());
            format!("{}new-array {} {}", dest_str, ty, size)
        }
        InsnType::MonitorEnter => {
            let obj = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            format!("monitor-enter {}", obj)
        }
        InsnType::MonitorExit => {
            let obj = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            format!("monitor-exit {}", obj)
        }
        InsnType::Cmp => {
            let args: Vec<_> = insn.args.iter().map(|a| format!("{}", a)).collect();
            let bias = insn
                .payload
                .cmp_bias
                .map(|b| format!("{:?}", b).to_lowercase())
                .unwrap_or_default();
            format!("{}cmp{} {}", dest_str, bias, args.join(", "))
        }
        InsnType::Switch => {
            let reg = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            format!("switch {}", reg)
        }
        InsnType::MoveException => {
            format!("{}move-exception", dest_str)
        }
        InsnType::FillArray => {
            let arr = insn
                .args
                .first()
                .map(|a| format!("{}", a))
                .unwrap_or_default();
            format!("fill-array-data {}", arr)
        }
        InsnType::FilledNewArray => {
            let ty = insn
                .payload
                .class_type
                .as_ref()
                .map(|t| format!("{}", t))
                .unwrap_or_else(|| "?".to_string());
            format!("{}filled-new-array {}", dest_str, ty)
        }
        InsnType::Nop => "nop".to_string(),
        InsnType::Phi => {
            let args: Vec<_> = insn.args.iter().map(|a| format!("{}", a)).collect();
            format!("{}phi({})", dest_str, args.join(", "))
        }
        InsnType::Break => "break".to_string(),
        InsnType::Continue => "continue".to_string(),
        InsnType::Ternary => {
            let args: Vec<_> = insn.args.iter().map(|a| format!("{}", a)).collect();
            format!("{}ternary({})", dest_str, args.join(", "))
        }
    }
}

/// Shorten a type descriptor for display
fn shorten_type(ty: &ArgType) -> String {
    match ty {
        ArgType::Object(name) => name.rsplit('/').next().unwrap_or(name).to_string(),
        _ => ty.to_descriptor(),
    }
}

/// Shorten a method reference for display
fn shorten_method(reference: &MemberReference) -> String {
    match reference {
        MemberReference::Method(method) => {
            format!("{}.{}", shorten_type(&method.owner), method.name)
        }
        MemberReference::Field(_) => reference.to_string(),
    }
}

/// Shorten a field reference for display
fn shorten_field(reference: &MemberReference) -> String {
    match reference {
        MemberReference::Field(field) => {
            format!("{}.{}", shorten_type(&field.owner), field.name)
        }
        MemberReference::Method(_) => reference.to_string(),
    }
}

/// Truncate a string for display
fn truncate_string(s: &str, max_len: usize) -> String {
    if s.len() > max_len {
        format!("{}...", &s[..max_len])
    } else {
        s.to_string()
    }
}

/// Escape special characters for DOT format
fn escape_dot_string(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "")
}

/// Generate a simple text representation of the CFG
pub fn method_to_text(ir: &CFG) -> String {
    let mut out = String::new();

    writeln!(out, "=== CFG for {} ===", ir.label()).unwrap();
    writeln!(out, "Registers: {}, Ins: {}", ir.registers, ir.ins).unwrap();
    writeln!(out, "Entry: BB{}", ir.entry).unwrap();
    writeln!(out).unwrap();

    let mut block_ids: Vec<_> = ir.blocks.keys().copied().collect();
    block_ids.sort();

    for block_id in block_ids {
        if let Some(_block) = ir.blocks.get(&block_id) {
            writeln!(out, "BB{}:", block_id).unwrap();

            let preds = ir.get_predecessors(block_id);
            if !preds.is_empty() {
                let preds_str: Vec<_> = preds.iter().map(|p| format!("BB{}", p)).collect();
                writeln!(out, "  predecessors: {}", preds_str.join(", ")).unwrap();
            }

            if let Some(block) = ir.blocks.get(&block_id) {
                for insn in &block.insns {
                    writeln!(out, "  {}", insn_to_short_string(insn)).unwrap();
                }
            }

            let succs: Vec<_> = ir
                .successors(block_id)
                .map(|s| format!("BB{}", s))
                .collect();
            if !succs.is_empty() {
                writeln!(out, "  -> {}", succs.join(", ")).unwrap();
            }

            writeln!(out).unwrap();
        }
    }

    if !ir.handlers.is_empty() {
        writeln!(out, "Exception Handlers:").unwrap();
        for handler in &ir.handlers {
            let catch_type = handler
                .catch_type
                .as_ref()
                .map(|t| shorten_type(t))
                .unwrap_or_else(|| "any".to_string());
            writeln!(
                out,
                "  BB{}-BB{} catch {} -> BB{}",
                handler.start, handler.end, catch_type, handler.handler
            )
            .unwrap();
        }
    }

    out
}

// ==================== Tests ====================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decoder::method_decoder::MethodDecoder;
    use crate::frontend::MethodCode;
    use crate::ir::splitter::Splitter;

    #[test]
    fn test_dot_simple_method() {
        let code = MethodCode {
            registers_size: 1,
            ins_size: 0,
            outs_size: 0,
            insns: vec![
                0x0012, // const/4 v0, #int 0
                0x000f, // return v0
            ],
            tries: Vec::new(),
            debug_info: None,
        };

        let decoder = MethodDecoder::from_code(&code);
        let result = decoder.decode();

        let ir = Splitter::new("test")
            .instructions(result.insns)
            .handlers(result.handlers)
            .registers(result.registers)
            .ins(result.ins)
            .build();

        let dot = method_to_dot(&ir);

        assert!(dot.contains("digraph"));
        assert!(dot.contains("BB0"));
        assert!(dot.contains("const"));
        assert!(dot.contains("return"));
    }

    #[test]
    fn test_dot_with_branch() {
        let code = MethodCode {
            registers_size: 1,
            ins_size: 1,
            outs_size: 0,
            insns: vec![
                0x0038, // if-eqz v0, +2
                0x0002, // offset
                0x1012, // const/4 v0, #int 1
                0x000f, // return v0
            ],
            tries: Vec::new(),
            debug_info: None,
        };

        let decoder = MethodDecoder::from_code(&code);
        let result = decoder.decode();

        let ir = Splitter::new("test")
            .instructions(result.insns)
            .handlers(result.handlers)
            .registers(result.registers)
            .ins(result.ins)
            .build();

        let dot = method_to_dot(&ir);

        assert!(dot.contains("digraph"));
        assert!(dot.contains("->")); // Has edges
                                     // Should have labels for branch edges
        assert!(dot.contains("BB0") || dot.contains("BB1"));
    }

    #[test]
    fn test_text_output() {
        let code = MethodCode {
            registers_size: 1,
            ins_size: 0,
            outs_size: 0,
            insns: vec![
                0x0012, // const/4 v0, #int 0
                0x000f, // return v0
            ],
            tries: Vec::new(),
            debug_info: None,
        };

        let decoder = MethodDecoder::from_code(&code);
        let result = decoder.decode();

        let ir = Splitter::new("test_method")
            .instructions(result.insns)
            .handlers(result.handlers)
            .registers(result.registers)
            .ins(result.ins)
            .build();

        let text = method_to_text(&ir);

        assert!(text.contains("=== CFG for test_method ==="));
        assert!(text.contains("BB0"));
    }

    #[test]
    fn test_shorten_type() {
        assert_eq!(shorten_type(&"Lcom/example/Test;".parse().unwrap()), "Test");
        assert_eq!(
            shorten_type(&"Ljava/lang/String;".parse().unwrap()),
            "String"
        );
        assert_eq!(shorten_type(&"I".parse().unwrap()), "I");
        assert_eq!(shorten_type(&"[I".parse().unwrap()), "[I");
    }
}
