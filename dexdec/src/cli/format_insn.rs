//! Instruction pretty-printer shared by IR and trace dumps.

use crate::ir::arg::InsnArg;
use crate::ir::insn::{InsnNode, InsnType};
use crate::ir::Utf16String;

/// Format a single instruction as a string.
pub fn format_insn(insn: &InsnNode) -> String {
    let result_str = if let Some(ref result) = insn.result {
        format!("{} = ", result)
    } else {
        String::new()
    };

    let args_str: Vec<String> = insn
        .args
        .iter()
        .map(|arg| match arg {
            InsnArg::Reg(r) => r.to_string(),
            InsnArg::Lit(lit) => format!("{}", lit.value),
            InsnArg::Wrapped(insn) => format!("<wrapped:{:?}>", insn.insn_type),
        })
        .collect();

    let ref_str = insn
        .payload
        .reference
        .as_ref()
        .map(ToString::to_string)
        .unwrap_or_else(|| "?".to_string());

    match insn.insn_type {
        InsnType::Const => {
            let val = insn
                .args
                .get(0)
                .map(|a| match a {
                    InsnArg::Lit(l) => l.value.to_string(),
                    _ => "?".to_string(),
                })
                .unwrap_or_else(|| "?".to_string());
            format!("{}const {}", result_str, val)
        }
        InsnType::ConstStr => {
            let s = insn
                .payload
                .string_value
                .as_ref()
                .map(Utf16String::to_string_lossy)
                .unwrap_or_else(|| "?".to_string());
            format!("{}const-string \"{}\"", result_str, s)
        }
        InsnType::ConstClass => {
            let c = insn
                .payload
                .class_type
                .as_ref()
                .map(|t| t.to_string())
                .unwrap_or_else(|| "?".to_string());
            format!("{}const-class {}", result_str, c)
        }
        InsnType::Move => format!("{}move {}", result_str, args_str.join(", ")),
        InsnType::CompoundAssign => {
            let target = insn
                .payload
                .compound_target
                .as_ref()
                .map(|arg| match arg {
                    InsnArg::Reg(r) => format!("v{}", r.reg_num),
                    InsnArg::Lit(lit) => lit.value.to_string(),
                    InsnArg::Wrapped(inner) => format!("<wrapped:{:?}>", inner.insn_type),
                })
                .unwrap_or_else(|| "?".to_string());
            let rhs = args_str.first().cloned().unwrap_or_else(|| "?".to_string());
            let op = insn
                .payload
                .arith_op
                .map(|op| op.to_string())
                .unwrap_or_else(|| "?".to_string());
            format!("{target} {op}= {rhs}")
        }
        InsnType::Return => {
            if args_str.is_empty() {
                "return-void".to_string()
            } else {
                format!("return {}", args_str.join(", "))
            }
        }
        InsnType::Arith => {
            let op = insn
                .payload
                .arith_op
                .as_ref()
                .map(|o| format!("{}", o))
                .unwrap_or_else(|| "?".to_string());
            format!("{}{} {}", result_str, op, args_str.join(", "))
        }
        InsnType::StringConcat => format!("{}str-concat {}", result_str, args_str.join(" + ")),
        InsnType::Cmp => {
            let bias = insn
                .payload
                .cmp_bias
                .as_ref()
                .map(|b| format!("{:?}", b))
                .unwrap_or_else(|| "?".to_string());
            format!(
                "{}cmp-{} {}",
                result_str,
                bias.to_lowercase(),
                args_str.join(", ")
            )
        }
        InsnType::If => {
            let op = insn
                .payload
                .if_op
                .as_ref()
                .map(|o| format!("{}", o))
                .unwrap_or_else(|| "?".to_string());
            let target = insn
                .payload
                .target
                .map(|t| format!(" @{}", t))
                .unwrap_or_default();
            format!("if {} {}{}", args_str.join(" "), op, target)
        }
        InsnType::Goto => {
            let target = insn
                .payload
                .target
                .map(|t| format!("@{}", t))
                .unwrap_or_else(|| "?".to_string());
            format!("goto {}", target)
        }
        InsnType::Invoke => {
            let style = insn
                .payload
                .invoke_type
                .as_ref()
                .map(|t| format!("{:?}", t).to_lowercase())
                .unwrap_or_else(|| "?".to_string());
            format!(
                "{}invoke-{} {}({})",
                result_str,
                style,
                ref_str,
                args_str.join(", ")
            )
        }
        InsnType::Constructor => {
            format!(
                "{}constructor {}({})",
                result_str,
                ref_str,
                args_str.join(", ")
            )
        }
        InsnType::MoveResult => format!("{}move-result", result_str),
        InsnType::Iget => format!("{}iget {}", result_str, ref_str),
        InsnType::Iput => format!("iput {} = {}", ref_str, args_str.join(", ")),
        InsnType::Sget => format!("{}sget {}", result_str, ref_str),
        InsnType::Sput => format!("sput {} = {}", ref_str, args_str.join(", ")),
        InsnType::NewInstance => {
            let ty = insn
                .payload
                .class_type
                .as_ref()
                .map(|t| t.to_string())
                .unwrap_or_else(|| "?".to_string());
            format!("{}new-instance {}", result_str, ty)
        }
        InsnType::NewArray => {
            let ty = insn
                .payload
                .class_type
                .as_ref()
                .map(|t| t.to_string())
                .unwrap_or_else(|| "?".to_string());
            format!("{}new-array {} {}", result_str, ty, args_str.join(", "))
        }
        InsnType::Aget => format!(
            "{}aget {}[{}]",
            result_str,
            args_str.get(0).unwrap_or(&"?".to_string()),
            args_str.get(1).unwrap_or(&"?".to_string())
        ),
        InsnType::Aput => format!(
            "aput {}[{}] = {}",
            args_str.get(0).unwrap_or(&"?".to_string()),
            args_str.get(1).unwrap_or(&"?".to_string()),
            args_str.get(2).unwrap_or(&"?".to_string())
        ),
        InsnType::ArrayLength => format!(
            "{}array-length {}",
            result_str,
            args_str.get(0).unwrap_or(&"?".to_string())
        ),
        InsnType::CheckCast => {
            let ty = insn
                .payload
                .class_type
                .as_ref()
                .map(|t| t.to_string())
                .unwrap_or_else(|| "?".to_string());
            format!(
                "{}check-cast {} {}",
                result_str,
                args_str.get(0).unwrap_or(&"?".to_string()),
                ty
            )
        }
        InsnType::InstanceOf => {
            let ty = insn
                .payload
                .class_type
                .as_ref()
                .map(|t| t.to_string())
                .unwrap_or_else(|| "?".to_string());
            format!(
                "{}instance-of {} {}",
                result_str,
                args_str.get(0).unwrap_or(&"?".to_string()),
                ty
            )
        }
        InsnType::Throw => format!("throw {}", args_str.get(0).unwrap_or(&"?".to_string())),
        InsnType::Switch => {
            let cases = insn
                .payload
                .switch_cases
                .as_ref()
                .map(|c| c.len().to_string())
                .unwrap_or_else(|| "?".to_string());
            format!(
                "switch {} ({} cases)",
                args_str.get(0).unwrap_or(&"?".to_string()),
                cases
            )
        }
        InsnType::Neg => format!(
            "{}neg {}",
            result_str,
            args_str.get(0).unwrap_or(&"?".to_string())
        ),
        InsnType::Not => format!(
            "{}not {}",
            result_str,
            args_str.get(0).unwrap_or(&"?".to_string())
        ),
        InsnType::Cast => {
            let ty = insn
                .payload
                .cast_type
                .as_ref()
                .map(|t| t.to_string())
                .unwrap_or_else(|| "?".to_string());
            format!(
                "{}cast ({}) {}",
                result_str,
                ty,
                args_str.get(0).unwrap_or(&"?".to_string())
            )
        }
        InsnType::MonitorEnter => format!(
            "monitor-enter {}",
            args_str.get(0).unwrap_or(&"?".to_string())
        ),
        InsnType::MonitorExit => format!(
            "monitor-exit {}",
            args_str.get(0).unwrap_or(&"?".to_string())
        ),
        InsnType::FillArray => {
            format!("fill-array {}", args_str.get(0).unwrap_or(&"?".to_string()))
        }
        InsnType::FilledNewArray => {
            format!("{}filled-new-array {}", result_str, args_str.join(", "))
        }
        InsnType::Nop => "nop".to_string(),
        InsnType::Phi => format!("{}phi {}", result_str, args_str.join(", ")),
        InsnType::MoveException => format!("{}move-exception", result_str),
        InsnType::Break => "break".to_string(),
        InsnType::Continue => "continue".to_string(),
        InsnType::Ternary => format!("{}ternary {}", result_str, args_str.join(", ")),
    }
}
