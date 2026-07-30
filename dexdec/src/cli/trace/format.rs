//! Formatting helpers for region and CFG traces.

use std::collections::BTreeMap;

use crate::ir::arg::InsnArg;
use crate::ir::{BlockId, RegionId, RegionKind, CFG};

use super::super::format_insn::format_insn;

pub fn format_block_id_list(ids: &[BlockId]) -> String {
    if ids.is_empty() {
        return "-".to_string();
    }
    ids.iter()
        .take(24)
        .map(|id| id.0.to_string())
        .collect::<Vec<_>>()
        .join(",")
        + if ids.len() > 24 { ",..." } else { "" }
}

pub fn format_block_map(mapping: &BTreeMap<BlockId, BlockId>) -> String {
    if mapping.is_empty() {
        return "-".to_string();
    }
    mapping
        .iter()
        .take(24)
        .map(|(source, target)| format!("{source}->{target}"))
        .collect::<Vec<_>>()
        .join(",")
        + if mapping.len() > 24 { ",..." } else { "" }
}

pub fn format_block_relations(relations: &[(BlockId, BlockId)]) -> String {
    if relations.is_empty() {
        return "-".to_string();
    }
    relations
        .iter()
        .take(24)
        .map(|(source, target)| format!("{source}->{target}"))
        .collect::<Vec<_>>()
        .join(",")
        + if relations.len() > 24 { ",..." } else { "" }
}

pub fn format_region_id(id: Option<RegionId>) -> String {
    id.map(|id| id.to_string())
        .unwrap_or_else(|| "-".to_string())
}

pub fn format_region_id_list(ids: &[RegionId]) -> String {
    if ids.is_empty() {
        return "-".to_string();
    }
    ids.iter()
        .take(24)
        .map(|id| id.to_string())
        .collect::<Vec<_>>()
        .join(",")
        + if ids.len() > 24 { ",..." } else { "" }
}

pub fn format_optional_block_id(id: Option<BlockId>) -> String {
    id.map(|id| id.to_string())
        .unwrap_or_else(|| "-".to_string())
}

pub fn format_optional_insn_arg(arg: Option<&InsnArg>) -> String {
    arg.map(|arg| arg.to_string())
        .unwrap_or_else(|| "-".to_string())
}

pub fn format_region_kind(kind: &RegionKind) -> String {
    match kind {
        RegionKind::Method => "method".to_string(),
        RegionKind::Try => "try".to_string(),
        RegionKind::Catch(catch) => format!(
            "catch({})",
            catch
                .exception_types
                .first()
                .map(ToString::to_string)
                .unwrap_or_else(|| "<invalid-empty-catch>".to_string())
        ),
        RegionKind::Finally => "finally".to_string(),
        RegionKind::Cleanup(_) => "cleanup".to_string(),
        RegionKind::Synchronized(_) => "synchronized".to_string(),
        RegionKind::Loop(_) => "loop".to_string(),
        RegionKind::Switch(_) => "switch".to_string(),
    }
}

pub fn format_exception_region_map(map: &BTreeMap<u32, Vec<RegionId>>) -> String {
    if map.is_empty() {
        return "-".to_string();
    }
    map.iter()
        .map(|(old, regions)| {
            format!(
                "try{}={}",
                old,
                regions
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("|")
            )
        })
        .collect::<Vec<_>>()
        .join(",")
}

pub fn format_trace_block(cfg: &CFG, id: BlockId) -> String {
    let Some(block) = cfg.block(id) else {
        return format!("  BB{} <missing>\n", id.0);
    };

    let mut out = String::new();
    out.push_str(&format!("  BB{} @{:04x}\n", id.0, block.offset));
    for insn in &block.insns {
        out.push_str(&format!("    {}\n", format_insn(insn)));
    }
    let succs: Vec<_> = cfg
        .successors_with_kind(id)
        .iter()
        .map(|(succ, kind)| format!("BB{}:{:?}", succ.0, kind))
        .collect();
    if !succs.is_empty() {
        out.push_str(&format!("    -> {}\n", succs.join(", ")));
    }
    out
}
