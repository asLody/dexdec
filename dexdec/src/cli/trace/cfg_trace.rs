//! CFG pass-trace observers and stage diffs.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Mutex;

use crate::ir::{AnalysisEvent, AnalysisObserver, BlockId, PassResult, CFG};

use super::format::{format_block_id_list, format_trace_block};

#[derive(Clone)]
pub struct CfgSnapshot {
    blocks: BTreeMap<BlockId, String>,
}

impl CfgSnapshot {
    pub fn from_cfg(cfg: &CFG) -> Self {
        let blocks = cfg
            .block_ids()
            .into_iter()
            .filter_map(|id| cfg.block(id).map(|_| (id, format_trace_block(cfg, id))))
            .collect();
        Self { blocks }
    }
}

struct CfgPassTraceState {
    output: String,
    previous: CfgSnapshot,
    blocks: Option<BTreeSet<BlockId>>,
    changed_details: bool,
}

/// Observes verified CFG pipeline stages and records diffs.
pub struct CfgPassTrace {
    state: Mutex<CfgPassTraceState>,
}

impl CfgPassTrace {
    pub fn new(
        output: String,
        previous: CfgSnapshot,
        blocks: Option<BTreeSet<BlockId>>,
        changed_details: bool,
    ) -> Self {
        Self {
            state: Mutex::new(CfgPassTraceState {
                output,
                previous,
                blocks,
                changed_details,
            }),
        }
    }

    pub fn output(&self) -> Result<String, Box<dyn std::error::Error>> {
        self.state
            .lock()
            .map(|state| state.output.clone())
            .map_err(|_| "CFG trace lock is poisoned".into())
    }
}

impl AnalysisObserver for CfgPassTrace {
    fn is_enabled(&self, kind: crate::ir::AnalysisEventKind) -> bool {
        kind == crate::ir::AnalysisEventKind::CfgTransform
    }

    fn observe(&self, event: AnalysisEvent<'_>) {
        let AnalysisEvent::CfgTransform {
            phase,
            name,
            result,
            cfg,
        } = event
        else {
            return;
        };
        let Ok(mut state) = self.state.lock() else {
            return;
        };
        let CfgPassTraceState {
            output,
            previous,
            blocks,
            changed_details,
        } = &mut *state;
        append_observed_cfg_stage(
            output,
            previous,
            phase,
            name,
            result,
            cfg,
            blocks,
            *changed_details,
        );
    }
}

pub fn append_decode_snapshot(
    output: &mut String,
    stage: &str,
    cfg: &CFG,
    trace_blocks: &Option<BTreeSet<BlockId>>,
    changed_details: bool,
) {
    let after = CfgSnapshot::from_cfg(cfg);
    output.push_str(&format!(
        "[{}] blocks={} handlers={}\n",
        stage,
        cfg.blocks.len(),
        cfg.handlers.len()
    ));
    append_selected_blocks(output, &after, trace_blocks, None, changed_details);
    output.push('\n');
}

fn append_observed_cfg_stage(
    output: &mut String,
    previous: &mut CfgSnapshot,
    group: &'static str,
    stage: &'static str,
    pass_result: PassResult,
    cfg: &CFG,
    trace_blocks: &Option<BTreeSet<BlockId>>,
    changed_details: bool,
) {
    let after = CfgSnapshot::from_cfg(cfg);
    append_stage_diff(
        output,
        &format!("{}/{} {:?}", group, stage, pass_result),
        previous,
        &after,
        cfg,
        trace_blocks,
        changed_details,
    );
    *previous = after;
}

fn append_stage_diff(
    output: &mut String,
    stage: &str,
    before: &CfgSnapshot,
    after: &CfgSnapshot,
    cfg: &CFG,
    trace_blocks: &Option<BTreeSet<BlockId>>,
    changed_details: bool,
) {
    let mut added = Vec::new();
    let mut removed = Vec::new();
    let mut changed = Vec::new();

    for id in after.blocks.keys() {
        match before.blocks.get(id) {
            None => added.push(*id),
            Some(before_block) if before_block != &after.blocks[id] => changed.push(*id),
            _ => {}
        }
    }
    for id in before.blocks.keys() {
        if !after.blocks.contains_key(id) {
            removed.push(*id);
        }
    }

    output.push_str(&format!(
        "[{}] blocks={} added={} removed={} changed={}\n",
        stage,
        cfg.blocks.len(),
        format_block_id_list(&added),
        format_block_id_list(&removed),
        format_block_id_list(&changed)
    ));

    let changed_filter = (!changed.is_empty()).then(|| changed.iter().copied().collect());
    append_selected_blocks(
        output,
        after,
        trace_blocks,
        changed_filter.as_ref(),
        changed_details,
    );
    output.push('\n');
}

fn append_selected_blocks(
    output: &mut String,
    snapshot: &CfgSnapshot,
    trace_blocks: &Option<BTreeSet<BlockId>>,
    changed_blocks: Option<&BTreeSet<BlockId>>,
    changed_details: bool,
) {
    let ids: Vec<_> = if let Some(trace_blocks) = trace_blocks {
        trace_blocks.iter().copied().collect()
    } else if changed_details {
        changed_blocks
            .map(|ids| ids.iter().copied().collect())
            .unwrap_or_default()
    } else {
        Vec::new()
    };

    for id in ids {
        if let Some(block) = snapshot.blocks.get(&id) {
            output.push_str(block);
        } else {
            output.push_str(&format!("  BB{} <missing>\n", id.0));
        }
    }
}
