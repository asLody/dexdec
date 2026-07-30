//! Split Critical Edges pass.
//!
//! A critical edge is an edge (u, v) such that u has multiple successors
//! and v has multiple predecessors. Splitting these edges makes it easier
//! to place PHI-node copies before semantic region construction.

use std::collections::{BTreeMap, BTreeSet};

use super::Pass;
use crate::ir::block::{Block, BlockId};
use crate::ir::cfg::{EdgeKind, CFG};
use crate::ir::insn::{InsnNode, InsnType};
use crate::ir::passes::PassResult;

/// Splits all critical edges in the CFG.
#[derive(Debug, Default)]
pub struct SplitCriticalEdges;

impl Pass for SplitCriticalEdges {
    type Error = std::convert::Infallible;

    fn name(&self) -> &'static str {
        "split_critical_edges"
    }

    fn run(&mut self, cfg: &mut CFG) -> Result<PassResult, Self::Error> {
        cfg.capture_exception_coverage();
        let mut changed = false;
        let block_ids = cfg.block_ids();

        let mut edges_to_split = BTreeMap::<(BlockId, BlockId), BTreeSet<EdgeKind>>::new();
        for u in block_ids {
            let succs = cfg.successors_with_kind(u);
            let normal_targets = succs
                .iter()
                .filter_map(|(target, kind)| (!kind.is_exception()).then_some(*target))
                .collect::<BTreeSet<_>>();
            if normal_targets.len() <= 1 {
                continue;
            }

            for (v, kind) in succs.to_vec() {
                if kind.is_exception() {
                    continue;
                }
                // Phi topology includes exceptional inputs, so a normal edge
                // is critical when the target has multiple incoming edges of
                // any kind.
                if cfg.incoming_edges(v).len() > 1 {
                    edges_to_split.entry((u, v)).or_default().insert(kind);
                }
            }
        }

        if edges_to_split.is_empty() {
            return Ok(PassResult::Unchanged);
        }

        // Find maximum block ID to generate new ones
        let mut next_id = cfg.block_ids().iter().map(|id| id.0).max().unwrap_or(0) + 1;

        for ((u, v), kinds) in edges_to_split {
            let mid_id = BlockId::new(next_id);
            next_id += 1;

            // 1. Create new intermediate block with a Goto to v
            let coverage = cfg.common_exception_coverage(u, v);
            let mut mid_block = Block::synthetic(mid_id);
            mid_block.push(InsnNode::new(InsnType::Goto, 0));
            cfg.add_block(mid_block);
            cfg.set_exception_coverage(mid_id, coverage);

            // 2. Redirect u -> v to u -> mid
            // Update successors in CFG
            // This is tricky because add_edge appends, so we need to find and replace.
            let u_succs_raw = cfg.successors_with_kind(u).to_vec();
            cfg.remove_all_edges_from(u);
            for (s, k) in u_succs_raw {
                if s == v && kinds.contains(&k) {
                    cfg.add_edge(u, mid_id, k);
                } else {
                    cfg.add_edge(u, s, k);
                }
            }

            // 3. Add edge mid -> v
            cfg.add_edge(mid_id, v, EdgeKind::Normal);

            changed = true;
        }

        Ok(changed.into())
    }
}
