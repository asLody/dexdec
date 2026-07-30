//! Isolate every `monitor-enter` at a CFG boundary.

use crate::ir::{Block, BlockId, EdgeKind, InsnType, CFG};

use super::{Pass, PassResult};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MonitorSplitError {
    MissingBlock(BlockId),
    EmptyPartition(BlockId),
    MissingPartition(BlockId),
}

impl std::fmt::Display for MonitorSplitError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingBlock(block) => write!(formatter, "missing monitor block {block}"),
            Self::EmptyPartition(block) => write!(formatter, "empty monitor partition in {block}"),
            Self::MissingPartition(block) => {
                write!(formatter, "monitor block {block} has no partition")
            }
        }
    }
}

impl std::error::Error for MonitorSplitError {}

#[derive(Debug, Default)]
pub struct SplitMonitorEntries;

impl Pass for SplitMonitorEntries {
    type Error = MonitorSplitError;

    fn name(&self) -> &'static str {
        "split_monitor_entries"
    }

    fn run(&mut self, cfg: &mut CFG) -> Result<PassResult, Self::Error> {
        cfg.capture_exception_coverage();
        let candidates = cfg
            .block_ids()
            .into_iter()
            .filter(|block| {
                cfg.block(*block).is_some_and(|block| {
                    block.insns.iter().enumerate().any(|(index, instruction)| {
                        instruction.insn_type == InsnType::MonitorEnter
                            && index + 1 < block.insns.len()
                    })
                })
            })
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            return Ok(PassResult::Unchanged);
        }

        let mut next = cfg
            .block_ids()
            .into_iter()
            .map(BlockId::raw)
            .max()
            .unwrap_or(0)
            + 1;
        for original_id in candidates {
            let outgoing = cfg.successors_with_kind(original_id).to_vec();
            let instructions = std::mem::take(
                &mut cfg
                    .block_mut(original_id)
                    .ok_or(MonitorSplitError::MissingBlock(original_id))?
                    .insns,
            );
            let mut boundaries = instructions
                .iter()
                .enumerate()
                .filter_map(|(index, instruction)| {
                    (instruction.insn_type == InsnType::MonitorEnter
                        && index + 1 < instructions.len())
                    .then_some(index + 1)
                })
                .collect::<Vec<_>>();
            boundaries.push(instructions.len());

            cfg.remove_all_edges_from(original_id);
            let mut previous = None;
            let mut start = 0;
            for (segment_index, end) in boundaries.into_iter().enumerate() {
                let id = if segment_index == 0 {
                    original_id
                } else {
                    let id = BlockId::new(next);
                    next += 1;
                    id
                };
                let segment = instructions[start..end].to_vec();
                if segment.is_empty() {
                    return Err(MonitorSplitError::EmptyPartition(original_id));
                }
                let coverage = cfg.exception_coverage_for(&segment);
                let offset = segment
                    .first()
                    .map(|instruction| instruction.offset)
                    .unwrap_or_default();
                if segment_index == 0 {
                    let block = cfg
                        .block_mut(id)
                        .ok_or(MonitorSplitError::MissingBlock(id))?;
                    block.offset = offset;
                    block.insns = segment;
                } else {
                    let mut block = Block::with_offset(id, offset);
                    block.insns = segment;
                    cfg.add_block(block);
                }
                cfg.set_exception_coverage(id, coverage);
                if let Some(previous) = previous {
                    cfg.add_edge(previous, id, EdgeKind::Normal);
                }
                for &(handler, kind) in &outgoing {
                    if kind == EdgeKind::Exception
                        && cfg.block(id).is_some_and(|block| {
                            block.insns.iter().any(crate::ir::InsnNode::can_throw)
                        })
                    {
                        cfg.add_edge(id, handler, kind);
                    }
                }
                previous = Some(id);
                start = end;
            }
            let tail = previous.ok_or(MonitorSplitError::MissingPartition(original_id))?;
            for (target, kind) in &outgoing {
                if *kind != EdgeKind::Exception {
                    cfg.add_edge(tail, *target, *kind);
                }
            }
        }
        Ok(PassResult::Changed)
    }
}
