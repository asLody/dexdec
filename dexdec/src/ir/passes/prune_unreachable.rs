//! Remove unreachable blocks pass.

use std::collections::BTreeSet;

use super::pipeline::{Pass, PassResult};
use crate::ir::{cfg::CFG, InsnType};

/// Removes unreachable blocks from the CFG.
///
/// A block is considered unreachable if there is no path from the
/// entry block to it. This pass removes all such blocks.
#[derive(Debug, Default)]
pub struct PruneUnreachable;

impl Pass for PruneUnreachable {
    type Error = std::convert::Infallible;

    fn name(&self) -> &'static str {
        "prune_unreachable"
    }

    fn run(&mut self, cfg: &mut CFG) -> Result<PassResult, Self::Error> {
        let reachable = cfg.reachable();
        let to_remove: Vec<_> = cfg
            .block_ids()
            .into_iter()
            .filter(|id| !reachable.contains(id))
            .collect();

        let mut changed = !to_remove.is_empty();
        let removed = to_remove.iter().copied().collect::<BTreeSet<_>>();
        for block in cfg.blocks.values_mut() {
            for phi in block
                .insns
                .iter_mut()
                .filter(|instruction| instruction.insn_type == InsnType::Phi)
            {
                if phi.args.len() != phi.payload.phi_edges.len() {
                    continue;
                }
                let mut arguments = std::mem::take(&mut phi.args).into_iter();
                let mut edges = std::mem::take(&mut phi.payload.phi_edges).into_iter();
                while let (Some(argument), Some(edge)) = (arguments.next(), edges.next()) {
                    if !removed.contains(&edge.0) {
                        phi.args.push(argument);
                        phi.payload.phi_edges.push(edge);
                    }
                }
            }
        }
        for id in to_remove {
            cfg.remove_block(id);
        }

        let handler_entries = cfg
            .blocks
            .values()
            .filter(|block| !block.synthetic)
            .map(|block| block.offset)
            .collect::<BTreeSet<_>>();
        let handler_count = cfg.handlers.len();
        cfg.handlers
            .retain(|handler| handler_entries.contains(&handler.handler));
        changed |= cfg.handlers.len() != handler_count;

        Ok(changed.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::block::{Block, BlockId};
    use crate::ir::cfg::EdgeKind;

    #[test]
    fn test_prune_unreachable() {
        let mut cfg = CFG::new("test");
        cfg.add_block(Block::new(0u32));
        cfg.add_block(Block::new(1u32));
        cfg.add_block(Block::new(2u32)); // unreachable
        cfg.entry = BlockId::new(0);
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);

        let result = PruneUnreachable.run(&mut cfg);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), PassResult::Changed);
        assert_eq!(cfg.num_blocks(), 2);
        assert!(cfg.block(BlockId::new(2)).is_none());
    }

    #[test]
    fn test_prune_all_reachable() {
        let mut cfg = CFG::new("test");
        cfg.add_block(Block::new(0u32));
        cfg.add_block(Block::new(1u32));
        cfg.entry = BlockId::new(0);
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);

        let result = PruneUnreachable.run(&mut cfg);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), PassResult::Unchanged);
        assert_eq!(cfg.num_blocks(), 2);
    }
}
