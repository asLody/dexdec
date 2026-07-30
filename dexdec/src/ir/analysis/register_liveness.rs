//! Register liveness used by pruned SSA construction.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{BlockId, CFG};

#[derive(Debug, Clone)]
pub struct RegisterLiveness {
    live_in: BTreeMap<BlockId, BTreeSet<u32>>,
    definitions: BTreeMap<BlockId, BTreeSet<u32>>,
}

impl RegisterLiveness {
    pub fn analyze(cfg: &CFG) -> Self {
        let mut definitions = BTreeMap::new();
        let mut upward_uses = BTreeMap::new();
        for block in cfg.blocks.values() {
            let mut block_definitions = BTreeSet::new();
            let mut block_uses = BTreeSet::new();
            for instruction in &block.insns {
                let uses = instruction
                    .args
                    .iter()
                    .flat_map(|argument| argument.regs_used())
                    .chain(
                        instruction
                            .payload
                            .compound_target
                            .iter()
                            .flat_map(|target| target.regs_used()),
                    );
                for register in uses {
                    if !block_definitions.contains(&register) {
                        block_uses.insert(register);
                    }
                }
                if let Some(result) = &instruction.result {
                    block_definitions.insert(result.reg_num);
                }
            }
            definitions.insert(block.id, block_definitions);
            upward_uses.insert(block.id, block_uses);
        }

        let mut live_in = cfg
            .block_ids()
            .into_iter()
            .map(|block| (block, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        let mut live_out = live_in.clone();
        loop {
            let mut changed = false;
            for block in cfg.block_ids().into_iter().rev() {
                let output = cfg
                    .successors(block)
                    .flat_map(|successor| live_in.get(&successor).into_iter().flatten().copied())
                    .collect::<BTreeSet<_>>();
                let mut input = upward_uses.get(&block).cloned().unwrap_or_default();
                let defined = definitions.get(&block).cloned().unwrap_or_default();
                input.extend(output.difference(&defined).copied());
                if live_out.get(&block) != Some(&output) {
                    live_out.insert(block, output);
                    changed = true;
                }
                if live_in.get(&block) != Some(&input) {
                    live_in.insert(block, input);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        Self {
            live_in,
            definitions,
        }
    }

    pub fn is_live_in(&self, block: BlockId, register: u32) -> bool {
        self.live_in
            .get(&block)
            .is_some_and(|values| values.contains(&register))
    }

    pub fn definition_blocks(&self, register: u32) -> impl Iterator<Item = BlockId> + '_ {
        self.definitions
            .iter()
            .filter(move |(_, values)| values.contains(&register))
            .map(|(block, _)| *block)
    }
}
