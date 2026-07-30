//! PHI Node Simplification Pass.
//!
//! This pass simplifies PHI nodes to reduce the complexity of the SSA form.
//! It performs the following optimizations:
//!
//! 1. **Same-arg PHI elimination**: Remove PHI where all arguments are the same
//! 2. **Self-referential PHI simplification**: Handle PHIs that reference themselves
//! 3. **Graph liveness**: Remove PHI components not reachable from a non-PHI use
//!
//! ## Example
//!
//! Before:
//! ```text
//! v0_2 = phi(v0_1, v0_1)  // Same args -> eliminated
//! v1_2 = phi(v1_1)        // Single arg -> becomes move
//! v2_2 = phi(v2_0, v2_1)  // Different args -> kept
//! ```
//!
//! After:
//! ```text
//! // v0_2 eliminated, uses replaced with v0_1
//! // v1_2 eliminated, uses replaced with v1_1
//! v2_2 = phi(v2_0, v2_1)  // Kept
//! ```

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::ir::{
    analysis::{InsnPosition, SsaInvariantError, SsaValueGraph, SsaVar},
    arg::{InsnArg, RegisterArg},
    cfg::CFG,
    insn::InsnType,
    passes::{Pass, PassResult},
    InstructionTransform, InstructionTree, InstructionTreeError, InstructionVisitor,
};

/// PHI simplification pass.
#[derive(Debug, Default)]
pub struct PhiSimplify;

#[derive(Debug, Clone)]
pub enum PhiSimplificationError {
    Ssa(SsaInvariantError),
    InstructionTree(InstructionTreeError),
    MissingResult(InsnPosition),
    InvalidInput(InsnPosition),
}

impl std::fmt::Display for PhiSimplificationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ssa(error) => write!(formatter, "invalid SSA graph: {error}"),
            Self::InstructionTree(error) => error.fmt(formatter),
            Self::MissingResult(position) => write!(formatter, "Phi at {position:?} has no result"),
            Self::InvalidInput(position) => write!(
                formatter,
                "Phi at {position:?} has a non-register or non-SSA input"
            ),
        }
    }
}

impl std::error::Error for PhiSimplificationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Ssa(error) => Some(error),
            Self::InstructionTree(error) => Some(error),
            _ => None,
        }
    }
}

impl PhiSimplify {
    pub fn new() -> Self {
        Self
    }
}

impl Pass for PhiSimplify {
    type Error = PhiSimplificationError;

    fn name(&self) -> &'static str {
        "phi_simplify"
    }

    fn run(&mut self, cfg: &mut CFG) -> Result<PassResult, Self::Error> {
        let values = SsaValueGraph::build(cfg).map_err(PhiSimplificationError::Ssa)?;
        let replacements = Self::compute_replacements(&values);
        let mut changed = !replacements.is_empty();
        Self::apply_replacements(cfg, &replacements)?;
        changed |= Self::remove_dead_phis(cfg)?;
        Ok(changed.into())
    }
}

impl PhiSimplify {
    /// Find PHIs that can be replaced with a single value.
    fn compute_replacements(values: &SsaValueGraph) -> BTreeMap<SsaVar, SsaVar> {
        let mut replacements = BTreeMap::new();
        for phi in values.phis() {
            let sources = phi
                .inputs
                .iter()
                .map(|input| input.value)
                .filter(|source| *source != phi.result)
                .collect::<BTreeSet<_>>();
            if let [source] = sources.iter().copied().collect::<Vec<_>>().as_slice() {
                replacements.insert(phi.result, *source);
            }
        }

        replacements
            .keys()
            .copied()
            .filter_map(|key| Self::replacement_root(key, &replacements).map(|root| (key, root)))
            .collect()
    }

    fn replacement_root(key: SsaVar, replacements: &BTreeMap<SsaVar, SsaVar>) -> Option<SsaVar> {
        let mut seen = BTreeSet::from([key]);
        let mut current = *replacements.get(&key)?;
        while let Some(next) = replacements.get(&current).copied() {
            if !seen.insert(current) {
                return None;
            }
            current = next;
        }
        (current != key).then_some(current)
    }

    /// Apply replacements: remove PHIs and update uses.
    fn apply_replacements(
        cfg: &mut CFG,
        replacements: &BTreeMap<SsaVar, SsaVar>,
    ) -> Result<(), PhiSimplificationError> {
        for block in cfg.blocks.values_mut() {
            // Remove replaced PHIs
            block.insns.retain(|insn| {
                if insn.insn_type != InsnType::Phi {
                    return true;
                }
                insn.result
                    .as_ref()
                    .and_then(SsaVar::from_reg)
                    .is_none_or(|key| !replacements.contains_key(&key))
            });

            // Update uses
            for insn in &mut block.insns {
                InstructionTree::transform_args(insn, &mut SsaReplacement { replacements })
                    .map_err(PhiSimplificationError::InstructionTree)?;
            }
        }
        Ok(())
    }

    /// Remove PHI nodes whose results are never used.
    fn remove_dead_phis(cfg: &mut CFG) -> Result<bool, PhiSimplificationError> {
        let mut dependencies = BTreeMap::<SsaVar, Vec<SsaVar>>::new();
        for (&block_id, block) in &cfg.blocks {
            for (index, insn) in block.insns.iter().enumerate() {
                if insn.insn_type != InsnType::Phi {
                    continue;
                }
                let position = InsnPosition {
                    block: block_id,
                    index,
                };
                let result = insn
                    .result
                    .as_ref()
                    .and_then(SsaVar::from_reg)
                    .ok_or(PhiSimplificationError::MissingResult(position))?;
                let inputs = insn
                    .args
                    .iter()
                    .map(|argument| {
                        argument
                            .as_register()
                            .and_then(SsaVar::from_reg)
                            .ok_or(PhiSimplificationError::InvalidInput(position))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                dependencies.insert(result, inputs);
            }
        }

        let mut live = BTreeSet::new();
        let mut pending = VecDeque::new();
        for block in cfg.blocks.values() {
            for insn in &block.insns {
                if insn.insn_type == InsnType::Phi {
                    continue;
                }
                let mut uses = SsaUses::default();
                InstructionTree::visit_args(insn, &mut uses);
                for used in uses.values {
                    if dependencies.contains_key(&used) && live.insert(used) {
                        pending.push_back(used);
                    }
                }
            }
        }
        while let Some(phi) = pending.pop_front() {
            for dependency in dependencies.get(&phi).into_iter().flatten().copied() {
                if dependencies.contains_key(&dependency) && live.insert(dependency) {
                    pending.push_back(dependency);
                }
            }
        }

        let mut changed = false;
        for block in cfg.blocks.values_mut() {
            let before_len = block.insns.len();
            block.insns.retain(|insn| {
                if insn.insn_type != InsnType::Phi {
                    return true;
                }
                if let Some(result) = &insn.result {
                    SsaVar::from_reg(result).is_some_and(|result| live.contains(&result))
                } else {
                    true
                }
            });
            if block.insns.len() != before_len {
                changed = true;
            }
        }

        Ok(changed)
    }
}

struct SsaReplacement<'a> {
    replacements: &'a BTreeMap<SsaVar, SsaVar>,
}

impl InstructionTransform for SsaReplacement<'_> {
    fn transform_register(&mut self, mut register: RegisterArg) -> InsnArg {
        if let Some(replacement) = SsaVar::from_reg(&register)
            .and_then(|variable| self.replacements.get(&variable))
            .copied()
        {
            replacement.apply_to(&mut register);
        }
        InsnArg::Reg(register)
    }
}

#[derive(Default)]
struct SsaUses {
    values: Vec<SsaVar>,
}

impl InstructionVisitor for SsaUses {
    fn visit_register(&mut self, register: &RegisterArg) {
        self.values.extend(SsaVar::from_reg(register));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{
        arg::RegisterArg,
        block::{Block, BlockId},
        cfg::EdgeKind,
        insn::InsnNode,
        ty::ArgType,
    };

    #[test]
    fn test_keeps_necessary_phi() {
        // PHI with different args should be kept
        let mut cfg = CFG::new("test");

        let mut block0 = Block::new(0u32);
        block0.push(InsnNode::const_val(
            RegisterArg::new_ssa(0, 0, ArgType::INT),
            1,
            ArgType::INT,
        ));
        cfg.add_block(block0);

        let mut block1 = Block::new(1u32);
        block1.push(InsnNode::const_val(
            RegisterArg::new_ssa(0, 1, ArgType::INT),
            2,
            ArgType::INT,
        ));
        cfg.add_block(block1);

        let mut block2 = Block::new(2u32);
        block2.push(InsnNode::const_val(
            RegisterArg::new_ssa(0, 2, ArgType::INT),
            3,
            ArgType::INT,
        ));
        cfg.add_block(block2);

        let mut block3 = Block::new(3u32);
        let phi = InsnNode::phi(
            RegisterArg::new_ssa(0, 3, ArgType::INT),
            vec![
                (1, InsnArg::reg_ssa(0, 1, ArgType::INT)),
                (2, InsnArg::reg_ssa(0, 2, ArgType::INT)),
            ],
        );
        block3.push(phi);
        let mut ret = InsnNode::new(InsnType::Return, 1);
        ret.add_arg(InsnArg::reg_ssa(0, 3, ArgType::INT));
        block3.push(ret);
        cfg.add_block(block3);

        cfg.add_edge(BlockId(0), BlockId(1), EdgeKind::Normal);
        cfg.add_edge(BlockId(0), BlockId(2), EdgeKind::Normal);
        cfg.add_edge(BlockId(1), BlockId(3), EdgeKind::Normal);
        cfg.add_edge(BlockId(2), BlockId(3), EdgeKind::Normal);
        cfg.entry = BlockId(0);

        let mut pass = PhiSimplify::new();
        pass.run(&mut cfg).unwrap();

        let block3 = cfg.block(BlockId(3)).unwrap();
        let phi_count = block3
            .insns
            .iter()
            .filter(|i| i.insn_type == InsnType::Phi)
            .count();
        assert_eq!(phi_count, 1, "PHI with different args should be kept");
    }

    #[test]
    fn test_eliminates_same_arg_phi() {
        // PHI where all args are the same should be eliminated
        let mut cfg = CFG::new("test");

        let mut block0 = Block::new(0u32);
        block0.push(InsnNode::const_val(
            RegisterArg::new_ssa(0, 0, ArgType::INT),
            1,
            ArgType::INT,
        ));
        cfg.add_block(block0);

        let block1 = Block::new(1u32);
        cfg.add_block(block1);

        let block2 = Block::new(2u32);
        cfg.add_block(block2);

        let mut block3 = Block::new(3u32);
        let phi = InsnNode::phi(
            RegisterArg::new_ssa(0, 1, ArgType::INT),
            vec![
                (1, InsnArg::reg_ssa(0, 0, ArgType::INT)),
                (2, InsnArg::reg_ssa(0, 0, ArgType::INT)),
            ],
        );
        block3.push(phi);
        let mut ret = InsnNode::new(InsnType::Return, 1);
        ret.add_arg(InsnArg::reg_ssa(0, 1, ArgType::INT));
        block3.push(ret);
        cfg.add_block(block3);

        cfg.add_edge(BlockId(0), BlockId(1), EdgeKind::Normal);
        cfg.add_edge(BlockId(0), BlockId(2), EdgeKind::Normal);
        cfg.add_edge(BlockId(1), BlockId(3), EdgeKind::Normal);
        cfg.add_edge(BlockId(2), BlockId(3), EdgeKind::Normal);
        cfg.entry = BlockId(0);

        let mut pass = PhiSimplify::new();
        pass.run(&mut cfg).unwrap();

        let block3 = cfg.block(BlockId(3)).unwrap();
        let phi_count = block3
            .insns
            .iter()
            .filter(|i| i.insn_type == InsnType::Phi)
            .count();
        assert_eq!(phi_count, 0, "PHI with same args should be eliminated");

        // Return should now use v0_0 directly
        let ret_insn = block3
            .insns
            .iter()
            .find(|i| i.insn_type == InsnType::Return)
            .expect("Return instruction should exist");
        if let Some(InsnArg::Reg(r)) = ret_insn.args.first() {
            assert_eq!(r.reg_num, 0);
            assert_eq!(r.ssa_version, Some(0), "Should use original SSA version");
        } else {
            panic!("Return should have register arg");
        }
    }

    #[test]
    fn test_dead_phi_elimination() {
        // PHI whose result is never used should be removed
        let mut cfg = CFG::new("test");

        let mut block0 = Block::new(0u32);
        block0.push(InsnNode::const_val(
            RegisterArg::new_ssa(0, 0, ArgType::INT),
            1,
            ArgType::INT,
        ));
        cfg.add_block(block0);

        let mut block1 = Block::new(1u32);
        block1.push(InsnNode::phi(
            RegisterArg::new_ssa(1, 0, ArgType::INT),
            vec![(0, InsnArg::reg_ssa(0, 0, ArgType::INT))],
        ));
        // Return uses only v0, leaving the Phi result dead.
        let mut ret = InsnNode::new(InsnType::Return, 1);
        ret.add_arg(InsnArg::reg_ssa(0, 0, ArgType::INT));
        block1.push(ret);
        cfg.add_block(block1);

        cfg.add_edge(BlockId(0), BlockId(1), EdgeKind::Normal);
        cfg.entry = BlockId(0);

        let mut pass = PhiSimplify::new();
        pass.run(&mut cfg).unwrap();

        let block1 = cfg.block(BlockId(1)).unwrap();
        let phi_count = block1
            .insns
            .iter()
            .filter(|i| i.insn_type == InsnType::Phi)
            .count();
        assert_eq!(phi_count, 0, "Dead PHI should be eliminated");
    }

    #[test]
    fn test_self_referential_phi() {
        // PHI like phi(v0_0, v0_1) where v0_1 = phi result should simplify
        let mut cfg = CFG::new("test");

        let mut block0 = Block::new(0u32);
        block0.push(InsnNode::const_val(
            RegisterArg::new_ssa(0, 0, ArgType::INT),
            1,
            ArgType::INT,
        ));
        cfg.add_block(block0);

        let mut block1 = Block::new(1u32);
        // v0_1 = phi(v0_0, v0_1) - references itself
        let phi = InsnNode::phi(
            RegisterArg::new_ssa(0, 1, ArgType::INT),
            vec![
                (0, InsnArg::reg_ssa(0, 0, ArgType::INT)),
                (1, InsnArg::reg_ssa(0, 1, ArgType::INT)),
            ],
        );
        block1.push(phi);
        let mut ret = InsnNode::new(InsnType::Return, 1);
        ret.add_arg(InsnArg::reg_ssa(0, 1, ArgType::INT));
        block1.push(ret);
        cfg.add_block(block1);

        cfg.add_edge(BlockId(0), BlockId(1), EdgeKind::Normal);
        cfg.add_edge(BlockId(1), BlockId(1), EdgeKind::Normal); // loop back
        cfg.entry = BlockId(0);

        let mut pass = PhiSimplify::new();
        pass.run(&mut cfg).unwrap();

        let block1 = cfg.block(BlockId(1)).unwrap();
        let phi_count = block1
            .insns
            .iter()
            .filter(|i| i.insn_type == InsnType::Phi)
            .count();
        assert_eq!(phi_count, 0, "Self-referential PHI should be eliminated");
    }
}
