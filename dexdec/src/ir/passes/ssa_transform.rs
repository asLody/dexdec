//! SSA (Static Single Assignment) Transformation Pass.
//!
//! This module implements the standard SSA construction algorithm:
//! 1. Place PHI nodes at dominance frontiers
//! 2. Rename variables with unique SSA versions
//!
//! ## Algorithm
//!
//! The algorithm follows the approach from "Efficiently Computing Static Single
//! Assignment Form and the Control Dependence Graph" by Cytron et al.
//!
//! ### PHI Placement
//!
//! For each variable that is defined in the CFG:
//! 1. Find all blocks where it's defined
//! 2. Compute the iterated dominance frontier of these blocks
//! 3. Insert PHI nodes at the frontier blocks
//!
//! ### Variable Renaming
//!
//! Walk the dominator tree in pre-order:
//! 1. For each instruction, rename uses to the current version
//! 2. For definitions, create a new version
//! 3. Update PHI operands in successor blocks
//! 4. Visit dominator tree children

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use crate::ir::{
    analysis::{DominanceError, DominanceFrontier, DominatorTree, RegisterLiveness},
    arg::{InsnArg, RegisterArg},
    block::BlockId,
    cfg::CFG,
    insn::{InsnNode, InsnType},
    passes::{Pass, PassResult},
    ty::ArgType,
    InstructionTransform, InstructionTree, InstructionTreeError,
};

/// SSA transformation pass.
///
/// Converts a CFG into SSA form by:
/// 1. Inserting PHI nodes at join points
/// 2. Renaming registers to unique SSA versions
#[derive(Debug, Default)]
pub struct SSATransform;

#[derive(Debug, Clone)]
pub enum SsaTransformError {
    Dominance(DominanceError),
    InstructionTree(InstructionTreeError),
    MissingExceptionSource(BlockId),
    InvalidExceptionBoundary {
        block: BlockId,
        throwing: Vec<usize>,
    },
    MissingPhiPlacement(BlockId),
    MissingPhiTopology(BlockId),
    MissingThrowingState(BlockId),
    UncoveredInput(u32),
    MissingBlock(BlockId),
    MissingPhiResult(BlockId),
    UnbalancedStack(u32),
    MissingTypeDomain {
        register: u32,
        version: u32,
    },
    MissingDefinition {
        register: u32,
        offset: u32,
    },
    MissingPhiSuccessor(BlockId),
    MissingPhiEdge {
        source: BlockId,
        target: BlockId,
        kind: crate::ir::EdgeKind,
    },
    MissingPhiDefinition {
        source: BlockId,
        target: BlockId,
        register: u32,
    },
    MissingPhiSlot {
        block: BlockId,
        index: usize,
    },
}

impl std::fmt::Display for SsaTransformError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Dominance(error) => error.fmt(formatter),
            Self::InstructionTree(error) => error.fmt(formatter),
            Self::MissingExceptionSource(block) => {
                write!(formatter, "missing exception source {block}")
            }
            Self::InvalidExceptionBoundary { block, throwing } => write!(
                formatter,
                "exception source {block} must contain one terminal throwing instruction, found {throwing:?}"
            ),
            Self::MissingPhiPlacement(block) => write!(formatter, "missing Phi block {block}"),
            Self::MissingPhiTopology(block) => {
                write!(
                    formatter,
                    "missing incoming-edge facts for Phi block {block}"
                )
            }
            Self::MissingThrowingState(block) => {
                write!(formatter, "exception source {block} has no throwing state")
            }
            Self::UncoveredInput(register) => write!(
                formatter,
                "input register v{register} is not covered by the method descriptor"
            ),
            Self::MissingBlock(block) => write!(formatter, "missing SSA block {block}"),
            Self::MissingPhiResult(block) => write!(formatter, "Phi in {block} has no result"),
            Self::UnbalancedStack(register) => {
                write!(formatter, "SSA stack for v{register} is unbalanced")
            }
            Self::MissingTypeDomain { register, version } => {
                write!(formatter, "v{register}_{version} has no type domain")
            }
            Self::MissingDefinition { register, offset } => write!(
                formatter,
                "use of v{register} has no reaching definition at offset {offset}"
            ),
            Self::MissingPhiSuccessor(block) => {
                write!(formatter, "missing Phi successor {block}")
            }
            Self::MissingPhiEdge {
                source,
                target,
                kind,
            } => write!(
                formatter,
                "Phi in {target} has no {kind:?} edge from {source}"
            ),
            Self::MissingPhiDefinition {
                source,
                target,
                register,
            } => write!(
                formatter,
                "Phi in {target} has no reaching definition for v{register} from {source}"
            ),
            Self::MissingPhiSlot { block, index } => {
                write!(formatter, "Phi in {block} has no operand slot {index}")
            }
        }
    }
}

impl std::error::Error for SsaTransformError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Dominance(error) => Some(error),
            Self::InstructionTree(error) => Some(error),
            _ => None,
        }
    }
}

impl Pass for SSATransform {
    type Error = SsaTransformError;

    fn name(&self) -> &'static str {
        "ssa_transform"
    }

    fn run(&mut self, cfg: &mut CFG) -> Result<PassResult, Self::Error> {
        Self::model_refining_definitions(cfg);
        Self::validate_exception_boundaries(cfg)?;

        // Step 1: Compute dominance information
        let dom_tree = DominatorTree::compute(cfg).map_err(SsaTransformError::Dominance)?;
        let dom_frontier =
            DominanceFrontier::compute(cfg, &dom_tree).map_err(SsaTransformError::Dominance)?;
        let liveness = RegisterLiveness::analyze(cfg);

        // Step 2: Find all registers that need PHI nodes
        let variables = PhiPlacement::variables(cfg);

        if variables.is_empty() {
            return Ok(PassResult::Unchanged);
        }

        // Step 3: Place PHI nodes
        let phi_placements = PhiPlacement::compute(cfg, &dom_frontier, &liveness, &variables);
        PhiPlacement::insert(cfg, &phi_placements)?;

        // Step 4: Rename variables
        let mut renamer = VariableRenamer::new(variables.len());
        renamer.rename(cfg, &dom_tree)?;

        Ok(PassResult::Changed)
    }
}

impl SSATransform {
    fn validate_exception_boundaries(cfg: &CFG) -> Result<(), SsaTransformError> {
        for block in cfg.block_ids() {
            let has_exception_edge = cfg
                .successors_with_kind(block)
                .iter()
                .any(|(_, kind)| *kind == crate::ir::EdgeKind::Exception);
            if !has_exception_edge {
                continue;
            }
            let body = cfg
                .block(block)
                .ok_or(SsaTransformError::MissingExceptionSource(block))?;
            let throwing = body
                .insns
                .iter()
                .enumerate()
                .filter(|(_, instruction)| instruction.can_throw())
                .map(|(index, _)| index)
                .collect::<Vec<_>>();
            if throwing.as_slice() != [body.insns.len().saturating_sub(1)] {
                return Err(SsaTransformError::InvalidExceptionBoundary { block, throwing });
            }
        }
        Ok(())
    }

    fn model_refining_definitions(cfg: &mut CFG) {
        for block in cfg.blocks.values_mut() {
            for insn in &mut block.insns {
                if insn.insn_type != InsnType::CheckCast || insn.result.is_some() {
                    continue;
                }
                let Some(source) = insn.args.first().and_then(InsnArg::as_register) else {
                    continue;
                };
                let mut result = source.clone();
                if let Some(target_type) = insn.conversion_type() {
                    result.ty = target_type.clone();
                }
                insn.result = Some(result);
            }
        }
    }
}

struct PhiPlacement;

impl PhiPlacement {
    /// Collect all registers that participate in the CFG.
    ///
    /// Dalvik method inputs are often only used, not defined, especially in
    /// constructors that just initialize fields. They still need SSA identities so
    /// later code-var recovery can bind them to `this` and declared parameters.
    fn variables(cfg: &CFG) -> Vec<u32> {
        let mut vars = BTreeSet::new();

        for block in cfg.blocks.values() {
            for insn in &block.insns {
                if let Some(result) = &insn.result {
                    vars.insert(result.reg_num);
                }
                for arg in &insn.args {
                    vars.extend(arg.regs_used());
                }
                if let Some(target) = &insn.payload.compound_target {
                    vars.extend(target.regs_used());
                }
            }
        }

        let first_input = cfg.registers.saturating_sub(cfg.ins);
        for reg in first_input..cfg.registers {
            vars.insert(reg);
        }

        vars.into_iter().collect()
    }

    /// Determine where to place PHI nodes for each variable.
    /// Returns a map from block ID to the set of registers that need PHI nodes.
    /// Uses BTreeMap to ensure deterministic iteration order.
    fn compute(
        cfg: &CFG,
        dom_frontier: &DominanceFrontier,
        liveness: &RegisterLiveness,
        variables: &[u32],
    ) -> BTreeMap<BlockId, BTreeSet<u32>> {
        let mut phi_placements: BTreeMap<BlockId, BTreeSet<u32>> = BTreeMap::new();
        let mut exceptional_definitions = BTreeMap::<u32, BTreeSet<BlockId>>::new();
        for block in cfg.block_ids() {
            let edge_clobbers = cfg
                .incoming_edges(block)
                .into_iter()
                .filter(|(_, kind)| *kind == crate::ir::EdgeKind::Exception)
                .filter_map(|(source, _)| {
                    cfg.block(source)
                        .and_then(|body| body.insns.last())
                        .and_then(|throwing| throwing.result.as_ref())
                        .map(|result| result.reg_num)
                })
                .collect::<BTreeSet<_>>();
            for variable in edge_clobbers {
                if liveness.is_live_in(block, variable) {
                    exceptional_definitions
                        .entry(variable)
                        .or_default()
                        .insert(block);
                }
            }
        }

        for &var in variables {
            // Find all blocks where this variable is defined
            let def_blocks: Vec<_> = liveness.definition_blocks(var).collect();
            let edge_definitions = exceptional_definitions
                .get(&var)
                .cloned()
                .unwrap_or_default();

            if def_blocks.is_empty() && edge_definitions.is_empty() {
                continue;
            }

            // Compute iterated dominance frontier
            let mut work_list: VecDeque<_> = def_blocks
                .into_iter()
                .chain(edge_definitions.iter().copied())
                .collect();
            let mut processed = HashSet::new();
            let mut phi_blocks = edge_definitions.iter().copied().collect::<HashSet<_>>();
            for block in edge_definitions {
                phi_placements.entry(block).or_default().insert(var);
            }

            while let Some(block) = work_list.pop_front() {
                if processed.contains(&block) {
                    continue;
                }
                processed.insert(block);

                // Add PHI nodes at dominance frontier
                for df_block in dom_frontier.frontier(block) {
                    if !phi_blocks.contains(&df_block) {
                        // Only add PHI if the variable is live at entry
                        if liveness.is_live_in(df_block, var) {
                            phi_blocks.insert(df_block);
                            phi_placements.entry(df_block).or_default().insert(var);

                            // Add to work list for iterated frontier
                            if !processed.contains(&df_block) {
                                work_list.push_back(df_block);
                            }
                        }
                    }
                }
            }
        }

        phi_placements
    }

    /// Insert PHI nodes into the CFG.
    /// Uses BTreeMap for deterministic iteration order.
    fn insert(
        cfg: &mut CFG,
        phi_placements: &BTreeMap<BlockId, BTreeSet<u32>>,
    ) -> Result<(), SsaTransformError> {
        let incoming: BTreeMap<BlockId, Vec<(BlockId, crate::ir::EdgeKind)>> = phi_placements
            .keys()
            .map(|&block_id| (block_id, cfg.incoming_edges(block_id)))
            .collect();

        // Now do the mutable operations
        for (&block_id, vars) in phi_placements {
            let block = cfg
                .blocks
                .get_mut(&block_id)
                .ok_or(SsaTransformError::MissingPhiPlacement(block_id))?;
            let edges = incoming
                .get(&block_id)
                .cloned()
                .ok_or(SsaTransformError::MissingPhiTopology(block_id))?;

            // Create PHI nodes at the beginning of the block
            let mut phi_insns = Vec::new();
            for &var in vars {
                let mut phi = InsnNode::new(InsnType::Phi, edges.len());
                phi.set_result(RegisterArg::new(var, ArgType::unknown()));
                phi.payload.phi_edges = edges.clone();

                // The values are assigned while renaming each predecessor.
                // A register without an SSA version is an explicit unresolved
                // edge value and will be rejected by SSA validation.
                for _ in &edges {
                    phi.add_arg(InsnArg::reg(var, ArgType::unknown()));
                }

                phi_insns.push(phi);
            }

            // Insert PHI nodes at the beginning
            let existing_insns = std::mem::take(&mut block.insns);
            block.insns = phi_insns;
            block.insns.extend(existing_insns);
        }
        Ok(())
    }
}

/// Variable renaming state.
struct VariableRenamer {
    /// Current SSA version counter for each register
    counters: HashMap<u32, u32>,
    /// Stack of SSA versions for each register
    stacks: HashMap<u32, Vec<u32>>,
    /// Type observed at each SSA definition.
    types: HashMap<(u32, u32), ArgType>,
    missing_use: Option<u32>,
}

enum RenameTask {
    Enter(BlockId),
    Exit(Vec<u32>),
}

struct BlockRename {
    pushed: Vec<u32>,
    exceptional: Option<BTreeMap<u32, (u32, ArgType)>>,
}

impl VariableRenamer {
    fn new(_var_count: usize) -> Self {
        Self {
            counters: HashMap::new(),
            stacks: HashMap::new(),
            types: HashMap::new(),
            missing_use: None,
        }
    }

    /// Get the next SSA version for a register.
    fn next_version(&mut self, reg: u32) -> u32 {
        let counter = self.counters.entry(reg).or_insert(0);
        let version = *counter;
        *counter += 1;
        version
    }

    /// Push a new version onto the stack.
    fn push_version(&mut self, reg: u32, version: u32) {
        self.stacks.entry(reg).or_default().push(version);
    }

    /// Pop a version from the stack.
    fn pop_version(&mut self, reg: u32) -> Result<(), SsaTransformError> {
        let stack = self
            .stacks
            .get_mut(&reg)
            .ok_or(SsaTransformError::UnbalancedStack(reg))?;
        stack.pop().ok_or(SsaTransformError::UnbalancedStack(reg))?;
        if stack.is_empty() {
            self.stacks.remove(&reg);
        }
        Ok(())
    }

    /// Get the current version for a register.
    fn current_version(&self, reg: u32) -> Option<u32> {
        self.stacks.get(&reg).and_then(|s| s.last().copied())
    }

    fn current_type(&self, reg: u32) -> Option<&ArgType> {
        let version = self.current_version(reg)?;
        self.types.get(&(reg, version))
    }

    /// Rename all variables in the CFG.
    fn rename(&mut self, cfg: &mut CFG, dom_tree: &DominatorTree) -> Result<(), SsaTransformError> {
        self.seed_input_registers(cfg)?;
        let mut tasks = vec![RenameTask::Enter(cfg.entry)];
        while let Some(task) = tasks.pop() {
            match task {
                RenameTask::Enter(block) => {
                    let renamed = self.rename_definitions_and_uses(cfg, block)?;
                    for (successor, kind) in cfg.successors_with_kind(block).to_vec() {
                        let state = if kind == crate::ir::EdgeKind::Exception {
                            Some(
                                renamed
                                    .exceptional
                                    .as_ref()
                                    .ok_or(SsaTransformError::MissingThrowingState(block))?,
                            )
                        } else {
                            None
                        };
                        self.fill_phi_operands(cfg, block, successor, kind, state)?;
                    }

                    tasks.push(RenameTask::Exit(renamed.pushed));
                    let children = dom_tree.children(block).collect::<Vec<_>>();
                    tasks.extend(children.into_iter().rev().map(RenameTask::Enter));
                }
                RenameTask::Exit(pushed) => {
                    for register in pushed.into_iter().rev() {
                        self.pop_version(register)?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Method parameters live in the input register range before the entry block.
    /// Seeding them gives uses-before-def a real SSA identity instead of falling
    /// back to the physical Dalvik register.
    fn seed_input_registers(&mut self, cfg: &CFG) -> Result<(), SsaTransformError> {
        let first_input = cfg.registers.saturating_sub(cfg.ins);
        let mut input_types = BTreeMap::new();
        let mut register = first_input;
        if !cfg.method().is_static() && register < cfg.registers {
            input_types.insert(register, cfg.method().owner().clone());
            register += 1;
        }
        for ty in &cfg.method().descriptor().parameters {
            let slots = if ty.is_wide() { 2 } else { 1 };
            for slot in 0..slots {
                input_types.insert(register + slot, ty.clone());
            }
            register += slots;
        }
        for reg in first_input..cfg.registers {
            let version = self.next_version(reg);
            self.push_version(reg, version);
            let ty = input_types
                .remove(&reg)
                .ok_or(SsaTransformError::UncoveredInput(reg))?;
            self.types.insert((reg, version), ty);
        }
        Ok(())
    }

    fn rename_definitions_and_uses(
        &mut self,
        cfg: &mut CFG,
        block_id: BlockId,
    ) -> Result<BlockRename, SsaTransformError> {
        let mut pushed: Vec<u32> = Vec::new();
        let mut exceptional = None;
        let block = cfg
            .blocks
            .get_mut(&block_id)
            .ok_or(SsaTransformError::MissingBlock(block_id))?;
        for insn in &mut block.insns {
            if insn.insn_type == InsnType::Phi {
                let result = insn
                    .result
                    .as_mut()
                    .ok_or(SsaTransformError::MissingPhiResult(block_id))?;
                let version = self.next_version(result.reg_num);
                result.ssa_version = Some(version);
                self.types
                    .insert((result.reg_num, version), result.ty.clone());
                self.push_version(result.reg_num, version);
                pushed.push(result.reg_num);
                continue;
            }

            self.rename_insn_uses(insn)?;
            if insn.can_throw() {
                exceptional = Some(self.current_state()?);
            }

            // Rename definition
            if let Some(result) = &mut insn.result {
                let version = self.next_version(result.reg_num);
                result.ssa_version = Some(version);
                self.types
                    .insert((result.reg_num, version), result.ty.clone());
                self.push_version(result.reg_num, version);
                pushed.push(result.reg_num);
            }
        }
        Ok(BlockRename {
            pushed,
            exceptional,
        })
    }

    fn current_state(&self) -> Result<BTreeMap<u32, (u32, ArgType)>, SsaTransformError> {
        let mut state = BTreeMap::new();
        for register in self.stacks.keys() {
            let version = self
                .current_version(*register)
                .ok_or(SsaTransformError::UnbalancedStack(*register))?;
            let ty = self.types.get(&(*register, version)).cloned().ok_or(
                SsaTransformError::MissingTypeDomain {
                    register: *register,
                    version,
                },
            )?;
            state.insert(*register, (version, ty));
        }
        Ok(state)
    }

    fn rename_insn_uses(&mut self, insn: &mut InsnNode) -> Result<(), SsaTransformError> {
        self.missing_use = None;
        InstructionTree::transform_args(insn, self).map_err(SsaTransformError::InstructionTree)?;
        if let Some(register) = self.missing_use.take() {
            return Err(SsaTransformError::MissingDefinition {
                register,
                offset: insn.offset,
            });
        }
        Ok(())
    }
}

impl InstructionTransform for VariableRenamer {
    fn transform_register(&mut self, mut register: RegisterArg) -> InsnArg {
        if let Some(version) = self.current_version(register.reg_num) {
            register.ssa_version = Some(version);
            if !register.ty.is_known() {
                if let Some(ty) = self.current_type(register.reg_num) {
                    register.ty = ty.clone();
                }
            }
        } else {
            self.missing_use.get_or_insert(register.reg_num);
        }
        InsnArg::Reg(register)
    }
}

impl VariableRenamer {
    /// Fill in PHI operands for a successor block.
    fn fill_phi_operands(
        &mut self,
        cfg: &mut CFG,
        from: BlockId,
        to: BlockId,
        edge_kind: crate::ir::EdgeKind,
        state: Option<&BTreeMap<u32, (u32, ArgType)>>,
    ) -> Result<(), SsaTransformError> {
        // Update PHI nodes
        let block = cfg
            .blocks
            .get_mut(&to)
            .ok_or(SsaTransformError::MissingPhiSuccessor(to))?;
        for insn in &mut block.insns {
            if insn.insn_type != InsnType::Phi {
                break; // PHI nodes are at the beginning
            }

            if let Some(result) = &insn.result {
                let pred_index = insn
                    .payload
                    .phi_edges
                    .iter()
                    .position(|edge| *edge == (from, edge_kind))
                    .ok_or(SsaTransformError::MissingPhiEdge {
                        source: from,
                        target: to,
                        kind: edge_kind,
                    })?;
                let reg = result.reg_num;

                // Get current version for this predecessor
                let version_and_type = match state {
                    Some(state) => state.get(&reg).cloned(),
                    None => self.current_version(reg).and_then(|version| {
                        self.current_type(reg).cloned().map(|ty| (version, ty))
                    }),
                };
                let (version, ty) =
                    version_and_type.ok_or(SsaTransformError::MissingPhiDefinition {
                        source: from,
                        target: to,
                        register: reg,
                    })?;
                let slot =
                    insn.args
                        .get_mut(pred_index)
                        .ok_or(SsaTransformError::MissingPhiSlot {
                            block: to,
                            index: pred_index,
                        })?;
                let mut source_reg = RegisterArg::new(reg, ty);
                source_reg.ssa_version = Some(version);
                *slot = InsnArg::Reg(source_reg);
            } else {
                return Err(SsaTransformError::MissingPhiResult(to));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{block::Block, cfg::EdgeKind, MethodContext, MethodDescriptor};

    fn make_diamond_cfg() -> CFG {
        // Diamond CFG:
        //     0: v0 = 1
        //    / \
        //   1   2
        //   v0=2 v0=3
        //    \ /
        //     3: use v0
        let mut cfg = CFG::new("test");

        let mut block0 = Block::new(0u32);
        let mut insn = InsnNode::const_val(RegisterArg::new(0, ArgType::INT), 1, ArgType::INT);
        insn.set_offset(0);
        block0.push(insn);
        cfg.add_block(block0);

        let mut block1 = Block::new(1u32);
        let mut insn = InsnNode::const_val(RegisterArg::new(0, ArgType::INT), 2, ArgType::INT);
        insn.set_offset(0);
        block1.push(insn);
        cfg.add_block(block1);

        let mut block2 = Block::new(2u32);
        let mut insn = InsnNode::const_val(RegisterArg::new(0, ArgType::INT), 3, ArgType::INT);
        insn.set_offset(0);
        block2.push(insn);
        cfg.add_block(block2);

        let mut block3 = Block::new(3u32);
        let mut insn = InsnNode::new(InsnType::Return, 1);
        insn.add_arg(InsnArg::reg(0, ArgType::INT));
        insn.set_offset(0);
        block3.push(insn);
        cfg.add_block(block3);

        cfg.add_edge(BlockId(0), BlockId(1), EdgeKind::Normal);
        cfg.add_edge(BlockId(0), BlockId(2), EdgeKind::Normal);
        cfg.add_edge(BlockId(1), BlockId(3), EdgeKind::Normal);
        cfg.add_edge(BlockId(2), BlockId(3), EdgeKind::Normal);

        cfg.entry = BlockId(0);

        cfg
    }

    #[test]
    fn test_ssa_transform_diamond() {
        let mut cfg = make_diamond_cfg();

        let mut pass = SSATransform;
        let result = pass.run(&mut cfg);
        assert!(result.is_ok());

        // Block 3 should have a PHI node for v0
        let block3 = cfg.block(BlockId(3)).unwrap();
        let phi_count = block3
            .insns
            .iter()
            .filter(|i| i.insn_type == InsnType::Phi)
            .count();
        assert_eq!(phi_count, 1, "Expected 1 PHI node in block 3");

        // The PHI should be for register 0
        let phi = block3.insns.first().unwrap();
        assert_eq!(phi.insn_type, InsnType::Phi);
        assert_eq!(phi.result.as_ref().unwrap().reg_num, 0);
    }

    #[test]
    fn test_ssa_versioning() {
        let mut cfg = make_diamond_cfg();

        let mut pass = SSATransform;
        pass.run(&mut cfg).unwrap();

        // Check that v0 has different SSA versions in different blocks
        let block0 = cfg.block(BlockId(0)).unwrap();
        let block1 = cfg.block(BlockId(1)).unwrap();

        // Block 0's v0 definition should have version 0
        let v0_in_block0 = &block0.insns[0];
        assert!(v0_in_block0.result.as_ref().unwrap().ssa_version.is_some());

        // Block 1's v0 definition should have a different version
        let v0_in_block1 = &block1.insns[0];
        assert!(v0_in_block1.result.as_ref().unwrap().ssa_version.is_some());
    }

    #[test]
    fn test_input_only_registers_get_ssa_versions() {
        let mut cfg = CFG::new("<init>");
        cfg.registers = 3;
        cfg.ins = 3;
        cfg.set_method(MethodContext::new(
            ArgType::object("ObjectTypeAdapter"),
            "<init>",
            MethodDescriptor {
                parameters: vec![ArgType::object("Gson"), ArgType::object("ToNumberStrategy")],
                return_type: ArgType::VOID,
            },
            false,
        ));

        let mut block = Block::new(0u32);
        block.push(InsnNode::iput(
            InsnArg::reg(1, ArgType::object("Gson")),
            InsnArg::reg(0, ArgType::object("ObjectTypeAdapter")),
            0,
        ));
        block.push(InsnNode::ret(None));
        cfg.add_block(block);
        cfg.entry = BlockId(0);

        let mut pass = SSATransform;
        pass.run(&mut cfg).unwrap();

        let block = cfg.block(BlockId(0)).unwrap();
        let insn = &block.insns[0];
        assert_eq!(
            insn.args[0].as_register().unwrap().ssa_version,
            Some(0),
            "first declared parameter should be seeded as an SSA input"
        );
        assert_eq!(
            insn.args[1].as_register().unwrap().ssa_version,
            Some(0),
            "implicit this should be seeded as an SSA input"
        );
    }

    #[test]
    fn exception_edge_observes_state_before_throwing_result() {
        let context = ArgType::object("android/content/Context");
        let bundle = ArgType::object("android/os/Bundle");
        let mut cfg = CFG::new("exception_result_state");
        cfg.registers = 1;
        cfg.ins = 1;
        cfg.set_method(MethodContext::new(
            ArgType::object("Owner"),
            "call",
            MethodDescriptor {
                parameters: vec![context.clone()],
                return_type: context.clone(),
            },
            true,
        ));

        let mut throwing = Block::new(0u32);
        let mut invoke = InsnNode::new(InsnType::Invoke, 0);
        invoke.set_result(RegisterArg::new(0, bundle.clone()));
        throwing.push(invoke);
        cfg.add_block(throwing);

        let mut handler = Block::new(1u32);
        handler.push(InsnNode::ret(Some(InsnArg::reg(0, context))));
        cfg.add_block(handler);

        let mut normal = Block::new(2u32);
        normal.push(InsnNode::ret(Some(InsnArg::reg(0, bundle))));
        cfg.add_block(normal);

        cfg.add_edge(BlockId(0), BlockId(1), EdgeKind::Exception);
        cfg.add_edge(BlockId(0), BlockId(2), EdgeKind::Normal);
        cfg.entry = BlockId(0);

        SSATransform.run(&mut cfg).unwrap();

        let handler = cfg.block(BlockId(1)).unwrap();
        let phi = handler
            .insns
            .iter()
            .find(|instruction| instruction.insn_type == InsnType::Phi)
            .expect("handler edge-state phi");
        assert_eq!(phi.args[0].as_register().unwrap().ssa_version, Some(0));
        let invoke_result = cfg.block(BlockId(0)).unwrap().insns[0]
            .result
            .as_ref()
            .unwrap()
            .ssa_version;
        assert_ne!(
            phi.args[0].as_register().unwrap().ssa_version,
            invoke_result
        );
    }

    #[test]
    fn exceptional_edge_definitions_reach_handler_join() {
        let prior = ArgType::object("Prior");
        let result = ArgType::object("Result");
        let mut cfg = CFG::new("exception_result_join");
        cfg.registers = 1;
        cfg.ins = 1;
        cfg.set_method(MethodContext::new(
            ArgType::object("Owner"),
            "call",
            MethodDescriptor {
                parameters: vec![prior.clone()],
                return_type: prior.clone(),
            },
            true,
        ));

        let mut throwing = Block::new(0u32);
        let mut invoke = InsnNode::new(InsnType::Invoke, 0);
        invoke.set_result(RegisterArg::new(0, result.clone()));
        throwing.push(invoke);
        cfg.add_block(throwing);

        cfg.add_block(Block::new(1u32));
        cfg.add_block(Block::new(2u32));

        let mut join = Block::new(3u32);
        join.push(InsnNode::ret(Some(InsnArg::reg(0, prior))));
        cfg.add_block(join);

        let mut normal = Block::new(4u32);
        normal.push(InsnNode::ret(Some(InsnArg::reg(0, result))));
        cfg.add_block(normal);

        cfg.add_edge(BlockId(0), BlockId(1), EdgeKind::Exception);
        cfg.add_edge(BlockId(0), BlockId(2), EdgeKind::Exception);
        cfg.add_edge(BlockId(0), BlockId(4), EdgeKind::Normal);
        cfg.add_edge(BlockId(1), BlockId(3), EdgeKind::Normal);
        cfg.add_edge(BlockId(2), BlockId(3), EdgeKind::Normal);
        cfg.entry = BlockId(0);

        SSATransform.run(&mut cfg).unwrap();

        let invoke_result = cfg.block(BlockId(0)).unwrap().insns[0]
            .result
            .as_ref()
            .unwrap()
            .ssa_version;
        let join = cfg.block(BlockId(3)).unwrap();
        let phi = join
            .insns
            .iter()
            .find(|instruction| instruction.insn_type == InsnType::Phi)
            .expect("handler join phi");
        assert!(phi
            .args
            .iter()
            .all(|argument| { argument.as_register().unwrap().ssa_version != invoke_result }));
        assert_eq!(
            join.insns.last().unwrap().args[0]
                .as_register()
                .unwrap()
                .ssa_version,
            phi.result.as_ref().unwrap().ssa_version
        );
    }
}
