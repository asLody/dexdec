//! Region transfer and cleanup-chain analysis.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    analysis::{ControlFlowFacts, InstructionEffects, SsaVar},
    BlockId, EdgeKind, InsnArg, InsnType, InstructionTransform, InstructionTree, RegisterArg,
    StatementOrigin, CFG,
};

use super::{
    InstructionElisions, RegionEdge, RegionExit, RegionExitKind, RegionId, RegionInvariantError,
    RegionKind, RegionLeave, RegionTransfer, RegionTransferKind, RegionTree, ResolvedRegionExit,
};

pub(super) struct RegionExitFacts {
    pub(super) transfers: Vec<RegionTransfer>,
    pub(super) leaves: Vec<ResolvedRegionExit>,
}

pub(super) struct OccurrenceElision<'a> {
    cfg: &'a CFG,
    tree: &'a RegionTree,
    handlers: &'a BTreeMap<RegionId, Vec<RegionId>>,
    elisions: &'a InstructionElisions,
}

impl<'a> OccurrenceElision<'a> {
    pub(super) fn new(
        cfg: &'a CFG,
        tree: &'a RegionTree,
        handlers: &'a BTreeMap<RegionId, Vec<RegionId>>,
        elisions: &'a InstructionElisions,
    ) -> Self {
        Self {
            cfg,
            tree,
            handlers,
            elisions,
        }
    }

    pub(super) fn contains(
        &self,
        region: RegionId,
        origin: &StatementOrigin,
    ) -> Result<bool, RegionInvariantError> {
        if !self.elisions.contains(origin) {
            return Ok(false);
        }
        if self.elisions.is_source_equivalent(origin) {
            return Ok(true);
        }
        let instruction = self
            .cfg
            .block(origin.block)
            .and_then(|block| {
                block
                    .insns
                    .iter()
                    .find(|instruction| instruction.id == origin.instruction)
            })
            .ok_or(RegionInvariantError::MissingBlock(origin.block))?;
        if !instruction.can_throw() {
            return Ok(true);
        }
        for (target, kind) in self.cfg.successors_with_kind(origin.block) {
            if *kind != EdgeKind::Exception {
                continue;
            }
            let target_owner = self.tree.owner(*target)?;
            for handler in self.handlers.get(&region).into_iter().flatten() {
                if target_owner == *handler || self.tree.is_ancestor(*handler, target_owner)? {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }
}

pub(super) struct RegionExitAnalysis<'a> {
    cfg: &'a CFG,
    tree: &'a RegionTree,
    elisions: &'a InstructionElisions,
    control_flow: &'a ControlFlowFacts,
    cleanup_representatives: &'a BTreeMap<BlockId, BlockId>,
    handlers: &'a BTreeMap<RegionId, Vec<RegionId>>,
    terminal_facts: TerminalContinuationFacts,
}

pub(super) struct CleanupChainAnalysis<'a> {
    tree: &'a RegionTree,
    handlers: &'a BTreeMap<RegionId, Vec<RegionId>>,
}

impl<'a> CleanupChainAnalysis<'a> {
    pub(super) fn new(
        tree: &'a RegionTree,
        handlers: &'a BTreeMap<RegionId, Vec<RegionId>>,
    ) -> Self {
        Self { tree, handlers }
    }

    pub(super) fn between(
        &self,
        source: RegionId,
        target: RegionId,
    ) -> Result<Vec<RegionId>, RegionInvariantError> {
        let mut result = Vec::new();
        let mut current_id = source;
        let target_ancestors = self
            .parent_chain(target)?
            .into_iter()
            .collect::<BTreeSet<_>>();
        let mut exited_child = None;

        while !target_ancestors.contains(&current_id) {
            let current = self
                .tree
                .region(current_id)
                .ok_or(RegionInvariantError::UnknownRegion(current_id))?;
            match current.kind {
                RegionKind::Try => {
                    let already_in_cleanup = match exited_child {
                        Some(child) => self
                            .tree
                            .region(child)
                            .ok_or(RegionInvariantError::UnknownRegion(child))?
                            .kind
                            .is_finally_handler(),
                        None => false,
                    };
                    if !already_in_cleanup {
                        let mut cleanups = Vec::new();
                        for child in self.handlers.get(&current_id).into_iter().flatten() {
                            if self
                                .tree
                                .region(*child)
                                .ok_or(RegionInvariantError::UnknownRegion(*child))?
                                .kind
                                .is_finally_handler()
                            {
                                cleanups.push(*child);
                            }
                        }
                        if cleanups.len() > 1 {
                            return Err(RegionInvariantError::AmbiguousCleanup {
                                region: current_id,
                                handlers: cleanups,
                            });
                        }
                        result.extend(cleanups);
                    }
                }
                RegionKind::Synchronized(_) => result.push(current_id),
                _ => {}
            }
            let parent =
                self.parent(current_id)?
                    .ok_or(RegionInvariantError::NoCommonAncestor {
                        left: source,
                        right: target,
                    })?;
            exited_child = Some(current_id);
            current_id = parent;
        }
        Ok(result)
    }

    fn parent_chain(&self, region: RegionId) -> Result<Vec<RegionId>, RegionInvariantError> {
        let mut chain = Vec::new();
        let mut visited = BTreeSet::new();
        let mut current = Some(region);
        while let Some(region) = current {
            if !visited.insert(region) {
                chain.push(region);
                return Err(RegionInvariantError::RegionParentCycle(chain));
            }
            chain.push(region);
            current = self.parent(region)?;
        }
        Ok(chain)
    }

    fn parent(&self, region: RegionId) -> Result<Option<RegionId>, RegionInvariantError> {
        let semantic_owners = self
            .handlers
            .iter()
            .filter_map(|(owner, handlers)| handlers.contains(&region).then_some(*owner))
            .collect::<Vec<_>>();
        let semantic_parent = semantic_owners
            .into_iter()
            .try_fold(None, |common, owner| {
                Ok::<_, RegionInvariantError>(Some(match common {
                    Some(common) => self.tree.common_ancestor(common, owner)?,
                    None => owner,
                }))
            })?;
        Ok(semantic_parent.or_else(|| self.tree.region(region).and_then(|region| region.parent)))
    }
}

impl<'a> RegionExitAnalysis<'a> {
    pub(super) fn new(
        cfg: &'a CFG,
        tree: &'a RegionTree,
        elisions: &'a InstructionElisions,
        control_flow: &'a ControlFlowFacts,
        cleanup_representatives: &'a BTreeMap<BlockId, BlockId>,
        handlers: &'a BTreeMap<RegionId, Vec<RegionId>>,
    ) -> Self {
        Self {
            cfg,
            tree,
            elisions,
            control_flow,
            cleanup_representatives,
            handlers,
            terminal_facts: TerminalContinuationFacts::analyze(cfg),
        }
    }

    pub(super) fn analyze(&self) -> Result<RegionExitFacts, RegionInvariantError> {
        let transfers = self.transfers()?;
        let mut leaves = Vec::new();
        for leave in self.leaves(&transfers)? {
            leaves.push(self.resolve(leave)?);
        }
        Ok(RegionExitFacts { transfers, leaves })
    }

    pub(super) fn cleanup_chain(
        &self,
        source: RegionId,
        target: RegionId,
    ) -> Result<Vec<RegionId>, RegionInvariantError> {
        CleanupChainAnalysis::new(self.tree, self.handlers).between(source, target)
    }

    fn transfers(&self) -> Result<Vec<RegionTransfer>, RegionInvariantError> {
        let mut transfers = Vec::new();
        for source_block in self.cfg.block_ids() {
            if self.cleanup_representatives.contains_key(&source_block) {
                continue;
            }
            let source_region = self.tree.owner(source_block)?;
            for &(target_block, edge_kind) in self.cfg.successors_with_kind(source_block) {
                if edge_kind == EdgeKind::Exception {
                    continue;
                }
                let target_region = self.tree.owner(target_block)?;
                let destination_block = self
                    .cleanup_representatives
                    .get(&target_block)
                    .copied()
                    .unwrap_or(target_block);
                let destination_region = self.tree.owner(destination_block)?;
                let kind = self.transfer_kind(source_region, destination_region)?;
                let mut transfer = RegionTransfer {
                    source_block,
                    target_block,
                    edge_kind,
                    source_region,
                    target_region,
                    destination_block,
                    destination_region,
                    leave_target: (kind == RegionTransferKind::Leave)
                        .then(|| self.tree.common_ancestor(source_region, destination_region))
                        .transpose()?,
                    kind,
                    exit_kind: self.exit_kind(source_block, destination_block, source_region)?,
                };
                if self.forwarded_cleanup_throw(&transfer)?.is_some() {
                    transfer.exit_kind = RegionExitKind::Throw;
                }
                transfers.push(transfer);
            }
        }
        Ok(transfers)
    }

    fn leaves(
        &self,
        transfers: &[RegionTransfer],
    ) -> Result<Vec<RegionLeave>, RegionInvariantError> {
        let mut leaves = Vec::new();
        for transfer in transfers {
            let forwarded_cleanup = self.forwarded_cleanup_throw(transfer)?;
            if !transfer.requires_leave(self.cfg) {
                continue;
            }
            let target = transfer.exit_destination(self.tree.root());
            let exit = match (forwarded_cleanup, transfer.exit_kind) {
                (Some(exception), RegionExitKind::Throw) => {
                    RegionExit::Throw(InsnArg::Reg(exception))
                }
                (None, RegionExitKind::FallThrough) => {
                    RegionExit::FallThrough(transfer.destination_block)
                }
                (None, RegionExitKind::Return) => self
                    .terminal_continuation(
                        transfer.source_block,
                        self.control_flow.continuation(transfer.destination_block),
                    )?
                    .ok_or(RegionInvariantError::InvalidLeaveKind {
                        block: transfer.source_block,
                        kind: transfer.exit_kind,
                    })?,
                (None, RegionExitKind::Break) => RegionExit::Break,
                (None, RegionExitKind::Continue) => RegionExit::Continue,
                (_, kind) => {
                    return Err(RegionInvariantError::InvalidLeaveKind {
                        block: transfer.source_block,
                        kind,
                    });
                }
            };
            let mut leave = RegionLeave::new(transfer.source_region, target, exit)
                .with_source_block(transfer.source_block)
                .with_edge(RegionEdge {
                    source: transfer.source_block,
                    target: transfer.target_block,
                    kind: transfer.edge_kind,
                });
            leave.control_target = self.control_target(transfer)?;
            leaves.push(leave);
        }

        for source_block in self.cfg.block_ids() {
            if self.cleanup_representatives.contains_key(&source_block) {
                continue;
            }
            let Some(exit) = self.terminal(source_block)? else {
                continue;
            };
            let kind = exit.kind();
            let terminal = self
                .cfg
                .block(source_block)
                .and_then(|block| block.insns.last());
            let source = self.tree.owner(source_block)?;
            if let Some(instruction) = terminal {
                let origin = StatementOrigin {
                    block: source_block,
                    instruction: instruction.id,
                };
                if OccurrenceElision::new(self.cfg, self.tree, self.handlers, self.elisions)
                    .contains(source, &origin)?
                {
                    continue;
                }
            }
            let target = if kind == RegionExitKind::Throw {
                let targets = self
                    .cfg
                    .successors_with_kind(source_block)
                    .iter()
                    .filter(|(_, edge)| *edge == EdgeKind::Exception)
                    .map(|(block, _)| self.tree.owner(*block))
                    .collect::<Result<Vec<_>, _>>()?;
                let mut targets = targets.into_iter();
                match targets.next() {
                    Some(first) => targets.try_fold(first, |ancestor, target| {
                        self.tree.common_ancestor(ancestor, target)
                    })?,
                    None => self.tree.root(),
                }
            } else {
                self.tree.root()
            };
            leaves.push(RegionLeave::new(source, target, exit).with_source_block(source_block));
        }

        for region in self.tree.regions() {
            let continuation = match &region.kind {
                RegionKind::Catch(catch) | RegionKind::Cleanup(catch) => catch.continuation,
                _ => None,
            };
            let Some(target_block) = continuation else {
                continue;
            };
            let destination = self.tree.owner(target_block)?;
            let target = self.tree.common_ancestor(region.id, destination)?;
            let control = self.control_exit(region.id, target_block)?;
            let exit = match control {
                Some(ControlExit {
                    kind: RegionExitKind::Break,
                    ..
                }) => RegionExit::Break,
                Some(ControlExit {
                    kind: RegionExitKind::Continue,
                    ..
                }) => RegionExit::Continue,
                _ => RegionExit::FallThrough(target_block),
            };
            let mut leave = RegionLeave::new(region.id, target, exit);
            leave.control_target = control.map(|control| control.target);
            leaves.push(leave);
        }
        Ok(leaves)
    }

    /// A nested compiler cleanup can forward its caught exception directly
    /// into an enclosing cleanup handler. Once that handler is represented
    /// lexically as a finally or catch-all cleanup, its physical entry no
    /// longer denotes an ordinary source continuation (and a finally could be
    /// replayed). Model the proven cleanup handler's logical completion as a
    /// rethrow instead.
    fn forwarded_cleanup_throw(
        &self,
        transfer: &RegionTransfer,
    ) -> Result<Option<RegisterArg>, RegionInvariantError> {
        if transfer.kind != RegionTransferKind::Leave
            || !matches!(
                transfer.exit_kind,
                RegionExitKind::FallThrough | RegionExitKind::Throw
            )
        {
            return Ok(None);
        }
        let source = self
            .tree
            .region(transfer.source_region)
            .ok_or(RegionInvariantError::UnknownRegion(transfer.source_region))?;
        let RegionKind::Cleanup(cleanup) = &source.kind else {
            return Ok(None);
        };
        let destination = self.tree.region(transfer.destination_region).ok_or(
            RegionInvariantError::UnknownRegion(transfer.destination_region),
        )?;
        if destination.entry != Some(transfer.destination_block) {
            return Ok(None);
        }
        let target = transfer.exit_destination(self.tree.root());
        let forwarded_handler = if matches!(&destination.kind, RegionKind::Finally) {
            self.cleanup_chain(transfer.source_region, target)?
                .contains(&transfer.destination_region)
        } else if matches!(&destination.kind, RegionKind::Cleanup(_)) {
            let mut attached = false;
            for (owner, handlers) in self.handlers {
                if handlers.contains(&transfer.destination_region)
                    && (*owner == transfer.source_region
                        || self.tree.is_ancestor(*owner, transfer.source_region)?)
                {
                    attached = true;
                    break;
                }
            }
            attached
        } else {
            false
        };
        if !forwarded_handler {
            return Ok(None);
        }
        Ok(cleanup.exception_value.clone())
    }

    fn resolve(&self, leave: RegionLeave) -> Result<ResolvedRegionExit, RegionInvariantError> {
        let cleanup_regions = self.cleanup_chain(leave.source, leave.target)?;
        Ok(ResolvedRegionExit {
            leave,
            cleanup_regions,
        })
    }

    fn transfer_kind(
        &self,
        source: RegionId,
        target: RegionId,
    ) -> Result<RegionTransferKind, RegionInvariantError> {
        Ok(if source == target {
            RegionTransferKind::Local
        } else if self.tree.is_ancestor(source, target)? {
            RegionTransferKind::Enter
        } else {
            RegionTransferKind::Leave
        })
    }

    fn exit_kind(
        &self,
        source_block: BlockId,
        target_block: BlockId,
        source_region: RegionId,
    ) -> Result<RegionExitKind, RegionInvariantError> {
        if let Some(exit) = self.terminal(source_block)? {
            return Ok(exit.kind());
        }
        if let Some(control) = self.control_exit(source_region, target_block)? {
            return Ok(control.kind);
        }
        let control_destination = self.control_flow.continuation(target_block);
        if let Some(exit) = self.terminal_continuation(source_block, control_destination)? {
            return Ok(exit.kind());
        }
        Ok(RegionExitKind::FallThrough)
    }

    fn control_target(
        &self,
        transfer: &RegionTransfer,
    ) -> Result<Option<RegionId>, RegionInvariantError> {
        match transfer.exit_kind {
            RegionExitKind::Continue | RegionExitKind::Break => self
                .control_exit(transfer.source_region, transfer.destination_block)?
                .filter(|control| control.kind == transfer.exit_kind)
                .map(|control| control.target)
                .map(Some)
                .ok_or(RegionInvariantError::MissingControlTarget {
                    block: transfer.source_block,
                    kind: transfer.exit_kind,
                }),
            _ => Ok(None),
        }
    }

    fn control_exit(
        &self,
        source: RegionId,
        destination: BlockId,
    ) -> Result<Option<ControlExit>, RegionInvariantError> {
        let destination = self.control_flow.structural_continuation(destination);
        let chain = self.tree.parent_chain(source)?;
        // Continue wins when an inner control's follow is an outer loop header.
        for target in chain.iter().copied() {
            let region = self
                .tree
                .region(target)
                .ok_or(RegionInvariantError::UnknownRegion(target))?;
            if matches!(&region.kind, RegionKind::Loop(_)) && region.entry == Some(destination) {
                return Ok(Some(ControlExit {
                    kind: RegionExitKind::Continue,
                    target,
                }));
            }
        }
        for target in chain {
            let region = self
                .tree
                .region(target)
                .ok_or(RegionInvariantError::UnknownRegion(target))?;
            if matches!(&region.kind, RegionKind::Loop(_) | RegionKind::Switch(_))
                && region.kind.follow() == Some(destination)
            {
                return Ok(Some(ControlExit {
                    kind: RegionExitKind::Break,
                    target,
                }));
            }
        }
        Ok(None)
    }

    fn terminal(&self, block: BlockId) -> Result<Option<RegionExit>, RegionInvariantError> {
        let body = self
            .cfg
            .block(block)
            .ok_or(RegionInvariantError::MissingBlock(block))?;
        let Some(insn) = body.terminator() else {
            return Ok(None);
        };
        Ok(match insn.insn_type {
            InsnType::Return => Some(RegionExit::Return(insn.get_arg(0).cloned())),
            InsnType::Throw => Some(RegionExit::Throw(
                insn.get_arg(0)
                    .cloned()
                    .ok_or(RegionInvariantError::MissingExitValue(block))?,
            )),
            _ => None,
        })
    }

    fn terminal_continuation(
        &self,
        source: BlockId,
        target: BlockId,
    ) -> Result<Option<RegionExit>, RegionInvariantError> {
        TerminalContinuation::new(
            self.cfg,
            self.tree,
            self.elisions.candidates(),
            &self.terminal_facts,
        )
        .analyze(source, target)
    }
}

#[derive(Debug, Clone, Copy)]
struct ControlExit {
    kind: RegionExitKind,
    target: RegionId,
}

struct TerminalContinuationFacts {
    phi_predecessors: BTreeSet<BlockId>,
}

impl TerminalContinuationFacts {
    fn analyze(cfg: &CFG) -> Self {
        let phi_predecessors = cfg
            .blocks
            .values()
            .flat_map(|block| &block.insns)
            .filter(|instruction| instruction.insn_type == InsnType::Phi)
            .flat_map(|instruction| {
                instruction
                    .payload
                    .phi_edges
                    .iter()
                    .map(|(predecessor, _)| *predecessor)
            })
            .collect();
        Self { phi_predecessors }
    }

    fn preserves(&self, block: BlockId) -> bool {
        self.phi_predecessors.contains(&block)
    }
}

struct TerminalContinuation<'a> {
    cfg: &'a CFG,
    tree: &'a RegionTree,
    elided: &'a BTreeSet<StatementOrigin>,
    facts: &'a TerminalContinuationFacts,
}

impl<'a> TerminalContinuation<'a> {
    fn new(
        cfg: &'a CFG,
        tree: &'a RegionTree,
        elided: &'a BTreeSet<StatementOrigin>,
        facts: &'a TerminalContinuationFacts,
    ) -> Self {
        Self {
            cfg,
            tree,
            elided,
            facts,
        }
    }

    fn analyze(
        &self,
        _source: BlockId,
        target: BlockId,
    ) -> Result<Option<RegionExit>, RegionInvariantError> {
        let scope = self.tree.owner(target)?;
        let mut current = target;
        let mut visited = BTreeSet::new();
        while visited.insert(current) {
            if self.facts.preserves(current)
                || self.tree.owner(current)? != scope
                || self
                    .cfg
                    .incoming_edges(current)
                    .iter()
                    .any(|(_, kind)| kind.is_exception())
            {
                return Ok(None);
            }
            let block = self
                .cfg
                .block(current)
                .ok_or(RegionInvariantError::MissingBlock(current))?;
            if block.synthetic {
                return Ok(None);
            }
            if let Some(terminal) = block.terminator() {
                if terminal.insn_type == InsnType::Return {
                    if self.transparent_prefix(current, block, Some(terminal.id)) {
                        return Ok(Some(RegionExit::Return(terminal.get_arg(0).cloned())));
                    }
                    return Ok(
                        TerminalValueSlice::new(self.elided).resolve(current, block, terminal)
                    );
                }
                let terminal_is_transparent = terminal.insn_type == InsnType::Goto
                    || InstructionEffects::is_ssa_bookkeeping(terminal)
                    || self.elided.contains(&StatementOrigin {
                        block: current,
                        instruction: terminal.id,
                    });
                if !terminal_is_transparent {
                    return Ok(None);
                }
            }
            if !self.transparent_prefix(current, block, None)
                || self
                    .cfg
                    .successors_with_kind(current)
                    .iter()
                    .any(|(_, kind)| kind.is_exception())
            {
                return Ok(None);
            }
            let successors = self.cfg.normal_successors(current).collect::<Vec<_>>();
            let [successor] = successors.as_slice() else {
                return Ok(None);
            };
            current = *successor;
        }
        Ok(None)
    }

    fn transparent_prefix(
        &self,
        block: BlockId,
        body: &crate::ir::Block,
        terminal: Option<crate::ir::InstructionId>,
    ) -> bool {
        body.insns
            .iter()
            .take_while(|instruction| terminal != Some(instruction.id))
            .all(|instruction| {
                InstructionEffects::is_ssa_bookkeeping(instruction)
                    || self.elided.contains(&StatementOrigin {
                        block,
                        instruction: instruction.id,
                    })
            })
    }
}

struct TerminalValueSlice<'a> {
    elided: &'a BTreeSet<StatementOrigin>,
    replacements: BTreeMap<SsaVar, InsnArg>,
}

impl<'a> TerminalValueSlice<'a> {
    fn new(elided: &'a BTreeSet<StatementOrigin>) -> Self {
        Self {
            elided,
            replacements: BTreeMap::new(),
        }
    }

    fn resolve(
        mut self,
        block_id: BlockId,
        block: &crate::ir::Block,
        terminal: &crate::ir::InsnNode,
    ) -> Option<RegionExit> {
        for instruction in block
            .insns
            .iter()
            .take_while(|instruction| instruction.id != terminal.id)
        {
            if self.elided.contains(&StatementOrigin {
                block: block_id,
                instruction: instruction.id,
            }) || instruction.insn_type == InsnType::Nop
            {
                continue;
            }
            if instruction.insn_type == InsnType::Phi {
                continue;
            }
            if !InstructionEffects::of_tree(instruction).is_pure() {
                return None;
            }
            let result = instruction.result.as_ref().and_then(SsaVar::from_reg)?;
            let replacement = if instruction.insn_type == InsnType::Move {
                self.substitute(instruction.get_arg(0)?.clone())?
            } else {
                let expression = InstructionTree::transform(
                    instruction.clone(),
                    &mut LocalValueSubstitution {
                        replacements: &self.replacements,
                    },
                )
                .ok()?;
                InsnArg::wrap(expression)
            };
            self.replacements.insert(result, replacement);
        }
        let value = match terminal.get_arg(0).cloned() {
            Some(value) => Some(self.substitute(value)?),
            None => None,
        };
        Some(RegionExit::Return(value))
    }

    fn substitute(&self, value: InsnArg) -> Option<InsnArg> {
        InstructionTree::transform_arg(
            value,
            &mut LocalValueSubstitution {
                replacements: &self.replacements,
            },
        )
        .ok()
    }
}

struct LocalValueSubstitution<'a> {
    replacements: &'a BTreeMap<SsaVar, InsnArg>,
}

impl InstructionTransform for LocalValueSubstitution<'_> {
    fn transform_register(&mut self, register: RegisterArg) -> InsnArg {
        SsaVar::from_reg(&register)
            .and_then(|key| self.replacements.get(&key))
            .cloned()
            .unwrap_or(InsnArg::Reg(register))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{ArgType, Block, CatchRegion, InsnArg, InsnNode, RegisterArg};

    #[test]
    fn cleanup_forwarding_to_enclosing_finally_is_a_rethrow() {
        let (leaves, exception, handler) = cleanup_forwarding_leaves(true);
        let forwarded = forwarded_cleanup_leave(&leaves);
        assert!(matches!(
            &forwarded.leave.exit,
            RegionExit::Throw(InsnArg::Reg(value)) if value == &exception
        ));
        assert_eq!(forwarded.cleanup_regions, vec![handler]);
    }

    #[test]
    fn cleanup_forwarding_to_enclosing_cleanup_is_a_rethrow() {
        let (leaves, exception, _) = cleanup_forwarding_leaves(false);
        let forwarded = forwarded_cleanup_leave(&leaves);
        assert!(matches!(
            &forwarded.leave.exit,
            RegionExit::Throw(InsnArg::Reg(value)) if value == &exception
        ));
        assert!(forwarded.cleanup_regions.is_empty());
    }

    fn cleanup_forwarding_leaves(
        source_level_finally: bool,
    ) -> (Vec<ResolvedRegionExit>, RegisterArg, RegionId) {
        let source = BlockId::new(0);
        let finally_entry = BlockId::new(1);
        let exception = RegisterArg::new_ssa(0, 0, ArgType::throwable());

        let mut cfg = CFG::new("forwarded_cleanup_throw");
        let mut adapter = Block::new(source.raw());
        adapter.push(InsnNode::goto(1));
        cfg.add_block(adapter);
        let mut cleanup_body = Block::new(finally_entry.raw());
        cleanup_body.push(InsnNode::throw(InsnArg::Reg(exception.clone())));
        cfg.add_block(cleanup_body);
        cfg.add_edge(source, finally_entry, EdgeKind::Normal);

        let mut tree = RegionTree::new(Some(source));
        tree.cover_method(&cfg).unwrap();
        let root = tree.root();
        let outer = tree.add_child(root, RegionKind::Try, Some(source)).unwrap();
        let inner = tree
            .add_child(outer, RegionKind::Try, Some(source))
            .unwrap();
        let adapter_region = tree
            .add_child(
                inner,
                RegionKind::Cleanup(CatchRegion {
                    exception_types: vec![ArgType::throwable()],
                    exception_value: Some(exception.clone()),
                    continuation: None,
                }),
                Some(source),
            )
            .unwrap();
        let destination_kind = if source_level_finally {
            RegionKind::Finally
        } else {
            RegionKind::Cleanup(CatchRegion {
                exception_types: vec![ArgType::throwable()],
                exception_value: Some(exception.clone()),
                continuation: None,
            })
        };
        let finally_region = tree
            .add_child(root, destination_kind, Some(finally_entry))
            .unwrap();
        for region in [outer, inner, adapter_region] {
            tree.add_block(region, source).unwrap();
        }
        tree.add_block(finally_region, finally_entry).unwrap();

        let handlers =
            BTreeMap::from([(outer, vec![finally_region]), (inner, vec![adapter_region])]);
        let control_flow = ControlFlowFacts::analyze(&cfg).unwrap();
        let elisions = InstructionElisions::default();
        let contractions = BTreeMap::new();
        let leaves = RegionExitAnalysis::new(
            &cfg,
            &tree,
            &elisions,
            &control_flow,
            &contractions,
            &handlers,
        )
        .analyze()
        .unwrap()
        .leaves;

        (leaves, exception, finally_region)
    }

    fn forwarded_cleanup_leave(leaves: &[ResolvedRegionExit]) -> &ResolvedRegionExit {
        leaves
            .iter()
            .find(|leave| leave.leave.source_block == Some(BlockId::new(0)))
            .expect("cleanup adapter leave")
    }

    #[test]
    fn resolves_a_synthetic_control_edge_to_its_logical_destination() {
        let mut cfg = CFG::new("control_continuation");
        cfg.add_block(Block::new(0u32));
        let mut edge = Block::synthetic(1u32);
        edge.push(InsnNode::goto(2));
        cfg.add_block(edge);
        cfg.add_block(Block::new(2u32));
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(1), BlockId::new(2), EdgeKind::Normal);

        let facts = ControlFlowFacts::analyze(&cfg).unwrap();

        assert_eq!(facts.continuation(BlockId::new(1)), BlockId::new(2));
    }

    #[test]
    fn preserves_a_synthetic_phi_copy_anchor() {
        let mut cfg = CFG::new("control_phi_anchor");
        cfg.add_block(Block::new(0u32));
        let mut edge = Block::synthetic(1u32);
        edge.push(InsnNode::goto(2));
        cfg.add_block(edge);
        let mut join = Block::new(2u32);
        join.push(InsnNode::phi(
            RegisterArg::new_ssa(0, 1, ArgType::INT),
            vec![(1, InsnArg::reg_ssa(0, 0, ArgType::INT))],
        ));
        cfg.add_block(join);
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(1), BlockId::new(2), EdgeKind::Normal);

        let facts = ControlFlowFacts::analyze(&cfg).unwrap();

        assert_eq!(facts.continuation(BlockId::new(1)), BlockId::new(1));
    }

    #[test]
    fn keeps_a_terminal_exception_entry_as_a_lexical_continuation() {
        let mut cfg = CFG::new("shared_terminal");
        let mut source = Block::new(0u32);
        source.push(InsnNode::goto(1));
        let mut target = Block::new(1u32);
        let mut return_value = InsnNode::new(InsnType::Return, 1);
        return_value.add_arg(InsnArg::reg_ssa(0, 0, ArgType::INT));
        target.push(return_value);
        cfg.add_block(source);
        cfg.add_block(target);
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Exception);

        let mut tree = RegionTree::new(Some(cfg.entry));
        tree.cover_method(&cfg).unwrap();
        let elided = BTreeSet::new();
        let facts = TerminalContinuationFacts::analyze(&cfg);
        let continuation = TerminalContinuation::new(&cfg, &tree, &elided, &facts)
            .analyze(BlockId::new(0), BlockId::new(1))
            .unwrap();

        assert!(continuation.is_none());
    }

    #[test]
    fn follows_an_acyclic_transparent_path_to_a_return() {
        let mut cfg = CFG::new("transparent_terminal");
        let mut source = Block::new(0u32);
        source.push(InsnNode::goto(1));
        let mut middle = Block::new(1u32);
        middle.push(InsnNode::goto(2));
        let mut target = Block::new(2u32);
        let mut return_value = InsnNode::new(InsnType::Return, 2);
        return_value.add_arg(InsnArg::reg_ssa(0, 0, ArgType::INT));
        target.push(return_value);
        cfg.add_block(source);
        cfg.add_block(middle);
        cfg.add_block(target);
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(1), BlockId::new(2), EdgeKind::Normal);

        let mut tree = RegionTree::new(Some(cfg.entry));
        tree.cover_method(&cfg).unwrap();
        let facts = TerminalContinuationFacts::analyze(&cfg);
        let continuation = TerminalContinuation::new(&cfg, &tree, &BTreeSet::new(), &facts)
            .analyze(BlockId::new(0), BlockId::new(1))
            .unwrap();

        assert!(matches!(continuation, Some(RegionExit::Return(Some(_)))));

        let facts = TerminalContinuationFacts {
            phi_predecessors: BTreeSet::from([BlockId::new(1)]),
        };
        let continuation = TerminalContinuation::new(&cfg, &tree, &BTreeSet::new(), &facts)
            .analyze(BlockId::new(0), BlockId::new(1))
            .unwrap();
        assert!(continuation.is_none());
    }

    #[test]
    fn slices_a_pure_terminal_definition_into_the_return_value() {
        let mut cfg = CFG::new("terminal_value_slice");
        let mut source = Block::new(0u32);
        source.push(InsnNode::goto(1));
        let mut target = Block::new(1u32);
        let mut definition =
            InsnNode::const_val(RegisterArg::new_ssa(0, 0, ArgType::INT), 1, ArgType::INT);
        definition.id = crate::ir::InstructionId::new(0);
        target.push(definition);
        let mut return_value = InsnNode::new(InsnType::Return, 1);
        return_value.id = crate::ir::InstructionId::new(1);
        return_value.add_arg(InsnArg::reg_ssa(0, 0, ArgType::INT));
        target.push(return_value);
        cfg.add_block(source);
        cfg.add_block(target);
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);

        let mut tree = RegionTree::new(Some(cfg.entry));
        tree.cover_method(&cfg).unwrap();
        let facts = TerminalContinuationFacts::analyze(&cfg);
        let continuation = TerminalContinuation::new(&cfg, &tree, &BTreeSet::new(), &facts)
            .analyze(BlockId::new(0), BlockId::new(1))
            .unwrap();

        assert!(matches!(
            continuation,
            Some(RegionExit::Return(Some(InsnArg::Wrapped(_))))
        ));
    }
}
