//! Equivalence proof for duplicated normal and exceptional cleanup bodies.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::ir::analysis::{
    DominatorTree, InstructionEffects, SsaClasses, SsaOrigins, SsaUseSite, SsaValueGraph, SsaVar,
};
use crate::ir::{
    BlockId, EdgeKind, IfOp, InsnArg, InsnNode, InsnType, InstructionEquivalence, InvokeType,
    StatementOrigin, CFG,
};

use super::{CleanupContraction, HandlerKind, TryRegion};

#[derive(Default)]
pub(super) struct CleanupRecoveryResult {
    pub(super) elided: BTreeSet<StatementOrigin>,
    pub(super) contractions: Vec<CleanupContraction>,
    pub(super) normal_contractions: Vec<CleanupContraction>,
    pub(super) value_bindings: BTreeSet<(SsaVar, SsaVar)>,
    pub(super) diagnostics: Vec<CleanupProofDiagnostic>,
}

#[derive(Debug, Clone)]
pub struct CleanupProofDiagnostic {
    pub region: u32,
    pub handler: u32,
    pub normal_entry: BlockId,
    pub candidate: BlockId,
    pub outcome: CleanupProofOutcome,
    pub mismatch: Option<CleanupMismatchDiagnostic>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CleanupProofOutcome {
    RootMismatch,
    FlowMismatch,
    Incomplete,
    NotIsolated,
    MissingEvidence,
    MissingCompletion,
    Proven,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CleanupMismatchDiagnostic {
    pub handler_block: BlockId,
    pub handler_index: usize,
    pub normal_block: BlockId,
    pub normal_index: usize,
    pub reason: CleanupMismatchReason,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CleanupMismatchReason {
    HandlerDomain,
    BlockCorrespondence,
    ExceptionalFlow,
    Instruction,
    HandlerAdvance,
    NormalAdvance,
    BranchFlow,
    TerminalFlow,
    PhiFlow,
}

pub(super) struct CleanupRecovery<'a> {
    cfg: &'a CFG,
    values: &'a SsaValueGraph,
    normal_dominators: &'a DominatorTree,
}

impl<'a> CleanupRecovery<'a> {
    pub(super) fn new(
        cfg: &'a CFG,
        values: &'a SsaValueGraph,
        normal_dominators: &'a DominatorTree,
    ) -> Self {
        Self {
            cfg,
            values,
            normal_dominators,
        }
    }

    pub(super) fn recover(
        &self,
        region: &mut TryRegion,
        nested_cleanup_blocks: &BTreeSet<BlockId>,
        nested_handler_blocks: &BTreeSet<BlockId>,
        cleanup_representatives: &BTreeMap<BlockId, BlockId>,
    ) -> Result<CleanupRecoveryResult, super::ExceptionInvariantError> {
        let catch_domains = region
            .handlers
            .iter()
            .filter(|handler| handler.kind == HandlerKind::Catch)
            .map(NormalFlowDomain::of_handler)
            .collect::<Vec<_>>();
        let handler_blocks = region
            .handlers
            .iter()
            .flat_map(|handler| {
                handler
                    .blocks
                    .iter()
                    .chain(&handler.adapter_blocks)
                    .chain(&handler.entry_blocks)
                    .copied()
            })
            .collect::<BTreeSet<_>>();
        let exits = region
            .normal_exit_blocks
            .iter()
            .copied()
            .filter(|source| {
                !handler_blocks.contains(source) && !nested_cleanup_blocks.contains(source)
            })
            .filter(|source| !cleanup_representatives.contains_key(source))
            .flat_map(|source| self.cfg.normal_successors(source))
            .filter(|target| {
                let semantic = Self::semantic_target(self.cfg, *target);
                !nested_handler_blocks.contains(target)
                    && !nested_handler_blocks.contains(&semantic)
            })
            .filter_map(|target| {
                let target = Self::semantic_target(self.cfg, target);
                let representative = Self::representative(target, cleanup_representatives);
                (representative == target).then_some(target)
            })
            .filter(|target| !region.blocks.contains(target))
            .collect::<BTreeSet<_>>();
        if exits.is_empty() {
            return Ok(CleanupRecoveryResult::default());
        }

        let mut result = CleanupRecoveryResult::default();
        let origins = SsaOrigins::analyze(self.values);
        let mut unresolved = BTreeSet::new();
        let mut recovered_finally = false;
        for handler in &mut region.handlers {
            if handler.kind != HandlerKind::Cleanup {
                continue;
            }
            let isolation_ingress = region
                .normal_exit_blocks
                .iter()
                .copied()
                .chain(handler.entry_blocks.iter().copied())
                .chain(handler.adapter_blocks.iter().copied())
                .collect::<BTreeSet<_>>();
            let owned =
                CleanupDomain::analyze(self.cfg, handler.semantic_entry, &handler.rethrow_blocks);
            let mut copies = BTreeSet::new();
            let mut copy_blocks = BTreeSet::new();
            let mut contractions = Vec::new();
            let mut value_bindings = BTreeSet::new();
            let mut proven = true;
            for normal_entry in exits.iter().copied() {
                let mut matched = None;
                for candidate in NormalCleanupCandidates::new(self.cfg, normal_entry).entries() {
                    let semantic_entry = CleanupSpecialization::new(
                        self.cfg,
                        self.values,
                        self.normal_dominators,
                        &handler.rethrow_blocks,
                    )
                    .entry(handler.semantic_entry, candidate);
                    if !CleanupRootFilter::new(self.cfg, &handler.rethrow_blocks)
                        .accepts(semantic_entry, candidate)
                    {
                        result.diagnostics.push(CleanupProofDiagnostic {
                            region: region.id,
                            handler: handler.id,
                            normal_entry,
                            candidate,
                            outcome: CleanupProofOutcome::RootMismatch,
                            mismatch: None,
                        });
                        continue;
                    }
                    let mut proof = CleanupProof::new(
                        self.cfg,
                        self.values,
                        &origins,
                        &owned,
                        &handler.rethrow_blocks,
                    );
                    let equivalent = proof.compare(semantic_entry, candidate)?;
                    let blocks = proof.contracted_normal_blocks(candidate);
                    let complete = proof.fully_contracts_normal_cleanup(&blocks);
                    let isolated = equivalent
                        && complete
                        && CleanupCopyIsolation::new(self.cfg).proves(
                            normal_entry,
                            candidate,
                            &blocks,
                            &isolation_ingress,
                        );
                    let completion = proof.normal_completion();
                    let evidence = proof.has_semantic_evidence();
                    let outcome = if !equivalent {
                        CleanupProofOutcome::FlowMismatch
                    } else if !complete {
                        CleanupProofOutcome::Incomplete
                    } else if !isolated {
                        CleanupProofOutcome::NotIsolated
                    } else if !evidence {
                        CleanupProofOutcome::MissingEvidence
                    } else if completion.is_none() {
                        CleanupProofOutcome::MissingCompletion
                    } else {
                        CleanupProofOutcome::Proven
                    };
                    result.diagnostics.push(CleanupProofDiagnostic {
                        region: region.id,
                        handler: handler.id,
                        normal_entry,
                        candidate,
                        outcome,
                        mismatch: proof.mismatch(),
                    });
                    if let (true, true, true, Some(completion)) =
                        (equivalent, isolated, evidence, completion)
                    {
                        let (completion, corridor) =
                            Self::semantic_target_with_corridor(self.cfg, completion);
                        let mut contraction_blocks = blocks.clone();
                        contraction_blocks.extend(corridor);
                        let value_bindings = proof.value_bindings();
                        matched = Some((
                            proof.matched_normal,
                            blocks.clone(),
                            value_bindings,
                            CleanupContraction {
                                entry: candidate,
                                blocks: contraction_blocks,
                                completion,
                            },
                        ));
                        break;
                    }
                }
                if let Some((instructions, blocks, bindings, contraction)) = matched {
                    copies.extend(instructions);
                    copy_blocks.extend(blocks);
                    value_bindings.extend(bindings);
                    contractions.push(contraction);
                } else {
                    proven = false;
                    break;
                }
            }
            if !proven {
                unresolved.insert(handler.id);
                continue;
            }
            handler.semantic_entry = handler.canonical_entry;
            let Some(catch_copies) = CatchCleanupRecovery::new(
                self.cfg,
                self.values,
                &origins,
                handler.semantic_entry,
                &owned,
                &handler.rethrow_blocks,
                self.normal_dominators,
            )
            .recover(&catch_domains)?
            else {
                unresolved.insert(handler.id);
                continue;
            };
            copies.extend(catch_copies.instructions);
            copy_blocks.extend(catch_copies.blocks);
            value_bindings.extend(catch_copies.value_bindings);
            contractions.extend(catch_copies.contractions);
            CleanupContractionClosure::new(self.cfg).expand(&mut contractions);
            handler.kind = HandlerKind::Finally;
            recovered_finally = true;
            copies.extend(DeadCleanupState::analyze(
                self.cfg,
                self.values,
                &copy_blocks,
                &copies,
            ));
            result.elided.extend(copies);
            result.value_bindings.extend(value_bindings);
            result
                .normal_contractions
                .extend(contractions.iter().cloned());
            result.contractions.extend(contractions);
            result
                .elided
                .extend(handler.rethrow_blocks.iter().filter_map(|block| {
                    let body = self.cfg.block(*block)?;
                    let instruction = body
                        .insns
                        .iter()
                        .rev()
                        .find(|insn| insn.insn_type == InsnType::Throw)?;
                    Some(StatementOrigin {
                        block: *block,
                        instruction: instruction.id,
                    })
                }));
        }
        if recovered_finally {
            for handler in &mut region.handlers {
                if unresolved.contains(&handler.id) {
                    Self::recover_catch_all(handler);
                }
            }
        }
        Ok(result)
    }

    fn recover_catch_all(handler: &mut super::CatchHandler) {
        handler.kind = HandlerKind::Catch;
        handler.catch_type = Some(crate::ir::ArgType::object("java/lang/Throwable"));
    }

    fn representative(mut block: BlockId, representatives: &BTreeMap<BlockId, BlockId>) -> BlockId {
        let mut visited = BTreeSet::new();
        while visited.insert(block) {
            let Some(representative) = representatives.get(&block).copied() else {
                break;
            };
            block = representative;
        }
        block
    }

    fn semantic_target(cfg: &CFG, block: BlockId) -> BlockId {
        Self::semantic_target_with_corridor(cfg, block).0
    }

    fn semantic_target_with_corridor(
        cfg: &CFG,
        mut block: BlockId,
    ) -> (BlockId, BTreeSet<BlockId>) {
        let mut visited = BTreeSet::new();
        let mut corridor = BTreeSet::new();
        while visited.insert(block) {
            let Some(body) = cfg.block(block) else {
                break;
            };
            if !body.insns.iter().all(|instruction| {
                matches!(
                    instruction.insn_type,
                    InsnType::Nop | InsnType::Phi | InsnType::Goto
                )
            }) || cfg
                .successors_with_kind(block)
                .iter()
                .any(|(_, kind)| kind.is_exception())
            {
                break;
            }
            let successors = cfg.normal_successors(block).collect::<Vec<_>>();
            let [successor] = successors.as_slice() else {
                break;
            };
            corridor.insert(block);
            block = *successor;
        }
        (block, corridor)
    }
}

/// Closes a proven cleanup quotient over private epsilon adapters.
///
/// DEX exception tables commonly route a duplicated cleanup operation through
/// an empty catch block before rejoining its normal completion. Such a block
/// has no source-level statement, but leaving it outside the quotient creates
/// a false entry into the enclosing region. The closure is intentionally
/// graph-based: a block is absorbed only when all of its incoming control is
/// already owned by the same cleanup component and it cannot escape or throw.
struct CleanupContractionClosure<'a> {
    cfg: &'a CFG,
}

impl<'a> CleanupContractionClosure<'a> {
    fn new(cfg: &'a CFG) -> Self {
        Self { cfg }
    }

    fn expand(&self, contractions: &mut [CleanupContraction]) {
        let completions = contractions
            .iter()
            .map(|contraction| contraction.completion)
            .collect::<BTreeSet<_>>();
        for completion in completions {
            let indices = contractions
                .iter()
                .enumerate()
                .filter_map(|(index, contraction)| {
                    (contraction.completion == completion).then_some(index)
                })
                .collect::<Vec<_>>();
            let mut component = indices
                .iter()
                .flat_map(|index| contractions[*index].blocks.iter().copied())
                .collect::<BTreeSet<_>>();
            let original = component.clone();
            loop {
                let additions = self
                    .cfg
                    .block_ids()
                    .into_iter()
                    .filter(|block| *block != completion && !component.contains(block))
                    .filter(|block| self.is_exclusive_epsilon(*block, completion, &component))
                    .collect::<Vec<_>>();
                if additions.is_empty() {
                    break;
                }
                component.extend(additions);
            }
            let additions = component
                .difference(&original)
                .copied()
                .collect::<BTreeSet<_>>();
            if let Some(index) = indices.first().copied() {
                contractions[index].blocks.extend(additions);
            }
        }
    }

    fn is_exclusive_epsilon(
        &self,
        block: BlockId,
        completion: BlockId,
        component: &BTreeSet<BlockId>,
    ) -> bool {
        let Some(body) = self.cfg.block(block) else {
            return false;
        };
        if !body.insns.iter().all(|instruction| {
            matches!(
                instruction.insn_type,
                InsnType::Nop | InsnType::Phi | InsnType::Goto | InsnType::MoveException
            )
        }) {
            return false;
        }
        let incoming = self.cfg.incoming_edges(block);
        if incoming.is_empty()
            || incoming
                .iter()
                .any(|(source, _)| !component.contains(source))
        {
            return false;
        }
        let successors = self.cfg.successors_with_kind(block);
        let normal = successors
            .iter()
            .filter(|(_, kind)| !kind.is_exception())
            .map(|(target, _)| *target)
            .collect::<BTreeSet<_>>();
        !normal.is_empty()
            && successors.iter().all(|(_, kind)| !kind.is_exception())
            && normal
                .iter()
                .all(|target| *target == completion || component.contains(target))
    }
}

struct CleanupCopyIsolation<'a> {
    cfg: &'a CFG,
    predecessors: BTreeMap<BlockId, Vec<BlockId>>,
    normal_predecessors: BTreeMap<BlockId, Vec<BlockId>>,
}

impl<'a> CleanupCopyIsolation<'a> {
    fn new(cfg: &'a CFG) -> Self {
        Self {
            cfg,
            predecessors: cfg.predecessor_snapshot(),
            normal_predecessors: cfg.normal_predecessor_snapshot(),
        }
    }

    fn proves(
        &self,
        entry: BlockId,
        candidate: BlockId,
        copies: &BTreeSet<BlockId>,
        ingress: &BTreeSet<BlockId>,
    ) -> bool {
        let forward = self.transparent_reach(entry, candidate);
        if !forward.contains(&candidate) {
            return false;
        }
        let mut owned = copies.clone();
        owned.extend(self.reverse_corridor(candidate, &forward));
        self.proves_ingress_corridor(&mut owned, ingress)
    }

    /// Extends an equivalent cleanup body through compiler-inserted edge
    /// blocks and proves that the resulting corridor is isolated.
    ///
    /// SSA destruction and critical-edge splitting may place pure move/goto
    /// blocks between a protected exit and its duplicated cleanup. Requiring a
    /// direct ingress predecessor rejects those graphs even though the bridge
    /// has no independent semantics. The proof below accepts an arbitrary
    /// transparent corridor only when every reverse root is an approved
    /// ingress, every forward edge remains inside the corridor, and all
    /// corridor blocks are reachable from an ingress.
    fn proves_ingress_corridor(
        &self,
        owned: &mut BTreeSet<BlockId>,
        ingress: &BTreeSet<BlockId>,
    ) -> bool {
        let body = owned.clone();
        let mut pending = owned.iter().copied().collect::<Vec<_>>();
        while let Some(block) = pending.pop() {
            for predecessor in self.predecessors.get(&block).into_iter().flatten().copied() {
                if owned.contains(&predecessor) || ingress.contains(&predecessor) {
                    continue;
                }
                if !NormalCleanupCandidates::new(self.cfg, predecessor).transparent(predecessor) {
                    return false;
                }
                owned.insert(predecessor);
                pending.push(predecessor);
            }
        }
        let bridges = owned.difference(&body).copied().collect::<BTreeSet<_>>();
        if bridges.iter().any(|block| {
            let successors = self
                .cfg
                .successors_with_kind(*block)
                .iter()
                .map(|(successor, _)| *successor)
                .collect::<Vec<_>>();
            successors.is_empty()
                || successors
                    .iter()
                    .any(|successor| !owned.contains(successor))
        }) {
            return false;
        }
        let mut reached = owned
            .intersection(ingress)
            .copied()
            .collect::<BTreeSet<_>>();
        let mut pending = ingress.iter().copied().collect::<Vec<_>>();
        while let Some(block) = pending.pop() {
            for (successor, _) in self.cfg.successors_with_kind(block) {
                if owned.contains(successor) && reached.insert(*successor) {
                    pending.push(*successor);
                }
            }
        }
        owned.iter().all(|block| reached.contains(block))
    }

    fn transparent_reach(&self, entry: BlockId, candidate: BlockId) -> BTreeSet<BlockId> {
        let mut reached = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if !reached.insert(block) || block == candidate {
                continue;
            }
            if !NormalCleanupCandidates::new(self.cfg, entry).transparent(block) {
                continue;
            }
            pending.extend(self.cfg.normal_successors(block));
        }
        reached
    }

    fn reverse_corridor(
        &self,
        candidate: BlockId,
        forward: &BTreeSet<BlockId>,
    ) -> BTreeSet<BlockId> {
        let mut corridor = BTreeSet::new();
        let mut pending = vec![candidate];
        while let Some(block) = pending.pop() {
            if !forward.contains(&block) || !corridor.insert(block) {
                continue;
            }
            pending.extend(
                self.normal_predecessors
                    .get(&block)
                    .into_iter()
                    .flatten()
                    .copied(),
            );
        }
        corridor
    }
}

#[derive(Clone)]
struct NormalFlowDomain {
    entry: BlockId,
    blocks: BTreeSet<BlockId>,
}

impl NormalFlowDomain {
    fn of_handler(handler: &super::CatchHandler) -> Self {
        let mut blocks = handler
            .blocks
            .iter()
            .chain(&handler.lexical_blocks)
            .copied()
            .collect::<BTreeSet<_>>();
        blocks.insert(handler.semantic_entry);
        Self {
            entry: handler.semantic_entry,
            blocks,
        }
    }
}

#[derive(Default)]
struct RecoveredCleanupCopies {
    instructions: BTreeSet<StatementOrigin>,
    blocks: BTreeSet<BlockId>,
    contractions: Vec<CleanupContraction>,
    value_bindings: BTreeSet<(SsaVar, SsaVar)>,
}

/// Proves the normal cleanup copies emitted at ordinary exits from catch
/// clauses belonging to the same protected scope.
struct CatchCleanupRecovery<'a> {
    cfg: &'a CFG,
    values: &'a SsaValueGraph,
    origins: &'a SsaOrigins,
    handler_entry: BlockId,
    handler_blocks: &'a BTreeSet<BlockId>,
    rethrow_blocks: &'a BTreeSet<BlockId>,
    normal_dominators: &'a DominatorTree,
}

impl<'a> CatchCleanupRecovery<'a> {
    fn new(
        cfg: &'a CFG,
        values: &'a SsaValueGraph,
        origins: &'a SsaOrigins,
        handler_entry: BlockId,
        handler_blocks: &'a BTreeSet<BlockId>,
        rethrow_blocks: &'a BTreeSet<BlockId>,
        normal_dominators: &'a DominatorTree,
    ) -> Self {
        Self {
            cfg,
            values,
            origins,
            handler_entry,
            handler_blocks,
            rethrow_blocks,
            normal_dominators,
        }
    }

    fn recover(
        &self,
        domains: &[NormalFlowDomain],
    ) -> Result<Option<RecoveredCleanupCopies>, super::ExceptionInvariantError> {
        let mut recovered = RecoveredCleanupCopies::default();
        for domain in domains {
            let mut proofs = BTreeMap::new();
            for candidate in &domain.blocks {
                let specialized = CleanupSpecialization::new(
                    self.cfg,
                    self.values,
                    self.normal_dominators,
                    self.rethrow_blocks,
                )
                .entry(self.handler_entry, *candidate);
                if !CleanupRootFilter::new(self.cfg, self.rethrow_blocks)
                    .accepts(specialized, *candidate)
                {
                    continue;
                }
                let mut proof = CleanupProof::new(
                    self.cfg,
                    self.values,
                    self.origins,
                    self.handler_blocks,
                    self.rethrow_blocks,
                );
                let equivalent = proof.compare(specialized, *candidate)?;
                let completion = proof.normal_completion();
                if let (true, Some(completion)) = (equivalent, completion) {
                    let contracted = proof.contracted_normal_blocks(*candidate);
                    let value_bindings = proof.value_bindings();
                    proofs.insert(
                        *candidate,
                        (proof.matched_normal, contracted, value_bindings, completion),
                    );
                }
            }

            let candidates = proofs.keys().copied().collect::<BTreeSet<_>>();
            let selected = candidates
                .iter()
                .copied()
                .filter(|candidate| {
                    !NormalCleanupCoverage::new(self.cfg, &domain.blocks, &candidates)
                        .reached_from_another_candidate(*candidate)
                })
                .collect::<BTreeSet<_>>();
            let covered = NormalCleanupCoverage::new(self.cfg, &domain.blocks, &selected)
                .covers_ordinary_exits(domain.entry);
            if !covered {
                return Ok(None);
            }
            for candidate in selected {
                let Some((instructions, blocks, bindings, completion)) = proofs.remove(&candidate)
                else {
                    continue;
                };
                let (completion, corridor) =
                    CleanupRecovery::semantic_target_with_corridor(self.cfg, completion);
                let mut contraction_blocks = blocks.clone();
                contraction_blocks.extend(corridor);
                recovered.instructions.extend(instructions);
                recovered.blocks.extend(blocks.iter().copied());
                recovered.value_bindings.extend(bindings);
                recovered.contractions.push(CleanupContraction {
                    entry: candidate,
                    blocks: contraction_blocks,
                    completion,
                });
            }
        }
        Ok(Some(recovered))
    }
}

struct NormalCleanupCoverage<'a> {
    cfg: &'a CFG,
    owned: &'a BTreeSet<BlockId>,
    cleanup_entries: &'a BTreeSet<BlockId>,
}

impl<'a> NormalCleanupCoverage<'a> {
    fn new(
        cfg: &'a CFG,
        owned: &'a BTreeSet<BlockId>,
        cleanup_entries: &'a BTreeSet<BlockId>,
    ) -> Self {
        Self {
            cfg,
            owned,
            cleanup_entries,
        }
    }

    fn covers_ordinary_exits(&self, entry: BlockId) -> bool {
        let mut pending = vec![entry];
        let mut visited = BTreeSet::new();
        while let Some(block) = pending.pop() {
            if !self.owned.contains(&block) || !visited.insert(block) {
                continue;
            }
            if self.cleanup_entries.contains(&block) {
                continue;
            }
            let successors = self.cfg.normal_successors(block).collect::<Vec<_>>();
            if successors.is_empty() {
                let throws = self.cfg.block(block).is_some_and(|body| {
                    body.terminator()
                        .is_some_and(|terminal| terminal.insn_type == InsnType::Throw)
                });
                if !throws {
                    return false;
                }
                continue;
            }
            if successors.iter().any(|target| !self.owned.contains(target)) {
                return false;
            }
            pending.extend(successors);
        }
        true
    }

    fn reached_from_another_candidate(&self, target: BlockId) -> bool {
        self.cleanup_entries
            .iter()
            .copied()
            .filter(|source| *source != target)
            .any(|source| self.reaches(source, target))
    }

    fn reaches(&self, source: BlockId, target: BlockId) -> bool {
        let mut pending = self.cfg.normal_successors(source).collect::<Vec<_>>();
        let mut visited = BTreeSet::new();
        while let Some(block) = pending.pop() {
            if !self.owned.contains(&block) || !visited.insert(block) {
                continue;
            }
            if block == target {
                return true;
            }
            pending.extend(self.cfg.normal_successors(block));
        }
        false
    }
}

struct CleanupRootFilter<'a> {
    cfg: &'a CFG,
    rethrow_blocks: &'a BTreeSet<BlockId>,
}

impl<'a> CleanupRootFilter<'a> {
    fn new(cfg: &'a CFG, rethrow_blocks: &'a BTreeSet<BlockId>) -> Self {
        Self {
            cfg,
            rethrow_blocks,
        }
    }

    fn accepts(&self, handler: BlockId, normal: BlockId) -> bool {
        match (
            self.first_observable(handler, true),
            self.first_observable(normal, false),
        ) {
            (Some(handler), Some(normal)) => {
                handler.operation_equivalent(normal)
                    && handler.args.len() == normal.args.len()
                    && handler
                        .args
                        .iter()
                        .zip(&normal.args)
                        .all(|(handler, normal)| Self::argument_shape(handler, normal))
            }
            _ => true,
        }
    }

    fn first_observable(&self, entry: BlockId, exceptional: bool) -> Option<&InsnNode> {
        let mut current = entry;
        let mut visited = BTreeSet::new();
        while visited.insert(current) {
            let block = self.cfg.block(current)?;
            if let Some((_, instruction)) = CleanupProof::body_instructions(
                block,
                exceptional && self.rethrow_blocks.contains(&current),
            )
            .into_iter()
            .next()
            {
                return Some(instruction);
            }
            let edges = CleanupProof::normal_flow_edges(self.cfg, current);
            let [(target, _)] = edges.as_slice() else {
                return None;
            };
            current = *target;
        }
        None
    }

    fn argument_shape(handler: &InsnArg, normal: &InsnArg) -> bool {
        match (handler, normal) {
            (InsnArg::Lit(handler), InsnArg::Lit(normal)) => handler == normal,
            (InsnArg::Reg(_), InsnArg::Reg(_)) => true,
            (InsnArg::Wrapped(handler), InsnArg::Wrapped(normal)) => {
                handler.operation_equivalent(normal)
                    && handler.args.len() == normal.args.len()
                    && handler
                        .args
                        .iter()
                        .zip(&normal.args)
                        .all(|(handler, normal)| Self::argument_shape(handler, normal))
            }
            _ => false,
        }
    }
}

struct DeadCleanupState;

struct CleanupConsumer {
    value: Option<SsaVar>,
    origin: StatementOrigin,
}

impl DeadCleanupState {
    fn analyze(
        cfg: &CFG,
        values: &SsaValueGraph,
        blocks: &BTreeSet<BlockId>,
        elided: &BTreeSet<StatementOrigin>,
    ) -> BTreeSet<StatementOrigin> {
        let definitions =
            blocks
                .iter()
                .filter_map(|block| cfg.block(*block).map(|body| (*block, body)))
                .flat_map(|(block, body)| {
                    body.insns.iter().filter_map(move |instruction| {
                        let removable = InstructionEffects::of_tree(instruction).is_pure()
                            || InstructionEffects::is_ssa_bookkeeping(instruction);
                        removable
                            .then(|| {
                                instruction.result.as_ref().and_then(SsaVar::from_reg).map(
                                    |value| {
                                        (
                                            value,
                                            StatementOrigin {
                                                block,
                                                instruction: instruction.id,
                                            },
                                        )
                                    },
                                )
                            })
                            .flatten()
                    })
                })
                .collect::<BTreeMap<_, _>>();

        let mut dependencies = BTreeMap::<SsaVar, BTreeSet<SsaVar>>::new();
        let mut live = BTreeSet::new();
        for value in definitions.keys().copied() {
            let Some(fact) = values.value(value) else {
                live.insert(value);
                continue;
            };
            for usage in &fact.uses {
                let Some(consumer) = Self::consumer(cfg, values, value, *usage) else {
                    live.insert(value);
                    continue;
                };
                if elided.contains(&consumer.origin) {
                    continue;
                }
                if let Some(consumer) = consumer
                    .value
                    .filter(|consumer| definitions.contains_key(consumer))
                {
                    dependencies.entry(consumer).or_default().insert(value);
                } else {
                    live.insert(value);
                }
            }
        }

        let mut pending = live.iter().copied().collect::<Vec<_>>();
        while let Some(consumer) = pending.pop() {
            for producer in dependencies.get(&consumer).into_iter().flatten().copied() {
                if live.insert(producer) {
                    pending.push(producer);
                }
            }
        }
        definitions
            .into_iter()
            .filter_map(|(value, origin)| (!live.contains(&value)).then_some(origin))
            .collect()
    }

    fn consumer(
        cfg: &CFG,
        values: &SsaValueGraph,
        value: SsaVar,
        usage: crate::ir::analysis::UsePosition,
    ) -> Option<CleanupConsumer> {
        match values.use_site(cfg, value, usage)? {
            crate::ir::analysis::SsaUseSite::Instruction(instruction) => Some(CleanupConsumer {
                value: instruction.result.as_ref().and_then(SsaVar::from_reg),
                origin: StatementOrigin {
                    block: usage.instruction.block,
                    instruction: instruction.id,
                },
            }),
            crate::ir::analysis::SsaUseSite::Phi(phi) => {
                let instruction = cfg
                    .block(phi.block)?
                    .insns
                    .iter()
                    .find(|instruction| instruction.id == phi.instruction)?;
                Some(CleanupConsumer {
                    value: Some(phi.result),
                    origin: StatementOrigin {
                        block: phi.block,
                        instruction: instruction.id,
                    },
                })
            }
        }
    }
}

struct CleanupDomain;

impl CleanupDomain {
    fn analyze(cfg: &CFG, entry: BlockId, rethrows: &BTreeSet<BlockId>) -> BTreeSet<BlockId> {
        let mut blocks = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if !blocks.insert(block) || rethrows.contains(&block) {
                continue;
            }
            pending.extend(
                cfg.successors_with_kind(block)
                    .iter()
                    .map(|(target, _)| *target),
            );
        }
        blocks
    }
}

struct NormalCleanupCandidates<'a> {
    cfg: &'a CFG,
    entry: BlockId,
}

impl<'a> NormalCleanupCandidates<'a> {
    fn new(cfg: &'a CFG, entry: BlockId) -> Self {
        Self { cfg, entry }
    }

    fn entries(&self) -> Vec<BlockId> {
        let mut distance = BTreeMap::from([(self.entry, 0usize)]);
        let mut pending = VecDeque::from([self.entry]);
        while let Some(block) = pending.pop_front() {
            if !self.transparent(block) {
                continue;
            }
            let next_distance = distance[&block] + 1;
            for successor in self.cfg.normal_successors(block) {
                if distance.contains_key(&successor) {
                    continue;
                }
                distance.insert(successor, next_distance);
                pending.push_back(successor);
            }
        }
        let mut candidates = distance
            .into_iter()
            .filter(|(candidate, _)| self.must_reach(*candidate))
            .collect::<Vec<_>>();
        candidates.sort_by_key(|(block, distance)| (*distance, *block));
        candidates.into_iter().map(|(block, _)| block).collect()
    }

    fn transparent(&self, block: BlockId) -> bool {
        self.cfg.block(block).is_some_and(|block| {
            block.insns.iter().all(|instruction| {
                InstructionEffects::of_tree(instruction).is_pure()
                    || matches!(
                        instruction.insn_type,
                        InsnType::Nop
                            | InsnType::Goto
                            | InsnType::If
                            | InsnType::Switch
                            | InsnType::Phi
                            | InsnType::Move
                            | InsnType::MoveException
                    )
            })
        })
    }

    fn must_reach(&self, candidate: BlockId) -> bool {
        let reachable = Self::reachable(self.cfg, self.entry);
        let mut guaranteed = BTreeSet::from([candidate]);
        loop {
            let additions = reachable
                .iter()
                .copied()
                .filter(|block| !guaranteed.contains(block))
                .filter(|block| {
                    let successors = self.cfg.normal_successors(*block).collect::<Vec<_>>();
                    !successors.is_empty()
                        && successors.iter().all(|target| guaranteed.contains(target))
                })
                .collect::<Vec<_>>();
            if additions.is_empty() {
                break;
            }
            guaranteed.extend(additions);
        }
        guaranteed.contains(&self.entry)
    }

    fn reachable(cfg: &CFG, entry: BlockId) -> BTreeSet<BlockId> {
        let mut blocks = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if !blocks.insert(block) {
                continue;
            }
            pending.extend(cfg.normal_successors(block));
        }
        blocks
    }
}

struct CleanupSpecialization<'a> {
    cfg: &'a CFG,
    nullness: SsaNullness<'a>,
    rethrow_blocks: &'a BTreeSet<BlockId>,
}

impl<'a> CleanupSpecialization<'a> {
    fn new(
        cfg: &'a CFG,
        values: &'a SsaValueGraph,
        normal_dominators: &'a DominatorTree,
        rethrow_blocks: &'a BTreeSet<BlockId>,
    ) -> Self {
        Self {
            cfg,
            nullness: SsaNullness::new(cfg, values, normal_dominators),
            rethrow_blocks,
        }
    }

    fn entry(mut self, handler: BlockId, normal: BlockId) -> BlockId {
        let handler = self.decision_entry(handler);
        if self.homologous_decision(handler, normal) {
            return handler;
        }
        let Some(branch) = self.specialized_branch(handler, normal) else {
            return handler;
        };
        self.cfg
            .successors_with_kind(handler)
            .iter()
            .find_map(|(target, kind)| (*kind == branch).then_some(*target))
            .unwrap_or(handler)
    }

    fn homologous_decision(&self, handler: BlockId, normal: BlockId) -> bool {
        let Some(handler) = self.cfg.block(handler).and_then(|block| block.terminator()) else {
            return false;
        };
        let Some(normal) = self.cfg.block(normal).and_then(|block| block.terminator()) else {
            return false;
        };
        handler.insn_type == InsnType::If
            && normal.insn_type == InsnType::If
            && handler.operation_equivalent(normal)
            && handler.args.len() == normal.args.len()
            && handler
                .args
                .iter()
                .zip(&normal.args)
                .all(|(handler, normal)| CleanupRootFilter::argument_shape(handler, normal))
    }

    fn decision_entry(&self, entry: BlockId) -> BlockId {
        let mut current = entry;
        let mut visited = BTreeSet::new();
        while visited.insert(current) {
            let Some(block) = self.cfg.block(current) else {
                break;
            };
            if block
                .terminator()
                .is_some_and(|instruction| instruction.insn_type == InsnType::If)
            {
                break;
            }
            if !CleanupProof::body_instructions(block, false).is_empty() {
                break;
            }
            let successors = self.cfg.normal_successors(current).collect::<Vec<_>>();
            let [successor] = successors.as_slice() else {
                break;
            };
            current = *successor;
        }
        current
    }

    fn specialized_branch(&mut self, handler: BlockId, normal: BlockId) -> Option<EdgeKind> {
        let condition = self.cfg.block(handler)?.terminator()?;
        if condition.insn_type != InsnType::If {
            return None;
        }
        let (register, literal) = match condition.args.as_slice() {
            [InsnArg::Reg(register), InsnArg::Lit(literal)]
            | [InsnArg::Lit(literal), InsnArg::Reg(register)] => (register, literal),
            _ => return None,
        };
        if literal.value != 0 {
            return None;
        }
        if let Some(normal_value) = self.normal_value(normal, register.reg_num) {
            if self.nullness.is_non_null_at(normal_value, normal) {
                return match condition.payload.if_op? {
                    IfOp::Eq => Some(EdgeKind::False),
                    IfOp::Ne => Some(EdgeKind::True),
                    IfOp::Lt | IfOp::Ge | IfOp::Gt | IfOp::Le => None,
                };
            }
        }
        self.operation_branch(handler, normal)
    }

    fn normal_value(&self, block: BlockId, register: u32) -> Option<SsaVar> {
        self.cfg.block(block)?.insns.iter().find_map(|instruction| {
            instruction
                .args
                .iter()
                .filter_map(InsnArg::as_register)
                .find(|argument| argument.reg_num == register)
                .and_then(SsaVar::from_reg)
        })
    }

    fn operation_branch(&self, handler: BlockId, normal: BlockId) -> Option<EdgeKind> {
        let filter = CleanupRootFilter::new(self.cfg, self.rethrow_blocks);
        let normal = filter.first_observable(normal, false)?;
        let mut matching = self
            .cfg
            .successors_with_kind(handler)
            .iter()
            .filter_map(|(target, kind)| {
                let candidate = filter.first_observable(*target, true)?;
                (candidate.operation_equivalent(normal)
                    && candidate.args.len() == normal.args.len()
                    && candidate
                        .args
                        .iter()
                        .zip(&normal.args)
                        .all(|(handler, normal)| {
                            CleanupRootFilter::argument_shape(handler, normal)
                        }))
                .then_some(*kind)
            })
            .collect::<Vec<_>>();
        matching.sort_unstable();
        matching.dedup();
        let [branch] = matching.as_slice() else {
            return None;
        };
        Some(*branch)
    }
}

struct SsaNullness<'a> {
    cfg: &'a CFG,
    values: &'a SsaValueGraph,
    normal_dominators: &'a DominatorTree,
    cache: BTreeMap<SsaVar, bool>,
    active: BTreeSet<SsaVar>,
}

impl<'a> SsaNullness<'a> {
    fn new(cfg: &'a CFG, values: &'a SsaValueGraph, normal_dominators: &'a DominatorTree) -> Self {
        Self {
            cfg,
            values,
            normal_dominators,
            cache: BTreeMap::new(),
            active: BTreeSet::new(),
        }
    }

    fn is_non_null_at(&mut self, value: SsaVar, point: BlockId) -> bool {
        self.is_definition_non_null(value) || self.has_dominating_dereference(value, point)
    }

    fn is_definition_non_null(&mut self, value: SsaVar) -> bool {
        if let Some(known) = self.cache.get(&value) {
            return *known;
        }
        if !self.active.insert(value) {
            return false;
        }
        let definition = self.definition(value).cloned();
        let known = definition
            .as_ref()
            .is_some_and(|instruction| match instruction.insn_type {
                InsnType::Constructor
                | InsnType::NewInstance
                | InsnType::NewArray
                | InsnType::FilledNewArray
                | InsnType::ConstStr
                | InsnType::ConstClass
                | InsnType::StringConcat => true,
                InsnType::Move | InsnType::Cast | InsnType::CheckCast => instruction
                    .args
                    .first()
                    .and_then(InsnArg::as_register)
                    .and_then(SsaVar::from_reg)
                    .is_some_and(|source| self.is_definition_non_null(source)),
                InsnType::Phi => {
                    !instruction.args.is_empty()
                        && instruction
                            .args
                            .iter()
                            .filter_map(InsnArg::as_register)
                            .filter_map(SsaVar::from_reg)
                            .all(|source| self.is_definition_non_null(source))
                }
                _ => false,
            });
        self.active.remove(&value);
        self.cache.insert(value, known);
        known
    }

    fn has_dominating_dereference(&self, value: SsaVar, point: BlockId) -> bool {
        self.cfg.blocks.iter().any(|(block, body)| {
            *block != point
                && self.normal_dominators.dominates(*block, point)
                && body
                    .insns
                    .iter()
                    .any(|instruction| Self::dereferences(instruction, value))
        })
    }

    fn dereferences(instruction: &InsnNode, value: SsaVar) -> bool {
        instruction.insn_type == InsnType::Invoke
            && instruction.payload.invoke_type != Some(InvokeType::Static)
            && instruction
                .args
                .first()
                .and_then(InsnArg::as_register)
                .and_then(SsaVar::from_reg)
                == Some(value)
    }

    fn definition(&self, value: SsaVar) -> Option<&InsnNode> {
        let position = self.values.value(value)?.definition?;
        self.cfg.block(position.block)?.insns.get(position.index)
    }
}

struct CleanupProof<'a> {
    cfg: &'a CFG,
    handler_blocks: &'a BTreeSet<BlockId>,
    rethrow_blocks: &'a BTreeSet<BlockId>,
    value_graph: &'a SsaValueGraph,
    aliases: SsaClasses,
    origins: &'a SsaOrigins,
    values: BTreeMap<SsaVar, SsaVar>,
    reverse_values: BTreeMap<SsaVar, SsaVar>,
    state_bindings: BTreeSet<(SsaVar, SsaVar)>,
    blocks: BTreeMap<BlockId, BlockId>,
    phi_edges: Vec<(BlockId, BlockId)>,
    visited: BTreeSet<(BlockId, usize, BlockId, usize)>,
    traversed_normal: BTreeSet<BlockId>,
    shared_normal: BTreeSet<BlockId>,
    matched_normal: BTreeSet<StatementOrigin>,
    mismatch: Option<CleanupMismatchDiagnostic>,
}

impl<'a> CleanupProof<'a> {
    fn new(
        cfg: &'a CFG,
        value_graph: &'a SsaValueGraph,
        origins: &'a SsaOrigins,
        handler_blocks: &'a BTreeSet<BlockId>,
        rethrow_blocks: &'a BTreeSet<BlockId>,
    ) -> Self {
        Self {
            cfg,
            handler_blocks,
            rethrow_blocks,
            value_graph,
            aliases: value_graph.copy_classes(),
            origins,
            values: BTreeMap::new(),
            reverse_values: BTreeMap::new(),
            state_bindings: BTreeSet::new(),
            blocks: BTreeMap::new(),
            phi_edges: Vec::new(),
            visited: BTreeSet::new(),
            traversed_normal: BTreeSet::new(),
            shared_normal: BTreeSet::new(),
            matched_normal: BTreeSet::new(),
            mismatch: None,
        }
    }

    fn mismatch(&self) -> Option<CleanupMismatchDiagnostic> {
        self.mismatch
    }

    fn reject(
        &mut self,
        handler_block: BlockId,
        handler_index: usize,
        normal_block: BlockId,
        normal_index: usize,
        reason: CleanupMismatchReason,
    ) -> Result<bool, super::ExceptionInvariantError> {
        self.mismatch.get_or_insert(CleanupMismatchDiagnostic {
            handler_block,
            handler_index,
            normal_block,
            normal_index,
            reason,
        });
        Ok(false)
    }

    fn compare(
        &mut self,
        handler: BlockId,
        normal: BlockId,
    ) -> Result<bool, super::ExceptionInvariantError> {
        let mut pending = vec![(handler, 0usize, normal, 0usize)];
        while let Some((handler, handler_index, normal, normal_index)) = pending.pop() {
            self.traversed_normal.insert(normal);
            if handler == normal {
                self.shared_normal.insert(normal);
            }
            if !self
                .visited
                .insert((handler, handler_index, normal, normal_index))
            {
                continue;
            }
            if !self.handler_blocks.contains(&handler) {
                return self.reject(
                    handler,
                    handler_index,
                    normal,
                    normal_index,
                    CleanupMismatchReason::HandlerDomain,
                );
            }
            let handler_block = self
                .cfg
                .block(handler)
                .ok_or(super::ExceptionInvariantError::MissingHandlerBlock(handler))?;
            let normal_block = self
                .cfg
                .block(normal)
                .ok_or(super::ExceptionInvariantError::MissingCleanupBlock(normal))?;
            let handler_insns =
                Self::body_instructions(handler_block, self.rethrow_blocks.contains(&handler));
            let normal_insns = Self::body_instructions(normal_block, false);
            if !self.bind_block(handler, normal) {
                return self.reject(
                    handler,
                    handler_index,
                    normal,
                    normal_index,
                    CleanupMismatchReason::BlockCorrespondence,
                );
            }

            let handler_rethrows = self.rethrow_blocks.contains(&handler);
            if handler_insns.is_empty() && normal_insns.is_empty() {
                if let Some(rethrow) = self.rethrow_closure(handler) {
                    if !self.bind_block(rethrow, normal) {
                        return self.reject(
                            handler,
                            handler_index,
                            normal,
                            normal_index,
                            CleanupMismatchReason::BlockCorrespondence,
                        );
                    }
                    continue;
                }
            }
            if let (Some((_, handler_insn)), Some((_, normal_insn))) = (
                handler_insns.get(handler_index),
                normal_insns.get(normal_index),
            ) {
                let handler_exceptional = self.exceptional_targets(handler);
                let normal_exceptional = self.exceptional_targets(normal);
                if handler_insn.can_throw() || normal_insn.can_throw() {
                    let Some(exceptional_pairs) = self.pair_exceptional_targets(
                        handler_insn,
                        &handler_exceptional,
                        normal_insn,
                        &normal_exceptional,
                    ) else {
                        return self.reject(
                            handler,
                            handler_index,
                            normal,
                            normal_index,
                            CleanupMismatchReason::ExceptionalFlow,
                        );
                    };
                    pending.extend(
                        exceptional_pairs
                            .into_iter()
                            .map(|(handler, normal)| (handler, 0, normal, 0)),
                    );
                }
                let prior_values = self.values.clone();
                if !self.instruction(handler_insn, normal_insn) {
                    return self.reject(
                        handler,
                        handler_index,
                        normal,
                        normal_index,
                        CleanupMismatchReason::Instruction,
                    );
                }
                // The normal cleanup copy is elided after this proof, so
                // values consumed by the two observable operations must be
                // represented by the same source variable. Branch operands
                // are recorded by `branch_relation`; straight-line cleanup
                // operations need the same treatment here.
                self.record_state_bindings(&prior_values);
                if handler != normal {
                    self.matched_normal.insert(StatementOrigin {
                        block: normal,
                        instruction: normal_insn.id,
                    });
                }
                pending.push((handler, handler_index + 1, normal, normal_index + 1));
                continue;
            }

            if handler_rethrows && handler_index >= handler_insns.len() {
                continue;
            }

            if handler_index < handler_insns.len() {
                let normal_edges = Self::normal_flow_edges(self.cfg, normal);
                let [(target, _)] = normal_edges.as_slice() else {
                    return self.reject(
                        handler,
                        handler_index,
                        normal,
                        normal_index,
                        CleanupMismatchReason::NormalAdvance,
                    );
                };
                pending.push((handler, handler_index, *target, 0));
                continue;
            }

            if normal_index < normal_insns.len() {
                if handler_rethrows {
                    return self.reject(
                        handler,
                        handler_index,
                        normal,
                        normal_index,
                        CleanupMismatchReason::HandlerAdvance,
                    );
                }
                let handler_edges = Self::normal_flow_edges(self.cfg, handler);
                let next = if let [(target, kind)] = handler_edges.as_slice() {
                    Some((*target, *kind))
                } else {
                    self.matching_handler_edge(&handler_edges, Some(normal_insns[normal_index].1))
                };
                let Some((target, _)) = next else {
                    return self.reject(
                        handler,
                        handler_index,
                        normal,
                        normal_index,
                        CleanupMismatchReason::HandlerAdvance,
                    );
                };
                pending.push((target, 0, normal, normal_index));
                continue;
            }

            let handler_edges = Self::normal_flow_edges(self.cfg, handler);
            let normal_edges = Self::normal_flow_edges(self.cfg, normal);
            match (handler_edges.as_slice(), normal_edges.as_slice()) {
                ([(handler_target, handler_kind)], [(normal_target, normal_kind)]) => {
                    if handler_kind != normal_kind {
                        return Ok(false);
                    }
                    pending.push((*handler_target, 0, *normal_target, 0));
                }
                ([(handler_target, _)], []) => {
                    pending.push((*handler_target, 0, normal, normal_index));
                }
                (handler_edges, []) if handler_edges.len() > 1 => {
                    let Some((handler_target, _)) = self.matching_handler_edge(handler_edges, None)
                    else {
                        return self.reject(
                            handler,
                            handler_index,
                            normal,
                            normal_index,
                            CleanupMismatchReason::HandlerAdvance,
                        );
                    };
                    pending.push((handler_target, 0, normal, normal_index));
                }
                (handler_edges, normal_edges)
                    if handler_edges.len() > 1 && normal_edges.len() > 1 =>
                {
                    let Some(branches) = self.pair_branches(
                        handler_block,
                        normal_block,
                        handler_edges,
                        normal_edges,
                    ) else {
                        return self.reject(
                            handler,
                            handler_index,
                            normal,
                            normal_index,
                            CleanupMismatchReason::BranchFlow,
                        );
                    };
                    if handler != normal {
                        if let Some(terminal) = normal_block.terminator() {
                            self.matched_normal.insert(StatementOrigin {
                                block: normal,
                                instruction: terminal.id,
                            });
                        }
                    }
                    pending.extend(
                        branches
                            .into_iter()
                            .map(|(handler, normal)| (handler, 0, normal, 0)),
                    );
                }
                ([], []) => {
                    if self.matching_terminal_throws(handler_block, normal_block) {
                        continue;
                    }
                    return self.reject(
                        handler,
                        handler_index,
                        normal,
                        normal_index,
                        CleanupMismatchReason::TerminalFlow,
                    );
                }
                _ => {
                    return self.reject(
                        handler,
                        handler_index,
                        normal,
                        normal_index,
                        CleanupMismatchReason::BranchFlow,
                    );
                }
            }
        }
        let valid = self.phi_edges.iter().all(|(handler, normal)| {
            self.blocks
                .get(handler)
                .is_some_and(|mapped| mapped == normal)
        });
        if !valid {
            self.mismatch.get_or_insert(CleanupMismatchDiagnostic {
                handler_block: handler,
                handler_index: 0,
                normal_block: normal,
                normal_index: 0,
                reason: CleanupMismatchReason::PhiFlow,
            });
        }
        Ok(valid)
    }

    fn value_bindings(&self) -> BTreeSet<(SsaVar, SsaVar)> {
        self.state_bindings.clone()
    }

    /// A nested cleanup may terminate its exceptional arm by replacing the
    /// in-flight exception (for example, when `monitorexit` itself throws).
    /// Such arms are closed completions of the two cleanup programs, not exits
    /// from the proof domain.  Compare their terminal values just like any
    /// other observable operation before accepting the product-graph leaf.
    fn matching_terminal_throws(
        &mut self,
        handler: &crate::ir::Block,
        normal: &crate::ir::Block,
    ) -> bool {
        let (Some(handler), Some(normal)) = (handler.terminator(), normal.terminator()) else {
            return false;
        };
        handler.insn_type == InsnType::Throw
            && normal.insn_type == InsnType::Throw
            && self.instruction(handler, normal)
    }

    fn rethrow_closure(&self, entry: BlockId) -> Option<BlockId> {
        let mut current = entry;
        let mut visited = BTreeSet::new();
        while visited.insert(current) {
            let block = self.cfg.block(current)?;
            let rethrow = self.rethrow_blocks.contains(&current);
            if !Self::body_instructions(block, rethrow).is_empty()
                || self
                    .cfg
                    .successors_with_kind(current)
                    .iter()
                    .any(|(_, kind)| *kind == EdgeKind::Exception)
            {
                return None;
            }
            if rethrow {
                return Some(current);
            }
            let edges = Self::normal_flow_edges(self.cfg, current);
            let [(target, _)] = edges.as_slice() else {
                return None;
            };
            current = *target;
        }
        None
    }

    fn bind_block(&mut self, handler: BlockId, normal: BlockId) -> bool {
        let Some(mapped) = self.blocks.get(&handler).copied() else {
            self.blocks.insert(handler, normal);
            return true;
        };
        if mapped == normal {
            return true;
        }
        if self.empty_path_reaches(mapped, normal) {
            self.blocks.insert(handler, normal);
            return true;
        }
        if self.empty_path_reaches(normal, mapped) {
            return true;
        }
        if !self.rethrow_blocks.contains(&handler) {
            return false;
        }
        if let Some(join) = self.empty_path_join(mapped, normal) {
            self.blocks.insert(handler, join);
            true
        } else {
            false
        }
    }

    fn empty_path_reaches(&self, entry: BlockId, target: BlockId) -> bool {
        self.empty_path(entry).contains(&target)
    }

    fn empty_path_join(&self, left: BlockId, right: BlockId) -> Option<BlockId> {
        let right = self.empty_path(right).into_iter().collect::<BTreeSet<_>>();
        self.empty_path(left)
            .into_iter()
            .find(|block| right.contains(block))
    }

    fn empty_path(&self, entry: BlockId) -> Vec<BlockId> {
        let mut current = entry;
        let mut visited = BTreeSet::new();
        let mut path = Vec::new();
        while visited.insert(current) {
            path.push(current);
            let Some(block) = self.cfg.block(current) else {
                break;
            };
            if !Self::body_instructions(block, false).is_empty()
                || self
                    .cfg
                    .successors_with_kind(current)
                    .iter()
                    .any(|(_, kind)| *kind == EdgeKind::Exception)
            {
                break;
            }
            let edges = Self::normal_flow_edges(self.cfg, current);
            let [(next, _)] = edges.as_slice() else {
                break;
            };
            current = *next;
        }
        path
    }

    fn exceptional_targets(&self, block: BlockId) -> BTreeSet<BlockId> {
        self.cfg
            .successors_with_kind(block)
            .iter()
            .filter_map(|(target, kind)| {
                (*kind == EdgeKind::Exception)
                    .then_some(CleanupRecovery::semantic_target(self.cfg, *target))
            })
            .collect()
    }

    fn pair_exceptional_targets(
        &self,
        handler_insn: &InsnNode,
        handler_targets: &BTreeSet<BlockId>,
        normal_insn: &InsnNode,
        normal_targets: &BTreeSet<BlockId>,
    ) -> Option<Vec<(BlockId, BlockId)>> {
        if handler_targets == normal_targets {
            return Some(Vec::new());
        }
        if handler_targets.len() != normal_targets.len() {
            return None;
        }

        let handler_clauses = self.exceptional_clauses(handler_insn, handler_targets);
        let normal_clauses = self.exceptional_clauses(normal_insn, normal_targets);
        if handler_clauses.len() == handler_targets.len()
            && normal_clauses.len() == normal_targets.len()
        {
            let mut unmatched = normal_clauses;
            let mut pairs = Vec::with_capacity(handler_clauses.len());
            for (handler_target, signature) in handler_clauses {
                let matches = unmatched
                    .iter()
                    .filter_map(|(target, candidate)| (candidate == &signature).then_some(*target))
                    .collect::<Vec<_>>();
                let [normal_target] = matches.as_slice() else {
                    return None;
                };
                if handler_target != *normal_target {
                    pairs.push((handler_target, *normal_target));
                }
                unmatched.remove(normal_target);
            }
            return unmatched.is_empty().then_some(pairs);
        }

        match (
            handler_targets.iter().next().copied(),
            normal_targets.iter().next().copied(),
        ) {
            (Some(handler), Some(normal))
                if handler_targets.len() == 1 && normal_targets.len() == 1 =>
            {
                Some(vec![(handler, normal)])
            }
            _ => None,
        }
    }

    fn exceptional_clauses(
        &self,
        instruction: &InsnNode,
        targets: &BTreeSet<BlockId>,
    ) -> BTreeMap<BlockId, BTreeSet<Option<crate::ir::ArgType>>> {
        let mut clauses = BTreeMap::<BlockId, BTreeSet<Option<crate::ir::ArgType>>>::new();
        for handler in self
            .cfg
            .handlers
            .iter()
            .filter(|handler| handler.covers(instruction.offset))
        {
            let Some(entry) = self
                .cfg
                .blocks
                .values()
                .find(|candidate| !candidate.synthetic && candidate.offset == handler.handler)
                .map(|candidate| candidate.id)
            else {
                continue;
            };
            let target = CleanupRecovery::semantic_target(self.cfg, entry);
            if targets.contains(&target) {
                clauses
                    .entry(target)
                    .or_default()
                    .insert(handler.catch_type.clone());
            }
        }
        clauses
    }

    fn pair_branches(
        &mut self,
        handler: &crate::ir::Block,
        normal: &crate::ir::Block,
        handler_edges: &[(BlockId, EdgeKind)],
        normal_edges: &[(BlockId, EdgeKind)],
    ) -> Option<Vec<(BlockId, BlockId)>> {
        let handler_term = handler.terminator()?;
        let normal_term = normal.terminator()?;
        let inverted = self.branch_relation(handler_term, normal_term)?;
        let mut pairs = Vec::with_capacity(handler_edges.len());
        for (handler_target, handler_kind) in handler_edges {
            let normal_kind = if inverted {
                Self::opposite_edge(*handler_kind)?
            } else {
                *handler_kind
            };
            let normal_target = normal_edges
                .iter()
                .find_map(|(target, kind)| (*kind == normal_kind).then_some(*target))?;
            pairs.push((*handler_target, normal_target));
        }
        (pairs.len() == normal_edges.len()).then_some(pairs)
    }

    fn branch_relation(&mut self, handler: &InsnNode, normal: &InsnNode) -> Option<bool> {
        let values = self.values.clone();
        let reverse_values = self.reverse_values.clone();
        let phi_edges = self.phi_edges.clone();
        let state_bindings = self.state_bindings.clone();
        if self.instruction(handler, normal) {
            self.record_state_bindings(&values);
            return Some(false);
        }
        self.values = values.clone();
        self.reverse_values = reverse_values.clone();
        self.phi_edges = phi_edges.clone();
        self.state_bindings = state_bindings.clone();

        if handler.insn_type == InsnType::If
            && normal.insn_type == InsnType::If
            && handler.payload.if_op == normal.payload.if_op.map(|operation| operation.invert())
        {
            let mut normalized = normal.clone();
            normalized.payload.if_op = handler.payload.if_op;
            if self.instruction(handler, &normalized) {
                self.record_state_bindings(&values);
                return Some(true);
            }
        }
        self.values = values;
        self.reverse_values = reverse_values;
        self.phi_edges = phi_edges;
        self.state_bindings = state_bindings;
        None
    }

    fn record_state_bindings(&mut self, prior: &BTreeMap<SsaVar, SsaVar>) {
        self.state_bindings.extend(
            self.values
                .iter()
                .filter(|(handler, normal)| prior.get(handler) != Some(*normal))
                .map(|(handler, normal)| (*handler, *normal)),
        );
    }

    fn opposite_edge(kind: EdgeKind) -> Option<EdgeKind> {
        match kind {
            EdgeKind::True => Some(EdgeKind::False),
            EdgeKind::False => Some(EdgeKind::True),
            _ => None,
        }
    }

    fn matching_handler_edge(
        &self,
        edges: &[(BlockId, EdgeKind)],
        normal: Option<&InsnNode>,
    ) -> Option<(BlockId, EdgeKind)> {
        let filter = CleanupRootFilter::new(self.cfg, self.rethrow_blocks);
        let mut matching =
            edges
                .iter()
                .copied()
                .filter(|(target, _)| {
                    let candidate = filter.first_observable(*target, true);
                    match (candidate, normal) {
                        (None, None) => true,
                        (Some(candidate), Some(normal)) => {
                            candidate.operation_equivalent(normal)
                                && candidate.args.len() == normal.args.len()
                                && candidate.args.iter().zip(&normal.args).all(
                                    |(handler, normal)| {
                                        CleanupRootFilter::argument_shape(handler, normal)
                                    },
                                )
                        }
                        _ => false,
                    }
                })
                .collect::<Vec<_>>();
        matching.sort_unstable();
        matching.dedup();
        let [edge] = matching.as_slice() else {
            return None;
        };
        Some(*edge)
    }

    fn normal_completion(&self) -> Option<BlockId> {
        let completions = self
            .rethrow_blocks
            .iter()
            .filter_map(|block| self.blocks.get(block).copied())
            .collect::<BTreeSet<_>>();
        (completions.len() == 1)
            .then(|| completions.first().copied())
            .flatten()
    }

    fn has_semantic_evidence(&self) -> bool {
        !self.matched_normal.is_empty()
            || self.shared_normal.iter().any(|block| {
                self.cfg.block(*block).is_some_and(|body| {
                    !Self::body_instructions(body, self.rethrow_blocks.contains(block)).is_empty()
                })
            })
    }

    fn contracted_normal_blocks(&self, root: BlockId) -> BTreeSet<BlockId> {
        let completion = self.normal_completion();
        let candidates = self
            .traversed_normal
            .iter()
            .copied()
            .filter(|block| {
                *block == root
                    || self
                        .cfg
                        .incoming_edges(*block)
                        .iter()
                        .all(|(source, _)| self.traversed_normal.contains(source))
            })
            .collect::<BTreeSet<_>>();
        let mut owned = BTreeSet::new();
        let mut pending = vec![root];
        while let Some(block) = pending.pop() {
            if !candidates.contains(&block) || !owned.insert(block) {
                continue;
            }
            pending.extend(
                self.cfg
                    .successors_with_kind(block)
                    .iter()
                    .map(|(target, _)| *target),
            );
        }
        let mut contractible = owned
            .difference(&self.shared_normal)
            .filter(|block| Some(**block) != completion)
            .copied()
            .collect::<BTreeSet<_>>();
        loop {
            let rejected = contractible
                .iter()
                .copied()
                .filter(|block| !self.normal_block_is_fully_matched(*block, &contractible))
                .collect::<Vec<_>>();
            if rejected.is_empty() {
                break;
            }
            for block in rejected {
                contractible.remove(&block);
            }
        }
        contractible
    }

    fn fully_contracts_normal_cleanup(&self, contractible: &BTreeSet<BlockId>) -> bool {
        let completion = self.normal_completion();
        self.traversed_normal.iter().all(|block| {
            self.shared_normal.contains(block)
                || Some(*block) == completion
                || contractible.contains(block)
        })
    }

    fn normal_block_is_fully_matched(
        &self,
        block: BlockId,
        contractible: &BTreeSet<BlockId>,
    ) -> bool {
        self.cfg.block(block).is_some_and(|body| {
            body.insns.iter().all(|instruction| {
                matches!(instruction.insn_type, InsnType::Nop | InsnType::Goto)
                    || self.matched_normal.contains(&StatementOrigin {
                        block,
                        instruction: instruction.id,
                    })
                    || self.unmatched_value_is_internal(instruction, contractible)
            })
        })
    }

    fn unmatched_value_is_internal(
        &self,
        instruction: &InsnNode,
        contractible: &BTreeSet<BlockId>,
    ) -> bool {
        if !InstructionEffects::of_tree(instruction).is_pure()
            && !InstructionEffects::is_ssa_bookkeeping(instruction)
        {
            return false;
        }
        let Some(value) = instruction.result.as_ref().and_then(SsaVar::from_reg) else {
            return true;
        };
        self.value_graph.value(value).is_some_and(|value| {
            value.uses.iter().all(|usage| {
                let consumer = match self.value_graph.use_site(self.cfg, value.variable, *usage) {
                    Some(SsaUseSite::Phi(phi)) => phi.block,
                    Some(SsaUseSite::Instruction(_)) | None => usage.instruction.block,
                };
                contractible.contains(&consumer)
            })
        })
    }

    fn body_instructions(block: &crate::ir::Block, elide_rethrow: bool) -> Vec<(usize, &InsnNode)> {
        block
            .insns
            .iter()
            .enumerate()
            .filter(|(_, insn)| {
                !InstructionEffects::is_ssa_bookkeeping(insn)
                    && !InstructionEffects::of_tree(insn).is_pure()
                    && !insn.insn_type.is_branch()
                    && insn.insn_type != InsnType::Return
                    && !(elide_rethrow && insn.insn_type == InsnType::Throw)
            })
            .collect()
    }

    fn instruction(&mut self, handler: &InsnNode, normal: &InsnNode) -> bool {
        let mut pending = vec![EquivalenceTask::Instruction(handler, normal)];
        while let Some(task) = pending.pop() {
            match task {
                EquivalenceTask::Instruction(handler, normal) => {
                    if !handler.operation_equivalent(normal)
                        || handler.args.len() != normal.args.len()
                    {
                        return false;
                    }
                    if handler.insn_type == InsnType::Phi {
                        if handler.payload.phi_edges.len() != normal.payload.phi_edges.len() {
                            return false;
                        }
                        for (
                            (handler_predecessor, handler_kind),
                            (normal_predecessor, normal_kind),
                        ) in handler
                            .payload
                            .phi_edges
                            .iter()
                            .zip(&normal.payload.phi_edges)
                        {
                            if handler_kind != normal_kind {
                                return false;
                            }
                            self.phi_edges
                                .push((*handler_predecessor, *normal_predecessor));
                        }
                    }
                    pending.extend(
                        handler
                            .args
                            .iter()
                            .zip(&normal.args)
                            .rev()
                            .map(|(handler, normal)| EquivalenceTask::Argument(handler, normal)),
                    );
                    match (
                        handler.payload.compound_target.as_ref(),
                        normal.payload.compound_target.as_ref(),
                    ) {
                        (Some(handler), Some(normal)) => {
                            pending.push(EquivalenceTask::Argument(handler, normal));
                        }
                        (None, None) => {}
                        _ => return false,
                    }
                    pending.push(EquivalenceTask::Result(
                        handler.result.as_ref(),
                        normal.result.as_ref(),
                    ));
                }
                EquivalenceTask::Argument(handler, normal) => match (handler, normal) {
                    (InsnArg::Lit(handler), InsnArg::Lit(normal)) => {
                        if handler != normal {
                            return false;
                        }
                    }
                    (InsnArg::Reg(handler), InsnArg::Reg(normal)) => {
                        if !self.equivalent_value(handler, normal) {
                            return false;
                        }
                    }
                    (InsnArg::Wrapped(handler), InsnArg::Wrapped(normal)) => {
                        pending.push(EquivalenceTask::Instruction(handler, normal));
                    }
                    _ => return false,
                },
                EquivalenceTask::Result(handler, normal) => match (handler, normal) {
                    (Some(handler), Some(normal)) if self.bind_result(handler, normal) => {}
                    (None, None) => {}
                    _ => return false,
                },
            }
        }
        true
    }

    fn equivalent_value(
        &mut self,
        handler: &crate::ir::RegisterArg,
        normal: &crate::ir::RegisterArg,
    ) -> bool {
        let Some(handler_key) = SsaVar::from_reg(handler) else {
            return false;
        };
        let Some(normal_key) = SsaVar::from_reg(normal) else {
            return false;
        };
        let handler_root = self.aliases.root(handler_key);
        let normal_root = self.aliases.root(normal_key);
        if let Some(bound) = self.values.get(&handler_root) {
            return *bound == normal_root;
        }
        if handler_root == normal_root {
            return true;
        }
        if handler_key.reg_num == normal_key.reg_num
            || handler_root.reg_num == normal_root.reg_num
            || self.origins.equivalent(handler_key, normal_key)
        {
            return self.bind_value_pair(handler_key, normal_key);
        }
        if handler.ty != normal.ty {
            return false;
        }
        let equivalent = self.equivalent_local_definition(handler_key, normal_key);
        if equivalent {
            return true;
        }
        self.bind_value_pair(handler_key, normal_key)
    }

    fn equivalent_local_definition(&mut self, handler: SsaVar, normal: SsaVar) -> bool {
        let Some(handler_position) = self
            .value_graph
            .value(handler)
            .and_then(|value| value.definition)
        else {
            return false;
        };
        let Some(normal_position) = self
            .value_graph
            .value(normal)
            .and_then(|value| value.definition)
        else {
            return false;
        };
        let corresponding_blocks = self.blocks.get(&handler_position.block)
            == Some(&normal_position.block)
            || self
                .phi_edges
                .contains(&(handler_position.block, normal_position.block));
        if !corresponding_blocks {
            return false;
        }
        let Some(handler_definition) = self
            .cfg
            .block(handler_position.block)
            .and_then(|block| block.insns.get(handler_position.index))
            .cloned()
        else {
            return false;
        };
        let Some(normal_definition) = self
            .cfg
            .block(normal_position.block)
            .and_then(|block| block.insns.get(normal_position.index))
            .cloned()
        else {
            return false;
        };
        let handler_local = InstructionEffects::is_ssa_bookkeeping(&handler_definition)
            || InstructionEffects::of_tree(&handler_definition).is_pure();
        let normal_local = InstructionEffects::is_ssa_bookkeeping(&normal_definition)
            || InstructionEffects::of_tree(&normal_definition).is_pure();
        if !handler_local || !normal_local {
            return false;
        }

        let values = self.values.clone();
        let reverse_values = self.reverse_values.clone();
        let phi_edges = self.phi_edges.clone();
        if !self.bind_value_pair(handler, normal)
            || !self.instruction(&handler_definition, &normal_definition)
        {
            self.values = values;
            self.reverse_values = reverse_values;
            self.phi_edges = phi_edges;
            return false;
        }
        true
    }

    fn bind_result(
        &mut self,
        handler: &crate::ir::RegisterArg,
        normal: &crate::ir::RegisterArg,
    ) -> bool {
        if handler.ty != normal.ty {
            return false;
        }
        let Some(handler_key) = SsaVar::from_reg(handler) else {
            return false;
        };
        let Some(normal_key) = SsaVar::from_reg(normal) else {
            return false;
        };
        self.bind_value_pair(handler_key, normal_key)
    }

    fn bind_value_pair(&mut self, handler: SsaVar, normal: SsaVar) -> bool {
        let handler_root = self.aliases.root(handler);
        let normal_root = self.aliases.root(normal);
        if self
            .values
            .get(&handler_root)
            .is_some_and(|bound| *bound != normal_root)
            || self
                .reverse_values
                .get(&normal_root)
                .is_some_and(|bound| *bound != handler_root)
        {
            return false;
        }
        self.values.entry(handler_root).or_insert(normal_root);
        self.reverse_values
            .entry(normal_root)
            .or_insert(handler_root);
        true
    }

    fn normal_flow_edges(cfg: &CFG, block: BlockId) -> Vec<(BlockId, EdgeKind)> {
        let mut edges = cfg
            .successors_with_kind(block)
            .iter()
            .copied()
            .filter(|(_, kind)| *kind != EdgeKind::Exception)
            .collect::<Vec<_>>();
        edges.sort_by_key(|(target, kind)| (*kind, *target));
        edges
    }
}

enum EquivalenceTask<'a> {
    Instruction(&'a InsnNode, &'a InsnNode),
    Argument(&'a InsnArg, &'a InsnArg),
    Result(
        Option<&'a crate::ir::RegisterArg>,
        Option<&'a crate::ir::RegisterArg>,
    ),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{ArgType, Block, RegisterArg};

    #[test]
    fn remaps_non_rethrow_handler_across_empty_normal_trampoline() {
        let handler = BlockId::new(0);
        let trampoline = BlockId::new(1);
        let target = BlockId::new(2);
        let observable = BlockId::new(3);
        let mut cfg = CFG::new("cleanup_empty_trampoline");
        cfg.add_block(Block::new(handler));
        cfg.add_block(Block::new(trampoline));
        cfg.add_block(Block::new(target));
        let mut observable_block = Block::new(observable);
        observable_block.push(InsnNode::monitor_exit(InsnArg::Reg(RegisterArg::new(
            0,
            ArgType::object("java/lang/Object"),
        ))));
        cfg.add_block(observable_block);
        cfg.add_edge(trampoline, target, EdgeKind::Normal);
        cfg.add_edge(observable, target, EdgeKind::Normal);

        let values = SsaValueGraph::default();
        let origins = SsaOrigins::analyze(&values);
        let handler_blocks = BTreeSet::from([handler]);
        let rethrow_blocks = BTreeSet::new();
        let mut proof =
            CleanupProof::new(&cfg, &values, &origins, &handler_blocks, &rethrow_blocks);
        assert!(proof.bind_block(handler, trampoline));
        assert!(proof.bind_block(handler, target));
        assert_eq!(proof.blocks.get(&handler), Some(&target));

        let mut proof =
            CleanupProof::new(&cfg, &values, &origins, &handler_blocks, &rethrow_blocks);
        assert!(proof.bind_block(handler, observable));
        assert!(!proof.bind_block(handler, target));
    }

    #[test]
    fn straight_line_cleanup_records_observable_argument_binding() {
        let handler = BlockId::new(0);
        let normal = BlockId::new(1);
        let handler_value = RegisterArg::new_ssa(
            1,
            7,
            ArgType::object("java/io/Closeable"),
        );
        let normal_value = RegisterArg::new_ssa(
            12,
            3,
            ArgType::object("java/io/Closeable"),
        );
        let mut cfg = CFG::new("cleanup_straight_line_state");
        let mut handler_block = Block::new(handler);
        handler_block.push(InsnNode::invoke(
            InvokeType::Static,
            0,
            vec![InsnArg::Reg(handler_value.clone())],
        ));
        cfg.add_block(handler_block);
        let mut normal_block = Block::new(normal);
        normal_block.push(InsnNode::invoke(
            InvokeType::Static,
            0,
            vec![InsnArg::Reg(normal_value.clone())],
        ));
        cfg.add_block(normal_block);

        let values = SsaValueGraph::default();
        let origins = SsaOrigins::analyze(&values);
        let handler_blocks = BTreeSet::from([handler]);
        let rethrow_blocks = BTreeSet::from([handler]);
        let mut proof =
            CleanupProof::new(&cfg, &values, &origins, &handler_blocks, &rethrow_blocks);

        assert!(proof.compare(handler, normal).expect("cleanup proof"));
        assert_eq!(
            proof.value_bindings(),
            BTreeSet::from([(
                SsaVar::from_reg(&handler_value).expect("handler SSA value"),
                SsaVar::from_reg(&normal_value).expect("normal SSA value"),
            )])
        );
    }
}
