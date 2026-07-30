//! Monitor-scope recovery proved from SSA identity and all-path release.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::analysis::{
    DominatorTree, InstructionEffects, SsaOrigins, SsaValueGraph, SsaVar, StrongComponents,
};
use crate::ir::{
    BlockId, CatchHandler, InsnArg, InsnNode, InsnType, StatementOrigin, TryRegion, CFG,
};

#[derive(Debug, Clone)]
pub(super) struct SynchronizationFact {
    pub(super) lock: InsnArg,
    pub(super) body_entry: BlockId,
    pub(super) enter_origin: StatementOrigin,
    pub(super) release_entries: BTreeSet<BlockId>,
    pub(super) release_origins: BTreeSet<StatementOrigin>,
    pub(super) scope_blocks: BTreeSet<BlockId>,
}

pub(super) struct SynchronizationAnalysis<'a> {
    cfg: &'a CFG,
    dominators: &'a DominatorTree,
    identities: BTreeMap<SsaVar, SsaVar>,
    origins: SsaOrigins,
    ordinary: BTreeSet<BlockId>,
    handler_entries: BTreeSet<BlockId>,
    proven_release_handlers: BTreeMap<SsaVar, BTreeMap<BlockId, BTreeSet<StatementOrigin>>>,
}

impl<'a> SynchronizationAnalysis<'a> {
    pub(super) fn new(
        cfg: &'a CFG,
        values: &SsaValueGraph,
        dominators: &'a DominatorTree,
        regions: &'a [TryRegion],
    ) -> Self {
        let mut classes = values.copy_classes();
        let identities = classes
            .groups()
            .into_iter()
            .flat_map(|(identity, members)| {
                members.into_iter().map(move |member| (member, identity))
            })
            .collect();
        let mut analysis = Self {
            cfg,
            dominators,
            identities,
            origins: SsaOrigins::analyze(values),
            ordinary: Self::reachable(cfg, cfg.entry),
            handler_entries: regions
                .iter()
                .flat_map(|region| {
                    region
                        .handlers
                        .iter()
                        .flat_map(|handler| handler.entry_blocks.iter().copied())
                })
                .collect(),
            proven_release_handlers: BTreeMap::new(),
        };
        for handler in regions
            .iter()
            .flat_map(|region| &region.handlers)
            .filter(|handler| Self::covers_throwables(handler))
        {
            if let Ok(proof) = analysis.prove_release(handler) {
                analysis
                    .proven_release_handlers
                    .entry(proof.lock)
                    .or_default()
                    .entry(handler.semantic_entry)
                    .or_default()
                    .extend(proof.releases);
            }
        }
        analysis
    }

    pub(super) fn region(&self, region: &TryRegion) -> Option<SynchronizationFact> {
        let Some(release) = self.cleanup_release(region) else {
            return None;
        };
        let candidates = self
            .cfg
            .block_ids()
            .into_iter()
            .filter_map(|block| self.monitor_entry(block, release.lock))
            .filter_map(|candidate| candidate.prove_scope(self, &release))
            .filter(|candidate| candidate.is_protected_by(self.cfg, region))
            .collect::<Vec<_>>();
        let nearest = candidates
            .iter()
            .filter(|candidate| {
                candidates.iter().all(|other| {
                    other.block == candidate.block
                        || self.dominators.dominates(other.block, candidate.block)
                })
            })
            .map(|candidate| &candidate.fact)
            .collect::<Vec<_>>();
        let [fact] = nearest.as_slice() else {
            return None;
        };
        Some((*fact).clone())
    }

    pub(super) fn canonical_fact<'b>(
        &self,
        facts: impl IntoIterator<Item = &'b SynchronizationFact>,
    ) -> Option<SynchronizationFact> {
        let facts = facts.into_iter().collect::<Vec<_>>();
        let first = (*facts.first()?).clone();
        let identity = self.identity(&first.lock)?;
        if facts.iter().any(|fact| {
            fact.enter_origin != first.enter_origin
                || fact.body_entry != first.body_entry
                || self.identity(&fact.lock) != Some(identity)
        }) {
            return None;
        }
        let candidate_entries = facts
            .iter()
            .flat_map(|fact| fact.release_entries.iter().copied())
            .collect::<BTreeSet<_>>();
        let scope = MonitorScopeFlow::new(
            self.cfg,
            &self.identities,
            &self.origins,
            identity,
            &candidate_entries,
        )
        .analyze(first.body_entry)
        .ok()?;
        if !scope
            .blocks
            .iter()
            .all(|block| self.dominators.dominates(first.enter_origin.block, *block))
        {
            return None;
        }
        let mut fact = first.clone();
        fact.release_entries = scope.reached_release_entries;
        fact.release_origins = facts
            .iter()
            .flat_map(|fact| fact.release_origins.iter().cloned())
            .chain(scope.releases)
            .collect();
        fact.scope_blocks = scope.blocks;
        Some(fact)
    }

    pub(super) fn standalone(
        &self,
        claimed: &BTreeSet<StatementOrigin>,
    ) -> Vec<SynchronizationFact> {
        let mut facts = self
            .cfg
            .block_ids()
            .into_iter()
            .filter_map(|block| {
                let node = self.cfg.block(block)?;
                let enters = node
                    .insns
                    .iter()
                    .filter(|instruction| instruction.insn_type == InsnType::MonitorEnter)
                    .collect::<Vec<_>>();
                let [enter] = enters.as_slice() else {
                    return None;
                };
                let enter_origin = StatementOrigin {
                    block,
                    instruction: enter.id,
                };
                if claimed.contains(&enter_origin) {
                    return None;
                }
                let lock = enter.args.first()?.clone();
                let identity = self.identity(&lock)?;
                let release_handlers = self.proven_release_handlers.get(&identity);
                let candidate_entries = release_handlers
                    .into_iter()
                    .flat_map(|handlers| handlers.keys().copied())
                    .collect();
                let successors = self.cfg.normal_successors(block).collect::<Vec<_>>();
                let [body_entry] = successors.as_slice() else {
                    return None;
                };
                let scope = match MonitorScopeFlow::new(
                    self.cfg,
                    &self.identities,
                    &self.origins,
                    identity,
                    &candidate_entries,
                )
                .analyze(*body_entry)
                {
                    Ok(scope) => scope,
                    Err(_) => {
                        return None;
                    }
                };
                let release_entries = scope.reached_release_entries;
                let mut release_origins = scope.releases;
                for entry in &release_entries {
                    release_origins.extend(
                        release_handlers
                            .and_then(|handlers| handlers.get(entry))
                            .into_iter()
                            .flatten()
                            .cloned(),
                    );
                }
                scope
                    .blocks
                    .iter()
                    .all(|owned| self.dominators.dominates(block, *owned))
                    .then_some(SynchronizationFact {
                        lock,
                        body_entry: *body_entry,
                        enter_origin,
                        release_entries,
                        release_origins,
                        scope_blocks: scope.blocks,
                    })
            })
            .collect::<Vec<_>>();
        facts.sort_by_key(|fact| std::cmp::Reverse(fact.scope_blocks.len()));
        facts
    }

    fn cleanup_release(&self, region: &TryRegion) -> Option<MonitorReleaseProof> {
        let cleanups = region
            .handlers
            .iter()
            .filter(|handler| Self::covers_throwables(handler))
            .collect::<Vec<_>>();
        if cleanups.is_empty() {
            return None;
        }
        let handlers = cleanups
            .into_iter()
            .map(|handler| {
                self.prove_release(handler)
                    .ok()
                    .map(|proof| (proof, handler.semantic_entry))
            })
            .collect::<Option<Vec<_>>>()?;
        let locks = handlers
            .iter()
            .map(|(proof, _)| proof.lock)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let [lock] = locks.as_slice() else {
            return None;
        };
        let mut handler_releases = BTreeMap::<BlockId, BTreeSet<StatementOrigin>>::new();
        for (proof, entry) in handlers {
            handler_releases
                .entry(entry)
                .or_default()
                .extend(proof.releases);
        }
        Some(MonitorReleaseProof {
            lock: *lock,
            handler_releases,
        })
    }

    fn prove_release(
        &self,
        handler: &CatchHandler,
    ) -> Result<HandlerReleaseProof, ReleaseProofError> {
        let owned = self.cleanup_domain(handler.semantic_entry);
        if !owned.contains(&handler.semantic_entry) {
            return Err(ReleaseProofError::MissingEntry(handler.semantic_entry));
        }
        if !StrongComponents::analyze(self.cfg, owned.iter().copied()).is_acyclic() {
            return Err(ReleaseProofError::CyclicDomain(handler.semantic_entry));
        }

        let exception = handler
            .exception_value
            .as_ref()
            .and_then(SsaVar::from_reg)
            .ok_or(ReleaseProofError::MissingExceptionValue(
                handler.semantic_entry,
            ))?;
        let mut lock = None;
        let mut releases = BTreeSet::new();
        let mut reached_throw = false;
        let mut visited = BTreeSet::new();
        let mut pending = vec![(handler.semantic_entry, None, false, ValueOrigins::default())];
        while let Some((block, predecessor, released, mut origins)) = pending.pop() {
            if !owned.contains(&block)
                || !visited.insert((block, predecessor, released, origins.clone()))
            {
                continue;
            }
            let node = self
                .cfg
                .block(block)
                .ok_or(ReleaseProofError::MissingBlock(block))?;
            let mut released = released;
            let mut terminal = false;
            for instruction in &node.insns {
                origins.propagate(instruction, predecessor, Some(exception));
                match instruction.insn_type {
                    InsnType::MonitorExit => {
                        if released {
                            return Err(ReleaseProofError::MultipleReleases(block));
                        }
                        let value = instruction
                            .args
                            .first()
                            .and_then(InsnArg::as_register)
                            .and_then(SsaVar::from_reg)
                            .map(|value| self.canonical(origins.resolve(value)))
                            .ok_or(ReleaseProofError::MissingLock(block))?;
                        if lock.is_some_and(|lock| lock != value) {
                            return Err(ReleaseProofError::ConflictingLocks(block));
                        }
                        lock = Some(value);
                        releases.insert(StatementOrigin {
                            block,
                            instruction: instruction.id,
                        });
                        released = true;
                    }
                    InsnType::Throw => {
                        let thrown = instruction
                            .args
                            .first()
                            .and_then(InsnArg::as_register)
                            .and_then(SsaVar::from_reg);
                        if !released
                            || !thrown.is_some_and(|value| {
                                self.canonical(origins.resolve(value))
                                    == self.canonical(origins.resolve(exception))
                            })
                        {
                            return Err(ReleaseProofError::InvalidRethrow(block));
                        }
                        terminal = true;
                        reached_throw = true;
                    }
                    _ if InstructionEffects::is_ssa_bookkeeping(instruction) => {}
                    _ => {
                        return Err(ReleaseProofError::UnexpectedInstruction {
                            block,
                            instruction: instruction.insn_type,
                        });
                    }
                }
            }
            if terminal {
                continue;
            }
            let successors = self.cfg.normal_successors(block).collect::<Vec<_>>();
            if successors.is_empty() {
                return Err(ReleaseProofError::UnreleasedTerminal(block));
            }
            if let Some(target) = successors.iter().find(|next| !owned.contains(next)) {
                return Err(ReleaseProofError::LeavesDomain {
                    block,
                    target: *target,
                });
            }
            pending.extend(
                successors
                    .into_iter()
                    .map(|next| (next, Some(block), released, origins.clone())),
            );
        }
        if !reached_throw {
            return Err(ReleaseProofError::MissingRethrow(handler.semantic_entry));
        }
        let lock = lock.ok_or(ReleaseProofError::MissingRelease(handler.semantic_entry))?;
        Ok(HandlerReleaseProof { lock, releases })
    }

    fn canonical(&self, value: SsaVar) -> SsaVar {
        let value = self.origins.unique(value).unwrap_or(value);
        self.identities.get(&value).copied().unwrap_or(value)
    }

    fn cleanup_domain(&self, entry: BlockId) -> BTreeSet<BlockId> {
        let mut domain = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if block != entry
                && (self.ordinary.contains(&block) || self.handler_entries.contains(&block))
            {
                continue;
            }
            if !domain.insert(block) {
                continue;
            }
            pending.extend(self.cfg.normal_successors(block));
        }
        domain
    }

    fn covers_throwables(handler: &CatchHandler) -> bool {
        handler.catch_type.is_none()
            || handler.catch_type.as_ref().and_then(|ty| ty.as_object())
                == Some("java/lang/Throwable")
    }

    fn reachable(cfg: &CFG, entry: BlockId) -> BTreeSet<BlockId> {
        let mut reachable = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if !reachable.insert(block) {
                continue;
            }
            pending.extend(cfg.normal_successors(block));
        }
        reachable
    }

    fn monitor_entry(&self, block: BlockId, cleanup_lock: SsaVar) -> Option<MonitorCandidate> {
        let node = self.cfg.block(block)?;
        let enters = node
            .insns
            .iter()
            .enumerate()
            .filter(|(_, instruction)| instruction.insn_type == InsnType::MonitorEnter)
            .collect::<Vec<_>>();
        let [(_, enter)] = enters.as_slice() else {
            return None;
        };
        let lock = enter.args.first()?.clone();
        (self.identity(&lock)? == cleanup_lock).then_some(())?;
        let successors = self.cfg.normal_successors(block).collect::<Vec<_>>();
        let [body_entry] = successors.as_slice() else {
            return None;
        };
        Some(MonitorCandidate {
            block,
            fact: SynchronizationFact {
                lock,
                body_entry: *body_entry,
                enter_origin: StatementOrigin {
                    block,
                    instruction: enter.id,
                },
                release_entries: BTreeSet::new(),
                release_origins: BTreeSet::new(),
                scope_blocks: BTreeSet::new(),
            },
        })
    }

    fn identity(&self, argument: &InsnArg) -> Option<SsaVar> {
        let value = argument.as_register().and_then(SsaVar::from_reg)?;
        self.identities.get(&value).copied()
    }
}

struct MonitorCandidate {
    block: BlockId,
    fact: SynchronizationFact,
}

impl MonitorCandidate {
    fn prove_scope(
        mut self,
        analysis: &SynchronizationAnalysis<'_>,
        release: &MonitorReleaseProof,
    ) -> Option<Self> {
        let scope = MonitorScopeFlow::new(
            analysis.cfg,
            &analysis.identities,
            &analysis.origins,
            release.lock,
            &release.entries(),
        )
        .analyze(self.fact.body_entry)
        .ok()?;
        if !scope
            .blocks
            .iter()
            .all(|owned| analysis.dominators.dominates(self.block, *owned))
        {
            return None;
        }
        if scope.reached_release_entries.is_empty() {
            return None;
        }
        self.fact.release_origins = scope
            .releases
            .into_iter()
            .chain(release.releases_for(&scope.reached_release_entries))
            .collect();
        self.fact.release_entries = scope.reached_release_entries;
        self.fact.scope_blocks = scope.blocks;
        Some(self)
    }

    fn is_protected_by(&self, cfg: &CFG, region: &TryRegion) -> bool {
        self.fact
            .scope_blocks
            .iter()
            .copied()
            .filter(|block| region.blocks.contains(block))
            .any(|block| {
                cfg.successors_with_kind(block)
                    .iter()
                    .any(|(target, kind)| {
                        kind.is_exception() && self.fact.release_entries.contains(target)
                    })
            })
    }
}

struct MonitorReleaseProof {
    lock: SsaVar,
    handler_releases: BTreeMap<BlockId, BTreeSet<StatementOrigin>>,
}

impl MonitorReleaseProof {
    fn entries(&self) -> BTreeSet<BlockId> {
        self.handler_releases.keys().copied().collect()
    }

    fn releases_for(&self, entries: &BTreeSet<BlockId>) -> BTreeSet<StatementOrigin> {
        entries
            .iter()
            .flat_map(|entry| {
                self.handler_releases
                    .get(entry)
                    .into_iter()
                    .flatten()
                    .cloned()
            })
            .collect()
    }
}

#[derive(Debug)]
struct HandlerReleaseProof {
    lock: SsaVar,
    releases: BTreeSet<StatementOrigin>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
struct ValueOrigins(BTreeMap<SsaVar, SsaVar>);

impl ValueOrigins {
    fn propagate(
        &mut self,
        instruction: &InsnNode,
        predecessor: Option<BlockId>,
        exception: Option<SsaVar>,
    ) {
        let Some(result) = instruction.result.as_ref().and_then(SsaVar::from_reg) else {
            return;
        };
        let source = match instruction.insn_type {
            InsnType::Phi => predecessor.and_then(|predecessor| {
                instruction
                    .payload
                    .phi_edges
                    .iter()
                    .zip(&instruction.args)
                    .find_map(|(&(source, _), argument)| {
                        (source == predecessor)
                            .then(|| argument.as_register().and_then(SsaVar::from_reg))
                            .flatten()
                    })
            }),
            InsnType::Move => instruction
                .args
                .first()
                .and_then(InsnArg::as_register)
                .and_then(SsaVar::from_reg),
            InsnType::MoveException => exception,
            _ => None,
        };
        self.0.remove(&result);
        if let Some(source) = source {
            self.0.insert(result, self.resolve(source));
        }
    }

    fn resolve(&self, value: SsaVar) -> SsaVar {
        self.0.get(&value).copied().unwrap_or(value)
    }
}

#[derive(Debug)]
enum ReleaseProofError {
    MissingEntry(BlockId),
    CyclicDomain(BlockId),
    MissingBlock(BlockId),
    MissingExceptionValue(BlockId),
    MissingLock(BlockId),
    MultipleReleases(BlockId),
    ConflictingLocks(BlockId),
    InvalidRethrow(BlockId),
    UnexpectedInstruction {
        block: BlockId,
        instruction: InsnType,
    },
    UnreleasedTerminal(BlockId),
    LeavesDomain {
        block: BlockId,
        target: BlockId,
    },
    MissingRethrow(BlockId),
    MissingRelease(BlockId),
}

struct MonitorScope {
    blocks: BTreeSet<BlockId>,
    releases: BTreeSet<StatementOrigin>,
    reached_release_entries: BTreeSet<BlockId>,
}

struct MonitorScopeFlow<'a> {
    cfg: &'a CFG,
    identities: &'a BTreeMap<SsaVar, SsaVar>,
    origins: &'a SsaOrigins,
    lock: SsaVar,
    release_entries: &'a BTreeSet<BlockId>,
}

impl<'a> MonitorScopeFlow<'a> {
    fn new(
        cfg: &'a CFG,
        identities: &'a BTreeMap<SsaVar, SsaVar>,
        origins: &'a SsaOrigins,
        lock: SsaVar,
        release_entries: &'a BTreeSet<BlockId>,
    ) -> Self {
        Self {
            cfg,
            identities,
            origins,
            lock,
            release_entries,
        }
    }

    fn analyze(&self, entry: BlockId) -> Result<MonitorScope, MonitorScopeError> {
        let mut depths = BTreeMap::<BlockId, u32>::new();
        let mut visited = BTreeSet::new();
        let mut blocks = BTreeSet::new();
        let mut releases = BTreeSet::new();
        let mut reached_release_entries = BTreeSet::new();
        let mut pending = vec![(entry, 1u32)];
        while let Some((block, depth)) = pending.pop() {
            if self.release_entries.contains(&block) {
                reached_release_entries.insert(block);
                continue;
            }
            match depths.get(&block) {
                Some(existing) if *existing != depth => {
                    return Err(MonitorScopeError::InconsistentDepth {
                        block,
                        existing: *existing,
                        incoming: depth,
                    });
                }
                Some(_) => {}
                None => {
                    depths.insert(block, depth);
                }
            }
            if !visited.insert((block, depth)) {
                continue;
            }
            blocks.insert(block);
            let transfer = self.transfer(block, depth)?;
            releases.extend(transfer.releases);
            let successors = self.cfg.successors_with_kind(block);
            if successors.is_empty() {
                if transfer.normal.is_some() {
                    return Err(MonitorScopeError::UnreleasedTerminal(block));
                }
                continue;
            }
            for &(target, kind) in successors {
                if kind.is_exception() && self.release_entries.contains(&target) {
                    reached_release_entries.insert(target);
                    continue;
                }
                let depth = if kind.is_exception() {
                    let Some(depth) = transfer.exceptional else {
                        continue;
                    };
                    if depth == 0 {
                        continue;
                    }
                    depth
                } else {
                    let Some(depth) = transfer.normal else {
                        continue;
                    };
                    depth
                };
                pending.push((target, depth));
            }
        }
        if reached_release_entries.is_empty() && releases.is_empty() {
            return Err(MonitorScopeError::MissingRelease);
        }
        Ok(MonitorScope {
            blocks,
            releases,
            reached_release_entries,
        })
    }

    fn transfer(
        &self,
        block: BlockId,
        mut depth: u32,
    ) -> Result<MonitorDepthTransfer, MonitorScopeError> {
        let body = self
            .cfg
            .block(block)
            .ok_or(MonitorScopeError::MissingBlock(block))?;
        let mut exceptional = None;
        let mut releases = BTreeSet::new();
        for instruction in &body.insns {
            let scope_release = instruction.insn_type == InsnType::MonitorExit
                && self.is_scope_lock(
                    instruction
                        .args
                        .first()
                        .ok_or(MonitorScopeError::MalformedMonitor(block))?,
                );
            // Once lock identity and all-path balance are proven, an
            // IllegalMonitorStateException edge from the compiler-generated
            // release is infeasible in source-level synchronized semantics.
            if instruction.can_throw() && !scope_release {
                let exceptional_depth = depth;
                match exceptional {
                    Some(existing) if existing != exceptional_depth => {
                        return Err(MonitorScopeError::InconsistentExceptionalDepth(block));
                    }
                    Some(_) => {}
                    None => exceptional = Some(exceptional_depth),
                }
            }
            match instruction.insn_type {
                InsnType::MonitorEnter => {
                    let lock = instruction
                        .args
                        .first()
                        .ok_or(MonitorScopeError::MalformedMonitor(block))?;
                    if self.is_scope_lock(lock) {
                        depth = depth
                            .checked_add(1)
                            .ok_or(MonitorScopeError::DepthOverflow(block))?;
                    }
                }
                InsnType::MonitorExit if scope_release => {
                    let before = depth;
                    depth = depth
                        .checked_sub(1)
                        .ok_or(MonitorScopeError::DepthUnderflow(block))?;
                    if before == 1 {
                        releases.insert(StatementOrigin {
                            block,
                            instruction: instruction.id,
                        });
                    }
                }
                _ => {}
            }
            if depth == 0 {
                break;
            }
        }
        Ok(MonitorDepthTransfer {
            normal: (depth != 0).then_some(depth),
            exceptional,
            releases,
        })
    }

    fn is_scope_lock(&self, argument: &InsnArg) -> bool {
        argument
            .as_register()
            .and_then(SsaVar::from_reg)
            .map(|value| self.origins.unique(value).unwrap_or(value))
            .map(|value| self.identities.get(&value).copied().unwrap_or(value))
            .is_some_and(|identity| identity == self.lock)
    }
}

#[derive(Debug)]
enum MonitorScopeError {
    MissingBlock(BlockId),
    MalformedMonitor(BlockId),
    InconsistentDepth {
        block: BlockId,
        existing: u32,
        incoming: u32,
    },
    InconsistentExceptionalDepth(BlockId),
    UnreleasedTerminal(BlockId),
    DepthOverflow(BlockId),
    DepthUnderflow(BlockId),
    MissingRelease,
}

struct MonitorDepthTransfer {
    normal: Option<u32>,
    exceptional: Option<u32>,
    releases: BTreeSet<StatementOrigin>,
}
