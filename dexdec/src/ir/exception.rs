//! Exception-region ownership derived from DEX metadata and CFG dataflow.
//!
//! The analysis never reconstructs `try`, `finally`, or synchronized cleanup
//! from instruction-tail templates. Protected ownership comes from native DEX
//! intervals, handler ownership comes from normal-flow reachability, and a
//! catch-all handler is classified by an all-path exceptional-value analysis.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;

#[path = "exception/cleanup.rs"]
mod cleanup;

use cleanup::CleanupRecovery;
pub use cleanup::{
    CleanupMismatchDiagnostic, CleanupMismatchReason, CleanupProofDiagnostic, CleanupProofOutcome,
};

use super::analysis::{
    DominanceError, DominatorTree, InstructionEffects, LexicalBoundaryAnalysis, SsaValueGraph,
    SsaVar, SubtypeRelation, ThrowEffect, TypeHierarchy,
};
use super::semantic::StatementOrigin;
use super::{ArgType, BlockId, EdgeKind, InsnArg, InsnType, MemberReference, RegisterArg, CFG};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum HandlerKind {
    Catch,
    Finally,
    Cleanup,
}

#[derive(Debug, Clone)]
pub struct CatchHandler {
    pub id: u32,
    pub catch_type: Option<super::ArgType>,
    pub handler_offset: u32,
    /// Physical DEX dispatch entries represented by this source-level handler.
    pub entry_blocks: BTreeSet<BlockId>,
    pub handler_block: BlockId,
    /// Entry of the source-level handler body after equivalent dispatch
    /// adapters have been coalesced.
    pub semantic_entry: BlockId,
    /// First non-bookkeeping continuation of the physical handler entry.
    pub canonical_entry: BlockId,
    /// SSA-only dispatch blocks contracted into `semantic_entry`.
    pub adapter_blocks: BTreeSet<BlockId>,
    pub blocks: Vec<BlockId>,
    /// Normal-flow domain used for semantic proofs. Unlike `blocks`, this may
    /// overlap another handler or an ordinary continuation.
    pub semantic_blocks: Vec<BlockId>,
    pub lexical_blocks: Vec<BlockId>,
    pub continuation: Option<BlockId>,
    pub exception_value: Option<RegisterArg>,
    pub canonical_exception_value: Option<RegisterArg>,
    pub rethrow_blocks: BTreeSet<BlockId>,
    pub kind: HandlerKind,
}

impl CatchHandler {
    pub fn is_catch_all(&self) -> bool {
        self.catch_type.is_none()
    }

    pub fn is_cleanup(&self) -> bool {
        self.kind == HandlerKind::Cleanup
    }

    pub fn is_source_finally(&self) -> bool {
        self.kind == HandlerKind::Finally
    }
}

#[derive(Debug, Clone)]
pub struct TryRegion {
    pub id: u32,
    pub start_offset: u32,
    pub end_offset: u32,
    pub blocks: Vec<BlockId>,
    pub handlers: Vec<CatchHandler>,
    pub parent: Option<u32>,
    pub children: Vec<u32>,
    pub normal_exit_blocks: Vec<BlockId>,
}

impl TryRegion {
    pub fn has_finally(&self) -> bool {
        self.handlers
            .iter()
            .any(|handler| handler.kind != HandlerKind::Catch)
    }

    pub fn finally_handler(&self) -> Option<&CatchHandler> {
        self.handlers
            .iter()
            .find(|handler| handler.kind != HandlerKind::Catch)
    }

    pub fn catch_handlers(&self) -> impl Iterator<Item = &CatchHandler> {
        self.handlers
            .iter()
            .filter(|handler| handler.kind == HandlerKind::Catch)
    }
}

#[derive(Debug, Clone)]
pub struct CleanupContraction {
    pub entry: BlockId,
    pub blocks: BTreeSet<BlockId>,
    pub completion: BlockId,
}

#[derive(Debug, Clone, Default)]
pub struct ExceptionAnalysis {
    pub regions: Vec<TryRegion>,
    pub block_to_regions: BTreeMap<BlockId, Vec<u32>>,
    pub handler_blocks: BTreeSet<BlockId>,
    pub handler_adapters: BTreeMap<BlockId, BlockId>,
    pub elided_instructions: BTreeSet<super::semantic::StatementOrigin>,
    pub cleanup_contractions: Vec<CleanupContraction>,
    pub cleanup_value_bindings: BTreeSet<(SsaVar, SsaVar)>,
    pub cleanup_proofs: Vec<CleanupProofDiagnostic>,
}

impl ExceptionAnalysis {
    pub fn is_in_try(&self, block: BlockId) -> bool {
        self.block_to_regions.contains_key(&block)
    }

    pub fn get_regions(&self, block: BlockId) -> Vec<&TryRegion> {
        self.block_to_regions
            .get(&block)
            .into_iter()
            .flatten()
            .filter_map(|id| self.region(*id))
            .collect()
    }

    pub fn is_handler_entry(&self, block: BlockId) -> bool {
        self.regions.iter().any(|region| {
            region
                .handlers
                .iter()
                .any(|handler| handler.entry_blocks.contains(&block))
        })
    }

    pub fn top_level_regions(&self) -> impl Iterator<Item = &TryRegion> {
        self.regions.iter().filter(|region| region.parent.is_none())
    }

    pub fn region(&self, id: u32) -> Option<&TryRegion> {
        self.regions.iter().find(|region| region.id == id)
    }

    pub fn regions_innermost_first(&self) -> impl Iterator<Item = &TryRegion> {
        let mut regions = self.regions.iter().collect::<Vec<_>>();
        regions.sort_by_key(|region| std::cmp::Reverse(self.depth(region.id)));
        regions.into_iter()
    }

    fn depth(&self, mut id: u32) -> usize {
        let mut depth = 0;
        while let Some(parent) = self.region(id).and_then(|region| region.parent) {
            depth += 1;
            id = parent;
        }
        depth
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ClauseKey(Vec<(Option<super::ArgType>, u32)>);

struct RawRegion {
    start: u32,
    end: u32,
    blocks: BTreeSet<BlockId>,
    clauses: Vec<usize>,
    key: ClauseKey,
}

struct ExceptionScope {
    id: u32,
    start: u32,
    end: u32,
    blocks: BTreeSet<BlockId>,
    clauses: Vec<usize>,
    parent: Option<u32>,
    children: Vec<u32>,
}

#[derive(Default)]
struct NestedHandlerDomains {
    all: BTreeMap<u32, BTreeSet<BlockId>>,
    cleanup: BTreeMap<u32, BTreeSet<BlockId>>,
}

impl NestedHandlerDomains {
    fn analyze(regions: &[TryRegion]) -> Self {
        let by_id = regions
            .iter()
            .map(|region| (region.id, region))
            .collect::<BTreeMap<_, _>>();
        let mut domains = Self::default();
        for owner in regions {
            let mut pending = owner.children.clone();
            let mut visited = BTreeSet::new();
            while let Some(child) = pending.pop() {
                if !visited.insert(child) {
                    continue;
                }
                let Some(region) = by_id.get(&child).copied() else {
                    continue;
                };
                for handler in &region.handlers {
                    let blocks = handler
                        .blocks
                        .iter()
                        .chain(&handler.adapter_blocks)
                        .chain(&handler.entry_blocks)
                        .copied()
                        .chain([handler.semantic_entry, handler.canonical_entry])
                        .collect::<BTreeSet<_>>();
                    domains
                        .all
                        .entry(owner.id)
                        .or_default()
                        .extend(blocks.iter().copied());
                    if handler.kind != HandlerKind::Catch {
                        domains.cleanup.entry(owner.id).or_default().extend(blocks);
                    }
                }
                pending.extend(region.children.iter().copied());
            }
        }
        domains
    }

    fn all(&self, region: u32) -> BTreeSet<BlockId> {
        self.all.get(&region).cloned().unwrap_or_default()
    }

    fn cleanup(&self, region: u32) -> BTreeSet<BlockId> {
        self.cleanup.get(&region).cloned().unwrap_or_default()
    }
}

pub struct ExceptionAnalyzer<'a> {
    cfg: &'a CFG,
    values: &'a SsaValueGraph,
    handler_entries: BTreeMap<u32, BlockId>,
    ordinary_reachable: BTreeSet<BlockId>,
    normal_predecessors: BTreeMap<BlockId, Vec<BlockId>>,
    synthetic_closure: SyntheticScopeClosure,
    hierarchy: &'a dyn TypeHierarchy,
}

#[derive(Debug, Clone)]
pub enum ExceptionInvariantError {
    Dominance(DominanceError),
    MissingCoverage(BlockId),
    MissingHandlerEntry(u32),
    NonExclusiveHandler(BlockId),
    MissingHandlerBlock(BlockId),
    MissingCleanupBlock(BlockId),
    MultipleExceptionValues(BlockId),
    ExceptionValueWithoutResult(BlockId),
    ExceptionValueWithoutSsa(BlockId),
    OverlappingProtectedRanges {
        left_end: u32,
        right_start: u32,
    },
    MissingHandlerStackRepresentative,
    MissingExceptionScope(u32),
    ProtectedHandlerEntryOverlap {
        handler: BlockId,
        region: u32,
    },
    ConflictingHandlerAdapter {
        block: BlockId,
        left: BlockId,
        right: BlockId,
    },
}

impl fmt::Display for ExceptionInvariantError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Dominance(error) => error.fmt(formatter),
            Self::MissingCoverage(block) => {
                write!(
                    formatter,
                    "block {block} has no captured exception coverage"
                )
            }
            Self::MissingHandlerEntry(offset) => {
                write!(
                    formatter,
                    "exception handler at offset {offset} has no CFG entry"
                )
            }
            Self::NonExclusiveHandler(block) => {
                write!(
                    formatter,
                    "handler entry {block} has no exclusive ownership"
                )
            }
            Self::MissingHandlerBlock(block) => write!(formatter, "missing handler block {block}"),
            Self::MissingCleanupBlock(block) => {
                write!(formatter, "missing normal cleanup block {block}")
            }
            Self::MultipleExceptionValues(block) => {
                write!(
                    formatter,
                    "handler entry {block} defines multiple exception values"
                )
            }
            Self::ExceptionValueWithoutResult(block) => {
                write!(formatter, "move-exception in {block} has no result")
            }
            Self::ExceptionValueWithoutSsa(block) => {
                write!(formatter, "move-exception in {block} has no SSA identity")
            }
            Self::OverlappingProtectedRanges {
                left_end,
                right_start,
            } => write!(
                formatter,
                "DEX protected ranges overlap at {right_start} before prior end {left_end}"
            ),
            Self::MissingHandlerStackRepresentative => {
                formatter.write_str("exception scope has no representative handler stack")
            }
            Self::MissingExceptionScope(region) => {
                write!(
                    formatter,
                    "missing exception scope {region} during coalescing"
                )
            }
            Self::ProtectedHandlerEntryOverlap { handler, region } => write!(
                formatter,
                "handler entry {handler} partially overlaps protected scope {region}"
            ),
            Self::ConflictingHandlerAdapter { block, left, right } => write!(
                formatter,
                "handler adapter {block} resolves to both {left} and {right}"
            ),
        }
    }
}

impl std::error::Error for ExceptionInvariantError {}

impl<'a> ExceptionAnalyzer<'a> {
    pub fn new(cfg: &'a CFG, values: &'a SsaValueGraph, hierarchy: &'a dyn TypeHierarchy) -> Self {
        let handler_entries = cfg
            .handlers
            .iter()
            .filter_map(|handler| {
                cfg.blocks
                    .values()
                    .find(|block| !block.synthetic && block.offset == handler.handler)
                    .map(|block| (handler.handler, block.id))
            })
            .collect();
        let ordinary_reachable = Self::normal_reachable(cfg, cfg.entry);
        let normal_predecessors = cfg.normal_predecessor_snapshot();
        let synthetic_closure = SyntheticScopeClosure::analyze(cfg, &normal_predecessors);
        Self {
            cfg,
            values,
            handler_entries,
            ordinary_reachable,
            normal_predecessors,
            synthetic_closure,
            hierarchy,
        }
    }

    pub fn analyze(&self) -> Result<ExceptionAnalysis, ExceptionInvariantError> {
        for block in self.cfg.block_ids() {
            if !self.cfg.has_exception_coverage(block) {
                return Err(ExceptionInvariantError::MissingCoverage(block));
            }
        }
        for clause in &self.cfg.handlers {
            if !self.handler_entries.contains_key(&clause.handler) {
                return Err(ExceptionInvariantError::MissingHandlerEntry(clause.handler));
            }
        }
        let scopes = HandlerStackForest::new(self).build(self.raw_regions())?;
        let ownership =
            HandlerBodies::new(self.cfg, &self.handler_entries, &self.ordinary_reachable);
        let semantics = HandlerSemanticDomains::analyze(self.cfg, &self.handler_entries);
        let mut handler_adapters = semantics.adapter_map()?;
        let mut regions = scopes
            .into_iter()
            .map(|scope| self.build_region(scope, &ownership, &semantics))
            .collect::<Result<Vec<_>, _>>()?;
        SharedHandlerDomains::analyze(self.cfg, &regions).apply(&mut regions);
        let mut regions = ExceptionScopeNormalization::new(self.cfg).apply(regions)?;
        let normal_dominators = DominatorTree::compute_normal(
            self.cfg,
            self.cfg.block_ids(),
            &self.normal_predecessors,
        )
        .map_err(ExceptionInvariantError::Dominance)?;
        HandlerDomains::assign(self.cfg, &mut regions);
        let nested_handlers = NestedHandlerDomains::analyze(&regions);
        let recovery_order = Self::cleanup_recovery_order(&regions);

        let mut elided_instructions = BTreeSet::new();
        let mut cleanup_contractions = Vec::new();
        let mut cleanup_value_bindings = BTreeSet::new();
        let mut cleanup_proofs = Vec::new();
        let mut cleanup_representatives = BTreeMap::new();
        for region_id in recovery_order {
            let region = regions
                .iter_mut()
                .find(|region| region.id == region_id)
                .ok_or(ExceptionInvariantError::MissingExceptionScope(region_id))?;
            let nested_cleanup = nested_handlers.cleanup(region.id);
            let nested_all = nested_handlers.all(region.id);
            let cleanup = CleanupRecovery::new(self.cfg, self.values, &normal_dominators).recover(
                region,
                &nested_cleanup,
                &nested_all,
                &cleanup_representatives,
            )?;
            elided_instructions.extend(cleanup.elided);
            cleanup_value_bindings.extend(cleanup.value_bindings);
            cleanup_proofs.extend(cleanup.diagnostics);
            for contraction in &cleanup.normal_contractions {
                for block in &contraction.blocks {
                    cleanup_representatives.insert(*block, contraction.completion);
                }
            }
            for contraction in cleanup.contractions {
                cleanup_contractions.push(contraction);
            }
            for handler in &region.handlers {
                for entry in &handler.entry_blocks {
                    let block = self
                        .cfg
                        .block(*entry)
                        .ok_or(ExceptionInvariantError::MissingHandlerBlock(*entry))?;
                    elided_instructions.extend(
                        block
                            .insns
                            .iter()
                            .filter(|instruction| instruction.insn_type == InsnType::MoveException)
                            .map(|instruction| StatementOrigin {
                                block: *entry,
                                instruction: instruction.id,
                            }),
                    );
                }
            }
        }
        // Cleanup recovery changes the exceptional continuation graph: a
        // protected block may reach an outer handler only after executing a
        // cleanup handler and rethrowing. Recompute the lexical hierarchy from
        // those semantic facts before partitioning handler ownership.
        regions = ExceptionScopeNormalization::new(self.cfg).apply(regions)?;
        HandlerDomains::assign(self.cfg, &mut regions);
        ElidedHandlerTails::new(self.cfg, &elided_instructions).trim(&mut regions);
        regions = ElidedExceptionScopes::prune(self.cfg, regions, &elided_instructions);
        PrecedingHandlerProtectionArtifacts::prune(
            self.cfg,
            &mut regions,
            self.hierarchy,
            self.values,
        );
        HandlerProtectedPartition::apply(self.cfg, &mut regions)?;
        HandlerDomains::assign(self.cfg, &mut regions);
        let live_handler_adapters = regions
            .iter()
            .flat_map(|region| &region.handlers)
            .flat_map(|handler| {
                handler
                    .entry_blocks
                    .iter()
                    .chain(&handler.adapter_blocks)
                    .copied()
            })
            .collect::<BTreeSet<_>>();
        handler_adapters.retain(|block, _| live_handler_adapters.contains(block));

        let mut analysis = ExceptionAnalysis {
            regions,
            handler_adapters,
            elided_instructions,
            cleanup_contractions,
            cleanup_value_bindings,
            cleanup_proofs,
            ..ExceptionAnalysis::default()
        };
        for region in &analysis.regions {
            for block in &region.blocks {
                analysis
                    .block_to_regions
                    .entry(*block)
                    .or_default()
                    .push(region.id);
            }
            for handler in &region.handlers {
                analysis
                    .handler_blocks
                    .extend(handler.blocks.iter().copied());
            }
        }
        Ok(analysis)
    }

    fn cleanup_recovery_order(regions: &[TryRegion]) -> Vec<u32> {
        let parents = regions
            .iter()
            .map(|region| (region.id, region.parent))
            .collect::<BTreeMap<_, _>>();
        let mut order = regions
            .iter()
            .map(|region| {
                let mut depth = 0usize;
                let mut current = region.parent;
                let mut visited = BTreeSet::new();
                while let Some(parent) = current {
                    if !visited.insert(parent) {
                        break;
                    }
                    depth += 1;
                    current = parents.get(&parent).copied().flatten();
                }
                (depth, region.start_offset, region.id)
            })
            .collect::<Vec<_>>();
        order.sort_by_key(|(depth, start, id)| (std::cmp::Reverse(*depth), *start, *id));
        order.into_iter().map(|(_, _, id)| id).collect()
    }

    fn raw_regions(&self) -> Vec<RawRegion> {
        let mut groups: BTreeMap<(u32, u32), Vec<usize>> = BTreeMap::new();
        for (index, handler) in self.cfg.handlers.iter().enumerate() {
            groups
                .entry((handler.start, handler.end))
                .or_default()
                .push(index);
        }
        groups
            .into_iter()
            .map(|((start, end), clauses)| {
                let own_entries = clauses
                    .iter()
                    .filter_map(|index| {
                        self.handler_entries.get(&self.cfg.handlers[*index].handler)
                    })
                    .copied()
                    .collect::<BTreeSet<_>>();
                let blocks = self
                    .cfg
                    .block_ids()
                    .into_iter()
                    .filter(|block| !own_entries.contains(block))
                    .filter(|block| self.cfg.exception_coverage(*block).contains(&(start, end)))
                    .collect();
                let key = ClauseKey(
                    clauses
                        .iter()
                        .map(|index| {
                            let handler = &self.cfg.handlers[*index];
                            (handler.catch_type.clone(), handler.handler)
                        })
                        .collect(),
                );
                RawRegion {
                    start,
                    end,
                    blocks,
                    clauses,
                    key,
                }
            })
            .collect()
    }

    fn build_region(
        &self,
        scope: ExceptionScope,
        ownership: &HandlerBodies,
        domains: &HandlerSemanticDomains,
    ) -> Result<TryRegion, ExceptionInvariantError> {
        let mut handlers = scope
            .clauses
            .iter()
            .map(|index| {
                let clause = &self.cfg.handlers[*index];
                let entry = *self
                    .handler_entries
                    .get(&clause.handler)
                    .ok_or(ExceptionInvariantError::MissingHandlerEntry(clause.handler))?;
                let blocks = ownership.blocks(entry);
                if !blocks.contains(&entry) {
                    return Err(ExceptionInvariantError::NonExclusiveHandler(entry));
                }
                let domain = domains.domain(entry);
                let semantics = HandlerSemantics::analyze(
                    self.cfg,
                    entry,
                    &domain.blocks,
                    domain.canonical_entry,
                )?;
                let kind = if clause.catch_type.is_some() {
                    HandlerKind::Catch
                } else {
                    semantics.kind()
                };
                Ok(CatchHandler {
                    id: *index as u32,
                    catch_type: clause.catch_type.clone(),
                    handler_offset: clause.handler,
                    entry_blocks: BTreeSet::from([entry]),
                    handler_block: entry,
                    semantic_entry: entry,
                    canonical_entry: domain.canonical_entry,
                    adapter_blocks: domain.adapter_blocks,
                    blocks: blocks.into_iter().collect(),
                    semantic_blocks: domain.blocks.into_iter().collect(),
                    lexical_blocks: Vec::new(),
                    continuation: None,
                    exception_value: semantics.exception_value,
                    canonical_exception_value: semantics.canonical_exception_value,
                    rethrow_blocks: semantics.rethrow_blocks,
                    kind,
                })
            })
            .collect::<Result<Vec<_>, ExceptionInvariantError>>()?;
        let physical_handler_entries = self
            .handler_entries
            .values()
            .copied()
            .collect::<BTreeSet<_>>();
        for handler in &mut handlers {
            if SharedExceptionContinuation::is_shared(
                self.cfg,
                &scope.blocks,
                handler,
                &self.ordinary_reachable,
                &physical_handler_entries,
            ) {
                handler.blocks.retain(|block| {
                    *block == handler.handler_block || handler.adapter_blocks.contains(block)
                });
            }
        }
        let handler_blocks = handlers
            .iter()
            .flat_map(|handler| handler.blocks.iter().copied())
            .collect::<BTreeSet<_>>();
        let mut protected_blocks = scope
            .blocks
            .difference(&handler_blocks)
            .copied()
            .collect::<BTreeSet<_>>();
        self.synthetic_closure.expand(&mut protected_blocks);
        let handler_stack = ClauseKey(
            scope
                .clauses
                .iter()
                .map(|index| {
                    let clause = &self.cfg.handlers[*index];
                    (clause.catch_type.clone(), clause.handler)
                })
                .collect(),
        );
        self.close_handler_entry_prefixes(&handler_stack, ownership, &mut protected_blocks);
        self.close_transparent_reentries(&handler_stack, &handler_blocks, &mut protected_blocks);
        self.synthetic_closure.expand(&mut protected_blocks);
        let normal_exit_blocks = protected_blocks
            .iter()
            .copied()
            .filter(|source| {
                self.cfg.normal_successors(*source).any(|target| {
                    !protected_blocks.contains(&target) && !handler_blocks.contains(&target)
                })
            })
            .collect();
        Ok(TryRegion {
            id: scope.id,
            start_offset: scope.start,
            end_offset: scope.end,
            blocks: protected_blocks.into_iter().collect(),
            handlers,
            parent: scope.parent,
            children: scope.children,
            normal_exit_blocks,
        })
    }

    fn close_handler_entry_prefixes(
        &self,
        handlers: &ClauseKey,
        ownership: &HandlerBodies,
        protected: &mut BTreeSet<BlockId>,
    ) {
        let paths = NormalPathClosure::new(self.cfg, &self.normal_predecessors);
        for (entry, owned) in ownership.handlers() {
            let targets = owned
                .intersection(protected)
                .copied()
                .collect::<BTreeSet<_>>();
            if targets.is_empty() || owned.is_subset(protected) {
                continue;
            }
            let candidates = owned
                .difference(protected)
                .copied()
                .filter(|block| self.block_is_transparent(*block, handlers))
                .collect::<BTreeSet<_>>();
            if let Some(prefix) = paths.between(&BTreeSet::from([entry]), &targets, &candidates) {
                protected.extend(prefix);
            }
        }
    }

    fn block_is_transparent(&self, block: BlockId, handlers: &ClauseKey) -> bool {
        self.cfg.block(block).is_some_and(|block| {
            block
                .insns
                .iter()
                .filter(|instruction| !instruction.payload.edge_copy)
                .all(|instruction| {
                    GapFacts::is_transparent(
                        ThrowEffect::of_tree(instruction),
                        handlers,
                        self.hierarchy,
                    )
                })
        })
    }

    fn close_transparent_reentries(
        &self,
        handlers: &ClauseKey,
        handler_blocks: &BTreeSet<BlockId>,
        protected: &mut BTreeSet<BlockId>,
    ) {
        let candidates = self
            .cfg
            .block_ids()
            .into_iter()
            .filter(|block| !protected.contains(block) && !handler_blocks.contains(block))
            .filter(|block| self.block_is_transparent(*block, handlers))
            .collect::<BTreeSet<_>>();
        let paths = NormalPathClosure::new(self.cfg, &self.normal_predecessors);
        protected.extend(paths.reentries(protected, &candidates));
    }

    fn normal_reachable(cfg: &CFG, entry: BlockId) -> BTreeSet<BlockId> {
        let mut reachable = BTreeSet::new();
        let mut work = vec![entry];
        while let Some(block) = work.pop() {
            if reachable.insert(block) {
                work.extend(cfg.normal_successors(block));
            }
        }
        reachable
    }
}

/// Removes a source-layout artifact created when two lexical try statements
/// are adjacent but the first statement's handler is emitted inside the
/// second statement's physical DEX range. The later range has a raw exception
/// edge from that handler, but the detached handler is not part of the later
/// source try statement. Pruning requires every terminal path through the
/// preceding handler to throw a known type that the later handlers cannot
/// catch; a matching throw proves that the ranges are lexically nested instead.
struct PrecedingHandlerProtectionArtifacts;

impl PrecedingHandlerProtectionArtifacts {
    fn prune(
        cfg: &CFG,
        regions: &mut [TryRegion],
        hierarchy: &dyn TypeHierarchy,
        values: &SsaValueGraph,
    ) {
        let snapshots = regions.to_vec();
        for protected in regions {
            // A catch-all range commonly protects monitor-exit or resource
            // cleanup emitted in an earlier handler. That ownership is
            // intentional even when the ranges happen to be adjacent.
            if protected
                .handlers
                .iter()
                .any(|handler| handler.catch_type.is_none())
            {
                continue;
            }
            let own_handlers = protected
                .handlers
                .iter()
                .map(|handler| handler.canonical_entry)
                .collect::<BTreeSet<_>>();
            let protected_handlers = ClauseKey(
                protected
                    .handlers
                    .iter()
                    .map(|handler| (handler.catch_type.clone(), handler.handler_offset))
                    .collect(),
            );
            let protected_blocks = protected.blocks.iter().copied().collect::<BTreeSet<_>>();
            let artifacts = snapshots
                .iter()
                .filter(|owner| owner.id != protected.id)
                .filter(|owner| owner.end_offset == protected.start_offset)
                .flat_map(|owner| &owner.handlers)
                .filter(|handler| !own_handlers.contains(&handler.canonical_entry))
                .filter(|handler| Self::detached(cfg, handler, &protected_blocks))
                .filter(|handler| {
                    Self::terminal_throws_escape(
                        cfg,
                        handler,
                        &protected_handlers,
                        hierarchy,
                        values,
                    )
                })
                .flat_map(|handler| {
                    handler
                        .blocks
                        .iter()
                        .chain(&handler.entry_blocks)
                        .chain(&handler.adapter_blocks)
                        .copied()
                })
                .collect::<BTreeSet<_>>();
            protected.blocks.retain(|block| !artifacts.contains(block));
        }
    }

    fn detached(cfg: &CFG, handler: &CatchHandler, protected: &BTreeSet<BlockId>) -> bool {
        let domain = handler
            .blocks
            .iter()
            .chain(&handler.entry_blocks)
            .chain(&handler.adapter_blocks)
            .copied()
            .collect::<BTreeSet<_>>();
        !domain.is_empty()
            && domain.iter().all(|block| {
                cfg.normal_successors(*block)
                    .all(|target| domain.contains(&target) || !protected.contains(&target))
            })
    }

    fn terminal_throws_escape(
        cfg: &CFG,
        handler: &CatchHandler,
        protected_handlers: &ClauseKey,
        hierarchy: &dyn TypeHierarchy,
        values: &SsaValueGraph,
    ) -> bool {
        let domain = handler
            .blocks
            .iter()
            .chain(&handler.entry_blocks)
            .chain(&handler.adapter_blocks)
            .copied()
            .collect::<BTreeSet<_>>();
        let mut saw_terminal = false;
        for block in &domain {
            if cfg
                .normal_successors(*block)
                .any(|target| domain.contains(&target))
            {
                continue;
            }
            let Some(terminal) = cfg.block(*block).and_then(|block| block.terminator()) else {
                return false;
            };
            if terminal.insn_type != InsnType::Throw {
                return false;
            }
            let Some(thrown) = terminal
                .args
                .first()
                .and_then(|argument| Self::thrown_type(cfg, values, argument))
            else {
                return false;
            };
            if protected_handlers.catches(thrown, hierarchy) {
                return false;
            }
            saw_terminal = true;
        }
        saw_terminal
    }

    fn thrown_type<'cfg>(
        cfg: &'cfg CFG,
        values: &SsaValueGraph,
        argument: &'cfg InsnArg,
    ) -> Option<&'cfg str> {
        if let Some(ty) = argument.declared_type().and_then(ArgType::as_object) {
            return Some(ty);
        }
        let value = argument
            .as_register()
            .and_then(SsaVar::from_reg)
            .and_then(|value| values.value(value))?;
        let definition = value.definition?;
        let instruction = cfg
            .block(definition.block)
            .and_then(|block| block.insns.get(definition.index))?;
        instruction
            .result
            .as_ref()
            .and_then(|result| result.ty.as_object())
            .or_else(|| {
                instruction
                    .payload
                    .class_type
                    .as_ref()
                    .and_then(ArgType::as_object)
            })
            .or_else(|| match instruction.payload.reference.as_ref() {
                Some(MemberReference::Method(method)) if method.is_constructor() => {
                    method.owner.as_object()
                }
                _ => None,
            })
    }
}

struct HandlerStackForest<'analysis, 'cfg> {
    analyzer: &'analysis ExceptionAnalyzer<'cfg>,
}

impl<'analysis, 'cfg> HandlerStackForest<'analysis, 'cfg> {
    fn new(analyzer: &'analysis ExceptionAnalyzer<'cfg>) -> Self {
        Self { analyzer }
    }

    fn build(
        &self,
        mut segments: Vec<RawRegion>,
    ) -> Result<Vec<ExceptionScope>, ExceptionInvariantError> {
        segments.sort_by_key(|segment| (segment.start, segment.end));
        let representatives = segments
            .iter()
            .map(|segment| (segment.key.clone(), segment.clauses.clone()))
            .collect::<BTreeMap<_, _>>();
        let keys = representatives.keys().cloned().collect::<Vec<_>>();
        let mut scopes = Vec::<ExceptionScope>::new();
        let mut active = Vec::<(ClauseKey, u32)>::new();
        let mut previous_end = None;

        for segment in segments {
            if let Some(left_end) = previous_end.filter(|end| *end > segment.start) {
                return Err(ExceptionInvariantError::OverlappingProtectedRanges {
                    left_end,
                    right_start: segment.start,
                });
            }

            let chain = Self::scope_chain(&keys, &segment.key);
            let mut common = active
                .iter()
                .zip(&chain)
                .take_while(|((active_key, _), expected)| active_key == *expected)
                .count();
            let gap = previous_end.filter(|end| *end <= segment.start).map(|end| {
                GapFacts::analyze(
                    self.analyzer.cfg,
                    &self.analyzer.normal_predecessors,
                    end,
                    segment.start,
                )
            });
            if let Some(gap) = &gap {
                let bridges = active
                    .iter()
                    .take(common)
                    .map_while(|(key, id)| {
                        gap.bridge(
                            key,
                            self.analyzer.hierarchy,
                            &scopes[*id as usize].blocks,
                            &segment.blocks,
                        )
                        .map(|blocks| (*id, blocks))
                    })
                    .collect::<Vec<_>>();
                common = bridges.len();
                for (id, blocks) in bridges {
                    let scope = &mut scopes[id as usize];
                    scope.blocks.extend(blocks);
                    scope.end = scope.end.max(segment.start);
                }
            } else if previous_end.is_some() {
                common = 0;
            }
            active.truncate(common);

            for key in chain.into_iter().skip(common) {
                let parent = active.last().map(|(_, id)| *id);
                let inherited_clause_count = active.last().map_or(0, |(parent, _)| {
                    parent
                        .is_suffix_of(&key)
                        .then_some(parent.0.len())
                        .unwrap_or(0)
                });
                let full_clauses = representatives
                    .get(&key)
                    .ok_or(ExceptionInvariantError::MissingHandlerStackRepresentative)?;
                let local_clause_count = key.0.len() - inherited_clause_count;
                let id = scopes.len() as u32;
                scopes.push(ExceptionScope {
                    id,
                    start: segment.start,
                    end: segment.end,
                    blocks: BTreeSet::new(),
                    clauses: full_clauses
                        .iter()
                        .take(local_clause_count)
                        .copied()
                        .collect(),
                    parent,
                    children: Vec::new(),
                });
                if let Some(parent) = parent {
                    scopes[parent as usize].children.push(id);
                }
                active.push((key, id));
            }

            for (_, id) in &active {
                let scope = &mut scopes[*id as usize];
                scope.start = scope.start.min(segment.start);
                scope.end = scope.end.max(segment.end);
                scope.blocks.extend(segment.blocks.iter().copied());
            }
            previous_end = Some(segment.end);
        }
        Ok(scopes)
    }

    fn scope_chain(keys: &[ClauseKey], stack: &ClauseKey) -> Vec<ClauseKey> {
        let mut chain = keys
            .iter()
            .filter(|candidate| candidate.is_suffix_of(stack))
            .cloned()
            .collect::<Vec<_>>();
        chain.sort_by_key(|key| key.0.len());
        chain
    }
}

impl ClauseKey {
    fn is_suffix_of(&self, stack: &Self) -> bool {
        self.0.len() <= stack.0.len() && stack.0[stack.0.len() - self.0.len()..] == self.0
    }

    fn catches(&self, thrown: &str, hierarchy: &dyn TypeHierarchy) -> bool {
        self.0.iter().any(|(catch_type, _)| {
            let Some(catch_type) = catch_type else {
                return true;
            };
            let Some(catch_type) = catch_type.as_object() else {
                return true;
            };
            hierarchy.subtype_relation(thrown, catch_type) != SubtypeRelation::No
        })
    }
}

struct GapFacts<'cfg> {
    cfg: &'cfg CFG,
    effects: BTreeMap<BlockId, Vec<ThrowEffect>>,
    predecessors: &'cfg BTreeMap<BlockId, Vec<BlockId>>,
}

impl<'cfg> GapFacts<'cfg> {
    fn analyze(
        cfg: &'cfg CFG,
        predecessors: &'cfg BTreeMap<BlockId, Vec<BlockId>>,
        start: u32,
        end: u32,
    ) -> Self {
        let mut effects = BTreeMap::<BlockId, Vec<ThrowEffect>>::new();
        for block in cfg.blocks.values().filter(|block| !block.synthetic) {
            for instruction in &block.insns {
                if instruction.payload.edge_copy
                    || instruction.offset < start
                    || end <= instruction.offset
                {
                    continue;
                }
                effects
                    .entry(block.id)
                    .or_default()
                    .push(ThrowEffect::of_tree(instruction));
            }
        }
        Self {
            cfg,
            effects,
            predecessors,
        }
    }

    /// Returns the transparent part of the gap that lies on a normal-flow path
    /// between the two protected fragments. Throwing side exits are deliberately
    /// excluded instead of causing the whole lexical gap to split the scope.
    fn bridge(
        &self,
        handlers: &ClauseKey,
        hierarchy: &dyn TypeHierarchy,
        left: &BTreeSet<BlockId>,
        right: &BTreeSet<BlockId>,
    ) -> Option<BTreeSet<BlockId>> {
        let mut candidates = self
            .effects
            .iter()
            .filter_map(|(block, effects)| {
                effects
                    .iter()
                    .all(|effect| Self::is_transparent(*effect, handlers, hierarchy))
                    .then_some(*block)
            })
            .collect::<BTreeSet<_>>();
        candidates.extend(self.cfg.blocks.values().filter_map(|block| {
            block
                .insns
                .iter()
                .all(InstructionEffects::is_ssa_bookkeeping)
                .then_some(block.id)
        }));

        NormalPathClosure::new(self.cfg, self.predecessors).between_with_exception_entry(
            left,
            right,
            &candidates,
        )
    }

    fn is_transparent(
        effect: ThrowEffect,
        handlers: &ClauseKey,
        hierarchy: &dyn TypeHierarchy,
    ) -> bool {
        match effect {
            ThrowEffect::None => true,
            ThrowEffect::SubtypesOf(thrown) => !handlers.catches(thrown, hierarchy),
            ThrowEffect::Any => false,
        }
    }
}

struct NormalPathClosure<'cfg> {
    cfg: &'cfg CFG,
    predecessors: &'cfg BTreeMap<BlockId, Vec<BlockId>>,
}

impl<'cfg> NormalPathClosure<'cfg> {
    fn new(cfg: &'cfg CFG, predecessors: &'cfg BTreeMap<BlockId, Vec<BlockId>>) -> Self {
        Self { cfg, predecessors }
    }

    fn between(
        &self,
        sources: &BTreeSet<BlockId>,
        targets: &BTreeSet<BlockId>,
        candidates: &BTreeSet<BlockId>,
    ) -> Option<BTreeSet<BlockId>> {
        self.between_from(sources, targets, candidates, std::iter::empty())
    }

    fn between_with_exception_entry(
        &self,
        sources: &BTreeSet<BlockId>,
        targets: &BTreeSet<BlockId>,
        candidates: &BTreeSet<BlockId>,
    ) -> Option<BTreeSet<BlockId>> {
        let exception_entries = sources
            .iter()
            .flat_map(|source| self.cfg.successors_with_kind(*source))
            .filter_map(|(target, kind)| kind.is_exception().then_some(*target))
            .filter(|target| targets.contains(target) || candidates.contains(target));
        self.between_from(sources, targets, candidates, exception_entries)
    }

    fn between_from(
        &self,
        sources: &BTreeSet<BlockId>,
        targets: &BTreeSet<BlockId>,
        candidates: &BTreeSet<BlockId>,
        extra_entries: impl IntoIterator<Item = BlockId>,
    ) -> Option<BTreeSet<BlockId>> {
        let mut visited = BTreeSet::new();
        let mut forward = BTreeSet::new();
        let mut reaches_target = false;
        let mut pending = sources
            .iter()
            .copied()
            .chain(extra_entries)
            .collect::<Vec<_>>();
        while let Some(block) = pending.pop() {
            if !visited.insert(block) {
                continue;
            }
            if targets.contains(&block) {
                reaches_target = true;
                continue;
            }
            if !sources.contains(&block) && !candidates.contains(&block) {
                continue;
            }
            if candidates.contains(&block) {
                forward.insert(block);
            }
            pending.extend(self.cfg.normal_successors(block));
        }
        if !reaches_target {
            return None;
        }

        let mut visited = BTreeSet::new();
        let mut backward = BTreeSet::new();
        let mut pending = targets.iter().copied().collect::<Vec<_>>();
        while let Some(block) = pending.pop() {
            if !visited.insert(block) {
                continue;
            }
            if !targets.contains(&block) && !candidates.contains(&block) {
                continue;
            }
            if candidates.contains(&block) {
                backward.insert(block);
            }
            pending.extend(self.predecessors.get(&block).into_iter().flatten().copied());
        }
        Some(forward.intersection(&backward).copied().collect())
    }

    fn reentries(
        &self,
        protected: &BTreeSet<BlockId>,
        candidates: &BTreeSet<BlockId>,
    ) -> BTreeSet<BlockId> {
        let mut visited = BTreeSet::new();
        let mut forward = BTreeSet::new();
        let mut pending = protected
            .iter()
            .flat_map(|block| self.cfg.normal_successors(*block))
            .collect::<Vec<_>>();
        while let Some(block) = pending.pop() {
            if protected.contains(&block) || !candidates.contains(&block) || !visited.insert(block)
            {
                continue;
            }
            forward.insert(block);
            pending.extend(self.cfg.normal_successors(block));
        }

        let mut visited = BTreeSet::new();
        let mut backward = BTreeSet::new();
        let mut pending = protected
            .iter()
            .flat_map(|block| self.predecessors.get(block).into_iter().flatten().copied())
            .collect::<Vec<_>>();
        while let Some(block) = pending.pop() {
            if protected.contains(&block) || !candidates.contains(&block) || !visited.insert(block)
            {
                continue;
            }
            backward.insert(block);
            pending.extend(self.predecessors.get(&block).into_iter().flatten().copied());
        }
        forward.intersection(&backward).copied().collect()
    }
}

/// Computes a single-entry exceptional corridor between two fragments of the
/// same handler scope. A catch-all or cleanup scope can temporarily shadow an
/// outer DEX handler stack; the stack resumes after the nested handler has
/// completed. The corridor is accepted only when every intermediate block is
/// owned by another exception scope and cannot escape anywhere except the
/// corridor or the resumed fragment.
struct ExceptionalPathClosure<'cfg> {
    cfg: &'cfg CFG,
}

impl<'cfg> ExceptionalPathClosure<'cfg> {
    fn new(cfg: &'cfg CFG) -> Self {
        Self { cfg }
    }

    fn between(
        &self,
        sources: &BTreeSet<BlockId>,
        targets: &BTreeSet<BlockId>,
        candidates: &BTreeSet<BlockId>,
    ) -> Option<BTreeSet<BlockId>> {
        let allowed = sources
            .iter()
            .chain(targets)
            .chain(candidates)
            .copied()
            .collect::<BTreeSet<_>>();
        let mut visited = BTreeSet::<(BlockId, bool)>::new();
        let mut pending = sources
            .iter()
            .copied()
            .map(|block| (block, false))
            .collect::<Vec<_>>();
        let mut reaches_target_exceptionally = false;
        while let Some((block, crossed_exception)) = pending.pop() {
            if !visited.insert((block, crossed_exception)) {
                continue;
            }
            if targets.contains(&block) {
                reaches_target_exceptionally |= crossed_exception;
                continue;
            }
            if !sources.contains(&block) && !candidates.contains(&block) {
                continue;
            }
            pending.extend(
                self.cfg
                    .successors_with_kind(block)
                    .iter()
                    .filter(|(target, _)| allowed.contains(target))
                    .map(|(target, kind)| (*target, crossed_exception || kind.is_exception())),
            );
        }
        if !reaches_target_exceptionally {
            return None;
        }

        let predecessors = self.cfg.predecessor_snapshot();
        let mut backward = BTreeSet::new();
        let mut pending = targets.iter().copied().collect::<Vec<_>>();
        while let Some(block) = pending.pop() {
            if !backward.insert(block) {
                continue;
            }
            pending.extend(
                predecessors
                    .get(&block)
                    .into_iter()
                    .flatten()
                    .filter(|predecessor| allowed.contains(predecessor))
                    .copied(),
            );
        }

        let corridor = candidates
            .iter()
            .filter(|block| {
                backward.contains(block)
                    && (visited.contains(&(**block, false)) || visited.contains(&(**block, true)))
            })
            .copied()
            .collect::<BTreeSet<_>>();
        (!corridor.is_empty() && self.is_closed(&corridor, targets)).then_some(corridor)
    }

    fn is_closed(&self, corridor: &BTreeSet<BlockId>, targets: &BTreeSet<BlockId>) -> bool {
        corridor.iter().all(|block| {
            self.cfg
                .successors_with_kind(*block)
                .iter()
                .all(|(target, _)| corridor.contains(target) || targets.contains(target))
        })
    }
}

struct ExceptionRegionHierarchy {
    regions: Vec<TryRegion>,
}

struct ExceptionScopeCoalescing<'cfg> {
    cfg: &'cfg CFG,
}

/// Proves that a protected scope is lexically nested in a fragmented outer
/// scope. DEX splits an outer try item around an inner try item, while the
/// inner handlers remain protected by one of the outer fragments. Handler
/// ownership therefore provides the missing nesting fact before the parent
/// forest can be reconstructed.
struct NestedProtectedDomain<'cfg, 'facts> {
    cfg: &'cfg CFG,
    boundary: &'facts BTreeSet<BlockId>,
}

impl<'cfg, 'facts> NestedProtectedDomain<'cfg, 'facts> {
    fn new(cfg: &'cfg CFG, boundary: &'facts BTreeSet<BlockId>) -> Self {
        Self { cfg, boundary }
    }

    fn contains(&self, region: &TryRegion) -> bool {
        let domain = region
            .handlers
            .iter()
            .flat_map(|handler| {
                handler
                    .blocks
                    .iter()
                    .copied()
                    .chain(handler.entry_blocks.iter().copied())
                    .chain(handler.adapter_blocks.iter().copied())
                    .chain(handler.rethrow_blocks.iter().copied())
            })
            .collect::<BTreeSet<_>>();
        !domain.is_empty()
            && domain.iter().all(|block| {
                let Some(body) = self.cfg.block(*block) else {
                    return false;
                };
                let successors = self.cfg.successors_with_kind(*block);
                let terminal_is_closed = match body.terminator().map(|insn| insn.insn_type) {
                    Some(InsnType::Return) => self.boundary.contains(block),
                    Some(InsnType::Throw) => {
                        self.boundary.contains(block) || !successors.is_empty()
                    }
                    _ => true,
                };
                terminal_is_closed
                    && successors.iter().all(|(target, _)| {
                        domain.contains(target) || self.boundary.contains(target)
                    })
            })
    }
}

/// Computes the least stable exception ownership model. Coalescing exposes
/// handler bodies needed to infer lexical nesting, while nesting exposes child
/// scopes that make interrupted outer handler fragments adjacent. Both steps
/// are monotone, so their joint fixed point is the semantic source of truth.
struct ExceptionScopeNormalization<'cfg> {
    cfg: &'cfg CFG,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExceptionScopeLayout(Vec<ExceptionScopeLayoutEntry>);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ExceptionScopeLayoutEntry {
    id: u32,
    parent: Option<u32>,
    blocks: Vec<BlockId>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct HandlerClauseSignature {
    catch_type: Option<super::ArgType>,
    kind: HandlerKind,
    continuation: BlockId,
}

#[derive(Debug, Clone, Copy)]
enum ScopeRewrite {
    Redundant { owner: u32, nested: u32 },
    InheritedCleanup { child: u32, parent: u32 },
    Connected { left: u32, right: u32 },
    CleanupBridge { left: u32, right: u32 },
    CleanupAlternatives(CleanupAlternativeScope),
    HandlerExtension { owner: u32, extension: u32 },
    CleanupContinuation { left: u32, right: u32 },
}

#[derive(Debug, Clone, Copy)]
struct CleanupAlternativeScope {
    normal: u32,
    exceptional: u32,
    cleanup: u32,
}

#[derive(Debug, Clone, Copy)]
enum ProtectedDomain {
    Left,
    Right,
    Union,
}

impl ScopeRewrite {
    fn regions(self) -> (u32, u32) {
        match self {
            Self::Redundant { owner, nested } => (owner, nested),
            Self::InheritedCleanup { child, parent } => (child, parent),
            Self::Connected { left, right }
            | Self::CleanupBridge { left, right }
            | Self::CleanupContinuation { left, right } => (left, right),
            Self::CleanupAlternatives(scope) => (scope.normal, scope.exceptional),
            Self::HandlerExtension { owner, extension } => (owner, extension),
        }
    }

    fn protected_domain(self) -> ProtectedDomain {
        match self {
            Self::Redundant { .. } | Self::HandlerExtension { .. } => ProtectedDomain::Left,
            Self::InheritedCleanup { .. } => {
                unreachable!("cleanup inheritance does not merge protected domains")
            }
            Self::Connected { .. }
            | Self::CleanupBridge { .. }
            | Self::CleanupAlternatives(_)
            | Self::CleanupContinuation { .. } => ProtectedDomain::Union,
        }
    }
}

impl<'cfg> ExceptionScopeNormalization<'cfg> {
    fn new(cfg: &'cfg CFG) -> Self {
        Self { cfg }
    }

    fn apply(
        &self,
        mut regions: Vec<TryRegion>,
    ) -> Result<Vec<TryRegion>, ExceptionInvariantError> {
        loop {
            let before = ExceptionScopeLayout::of(&regions);
            regions = ExceptionScopeCoalescing::new(self.cfg).apply(regions)?;
            regions = ExceptionScopeNesting::new(self.cfg)
                .apply(regions)?
                .without_empty_scopes();
            if ExceptionScopeLayout::of(&regions) == before {
                return Ok(regions);
            }
        }
    }
}

impl ExceptionScopeLayout {
    fn of(regions: &[TryRegion]) -> Self {
        let mut entries = regions
            .iter()
            .map(|region| ExceptionScopeLayoutEntry {
                id: region.id,
                parent: region.parent,
                blocks: region.blocks.clone(),
            })
            .collect::<Vec<_>>();
        entries.sort_unstable();
        Self(entries)
    }
}

impl<'cfg> ExceptionScopeCoalescing<'cfg> {
    fn new(cfg: &'cfg CFG) -> Self {
        Self { cfg }
    }

    fn apply(
        &self,
        mut regions: Vec<TryRegion>,
    ) -> Result<Vec<TryRegion>, ExceptionInvariantError> {
        while let Some(relation) = self.relation(&regions) {
            self.merge(&mut regions, relation)?;
        }
        Ok(regions)
    }

    fn relation(&self, regions: &[TryRegion]) -> Option<ScopeRewrite> {
        if let Some((owner, nested)) = self.redundant_nested_handler_scope(regions) {
            return Some(ScopeRewrite::Redundant { owner, nested });
        }
        if let Some((child, parent)) = self.inherited_cleanup(regions) {
            return Some(ScopeRewrite::InheritedCleanup { child, parent });
        }
        if let Some((owner, extension)) = self.handler_extension(regions) {
            return Some(ScopeRewrite::HandlerExtension { owner, extension });
        }
        if let Some(scope) = self.cleanup_alternatives(regions) {
            return Some(ScopeRewrite::CleanupAlternatives(scope));
        }
        if let Some((left, right)) = self.cleanup_bridge(regions) {
            return Some(ScopeRewrite::CleanupBridge { left, right });
        }
        if let Some((left, right)) = self.cleanup_continuation(regions) {
            return Some(ScopeRewrite::CleanupContinuation { left, right });
        }
        self.connected_fragments(regions)
            .map(|(left, right)| ScopeRewrite::Connected { left, right })
    }

    fn redundant_nested_handler_scope(&self, regions: &[TryRegion]) -> Option<(u32, u32)> {
        for inner in regions {
            let Some(parent) = inner.parent else {
                continue;
            };
            let Some(outer) = regions.iter().find(|candidate| candidate.id == parent) else {
                continue;
            };
            if inner.handlers.is_empty()
                || !inner
                    .blocks
                    .iter()
                    .all(|block| outer.blocks.contains(block))
            {
                continue;
            }
            let handlers_are_inherited = inner.handlers.iter().all(|handler| {
                outer.handlers.iter().any(|candidate| {
                    candidate.catch_type == handler.catch_type
                        && candidate.kind == handler.kind
                        && candidate.canonical_entry == handler.canonical_entry
                })
            });
            if handlers_are_inherited {
                return Some((outer.id, inner.id));
            }
        }
        None
    }

    fn inherited_cleanup(&self, regions: &[TryRegion]) -> Option<(u32, u32)> {
        for child in regions {
            let Some(parent) = child.parent else {
                continue;
            };
            let Some(parent) = regions.iter().find(|candidate| candidate.id == parent) else {
                continue;
            };
            if parent.handlers.is_empty()
                || !child
                    .blocks
                    .iter()
                    .all(|block| parent.blocks.contains(block))
                || parent
                    .handlers
                    .iter()
                    .any(|handler| handler.kind == HandlerKind::Catch)
            {
                continue;
            }
            let cleanup_is_represented = parent.handlers.iter().all(|handler| {
                child.handlers.iter().any(|candidate| {
                    candidate.catch_type == handler.catch_type
                        && candidate.kind == handler.kind
                        && candidate.canonical_entry == handler.canonical_entry
                })
            });
            if cleanup_is_represented {
                return Some((child.id, parent.id));
            }
        }
        None
    }

    fn connected_fragments(&self, regions: &[TryRegion]) -> Option<(u32, u32)> {
        let mut candidates = Vec::new();
        for left in regions {
            let signature = Self::effective_handler_signature(left, regions);
            if signature.is_empty() {
                continue;
            }
            for right in regions {
                if left.id == right.id
                    || signature != Self::effective_handler_signature(right, regions)
                {
                    continue;
                }
                let ordered = left.start_offset <= right.start_offset;
                let siblings = Self::parent_outside_cleanup_envelopes(left, regions)
                    == Self::parent_outside_cleanup_envelopes(right, regions);
                let overlaps = left.blocks.iter().any(|block| right.blocks.contains(block));
                let bridge = (siblings && (ordered || overlaps))
                    .then(|| self.transparent_bridge(left, right, regions))
                    .flatten();
                if bridge.is_some() {
                    candidates.push((
                        usize::from(left.parent != right.parent),
                        left.start_offset,
                        right.start_offset,
                        left.id,
                        right.id,
                    ));
                }
            }
        }
        candidates.sort_unstable();
        candidates
            .first()
            .map(|(_, _, _, left, right)| (*left, *right))
    }

    /// DEX protects each catch body separately when it must execute the same
    /// cleanup as the corresponding try body. Those table entries are pieces
    /// of one lexical cleanup scope, not nested try/finally statements.
    fn handler_extension(&self, regions: &[TryRegion]) -> Option<(u32, u32)> {
        let parents = regions
            .iter()
            .map(|region| (region.id, region.parent))
            .collect::<BTreeMap<_, _>>();
        for extension in regions {
            if extension
                .handlers
                .iter()
                .any(|handler| handler.kind == HandlerKind::Catch)
            {
                continue;
            }
            let Some(extension_cleanup) = Self::cleanup_signature(extension) else {
                continue;
            };
            let protected = extension.blocks.iter().copied().collect::<BTreeSet<_>>();
            if protected.is_empty() {
                continue;
            }
            let mut owners = regions
                .iter()
                .filter(|owner| owner.id != extension.id)
                .filter_map(|owner| {
                    if Self::cleanup_signature(owner).as_ref() != Some(&extension_cleanup) {
                        return None;
                    }
                    let handler_domain = regions
                        .iter()
                        .filter(|region| {
                            region.id == owner.id
                                || Self::descends_from(region.id, owner.id, &parents)
                        })
                        .flat_map(|region| &region.handlers)
                        .flat_map(|handler| handler.semantic_blocks.iter().copied())
                        .collect::<BTreeSet<_>>();
                    let body = owner.blocks.iter().copied().collect::<BTreeSet<_>>();
                    let enters_protected_handler = owner.handlers.iter().any(|handler| {
                        protected.contains(&handler.semantic_entry)
                            || handler
                                .entry_blocks
                                .iter()
                                .any(|entry| protected.contains(entry))
                    });
                    (body.is_disjoint(&protected)
                        && enters_protected_handler
                        && protected.is_subset(&handler_domain))
                    .then_some((handler_domain.len(), owner.id))
                })
                .collect::<Vec<_>>();
            owners.sort_unstable();
            if let Some((_, owner)) = owners.first().copied() {
                return Some((owner, extension.id));
            }
        }
        None
    }

    fn descends_from(mut region: u32, ancestor: u32, parents: &BTreeMap<u32, Option<u32>>) -> bool {
        let mut visited = BTreeSet::new();
        while visited.insert(region) {
            let Some(parent) = parents.get(&region).copied().flatten() else {
                return false;
            };
            if parent == ancestor {
                return true;
            }
            region = parent;
        }
        false
    }

    /// Proves that two handler fragments are the normal and exceptional
    /// completions of one cleanup scope.
    fn cleanup_alternatives(&self, regions: &[TryRegion]) -> Option<CleanupAlternativeScope> {
        for cleanup in regions {
            let rethrows = cleanup
                .handlers
                .iter()
                .filter(|handler| handler.kind != HandlerKind::Catch)
                .flat_map(|handler| handler.rethrow_blocks.iter().copied())
                .collect::<BTreeSet<_>>();
            if rethrows.is_empty() {
                continue;
            }

            let mut exceptional = regions
                .iter()
                .filter(|candidate| candidate.id != cleanup.id)
                .filter(|candidate| candidate.parent == cleanup.parent)
                .filter(|candidate| {
                    let scope = Self::scope_regions(candidate.id, regions);
                    rethrows.is_subset(&Self::scope_blocks(&scope, regions))
                })
                .collect::<Vec<_>>();
            exceptional.sort_by_key(|candidate| (candidate.blocks.len(), candidate.start_offset));

            for exceptional in exceptional {
                let signature = Self::handler_signature(exceptional);
                if signature.is_empty() {
                    continue;
                }
                let mut normal = regions
                    .iter()
                    .filter(|candidate| {
                        candidate.id != cleanup.id && candidate.id != exceptional.id
                    })
                    .filter(|candidate| candidate.parent == cleanup.parent)
                    .filter(|candidate| Self::handler_signature(candidate) == signature)
                    .filter(|candidate| candidate.end_offset <= exceptional.start_offset)
                    .filter(|candidate| {
                        self.transparent_bridge(cleanup, candidate, regions)
                            .is_some()
                    })
                    .collect::<Vec<_>>();
                normal.sort_by_key(|candidate| std::cmp::Reverse(candidate.end_offset));
                if let Some(normal) = normal.first() {
                    return Some(CleanupAlternativeScope {
                        normal: normal.id,
                        exceptional: exceptional.id,
                        cleanup: cleanup.id,
                    });
                }
            }
        }
        None
    }

    /// Joins two pieces of one handler scope when a nested cleanup interrupts
    /// their ordinary control flow. The cleanup's rethrow edges are the
    /// semantic continuation between the pieces.
    fn cleanup_bridge(&self, regions: &[TryRegion]) -> Option<(u32, u32)> {
        for cleanup in regions {
            let rethrows = cleanup
                .handlers
                .iter()
                .filter(|handler| handler.kind != HandlerKind::Catch)
                .flat_map(|handler| handler.rethrow_blocks.iter().copied())
                .collect::<BTreeSet<_>>();
            if rethrows.is_empty() {
                continue;
            }
            for left in regions {
                if left.id == cleanup.id
                    || left.parent != cleanup.parent
                    || !self.enters(left, cleanup)
                {
                    continue;
                }
                let signature = Self::handler_signature(left);
                if signature.is_empty() {
                    continue;
                }
                let mut continuations = regions
                    .iter()
                    .filter(|right| right.id != cleanup.id && right.id != left.id)
                    .filter(|right| right.parent == left.parent)
                    .filter(|right| Self::handler_signature(right) == signature)
                    .filter(|right| rethrows.iter().all(|block| right.blocks.contains(block)))
                    .collect::<Vec<_>>();
                continuations.sort_by_key(|right| (right.blocks.len(), right.start_offset));
                if let Some(right) = continuations.first() {
                    return Some((left.id, right.id));
                }
            }
        }
        None
    }

    fn cleanup_continuation(&self, regions: &[TryRegion]) -> Option<(u32, u32)> {
        for inner in regions {
            let rethrows = inner
                .handlers
                .iter()
                .filter(|handler| handler.kind != HandlerKind::Catch)
                .flat_map(|handler| handler.rethrow_blocks.iter().copied())
                .collect::<BTreeSet<_>>();
            if rethrows.is_empty() {
                continue;
            }
            let mut left = regions
                .iter()
                .filter(|candidate| candidate.id != inner.id)
                .filter(|candidate| candidate.end_offset <= inner.start_offset)
                .filter(|candidate| self.enters(candidate, inner))
                .collect::<Vec<_>>();
            left.sort_by_key(|candidate| std::cmp::Reverse(candidate.end_offset));
            for left in left {
                let signature = Self::cleanup_signature(left)?;
                let mut right = regions
                    .iter()
                    .filter(|candidate| candidate.id != inner.id && candidate.id != left.id)
                    .filter(|candidate| candidate.start_offset < inner.end_offset)
                    .filter(|candidate| inner.end_offset <= candidate.end_offset)
                    .filter(|candidate| {
                        Self::cleanup_signature(candidate).as_ref() == Some(&signature)
                    })
                    .filter(|candidate| {
                        rethrows
                            .iter()
                            .all(|block| candidate.blocks.contains(block))
                    })
                    .collect::<Vec<_>>();
                right.sort_by_key(|candidate| candidate.start_offset);
                if let Some(right) = right.first() {
                    return Some((left.id, right.id));
                }
            }
        }
        None
    }

    fn handler_signature(region: &TryRegion) -> Vec<HandlerClauseSignature> {
        region
            .handlers
            .iter()
            .map(|handler| HandlerClauseSignature {
                catch_type: handler.catch_type.clone(),
                kind: handler.kind,
                continuation: handler.canonical_entry,
            })
            .collect()
    }

    fn effective_handler_signature(
        region: &TryRegion,
        regions: &[TryRegion],
    ) -> Vec<HandlerClauseSignature> {
        let mut signature = Self::handler_signature(region);
        let mut parent = region.parent;
        let mut visited = BTreeSet::new();
        while let Some(parent_id) = parent {
            if !visited.insert(parent_id) {
                break;
            }
            let Some(owner) = regions.iter().find(|candidate| candidate.id == parent_id) else {
                break;
            };
            if owner.handlers.is_empty()
                || owner
                    .handlers
                    .iter()
                    .any(|handler| handler.kind == HandlerKind::Catch)
            {
                break;
            }
            signature.extend(Self::handler_signature(owner));
            parent = owner.parent;
        }
        signature.sort_unstable();
        signature.dedup();
        signature
    }

    fn cleanup_signature(region: &TryRegion) -> Option<Vec<HandlerClauseSignature>> {
        let mut signature = region
            .handlers
            .iter()
            .filter(|handler| handler.kind != HandlerKind::Catch)
            .map(|handler| HandlerClauseSignature {
                catch_type: handler.catch_type.clone(),
                kind: handler.kind,
                continuation: handler.canonical_entry,
            })
            .collect::<Vec<_>>();
        signature.sort_unstable();
        (!signature.is_empty()).then_some(signature)
    }

    fn enters(&self, left: &TryRegion, inner: &TryRegion) -> bool {
        let sources = left.blocks.iter().copied().collect::<BTreeSet<_>>();
        let targets = inner.blocks.iter().copied().collect::<BTreeSet<_>>();
        let mut pending = sources
            .iter()
            .flat_map(|source| self.cfg.normal_successors(*source))
            .collect::<Vec<_>>();
        let mut visited = BTreeSet::new();

        while let Some(block) = pending.pop() {
            if targets.contains(&block) {
                return true;
            }
            if sources.contains(&block) || !visited.insert(block) {
                continue;
            }
            let Some(body) = self.cfg.block(block) else {
                continue;
            };
            if body.insns.iter().any(|instruction| instruction.can_throw()) {
                continue;
            }
            pending.extend(self.cfg.normal_successors(block));
        }
        false
    }

    /// Finds an unprotected path of non-throwing blocks between two fragments
    /// with the same handler clauses. DEX commonly leaves argument moves
    /// outside try items; including those blocks in the source try does not
    /// alter its exceptional behavior.
    fn transparent_bridge(
        &self,
        left: &TryRegion,
        right: &TryRegion,
        regions: &[TryRegion],
    ) -> Option<BTreeSet<BlockId>> {
        // A lexical try scope includes the protected bodies of all nested try
        // regions. Treating those bodies as unrelated occupied blocks splits a
        // single DEX exception table at every nested try, even when both
        // fragments have identical handler semantics.
        let left_scope = Self::scope_regions(left.id, regions);
        let right_scope = Self::scope_regions(right.id, regions);
        let endpoint_scopes = left_scope
            .union(&right_scope)
            .copied()
            .collect::<BTreeSet<_>>();
        let left_blocks = Self::scope_blocks(&left_scope, regions);
        let right_blocks = Self::scope_blocks(&right_scope, regions);
        let outer_blocks = left_blocks
            .union(&right_blocks)
            .copied()
            .collect::<BTreeSet<_>>();
        let handler_signature = Self::handler_signature(left);
        let catch_signature = Self::catch_signature(left);
        let lexical_parent = Self::parent_outside_cleanup_envelopes(left, regions);
        let equivalent_scopes = regions
            .iter()
            .filter(|region| {
                (region.parent == left.parent
                    && Self::handler_signature(region) == handler_signature)
                    || (!catch_signature.is_empty()
                        && Self::catch_signature(region) == catch_signature
                        && Self::parent_outside_cleanup_envelopes(region, regions)
                            == lexical_parent)
            })
            .flat_map(|region| Self::scope_regions(region.id, regions))
            .collect::<BTreeSet<_>>();
        let mut exception_boundary = Self::scope_blocks(&equivalent_scopes, regions);
        exception_boundary.extend(
            regions
                .iter()
                .filter(|region| equivalent_scopes.contains(&region.id))
                .flat_map(|region| &region.handlers)
                .flat_map(|handler| handler.semantic_blocks.iter().copied()),
        );
        let nested_domains = NestedProtectedDomain::new(self.cfg, &exception_boundary);
        let enclosing = Self::enclosing_regions(left, right, regions);
        let transparent_scopes = regions
            .iter()
            .filter(|region| {
                !endpoint_scopes.contains(&region.id)
                    && !enclosing.contains(&region.id)
                    && (Self::handler_signature(region) == handler_signature
                        || Self::preserves_exception(region)
                        || nested_domains.contains(region))
            })
            .map(|region| region.id)
            .collect::<BTreeSet<_>>();
        let transparent_blocks = regions
            .iter()
            .filter(|region| transparent_scopes.contains(&region.id))
            .flat_map(|region| region.blocks.iter().copied())
            .collect::<BTreeSet<_>>();
        let mut occupied = BTreeSet::new();
        for region in regions {
            if !endpoint_scopes.contains(&region.id)
                && !enclosing.contains(&region.id)
                && !transparent_scopes.contains(&region.id)
            {
                occupied.extend(region.blocks.iter().copied());
            }
            // Exception handlers are never part of a normal lexical bridge,
            // including handlers owned by either endpoint scope.
            occupied.extend(
                region
                    .handlers
                    .iter()
                    .flat_map(|handler| handler.blocks.iter().copied()),
            );
        }
        let candidates = self
            .cfg
            .blocks
            .iter()
            .filter(|(block, _)| {
                !left_blocks.contains(block)
                    && !right_blocks.contains(block)
                    && !occupied.contains(block)
            })
            .filter_map(|(block, body)| {
                (transparent_blocks.contains(block)
                    || body
                        .insns
                        .iter()
                        .all(|instruction| !instruction.can_throw()))
                .then_some(*block)
            })
            .collect::<BTreeSet<_>>();
        let predecessors = self.cfg.normal_predecessor_snapshot();
        let closure = NormalPathClosure::new(self.cfg, &predecessors);
        let bridge = if left_blocks.is_disjoint(&right_blocks) {
            closure
                .between(&left_blocks, &right_blocks, &candidates)
                .or_else(|| {
                    self.through_exception_scopes(
                        &left_blocks,
                        &right_blocks,
                        &endpoint_scopes,
                        regions,
                    )
                })
        } else {
            // Equivalent DEX ranges can overlap when a compiler repeats the
            // outer handler around a nested try. Their missing lexical body is
            // the normal-flow corridor that leaves and re-enters the protected
            // union, including nested protected domains whose handlers are
            // already covered by that union.
            Some(closure.reentries(&outer_blocks, &candidates))
        };
        bridge
    }

    fn through_exception_scopes(
        &self,
        sources: &BTreeSet<BlockId>,
        targets: &BTreeSet<BlockId>,
        endpoint_scopes: &BTreeSet<u32>,
        regions: &[TryRegion],
    ) -> Option<BTreeSet<BlockId>> {
        let endpoint_handlers = regions
            .iter()
            .filter(|region| endpoint_scopes.contains(&region.id))
            .flat_map(|region| &region.handlers)
            .flat_map(|handler| handler.blocks.iter().copied())
            .collect::<BTreeSet<_>>();
        let candidates = regions
            .iter()
            .flat_map(|region| {
                region.blocks.iter().copied().chain(
                    region
                        .handlers
                        .iter()
                        .flat_map(|handler| handler.blocks.iter().copied()),
                )
            })
            .filter(|block| {
                !sources.contains(block)
                    && !targets.contains(block)
                    && !endpoint_handlers.contains(block)
            })
            .collect::<BTreeSet<_>>();
        ExceptionalPathClosure::new(self.cfg).between(sources, targets, &candidates)
    }

    fn preserves_exception(region: &TryRegion) -> bool {
        !region.handlers.is_empty()
            && region.handlers.iter().all(|handler| {
                handler.kind == HandlerKind::Cleanup && !handler.rethrow_blocks.is_empty()
            })
    }

    fn catch_signature(region: &TryRegion) -> Vec<HandlerClauseSignature> {
        let mut signature = region
            .handlers
            .iter()
            .filter(|handler| handler.kind == HandlerKind::Catch)
            .map(|handler| HandlerClauseSignature {
                catch_type: handler.catch_type.clone(),
                kind: handler.kind,
                continuation: handler.canonical_entry,
            })
            .collect::<Vec<_>>();
        signature.sort_unstable();
        signature
    }

    fn parent_outside_cleanup_envelopes(region: &TryRegion, regions: &[TryRegion]) -> Option<u32> {
        let mut parent = region.parent;
        let mut visited = BTreeSet::new();
        while let Some(parent_id) = parent {
            if !visited.insert(parent_id) {
                break;
            }
            let Some(owner) = regions.iter().find(|candidate| candidate.id == parent_id) else {
                break;
            };
            if owner.handlers.is_empty()
                || owner
                    .handlers
                    .iter()
                    .any(|handler| handler.kind == HandlerKind::Catch)
            {
                break;
            }
            parent = owner.parent;
        }
        parent
    }

    fn scope_regions(owner: u32, regions: &[TryRegion]) -> BTreeSet<u32> {
        let parents = regions
            .iter()
            .map(|region| (region.id, region.parent))
            .collect::<BTreeMap<_, _>>();
        regions
            .iter()
            .filter(|region| region.id == owner || Self::descends_from(region.id, owner, &parents))
            .map(|region| region.id)
            .collect()
    }

    fn scope_blocks(scope: &BTreeSet<u32>, regions: &[TryRegion]) -> BTreeSet<BlockId> {
        regions
            .iter()
            .filter(|region| scope.contains(&region.id))
            .flat_map(|region| region.blocks.iter().copied())
            .collect()
    }

    fn enclosing_regions(
        left: &TryRegion,
        right: &TryRegion,
        regions: &[TryRegion],
    ) -> BTreeSet<u32> {
        let parents = regions
            .iter()
            .map(|region| (region.id, region.parent))
            .collect::<BTreeMap<_, _>>();
        let mut enclosing = BTreeSet::new();
        let mut pending = left
            .parent
            .into_iter()
            .chain(right.parent)
            .collect::<Vec<_>>();
        while let Some(region) = pending.pop() {
            if !enclosing.insert(region) {
                continue;
            }
            pending.extend(parents.get(&region).copied().flatten());
        }
        let start = left.start_offset.min(right.start_offset);
        let end = left.end_offset.max(right.end_offset);
        enclosing.extend(regions.iter().filter_map(|region| {
            let strictly_contains = region.start_offset <= start
                && end <= region.end_offset
                && (region.start_offset < start || end < region.end_offset);
            (region.id != left.id && region.id != right.id && strictly_contains)
                .then_some(region.id)
        }));
        enclosing
    }

    fn merge(
        &self,
        regions: &mut Vec<TryRegion>,
        relation: ScopeRewrite,
    ) -> Result<(), ExceptionInvariantError> {
        if let ScopeRewrite::InheritedCleanup { child, parent } = relation {
            return self.inherit_cleanup(regions, child, parent);
        }
        let (left, right) = relation.regions();
        let left_index = regions
            .iter()
            .position(|region| region.id == left)
            .ok_or(ExceptionInvariantError::MissingExceptionScope(left))?;
        let right_index = regions
            .iter()
            .position(|region| region.id == right)
            .ok_or(ExceptionInvariantError::MissingExceptionScope(right))?;
        let right_region = regions.remove(right_index);
        let left_index = if right_index < left_index {
            left_index - 1
        } else {
            left_index
        };
        let domain = relation.protected_domain();
        // `right_region` was removed to make parent/child rewiring
        // unambiguous, but bridge analysis needs both endpoint subtrees.
        let mut bridge_context = regions.clone();
        bridge_context.push(right_region.clone());
        let bridge = matches!(domain, ProtectedDomain::Union)
            .then(|| self.transparent_bridge(&regions[left_index], &right_region, &bridge_context))
            .flatten()
            .unwrap_or_default();
        let cleanup_scope = match relation {
            ScopeRewrite::CleanupAlternatives(scope) => bridge_context
                .iter()
                .find(|region| region.id == scope.cleanup)
                .cloned(),
            _ => None,
        };
        let mut bridge = bridge;
        if let Some(cleanup) = &cleanup_scope {
            let scope = Self::scope_regions(cleanup.id, &bridge_context);
            bridge.extend(Self::scope_blocks(&scope, &bridge_context));
            if let Some(normal) = bridge_context.iter().find(|region| region.id == left) {
                bridge.extend(
                    self.transparent_bridge(cleanup, normal, &bridge_context)
                        .unwrap_or_default(),
                );
            }
        }
        let parents = ExceptionParentForest::of(&bridge_context);
        {
            let left_region = &mut regions[left_index];
            let merged_parent = match (left_region.parent, right_region.parent) {
                (declared, Some(parent)) if parent == left => declared,
                (Some(parent), inferred) if parent == right => inferred,
                (declared, inferred) => parents.reconcile(right, declared, inferred)?,
            };
            left_region.parent = merged_parent;
            match domain {
                ProtectedDomain::Left => {}
                ProtectedDomain::Right => {
                    left_region.start_offset = right_region.start_offset;
                    left_region.end_offset = right_region.end_offset;
                    left_region.blocks = right_region.blocks.clone();
                }
                ProtectedDomain::Union => {
                    left_region.start_offset =
                        left_region.start_offset.min(right_region.start_offset);
                    left_region.end_offset = left_region.end_offset.max(right_region.end_offset);
                    if let Some(cleanup) = &cleanup_scope {
                        left_region.start_offset =
                            left_region.start_offset.min(cleanup.start_offset);
                        left_region.end_offset = left_region.end_offset.max(cleanup.end_offset);
                    }
                    left_region.blocks.extend(bridge);
                    left_region
                        .blocks
                        .extend(right_region.blocks.iter().copied());
                }
            }
            left_region.blocks.sort_unstable();
            left_region.blocks.dedup();
            left_region.children.extend(right_region.children);
            left_region.children.sort_unstable();
            left_region.children.dedup();
            for handler in right_region.handlers {
                let target = left_region.handlers.iter_mut().find(|candidate| {
                    candidate.catch_type == handler.catch_type
                        && candidate.kind == handler.kind
                        && candidate.canonical_entry == handler.canonical_entry
                });
                if let Some(target) = target {
                    target.entry_blocks.extend(handler.entry_blocks);
                    target.adapter_blocks.extend(handler.adapter_blocks);
                    if target.entry_blocks.len() > 1 {
                        target.semantic_entry = target.canonical_entry;
                        target.exception_value = target
                            .canonical_exception_value
                            .clone()
                            .or(handler.canonical_exception_value)
                            .or_else(|| target.exception_value.clone())
                            .or(handler.exception_value);
                    }
                    target.blocks.extend(handler.blocks);
                    target.blocks.sort_unstable();
                    target.blocks.dedup();
                    target.semantic_blocks.extend(handler.semantic_blocks);
                    target.semantic_blocks.sort_unstable();
                    target.semantic_blocks.dedup();
                    target.rethrow_blocks.extend(handler.rethrow_blocks);
                } else {
                    left_region.handlers.push(handler);
                }
            }
            left_region
                .handlers
                .sort_by_key(|handler| (handler.catch_type.is_none(), handler.id));
        }
        for region in regions.iter_mut() {
            if region.parent == Some(right) {
                region.parent = Some(left);
            }
            for child in &mut region.children {
                if *child == right {
                    *child = left;
                }
            }
            let region_id = region.id;
            region.children.retain(|child| *child != region_id);
            region.children.sort_unstable();
            region.children.dedup();
        }
        self.recompute_exits(&mut regions[left_index]);
        Ok(())
    }

    fn inherit_cleanup(
        &self,
        regions: &mut [TryRegion],
        child: u32,
        parent: u32,
    ) -> Result<(), ExceptionInvariantError> {
        let inherited = regions
            .iter()
            .find(|region| region.id == parent)
            .ok_or(ExceptionInvariantError::MissingExceptionScope(parent))?
            .handlers
            .iter()
            .map(|handler| {
                (
                    handler.catch_type.clone(),
                    handler.kind,
                    handler.canonical_entry,
                )
            })
            .collect::<BTreeSet<_>>();
        let child = regions
            .iter_mut()
            .find(|region| region.id == child)
            .ok_or(ExceptionInvariantError::MissingExceptionScope(child))?;
        child.handlers.retain(|handler| {
            !inherited.contains(&(
                handler.catch_type.clone(),
                handler.kind,
                handler.canonical_entry,
            ))
        });
        self.recompute_exits(child);
        Ok(())
    }

    fn recompute_exits(&self, region: &mut TryRegion) {
        let blocks = region.blocks.iter().copied().collect::<BTreeSet<_>>();
        let handlers = region
            .handlers
            .iter()
            .flat_map(|handler| handler.blocks.iter().copied())
            .collect::<BTreeSet<_>>();
        region.normal_exit_blocks = blocks
            .iter()
            .copied()
            .filter(|source| {
                self.cfg
                    .normal_successors(*source)
                    .any(|target| !blocks.contains(&target) && !handlers.contains(&target))
            })
            .collect();
    }
}

struct ExceptionScopeNesting<'cfg> {
    cfg: &'cfg CFG,
}

struct ExceptionParentForest {
    parents: BTreeMap<u32, Option<u32>>,
}

impl ExceptionParentForest {
    fn of(regions: &[TryRegion]) -> Self {
        Self {
            parents: regions
                .iter()
                .map(|region| (region.id, region.parent))
                .collect(),
        }
    }

    fn reconcile(
        &self,
        _region: u32,
        declared: Option<u32>,
        inferred: Option<u32>,
    ) -> Result<Option<u32>, ExceptionInvariantError> {
        let (Some(declared), Some(inferred)) = (declared, inferred) else {
            return Ok(declared.or(inferred));
        };
        Ok(self.common_ancestor(declared, inferred))
    }

    fn reparent(&mut self, region: u32, parent: Option<u32>) {
        self.parents.insert(region, parent);
    }

    fn common_ancestor(&self, left: u32, mut right: u32) -> Option<u32> {
        let mut left_ancestors = BTreeSet::new();
        let mut current = Some(left);
        while let Some(region) = current {
            if !left_ancestors.insert(region) {
                break;
            }
            current = self.parents.get(&region).copied().flatten();
        }

        let mut visited = BTreeSet::new();
        while visited.insert(right) {
            if left_ancestors.contains(&right) {
                return Some(right);
            }
            right = self.parents.get(&right).copied().flatten()?;
        }
        None
    }
}

impl<'cfg> ExceptionScopeNesting<'cfg> {
    fn new(cfg: &'cfg CFG) -> Self {
        Self { cfg }
    }

    fn apply(
        &self,
        mut regions: Vec<TryRegion>,
    ) -> Result<ExceptionRegionHierarchy, ExceptionInvariantError> {
        let relations = regions
            .iter()
            .filter_map(|inner| {
                let cleanup_blocks = inner
                    .handlers
                    .iter()
                    .filter(|handler| handler.kind != HandlerKind::Catch)
                    .flat_map(|handler| handler.blocks.iter().copied())
                    .collect::<BTreeSet<_>>();
                let rethrows = inner
                    .handlers
                    .iter()
                    .filter(|handler| handler.kind != HandlerKind::Catch)
                    .flat_map(|handler| handler.rethrow_blocks.iter().copied())
                    .collect::<BTreeSet<_>>();
                if rethrows.is_empty() {
                    return None;
                }
                let outer = regions
                    .iter()
                    .filter(|outer| outer.id != inner.id)
                    .filter(|outer| {
                        outer.start_offset <= inner.start_offset
                            && inner.end_offset <= outer.end_offset
                    })
                    .filter(|outer| rethrows.iter().all(|block| outer.blocks.contains(block)))
                    .filter(|outer| {
                        !outer
                            .blocks
                            .iter()
                            .all(|block| cleanup_blocks.contains(block))
                    })
                    .min_by_key(|outer| outer.blocks.len())?;
                Some((inner.id, outer.id, cleanup_blocks))
            })
            .collect::<Vec<_>>();
        let indices = regions
            .iter()
            .enumerate()
            .map(|(index, region)| (region.id, index))
            .collect::<BTreeMap<_, _>>();
        let mut parents = ExceptionParentForest::of(&regions);
        let mut cleanup = BTreeMap::<u32, BTreeSet<BlockId>>::new();
        for (inner, outer, cleanup_blocks) in relations {
            let inner_index = indices[&inner];
            let parent = parents.reconcile(inner, regions[inner_index].parent, Some(outer))?;
            regions[inner_index].parent = parent;
            parents.reparent(inner, parent);
            cleanup.entry(inner).or_default().extend(cleanup_blocks);
        }

        let normal_domains = regions
            .iter()
            .map(|region| {
                (
                    region.id,
                    Self::normal_domain(self.cfg, region.blocks.iter().copied()),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let lexical_relations = regions
            .iter()
            .filter(|inner| inner.parent.is_none())
            .filter_map(|inner| {
                let handler_blocks = inner
                    .handlers
                    .iter()
                    .flat_map(|handler| handler.blocks.iter().copied())
                    .collect::<BTreeSet<_>>();
                if handler_blocks.is_empty() {
                    return None;
                }
                let outer = regions
                    .iter()
                    .filter(|outer| outer.id != inner.id)
                    .filter(|outer| {
                        outer.start_offset <= inner.start_offset
                            && inner.end_offset <= outer.end_offset
                    })
                    .filter(|outer| {
                        inner.blocks.first().is_some_and(|entry| {
                            normal_domains
                                .get(&outer.id)
                                .is_some_and(|domain| domain.contains(entry))
                        })
                    })
                    .filter(|outer| {
                        handler_blocks
                            .iter()
                            .all(|block| outer.blocks.contains(block))
                    })
                    .filter(|outer| {
                        !outer
                            .blocks
                            .iter()
                            .all(|block| handler_blocks.contains(block))
                    })
                    .min_by_key(|outer| outer.blocks.len())?;
                Some((inner.id, outer.id))
            })
            .collect::<Vec<_>>();
        for (inner, outer) in lexical_relations {
            regions[indices[&inner]].parent = Some(outer);
        }

        let mut pending = regions
            .iter()
            .filter(|region| region.parent.is_some())
            .map(|region| region.id)
            .collect::<VecDeque<_>>();
        while let Some(inner) = pending.pop_front() {
            let inner_index = indices[&inner];
            let Some(outer) = regions[inner_index].parent else {
                continue;
            };
            let outer_index = *indices
                .get(&outer)
                .ok_or(ExceptionInvariantError::MissingExceptionScope(outer))?;
            let inherited = regions[inner_index]
                .blocks
                .iter()
                .copied()
                .chain(cleanup.get(&inner).into_iter().flatten().copied())
                .collect::<BTreeSet<_>>();
            let mut blocks = regions[outer_index]
                .blocks
                .iter()
                .copied()
                .collect::<BTreeSet<_>>();
            let previous = blocks.len();
            blocks.extend(inherited);
            let changed = blocks.len() != previous;
            regions[outer_index].blocks = blocks.into_iter().collect();
            if changed {
                if regions[outer_index].parent.is_some() {
                    pending.push_back(outer);
                }
            }
        }
        for region in &mut regions {
            self.recompute_exits(region);
        }
        Ok(ExceptionRegionHierarchy::new(regions))
    }

    fn normal_domain(cfg: &CFG, entries: impl IntoIterator<Item = BlockId>) -> BTreeSet<BlockId> {
        let mut domain = BTreeSet::new();
        let mut pending = entries.into_iter().collect::<Vec<_>>();
        while let Some(block) = pending.pop() {
            if !domain.insert(block) {
                continue;
            }
            pending.extend(cfg.normal_successors(block));
        }
        domain
    }

    fn recompute_exits(&self, region: &mut TryRegion) {
        let blocks = region.blocks.iter().copied().collect::<BTreeSet<_>>();
        let handlers = region
            .handlers
            .iter()
            .flat_map(|handler| handler.blocks.iter().copied())
            .collect::<BTreeSet<_>>();
        region.normal_exit_blocks = blocks
            .iter()
            .copied()
            .filter(|source| {
                self.cfg
                    .normal_successors(*source)
                    .any(|target| !blocks.contains(&target) && !handlers.contains(&target))
            })
            .collect();
    }
}

struct ElidedHandlerTails<'cfg, 'facts> {
    cfg: &'cfg CFG,
    elided: &'facts BTreeSet<StatementOrigin>,
}

struct ElidedExceptionScopes;

impl ElidedExceptionScopes {
    fn prune(
        cfg: &CFG,
        regions: Vec<TryRegion>,
        elided: &BTreeSet<StatementOrigin>,
    ) -> Vec<TryRegion> {
        let parents = regions
            .iter()
            .map(|region| (region.id, region.parent))
            .collect::<BTreeMap<_, _>>();
        let directly_removable = regions
            .iter()
            .filter(|region| {
                let empty = Self::scope_is_empty(cfg, region, elided);
                let non_throwing_catch = region
                    .handlers
                    .iter()
                    .all(|handler| handler.kind == HandlerKind::Catch)
                    && region
                        .blocks
                        .iter()
                        .all(|block| !Self::block_can_throw(cfg, *block, elided));
                let non_throwing_subsumed = !region.blocks.is_empty()
                    && region
                        .blocks
                        .iter()
                        .all(|block| !Self::block_can_throw(cfg, *block, elided))
                    && regions.iter().any(|owner| {
                        owner.id != region.id
                            && region
                                .blocks
                                .iter()
                                .all(|block| owner.blocks.contains(block))
                            && region
                                .handlers
                                .iter()
                                .filter(|handler| handler.kind != HandlerKind::Catch)
                                .all(|handler| {
                                    owner.handlers.iter().any(|candidate| {
                                        candidate.kind == HandlerKind::Finally
                                            && candidate.canonical_entry == handler.canonical_entry
                                    })
                                })
                    });
                empty || non_throwing_catch || non_throwing_subsumed
            })
            .map(|region| region.id)
            .collect::<BTreeSet<_>>();
        let mut removable = BTreeSet::new();
        loop {
            let additions = regions
                .iter()
                .filter(|region| directly_removable.contains(&region.id))
                .filter(|region| {
                    region
                        .children
                        .iter()
                        .all(|child| removable.contains(child))
                })
                .map(|region| region.id)
                .filter(|region| !removable.contains(region))
                .collect::<Vec<_>>();
            if additions.is_empty() {
                break;
            }
            removable.extend(additions);
        }
        let mut retained = regions
            .into_iter()
            .filter(|region| !removable.contains(&region.id))
            .collect::<Vec<_>>();
        for region in &mut retained {
            let mut parent = region.parent;
            while parent.is_some_and(|parent| removable.contains(&parent)) {
                parent = parent.and_then(|parent| parents.get(&parent).copied().flatten());
            }
            region.parent = parent;
            region.children.clear();
        }
        let indices = retained
            .iter()
            .enumerate()
            .map(|(index, region)| (region.id, index))
            .collect::<BTreeMap<_, _>>();
        for child in 0..retained.len() {
            let Some(parent) = retained[child].parent else {
                continue;
            };
            if let Some(parent_index) = indices.get(&parent).copied() {
                let child_id = retained[child].id;
                retained[parent_index].children.push(child_id);
            }
        }
        retained
    }

    fn scope_is_empty(cfg: &CFG, region: &TryRegion, elided: &BTreeSet<StatementOrigin>) -> bool {
        region
            .blocks
            .iter()
            .chain(
                region
                    .handlers
                    .iter()
                    .flat_map(|handler| handler.blocks.iter()),
            )
            .all(|block| Self::block_is_empty(cfg, *block, elided))
    }

    fn block_can_throw(cfg: &CFG, block: BlockId, elided: &BTreeSet<StatementOrigin>) -> bool {
        cfg.block(block).is_some_and(|body| {
            body.insns.iter().any(|instruction| {
                instruction.can_throw()
                    && !(instruction.id.is_valid()
                        && elided.contains(&StatementOrigin {
                            block,
                            instruction: instruction.id,
                        }))
            })
        })
    }

    fn block_is_empty(cfg: &CFG, block: BlockId, elided: &BTreeSet<StatementOrigin>) -> bool {
        cfg.block(block).is_some_and(|body| {
            body.insns.iter().all(|instruction| {
                matches!(
                    instruction.insn_type,
                    InsnType::Nop | InsnType::Phi | InsnType::Goto
                ) || (instruction.id.is_valid()
                    && elided.contains(&StatementOrigin {
                        block,
                        instruction: instruction.id,
                    }))
            })
        })
    }
}

struct HandlerProtectedPartition;

impl HandlerProtectedPartition {
    fn apply(cfg: &CFG, regions: &mut [TryRegion]) -> Result<(), ExceptionInvariantError> {
        let mut protected = regions
            .iter()
            .map(|region| {
                (
                    region.id,
                    region.blocks.iter().copied().collect::<BTreeSet<_>>(),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let normal_predecessors = cfg.normal_predecessor_snapshot();
        let mut entry_removals = BTreeSet::new();
        for owner in regions.iter_mut() {
            for handler in &mut owner.handlers {
                let mut owned = handler.blocks.iter().copied().collect::<BTreeSet<_>>();
                if protected.get(&owner.id).is_some_and(|blocks| {
                    Self::detach_shared_continuation(
                        handler,
                        &mut owned,
                        blocks,
                        &normal_predecessors,
                    )
                }) {
                    entry_removals.insert((owner.id, handler.handler_block));
                }
                let protected_regions = protected.keys().copied().collect::<Vec<_>>();
                for region in protected_regions {
                    let mut blocks = protected
                        .get(&region)
                        .cloned()
                        .ok_or(ExceptionInvariantError::MissingExceptionScope(region))?;
                    if region == owner.id
                        || owned.is_disjoint(&blocks)
                        || blocks.is_subset(&owned)
                        || owned.is_subset(&blocks)
                    {
                        continue;
                    }
                    if blocks.contains(&handler.handler_block) {
                        let closed = Self::transparent_frontier_closure(cfg, &owned, &blocks);
                        if closed.len() != blocks.len() {
                            blocks = closed;
                            protected.insert(region, blocks.clone());
                        }
                        if blocks.is_subset(&owned) || owned.is_subset(&blocks) {
                            continue;
                        }
                        if let Some(boundary) = LexicalBoundaryAnalysis::new(cfg).partition(
                            handler.handler_block,
                            &owned,
                            &blocks,
                        ) {
                            if handler
                                .continuation
                                .is_none_or(|continuation| continuation == boundary.continuation)
                            {
                                owned = boundary.blocks;
                                handler.continuation = Some(boundary.continuation);
                                continue;
                            }
                        }
                        if Self::detach_shared_continuation(
                            handler,
                            &mut owned,
                            &blocks,
                            &normal_predecessors,
                        ) {
                            continue;
                        }
                        // Raw DEX protection and handler ownership are a DAG.
                        // Preserve a crossing that has no provable single
                        // continuation; RegionTree construction owns the
                        // later lexical fragmentation because it has both
                        // handler and protected-region ancestry.
                        continue;
                    }
                    owned
                        .retain(|block| *block == handler.handler_block || !blocks.contains(block));
                }
                handler.blocks.retain(|block| owned.contains(block));
                let semantic = handler
                    .semantic_blocks
                    .iter()
                    .copied()
                    .collect::<BTreeSet<_>>();
                handler
                    .rethrow_blocks
                    .retain(|block| semantic.contains(block));
            }
        }
        for (region, block) in entry_removals {
            if let Some(blocks) = protected.get_mut(&region) {
                blocks.remove(&block);
            }
        }
        for region in regions {
            if let Some(blocks) = protected.get(&region.id) {
                region.blocks = blocks.iter().copied().collect();
            }
        }
        Ok(())
    }

    fn transparent_frontier_closure(
        cfg: &CFG,
        domain: &BTreeSet<BlockId>,
        scope: &BTreeSet<BlockId>,
    ) -> BTreeSet<BlockId> {
        let predecessors = cfg.normal_predecessor_snapshot();
        let mut closed = scope.clone();
        loop {
            let additions = closed
                .intersection(domain)
                .flat_map(|block| {
                    cfg.normal_successors(*block)
                        .chain(predecessors.get(block).into_iter().flatten().copied())
                })
                .filter(|target| domain.contains(target) && !closed.contains(target))
                .filter(|target| Self::is_exception_transparent(cfg, *target))
                .collect::<BTreeSet<_>>();
            if additions.is_empty() {
                return closed;
            }
            closed.extend(additions);
        }
    }

    fn is_exception_transparent(cfg: &CFG, block: BlockId) -> bool {
        cfg.block(block).is_some_and(|block| {
            block
                .insns
                .iter()
                .all(|instruction| !instruction.can_throw())
                && cfg
                    .successors_with_kind(block.id)
                    .iter()
                    .all(|(_, kind)| !kind.is_exception())
        })
    }

    fn detach_shared_continuation(
        handler: &mut CatchHandler,
        owned: &mut BTreeSet<BlockId>,
        protected: &BTreeSet<BlockId>,
        predecessors: &BTreeMap<BlockId, Vec<BlockId>>,
    ) -> bool {
        let Some(continuation) =
            SharedHandlerContinuation::analyze(handler, owned, protected, predecessors)
        else {
            return false;
        };
        owned.remove(&continuation);
        handler.continuation = Some(continuation);
        true
    }
}

struct SharedHandlerContinuation;

impl SharedHandlerContinuation {
    fn analyze(
        handler: &CatchHandler,
        owned: &BTreeSet<BlockId>,
        protected: &BTreeSet<BlockId>,
        predecessors: &BTreeMap<BlockId, Vec<BlockId>>,
    ) -> Option<BlockId> {
        let entry = handler.semantic_entry;
        protected.contains(&entry).then_some(())?;
        owned
            .iter()
            .all(|block| *block == entry || handler.adapter_blocks.contains(block))
            .then_some(())?;
        let semantic_owned = owned
            .iter()
            .copied()
            .chain(std::iter::once(entry))
            .collect::<BTreeSet<_>>();
        semantic_owned
            .intersection(protected)
            .copied()
            .eq(std::iter::once(entry))
            .then_some(())?;
        predecessors
            .get(&entry)?
            .iter()
            .any(|predecessor| !semantic_owned.contains(predecessor))
            .then_some(entry)
    }
}

impl<'cfg, 'facts> ElidedHandlerTails<'cfg, 'facts> {
    fn new(cfg: &'cfg CFG, elided: &'facts BTreeSet<StatementOrigin>) -> Self {
        Self { cfg, elided }
    }

    fn trim(&self, regions: &mut [TryRegion]) {
        for handler in regions
            .iter_mut()
            .flat_map(|region| &mut region.handlers)
            .filter(|handler| handler.kind == HandlerKind::Catch)
        {
            let mut owned = handler.blocks.iter().copied().collect::<BTreeSet<_>>();
            loop {
                let tails = owned
                    .iter()
                    .copied()
                    .filter(|block| *block != handler.handler_block)
                    .filter(|block| self.is_elided_tail(*block, &owned))
                    .collect::<BTreeSet<_>>();
                if tails.is_empty() {
                    break;
                }
                owned.retain(|block| !tails.contains(block));
            }
            handler.blocks.retain(|block| owned.contains(block));
        }
    }

    fn is_elided_tail(&self, block: BlockId, owned: &BTreeSet<BlockId>) -> bool {
        let Some(body) = self.cfg.block(block) else {
            return false;
        };
        let has_only_elided_body = body.insns.iter().all(|instruction| {
            matches!(
                instruction.insn_type,
                InsnType::Nop | InsnType::Phi | InsnType::Goto | InsnType::MoveException
            ) || self.elided.contains(&StatementOrigin {
                block,
                instruction: instruction.id,
            })
        });
        let normal = self.cfg.normal_successors(block).collect::<Vec<_>>();
        let has_exception = self
            .cfg
            .successors_with_kind(block)
            .iter()
            .any(|(_, kind)| *kind == EdgeKind::Exception);
        has_only_elided_body
            && !has_exception
            && !normal.is_empty()
            && normal.iter().all(|target| !owned.contains(target))
    }
}

impl ExceptionRegionHierarchy {
    fn new(regions: Vec<TryRegion>) -> Self {
        Self { regions }
    }

    fn without_empty_scopes(self) -> Vec<TryRegion> {
        let parents = self
            .regions
            .iter()
            .map(|region| (region.id, region.parent))
            .collect::<BTreeMap<_, _>>();
        let retained = self
            .regions
            .iter()
            .filter(|region| !region.blocks.is_empty())
            .map(|region| region.id)
            .collect::<BTreeSet<_>>();
        let mut regions = self
            .regions
            .into_iter()
            .filter(|region| retained.contains(&region.id))
            .collect::<Vec<_>>();
        for region in &mut regions {
            let mut parent = region.parent;
            while parent.is_some_and(|id| !retained.contains(&id)) {
                parent = parent.and_then(|id| parents.get(&id).copied().flatten());
            }
            region.parent = parent;
            region.children.clear();
        }
        let indices = regions
            .iter()
            .enumerate()
            .map(|(index, region)| (region.id, index))
            .collect::<BTreeMap<_, _>>();
        for child in 0..regions.len() {
            let Some(parent) = regions[child].parent else {
                continue;
            };
            if let Some(parent_index) = indices.get(&parent).copied() {
                let child_id = regions[child].id;
                regions[parent_index].children.push(child_id);
            }
        }
        regions
    }
}

struct HandlerBodies {
    owners: BTreeMap<BlockId, BTreeSet<BlockId>>,
    entries: BTreeSet<BlockId>,
}

#[derive(Clone)]
struct HandlerSemanticDomain {
    canonical_entry: BlockId,
    adapter_blocks: BTreeSet<BlockId>,
    blocks: BTreeSet<BlockId>,
}

struct HandlerSemanticDomains {
    domains: BTreeMap<BlockId, HandlerSemanticDomain>,
}

impl HandlerSemanticDomains {
    fn analyze(cfg: &CFG, entries: &BTreeMap<u32, BlockId>) -> Self {
        let entries = entries.values().copied().collect::<BTreeSet<_>>();
        let entry_clauses = HandlerEntryClauses::analyze(cfg, entries.iter().copied());
        let binding_entries = entries
            .iter()
            .copied()
            .filter(|entry| {
                cfg.block(*entry).is_some_and(|block| {
                    block
                        .insns
                        .iter()
                        .any(|instruction| instruction.insn_type == InsnType::MoveException)
                })
            })
            .collect::<BTreeSet<_>>();
        let domains = entries
            .iter()
            .copied()
            .map(|entry| {
                let compatible_entries = entry_clauses.compatible_with(entry);
                let mut blocks = BTreeSet::new();
                let mut pending = vec![entry];
                while let Some(block) = pending.pop() {
                    if (block != entry
                        && binding_entries.contains(&block)
                        && !compatible_entries.contains(&block))
                        || !blocks.insert(block)
                    {
                        continue;
                    }
                    pending.extend(cfg.normal_successors(block));
                }
                let exception_flow = cfg
                    .block(entry)
                    .and_then(|block| {
                        block.insns.iter().find_map(|instruction| {
                            (instruction.insn_type == InsnType::MoveException)
                                .then(|| instruction.result.as_ref().and_then(SsaVar::from_reg))
                                .flatten()
                        })
                    })
                    .map(|exception| HandlerSemantics::exception_flow(cfg, &blocks, exception))
                    .unwrap_or_default();
                let continuation =
                    HandlerContinuation::new(cfg, &blocks, &exception_flow).from(entry);
                (
                    entry,
                    HandlerSemanticDomain {
                        canonical_entry: continuation.entry,
                        adapter_blocks: continuation.adapters,
                        blocks,
                    },
                )
            })
            .collect();
        Self { domains }
    }

    fn domain(&self, entry: BlockId) -> HandlerSemanticDomain {
        self.domains
            .get(&entry)
            .cloned()
            .unwrap_or_else(|| HandlerSemanticDomain {
                canonical_entry: entry,
                adapter_blocks: BTreeSet::new(),
                blocks: BTreeSet::from([entry]),
            })
    }

    fn adapter_map(&self) -> Result<BTreeMap<BlockId, BlockId>, ExceptionInvariantError> {
        let mut adapters = BTreeMap::new();
        for domain in self.domains.values() {
            for block in &domain.adapter_blocks {
                if let Some(left) = adapters.insert(*block, domain.canonical_entry) {
                    if left != domain.canonical_entry {
                        return Err(ExceptionInvariantError::ConflictingHandlerAdapter {
                            block: *block,
                            left,
                            right: domain.canonical_entry,
                        });
                    }
                }
            }
        }
        Ok(adapters)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct SharedHandlerKey {
    entry: BlockId,
    kind: HandlerKind,
}

impl SharedHandlerKey {
    fn from_handler(handler: &CatchHandler) -> Self {
        Self {
            entry: handler.canonical_entry,
            kind: handler.kind,
        }
    }
}

struct SharedHandlerDomain {
    entries: BTreeSet<BlockId>,
    exception: Option<RegisterArg>,
    proven: bool,
}

struct SharedHandlerDomains {
    domains: BTreeMap<SharedHandlerKey, SharedHandlerDomain>,
}

impl SharedHandlerDomains {
    fn analyze(cfg: &CFG, regions: &[TryRegion]) -> Self {
        let mut groups = BTreeMap::<SharedHandlerKey, Vec<&CatchHandler>>::new();
        for handler in regions.iter().flat_map(|region| &region.handlers) {
            groups
                .entry(SharedHandlerKey::from_handler(handler))
                .or_default()
                .push(handler);
        }
        let domains = groups
            .into_iter()
            .map(|(key, handlers)| {
                let entries = handlers
                    .iter()
                    .flat_map(|handler| handler.entry_blocks.iter().copied())
                    .collect::<BTreeSet<_>>();
                let flows = handlers
                    .iter()
                    .map(|handler| Self::exception_flow(cfg, handler))
                    .collect::<Option<Vec<_>>>();
                let common = flows.and_then(|flows| {
                    let mut flows = flows.into_iter();
                    let mut common = flows.next()?;
                    for flow in flows {
                        common.retain(|value| flow.contains(value));
                    }
                    Some(common)
                });
                let exception = common
                    .as_ref()
                    .and_then(|values| Self::reaching_definition(cfg, key.entry, values));
                let proven = entries.len() > 1 && exception.is_some();
                (
                    key,
                    SharedHandlerDomain {
                        entries,
                        exception,
                        proven,
                    },
                )
            })
            .collect();
        Self { domains }
    }

    fn apply(&self, regions: &mut [TryRegion]) {
        for handler in regions.iter_mut().flat_map(|region| &mut region.handlers) {
            let key = SharedHandlerKey::from_handler(handler);
            let Some(domain) = self.domains.get(&key) else {
                continue;
            };
            if !domain.proven || domain.entries.is_empty() {
                continue;
            }
            handler.semantic_entry = handler.canonical_entry;
            handler.canonical_exception_value = domain.exception.clone();
            handler.exception_value = domain.exception.clone();
        }
    }

    fn exception_flow(cfg: &CFG, handler: &CatchHandler) -> Option<BTreeSet<SsaVar>> {
        let exception = handler
            .exception_value
            .as_ref()
            .and_then(SsaVar::from_reg)?;
        let blocks = handler
            .semantic_blocks
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        Some(HandlerSemantics::exception_flow(cfg, &blocks, exception))
    }

    fn reaching_definition(
        cfg: &CFG,
        entry: BlockId,
        candidates: &BTreeSet<SsaVar>,
    ) -> Option<RegisterArg> {
        cfg.block_ids()
            .into_iter()
            .filter_map(|block| {
                let distance = Self::distance(cfg, block, entry)?;
                cfg.block(block)?.insns.iter().find_map(|instruction| {
                    let result = instruction.result.as_ref()?;
                    let value = SsaVar::from_reg(result)?;
                    candidates
                        .contains(&value)
                        .then(|| (distance, block, result.clone()))
                })
            })
            .min_by_key(|(distance, block, value)| {
                (*distance, *block, value.reg_num, value.ssa_version)
            })
            .map(|(_, _, value)| value)
    }

    fn distance(cfg: &CFG, source: BlockId, target: BlockId) -> Option<usize> {
        let mut pending = VecDeque::from([(source, 0usize)]);
        let mut visited = BTreeSet::new();
        while let Some((block, distance)) = pending.pop_front() {
            if !visited.insert(block) {
                continue;
            }
            if block == target {
                return Some(distance);
            }
            pending.extend(
                cfg.normal_successors(block)
                    .map(|successor| (successor, distance + 1)),
            );
        }
        None
    }
}

struct HandlerEntryClauses {
    clauses: BTreeMap<BlockId, BTreeSet<Option<ArgType>>>,
}

impl HandlerEntryClauses {
    fn analyze(cfg: &CFG, entries: impl IntoIterator<Item = BlockId>) -> Self {
        let by_offset = entries
            .into_iter()
            .filter_map(|entry| cfg.block(entry).map(|block| (block.offset, entry)))
            .collect::<BTreeMap<_, _>>();
        let mut clauses = BTreeMap::<BlockId, BTreeSet<Option<ArgType>>>::new();
        for handler in &cfg.handlers {
            let Some(entry) = by_offset.get(&handler.handler).copied() else {
                continue;
            };
            clauses
                .entry(entry)
                .or_default()
                .insert(handler.catch_type.clone());
        }
        Self { clauses }
    }

    fn compatible_with(&self, entry: BlockId) -> BTreeSet<BlockId> {
        let Some(clauses) = self.clauses.get(&entry) else {
            return BTreeSet::from([entry]);
        };
        self.clauses
            .iter()
            .filter_map(|(candidate, candidate_clauses)| {
                (candidate_clauses == clauses).then_some(*candidate)
            })
            .collect()
    }
}

struct HandlerContinuationFact {
    entry: BlockId,
    adapters: BTreeSet<BlockId>,
}

struct HandlerContinuation<'a> {
    cfg: &'a CFG,
    domain: &'a BTreeSet<BlockId>,
    exception_flow: &'a BTreeSet<SsaVar>,
}

struct HandlerAdapterEffects;

impl HandlerAdapterEffects {
    fn is_transparent(block: &super::Block, exception_flow: &BTreeSet<SsaVar>) -> bool {
        block.insns.iter().all(|instruction| {
            let is_bookkeeping = InstructionEffects::is_ssa_bookkeeping(instruction)
                || instruction.insn_type == InsnType::Const;
            let carries_caught_exception = instruction.insn_type != InsnType::MoveException
                && instruction
                    .result
                    .as_ref()
                    .and_then(SsaVar::from_reg)
                    .is_some_and(|result| exception_flow.contains(&result));
            is_bookkeeping && !carries_caught_exception
        })
    }
}

impl<'a> HandlerContinuation<'a> {
    fn new(
        cfg: &'a CFG,
        domain: &'a BTreeSet<BlockId>,
        exception_flow: &'a BTreeSet<SsaVar>,
    ) -> Self {
        Self {
            cfg,
            domain,
            exception_flow,
        }
    }

    fn from(&self, entry: BlockId) -> HandlerContinuationFact {
        let mut current = entry;
        let mut visited = BTreeSet::new();
        let mut adapters = BTreeSet::new();
        while visited.insert(current) {
            let Some(block) = self.cfg.block(current) else {
                break;
            };
            if !HandlerAdapterEffects::is_transparent(block, self.exception_flow) {
                break;
            }
            let successors = self
                .cfg
                .normal_successors(current)
                .filter(|target| self.domain.contains(target))
                .collect::<Vec<_>>();
            let [successor] = successors.as_slice() else {
                break;
            };
            adapters.insert(current);
            current = *successor;
        }
        HandlerContinuationFact {
            entry: current,
            adapters,
        }
    }
}

struct SyntheticScopeClosure {
    components: Vec<SyntheticComponent>,
}

struct SyntheticComponent {
    blocks: BTreeSet<BlockId>,
    boundary: BTreeSet<BlockId>,
}

impl SyntheticScopeClosure {
    fn analyze(cfg: &CFG, predecessors: &BTreeMap<BlockId, Vec<BlockId>>) -> Self {
        let synthetic = cfg
            .blocks
            .values()
            .filter(|block| block.synthetic)
            .map(|block| block.id)
            .collect::<BTreeSet<_>>();
        let mut unseen = synthetic.clone();
        let mut components = Vec::new();
        while let Some(seed) = unseen.pop_first() {
            let mut blocks = BTreeSet::new();
            let mut pending = vec![seed];
            while let Some(block) = pending.pop() {
                if !blocks.insert(block) {
                    continue;
                }
                let neighbors = predecessors
                    .get(&block)
                    .into_iter()
                    .flatten()
                    .copied()
                    .chain(cfg.normal_successors(block));
                for neighbor in neighbors.filter(|neighbor| synthetic.contains(neighbor)) {
                    unseen.remove(&neighbor);
                    pending.push(neighbor);
                }
            }
            let boundary = blocks
                .iter()
                .flat_map(|block| {
                    predecessors
                        .get(block)
                        .into_iter()
                        .flatten()
                        .copied()
                        .chain(cfg.normal_successors(*block))
                })
                .filter(|block| !synthetic.contains(block))
                .collect();
            components.push(SyntheticComponent { blocks, boundary });
        }
        Self { components }
    }

    fn expand(&self, blocks: &mut BTreeSet<BlockId>) {
        for component in &self.components {
            if !component.boundary.is_empty() && component.boundary.is_subset(blocks) {
                blocks.extend(component.blocks.iter().copied());
            }
        }
    }
}

impl HandlerBodies {
    fn new(cfg: &CFG, entries: &BTreeMap<u32, BlockId>, ordinary: &BTreeSet<BlockId>) -> Self {
        let entries = entries.values().copied().collect::<BTreeSet<_>>();
        let mut owners: BTreeMap<BlockId, BTreeSet<BlockId>> = BTreeMap::new();
        for entry in &entries {
            let mut visited = BTreeSet::new();
            let mut work = vec![*entry];
            while let Some(block) = work.pop() {
                if (block != *entry && ordinary.contains(&block))
                    || (block != *entry && entries.contains(&block))
                    || !visited.insert(block)
                {
                    continue;
                }
                owners.entry(block).or_default().insert(*entry);
                work.extend(cfg.normal_successors(block));
            }
        }
        Self { owners, entries }
    }

    fn blocks(&self, entry: BlockId) -> BTreeSet<BlockId> {
        self.owners
            .iter()
            .filter_map(|(block, owners)| {
                (owners.len() == 1 && owners.contains(&entry)).then_some(*block)
            })
            .collect()
    }

    fn handlers(&self) -> impl Iterator<Item = (BlockId, BTreeSet<BlockId>)> + '_ {
        self.entries
            .iter()
            .copied()
            .map(|entry| (entry, self.blocks(entry)))
    }
}

#[derive(Clone, Default)]
struct HandlerDomain {
    blocks: BTreeSet<BlockId>,
    continuation: Option<BlockId>,
}

struct HandlerDomains;

struct SharedExceptionContinuation;

impl SharedExceptionContinuation {
    fn is_shared(
        cfg: &CFG,
        protected: &BTreeSet<BlockId>,
        handler: &CatchHandler,
        ordinary: &BTreeSet<BlockId>,
        physical_handler_entries: &BTreeSet<BlockId>,
    ) -> bool {
        let entry = handler.semantic_entry;
        handler.exception_value.is_none()
            && (ordinary.contains(&entry)
                || cfg
                    .block_ids()
                    .into_iter()
                    .filter(|block| !physical_handler_entries.contains(block))
                    .any(|block| cfg.normal_successors(block).any(|target| target == entry))
                || protected.iter().any(|block| {
                    cfg.normal_successors(*block)
                        .any(|successor| successor == entry)
                }))
    }
}

impl HandlerDomains {
    fn assign(cfg: &CFG, regions: &mut [TryRegion]) {
        let domains = Self::analyze(cfg, regions);
        for region in regions {
            for handler in &mut region.handlers {
                let domain = domains
                    .get(&(region.id, handler.semantic_entry))
                    .cloned()
                    .unwrap_or_default();
                handler.lexical_blocks = domain.blocks.into_iter().collect();
                handler.continuation = domain.continuation;
            }
        }
    }

    fn analyze(cfg: &CFG, regions: &[TryRegion]) -> BTreeMap<(u32, BlockId), HandlerDomain> {
        let ordinary = Self::reachable_from(cfg, [cfg.entry], &BTreeSet::new());
        let entries = regions
            .iter()
            .flat_map(|region| region.handlers.iter().map(|handler| handler.semantic_entry))
            .collect::<BTreeSet<_>>();
        let physical_handler_entries = regions
            .iter()
            .flat_map(|region| &region.handlers)
            .flat_map(|handler| handler.entry_blocks.iter().copied())
            .collect::<BTreeSet<_>>();
        let continuations = regions
            .iter()
            .flat_map(|region| {
                region.handlers.iter().filter(|handler| {
                    Self::is_shared_entry(
                        cfg,
                        region,
                        handler,
                        &ordinary,
                        &physical_handler_entries,
                    )
                })
            })
            .map(|handler| handler.semantic_entry)
            .collect::<BTreeSet<_>>();
        let reachable = entries
            .iter()
            .copied()
            .map(|entry| {
                (
                    entry,
                    Self::handler_reachable(cfg, entry, &entries, &continuations, &ordinary),
                )
            })
            .collect::<BTreeMap<_, _>>();
        // A no-op catch can target a continuation shared with ordinary flow.
        // Such a target is not an exception-only descendant of an enclosing
        // handler. Keep handler-local continuations eligible for ownership.
        let ordinary_continuations = continuations
            .intersection(&ordinary)
            .copied()
            .collect::<BTreeSet<_>>();
        let descendants =
            Self::handler_descendants(regions, &entries, &ordinary_continuations, &reachable);

        regions
            .iter()
            .flat_map(|region| {
                region.handlers.iter().map(|handler| {
                    let entry = handler.semantic_entry;
                    if continuations.contains(&entry) {
                        return (
                            (region.id, entry),
                            HandlerDomain {
                                blocks: BTreeSet::new(),
                                continuation: Some(entry),
                            },
                        );
                    }

                    let family = std::iter::once(entry)
                        .chain(descendants.get(&entry).into_iter().flatten().copied())
                        .collect::<BTreeSet<_>>();
                    let mut blocks = family
                        .iter()
                        .flat_map(|member| reachable.get(member).into_iter().flatten())
                        .filter(|block| {
                            reachable.iter().all(|(other, other_blocks)| {
                                !other_blocks.contains(block) || family.contains(other)
                            })
                        })
                        .copied()
                        .collect::<BTreeSet<_>>();
                    let protected_continuations =
                        Self::reachable_from(cfg, Self::protected_body(region), &entries);
                    blocks.retain(|block| {
                        *block == entry || !protected_continuations.contains(block)
                    });
                    if let Some(parent) = region.parent {
                        let mut envelope = BTreeSet::new();
                        let mut current = Some(parent);
                        while let Some(owner) = current {
                            let Some(owner) = regions.iter().find(|region| region.id == owner)
                            else {
                                break;
                            };
                            envelope.extend(owner.blocks.iter().copied());
                            current = owner.parent;
                        }
                        blocks.retain(|block| *block == entry || envelope.contains(block));
                    }
                    let mut continuation = handler.continuation;
                    let protected = Self::protected_body(region);
                    let reentries = blocks
                        .iter()
                        .copied()
                        .filter(|block| !protected.contains(block))
                        .flat_map(|block| cfg.normal_successors(block))
                        .filter(|target| protected.contains(target))
                        .collect::<BTreeSet<_>>();
                    let mut reentries = reentries.into_iter();
                    if let (Some(reentry), None) = (reentries.next(), reentries.next()) {
                        blocks.retain(|block| !protected.contains(block));
                        continuation = Some(reentry);
                    }
                    if let Some(boundary) =
                        Self::nearest_lexical_boundary(cfg, entry, &blocks, regions, region.id)
                    {
                        let handler_local = blocks.contains(&boundary.continuation)
                            && !ordinary.contains(&boundary.continuation);
                        if !handler_local {
                            blocks = boundary.blocks;
                            continuation = Some(boundary.continuation);
                        }
                    }
                    (
                        (region.id, entry),
                        HandlerDomain {
                            blocks,
                            continuation,
                        },
                    )
                })
            })
            .collect()
    }

    fn is_shared_entry(
        cfg: &CFG,
        region: &TryRegion,
        handler: &CatchHandler,
        ordinary: &BTreeSet<BlockId>,
        physical_handler_entries: &BTreeSet<BlockId>,
    ) -> bool {
        let entry = handler.semantic_entry;
        handler.continuation == Some(entry)
            || SharedExceptionContinuation::is_shared(
                cfg,
                &Self::protected_body(region),
                handler,
                ordinary,
                physical_handler_entries,
            )
    }

    fn nearest_lexical_boundary(
        cfg: &CFG,
        entry: BlockId,
        domain: &BTreeSet<BlockId>,
        regions: &[TryRegion],
        owner: u32,
    ) -> Option<super::analysis::LexicalBoundary> {
        let analysis = LexicalBoundaryAnalysis::new(cfg);
        regions
            .iter()
            .filter(|region| region.id != owner)
            .filter_map(|region| {
                let scope = region.blocks.iter().copied().collect::<BTreeSet<_>>();
                analysis.partition(entry, domain, &scope)
            })
            .min_by_key(|boundary| (boundary.blocks.len(), boundary.continuation))
    }

    /// Returns the lexical try body rather than the raw DEX protection set.
    ///
    /// A finally table also protects the bytecode of sibling catch clauses.
    /// Those blocks remain part of the physical protection interval after
    /// exception-scope coalescing, but they are lexically owned by the catch.
    fn protected_body(region: &TryRegion) -> BTreeSet<BlockId> {
        let handler_blocks = region
            .handlers
            .iter()
            .flat_map(|handler| handler.blocks.iter().copied())
            .collect::<BTreeSet<_>>();
        region
            .blocks
            .iter()
            .copied()
            .filter(|block| !handler_blocks.contains(block))
            .collect()
    }

    fn handler_reachable(
        cfg: &CFG,
        entry: BlockId,
        entries: &BTreeSet<BlockId>,
        continuations: &BTreeSet<BlockId>,
        ordinary: &BTreeSet<BlockId>,
    ) -> BTreeSet<BlockId> {
        let mut reachable = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if block != entry
                && (ordinary.contains(&block)
                    || (entries.contains(&block) && !continuations.contains(&block)))
            {
                continue;
            }
            if !reachable.insert(block) {
                continue;
            }
            pending.extend(cfg.normal_successors(block));
        }
        reachable
    }

    fn handler_descendants(
        regions: &[TryRegion],
        entries: &BTreeSet<BlockId>,
        ordinary_continuations: &BTreeSet<BlockId>,
        reachable: &BTreeMap<BlockId, BTreeSet<BlockId>>,
    ) -> BTreeMap<BlockId, BTreeSet<BlockId>> {
        let mut descendants = entries
            .iter()
            .copied()
            .map(|entry| (entry, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        for outer in entries {
            let Some(outer_blocks) = reachable.get(outer) else {
                continue;
            };
            for region in regions {
                let Some(protected_entry) = region.blocks.first().copied() else {
                    continue;
                };
                if outer_blocks.contains(&protected_entry) {
                    descendants.entry(*outer).or_default().extend(
                        region
                            .handlers
                            .iter()
                            .map(|handler| handler.semantic_entry)
                            .filter(|entry| {
                                entry != outer && !ordinary_continuations.contains(entry)
                            }),
                    );
                }
            }
        }
        loop {
            let additions = descendants
                .iter()
                .map(|(entry, direct)| {
                    let nested = direct
                        .iter()
                        .flat_map(|child| descendants.get(child).into_iter().flatten())
                        .copied()
                        .collect::<BTreeSet<_>>();
                    (*entry, nested)
                })
                .collect::<Vec<_>>();
            let mut changed = false;
            for (entry, nested) in additions {
                let descendants = descendants.entry(entry).or_default();
                let previous = descendants.len();
                descendants.extend(nested);
                changed |= descendants.len() != previous;
            }
            if !changed {
                break;
            }
        }
        descendants
    }

    fn reachable_from(
        cfg: &CFG,
        entries: impl IntoIterator<Item = BlockId>,
        handler_entries: &BTreeSet<BlockId>,
    ) -> BTreeSet<BlockId> {
        let mut reachable = BTreeSet::new();
        let mut pending = entries.into_iter().collect::<Vec<_>>();
        while let Some(block) = pending.pop() {
            if handler_entries.contains(&block) || !reachable.insert(block) {
                continue;
            }
            pending.extend(cfg.normal_successors(block));
        }
        reachable
    }
}

#[derive(Default)]
struct HandlerSemantics {
    exception_value: Option<RegisterArg>,
    canonical_exception_value: Option<RegisterArg>,
    rethrow_blocks: BTreeSet<BlockId>,
    must_rethrow: bool,
}

impl HandlerSemantics {
    fn analyze(
        cfg: &CFG,
        entry: BlockId,
        blocks: &BTreeSet<BlockId>,
        canonical_entry: BlockId,
    ) -> Result<Self, ExceptionInvariantError> {
        let entry_block = cfg
            .block(entry)
            .ok_or(ExceptionInvariantError::MissingHandlerBlock(entry))?;
        let exception_values = entry_block
            .insns
            .iter()
            .filter(|insn| insn.insn_type == InsnType::MoveException)
            .collect::<Vec<_>>();
        let [] = exception_values.as_slice() else {
            let [move_exception] = exception_values.as_slice() else {
                return Err(ExceptionInvariantError::MultipleExceptionValues(entry));
            };
            let exception_value = move_exception
                .result
                .clone()
                .ok_or(ExceptionInvariantError::ExceptionValueWithoutResult(entry))?;
            let exception_key = SsaVar::from_reg(&exception_value)
                .ok_or(ExceptionInvariantError::ExceptionValueWithoutSsa(entry))?;
            let derived = Self::exception_flow(cfg, blocks, exception_key);
            let rethrows = blocks
                .iter()
                .copied()
                .filter(|block| Self::rethrows_exception(cfg, *block, &derived))
                .collect::<BTreeSet<_>>();
            let must_rethrow =
                FiniteExitAnalysis::new(cfg, blocks, &rethrows).all_paths_rethrow(entry);
            let canonical_exception_value = cfg.block(canonical_entry).and_then(|block| {
                block.insns.iter().find_map(|instruction| {
                    instruction.result.as_ref().and_then(|result| {
                        SsaVar::from_reg(result)
                            .filter(|value| derived.contains(value))
                            .map(|_| result.clone())
                    })
                })
            });
            return Ok(Self {
                exception_value: Some(exception_value),
                canonical_exception_value,
                must_rethrow,
                rethrow_blocks: rethrows,
            });
        };
        Ok(Self::default())
    }

    fn kind(&self) -> HandlerKind {
        if !self.must_rethrow || self.rethrow_blocks.is_empty() {
            HandlerKind::Catch
        } else {
            HandlerKind::Cleanup
        }
    }

    fn exception_flow(
        cfg: &CFG,
        blocks: &BTreeSet<BlockId>,
        exception: SsaVar,
    ) -> BTreeSet<SsaVar> {
        let mut derived = BTreeSet::from([exception]);
        loop {
            let mut additions = BTreeSet::new();
            for block in blocks.iter().filter_map(|block| cfg.block(*block)) {
                for instruction in &block.insns {
                    let Some(result) = instruction.result.as_ref().and_then(SsaVar::from_reg)
                    else {
                        continue;
                    };
                    let propagates = match instruction.insn_type {
                        InsnType::Move => instruction
                            .args
                            .first()
                            .and_then(InsnArg::as_register)
                            .and_then(SsaVar::from_reg)
                            .is_some_and(|source| derived.contains(&source)),
                        InsnType::Phi => {
                            let relevant = instruction
                                .payload
                                .phi_edges
                                .iter()
                                .zip(&instruction.args)
                                .filter(|((predecessor, kind), _)| {
                                    *kind == EdgeKind::Normal && blocks.contains(predecessor)
                                })
                                .filter_map(|(_, argument)| {
                                    argument.as_register().and_then(SsaVar::from_reg)
                                })
                                .collect::<Vec<_>>();
                            !relevant.is_empty()
                                && relevant.iter().all(|source| derived.contains(source))
                        }
                        _ => false,
                    };
                    if propagates {
                        additions.insert(result);
                    }
                }
            }
            let previous = derived.len();
            derived.extend(additions);
            if derived.len() == previous {
                break;
            }
        }
        derived
    }

    fn rethrows_exception(cfg: &CFG, block: BlockId, derived: &BTreeSet<SsaVar>) -> bool {
        cfg.block(block)
            .and_then(|block| block.terminator())
            .filter(|insn| insn.insn_type == InsnType::Throw)
            .and_then(|throw| throw.args.first())
            .and_then(InsnArg::as_register)
            .and_then(SsaVar::from_reg)
            .is_some_and(|value| derived.contains(&value))
    }
}

/// Classifies the finite normal exits of a handler domain.
///
/// A cleanup may contain a loop, so backward universal reachability from the
/// rethrow blocks is too strong: it rejects an SCC even when every finite path
/// out of that SCC rethrows the original exception.  Exceptional instruction
/// edges are deliberately outside this analysis because cleanup code is
/// allowed to replace the pending exception with a new one.
struct FiniteExitAnalysis<'a> {
    cfg: &'a CFG,
    owned: &'a BTreeSet<BlockId>,
    rethrows: &'a BTreeSet<BlockId>,
}

impl<'a> FiniteExitAnalysis<'a> {
    fn new(cfg: &'a CFG, owned: &'a BTreeSet<BlockId>, rethrows: &'a BTreeSet<BlockId>) -> Self {
        Self {
            cfg,
            owned,
            rethrows,
        }
    }

    fn all_paths_rethrow(&self, entry: BlockId) -> bool {
        let mut pending = vec![entry];
        let mut visited = BTreeSet::new();
        let mut reaches_rethrow = false;

        while let Some(block) = pending.pop() {
            if !self.owned.contains(&block) || !visited.insert(block) {
                continue;
            }
            if self.rethrows.contains(&block) {
                reaches_rethrow = true;
                continue;
            }

            let successors = self.cfg.normal_successors(block).collect::<Vec<_>>();
            if successors.is_empty() || successors.iter().any(|target| !self.owned.contains(target))
            {
                return false;
            }
            pending.extend(successors);
        }

        reaches_rethrow
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::analysis::ClassHierarchyIndex;
    use crate::ir::{Block, InsnNode};

    fn exception_hierarchy() -> ClassHierarchyIndex {
        let mut hierarchy = ClassHierarchyIndex::default();
        hierarchy.add("java/lang/Object", Vec::new());
        hierarchy.add("java/lang/Throwable", vec!["java/lang/Object".to_string()]);
        hierarchy.add(
            "java/lang/Exception",
            vec!["java/lang/Throwable".to_string()],
        );
        hierarchy.add(
            "java/lang/RuntimeException",
            vec!["java/lang/Exception".to_string()],
        );
        hierarchy.add(
            "test/AnnotatedException",
            vec!["java/lang/Exception".to_string()],
        );
        hierarchy
    }

    fn catch_handler(entry: u32, blocks: &[u32]) -> CatchHandler {
        let blocks = blocks.iter().copied().map(BlockId::new).collect::<Vec<_>>();
        CatchHandler {
            id: entry,
            catch_type: Some(ArgType::object("java/lang/Exception")),
            handler_offset: entry,
            entry_blocks: BTreeSet::from([BlockId::new(entry)]),
            handler_block: BlockId::new(entry),
            semantic_entry: BlockId::new(entry),
            canonical_entry: BlockId::new(entry),
            adapter_blocks: BTreeSet::new(),
            semantic_blocks: blocks.clone(),
            lexical_blocks: blocks.clone(),
            blocks,
            continuation: None,
            exception_value: None,
            canonical_exception_value: None,
            rethrow_blocks: BTreeSet::new(),
            kind: HandlerKind::Catch,
        }
    }

    fn try_region(
        id: u32,
        start: u32,
        end: u32,
        blocks: &[u32],
        handlers: Vec<CatchHandler>,
    ) -> TryRegion {
        TryRegion {
            id,
            start_offset: start,
            end_offset: end,
            blocks: blocks.iter().copied().map(BlockId::new).collect(),
            handlers,
            parent: None,
            children: Vec::new(),
            normal_exit_blocks: Vec::new(),
        }
    }

    #[test]
    fn shared_noop_catch_continuation_is_not_inherited_by_outer_handler() {
        let mut cfg = CFG::new("shared_noop_catch_continuation");
        for block in 0..=7 {
            cfg.add_block(Block::new(block));
        }
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(1), BlockId::new(2), EdgeKind::Exception);
        cfg.add_edge(BlockId::new(1), BlockId::new(6), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(2), BlockId::new(3), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(3), BlockId::new(6), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(3), BlockId::new(6), EdgeKind::Exception);
        cfg.add_edge(BlockId::new(6), BlockId::new(7), EdgeKind::Normal);

        let mut regions = vec![
            try_region(0, 1, 2, &[1], vec![catch_handler(2, &[2, 3, 6])]),
            try_region(1, 3, 4, &[3], vec![catch_handler(6, &[6, 7])]),
        ];
        HandlerDomains::assign(&cfg, &mut regions);

        assert_eq!(
            regions[0].handlers[0].lexical_blocks,
            vec![BlockId::new(2), BlockId::new(3)]
        );
        assert_eq!(regions[1].handlers[0].lexical_blocks, Vec::new());
        assert_eq!(regions[1].handlers[0].continuation, Some(BlockId::new(6)));
    }

    #[test]
    fn detached_preceding_handler_is_not_owned_by_adjacent_try() {
        let mut cfg = CFG::new("adjacent_handler_protection");
        for block in 0..=4 {
            cfg.add_block(Block::new(block));
        }
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Exception);
        cfg.add_edge(BlockId::new(0), BlockId::new(3), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(3), BlockId::new(4), EdgeKind::Exception);
        cfg.add_edge(BlockId::new(1), BlockId::new(2), EdgeKind::Normal);
        let constructed = RegisterArg::new_ssa(0, 0, ArgType::object("java/lang/RuntimeException"));
        let mut construction = InsnNode::new(InsnType::Constructor, 0);
        construction.set_result(constructed);
        cfg.block_mut(BlockId::new(1)).unwrap().push(construction);
        cfg.block_mut(BlockId::new(2))
            .unwrap()
            .push(InsnNode::throw(InsnArg::reg_ssa(
                0,
                0,
                ArgType::unknown_object(),
            )));
        let values = SsaValueGraph::build(&cfg).unwrap();
        let mut outer = catch_handler(4, &[4]);
        outer.catch_type = Some(ArgType::object("test/AnnotatedException"));
        let mut regions = vec![
            try_region(0, 10, 20, &[0], vec![catch_handler(1, &[1, 2])]),
            try_region(1, 20, 40, &[1, 2, 3], vec![outer]),
        ];

        PrecedingHandlerProtectionArtifacts::prune(
            &cfg,
            &mut regions,
            &exception_hierarchy(),
            &values,
        );

        assert_eq!(regions[1].blocks, vec![BlockId::new(3)]);
    }

    #[test]
    fn preceding_handler_flowing_into_adjacent_try_remains_protected() {
        let mut cfg = CFG::new("connected_adjacent_handler_protection");
        for block in 0..=4 {
            cfg.add_block(Block::new(block));
        }
        cfg.add_edge(BlockId::new(1), BlockId::new(2), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(2), BlockId::new(3), EdgeKind::Normal);
        let mut regions = vec![
            try_region(0, 10, 20, &[0], vec![catch_handler(1, &[1, 2])]),
            try_region(1, 20, 40, &[1, 2, 3], vec![catch_handler(4, &[4])]),
        ];

        PrecedingHandlerProtectionArtifacts::prune(
            &cfg,
            &mut regions,
            &exception_hierarchy(),
            &SsaValueGraph::default(),
        );

        assert_eq!(
            regions[1].blocks,
            vec![BlockId::new(1), BlockId::new(2), BlockId::new(3)]
        );
    }

    #[test]
    fn catch_all_keeps_preceding_handler_protected_for_cleanup() {
        let mut cfg = CFG::new("catch_all_cleanup_protection");
        for block in 0..=4 {
            cfg.add_block(Block::new(block));
        }
        cfg.add_edge(BlockId::new(1), BlockId::new(2), EdgeKind::Normal);
        let mut cleanup = catch_handler(4, &[4]);
        cleanup.catch_type = None;
        let mut regions = vec![
            try_region(0, 10, 20, &[0], vec![catch_handler(1, &[1, 2])]),
            try_region(1, 20, 40, &[1, 2, 3], vec![cleanup]),
        ];

        PrecedingHandlerProtectionArtifacts::prune(
            &cfg,
            &mut regions,
            &exception_hierarchy(),
            &SsaValueGraph::default(),
        );

        assert_eq!(
            regions[1].blocks,
            vec![BlockId::new(1), BlockId::new(2), BlockId::new(3)]
        );
    }

    #[test]
    fn caught_throw_keeps_preceding_handler_inside_adjacent_try() {
        let mut cfg = CFG::new("caught_handler_throw");
        for block in 0..=4 {
            cfg.add_block(Block::new(block));
        }
        cfg.add_edge(BlockId::new(1), BlockId::new(2), EdgeKind::Normal);
        cfg.block_mut(BlockId::new(2))
            .unwrap()
            .push(InsnNode::throw(InsnArg::reg(
                0,
                ArgType::object("test/AnnotatedException"),
            )));
        let mut outer = catch_handler(4, &[4]);
        outer.catch_type = Some(ArgType::object("test/AnnotatedException"));
        let mut regions = vec![
            try_region(0, 10, 20, &[0], vec![catch_handler(1, &[1, 2])]),
            try_region(1, 20, 40, &[1, 2, 3], vec![outer]),
        ];

        PrecedingHandlerProtectionArtifacts::prune(
            &cfg,
            &mut regions,
            &exception_hierarchy(),
            &SsaValueGraph::default(),
        );

        assert_eq!(
            regions[1].blocks,
            vec![BlockId::new(1), BlockId::new(2), BlockId::new(3)]
        );
    }

    #[test]
    fn handler_adapter_stops_at_exception_state_transfer() {
        let mut cfg = CFG::new("handler_exception_state_transfer");
        let caught = RegisterArg::new_ssa(0, 0, ArgType::throwable());
        let state = RegisterArg::new_ssa(1, 0, ArgType::throwable());

        let mut entry = Block::new(0);
        entry.push(InsnNode::move_exception(caught.clone()));
        cfg.add_block(entry);

        let mut transfer = Block::new(1);
        transfer.push(InsnNode::mov(state.clone(), InsnArg::Reg(caught.clone())));
        cfg.add_block(transfer);
        cfg.add_block(Block::new(2));
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(1), BlockId::new(2), EdgeKind::Normal);

        let domain = BTreeSet::from([BlockId::new(0), BlockId::new(1), BlockId::new(2)]);
        let exception_flow = BTreeSet::from([
            SsaVar::from_reg(&caught).expect("caught SSA value"),
            SsaVar::from_reg(&state).expect("state SSA value"),
        ]);
        let continuation =
            HandlerContinuation::new(&cfg, &domain, &exception_flow).from(BlockId::new(0));

        assert_eq!(continuation.entry, BlockId::new(1));
        assert_eq!(continuation.adapters, BTreeSet::from([BlockId::new(0)]));
    }
}
