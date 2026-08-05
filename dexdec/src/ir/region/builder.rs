use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    analysis::{ControlFlowFacts, DominatorTree, SsaValueGraph},
    exception::{ExceptionAnalysis, HandlerKind},
    EdgeKind, CFG,
};

use super::{
    control::ControlRegionAnalysis,
    exceptions::{
        ExceptionRegionCanonicalizer, ExceptionRegionRelaminarizer, ExceptionRegionTreeBuilder,
        LexicalTryAnalysis,
    },
    exits::RegionExitAnalysis,
    synchronization::{SynchronizationAnalysis, SynchronizationFact},
    LexicalOwnershipClosure, RegionGraph, RegionId, RegionInvariantError, RegionKind, RegionTree,
};

pub struct RegionGraphBuilder<'a> {
    cfg: &'a CFG,
    exceptions: &'a ExceptionAnalysis,
    values: &'a SsaValueGraph,
}

impl<'a> RegionGraphBuilder<'a> {
    pub fn new(cfg: &'a CFG, exceptions: &'a ExceptionAnalysis, values: &'a SsaValueGraph) -> Self {
        Self {
            cfg,
            exceptions,
            values,
        }
    }

    pub fn build(self) -> Result<RegionGraph, RegionInvariantError> {
        let cfg = self.cfg;
        let analysis = self.exceptions;
        let exceptional_cleanup = ExceptionalCleanupFlow::analyze(cfg, analysis);
        let mut cleanup_representatives = BTreeMap::new();
        for contraction in &analysis.cleanup_contractions {
            for block in &contraction.blocks {
                if *block == contraction.completion {
                    continue;
                }
                if let Some(left) = cleanup_representatives.insert(*block, contraction.completion) {
                    if left != contraction.completion {
                        return Err(RegionInvariantError::ConflictingCleanupContraction {
                            block: *block,
                            left,
                            right: contraction.completion,
                        });
                    }
                }
            }
        }
        let control_flow = ControlFlowFacts::analyze(cfg)?;
        let envelope_cfg = ContractedControlFlow::new(cfg, &cleanup_representatives).build();
        let envelope_flow = ControlFlowFacts::analyze(&envelope_cfg)?;
        let control_regions = ControlRegionAnalysis::new(&envelope_cfg, &envelope_flow);
        let mut control_tree = RegionTree::new(Some(cfg.entry));
        control_tree.cover_method(cfg)?;
        control_regions.apply(&mut control_tree)?;
        control_tree.canonicalize_nesting()?;
        let (mut tree, mut exception_region_map, mut exception_handlers) =
            ExceptionRegionTreeBuilder::new(
                analysis,
                cfg,
                &control_flow,
                &envelope_cfg,
                &envelope_flow,
                &cleanup_representatives,
                control_tree,
            )
            .build()?;
        tree.cover_method(cfg)?;
        LexicalTryAnalysis::new(cfg, &control_flow).apply(&mut tree, &exception_region_map)?;
        let exact_dominators = DominatorTree::compute(cfg)?;
        let mut elisions =
            super::InstructionElisions::from_candidates(analysis.elided_instructions.clone());
        let synchronization =
            SynchronizationAnalysis::new(cfg, self.values, &exact_dominators, &analysis.regions);
        let mut synchronized = analysis
            .regions
            .iter()
            .filter_map(|source| {
                let fact = synchronization.region(source)?;
                let regions = exception_region_map.get(&source.id)?;
                let owner = regions
                    .iter()
                    .copied()
                    .find(|region| {
                        tree.region(*region)
                            .is_some_and(|region| region.owns_block(fact.body_entry))
                    })
                    .or_else(|| regions.first().copied())?;
                Some(SynchronizationCandidate {
                    owner,
                    source_regions: regions.clone(),
                    fact,
                })
            })
            .collect::<Vec<_>>();
        synchronized =
            SynchronizationCandidate::canonicalize(&synchronization, &tree, synchronized)?;
        let claimed_enters = synchronized
            .iter()
            .map(|candidate| candidate.fact.enter_origin.clone())
            .collect();
        for fact in synchronization.standalone(&claimed_enters) {
            synchronized.push(SynchronizationCandidate::from_release_ownership(
                analysis,
                &tree,
                &exception_region_map,
                fact,
            )?);
        }
        synchronized =
            SynchronizationCandidate::canonicalize(&synchronization, &tree, synchronized)?;
        synchronized = SynchronizationCandidate::schedule(synchronized);
        for candidate in synchronized {
            let region_id = candidate.owner;
            let handlers = candidate.handlers(&exception_handlers);
            let release_segments = candidate.release_segments(cfg, &tree, &exception_handlers);
            let fact = candidate.fact;
            let mut lexical_scope = fact.scope_blocks.clone();
            lexical_scope.extend(fact.release_origins.iter().map(|origin| origin.block));
            let rewrite = tree.synchronize(
                cfg,
                &exception_handlers,
                region_id,
                &handlers,
                fact.lock,
                fact.enter_origin.block,
                fact.body_entry,
                &lexical_scope,
                &fact.release_entries,
                &release_segments,
                cfg.method().is_declared_synchronized() && fact.enter_origin.block == cfg.entry,
            )?;
            for (split, split_handlers) in &rewrite.handler_splits {
                for regions in exception_region_map.values_mut() {
                    if regions.contains(&region_id) {
                        regions.push(*split);
                        regions.sort_unstable();
                        regions.dedup();
                    }
                }
                exception_handlers.insert(*split, split_handlers.clone());
                if let Some(owner_handlers) = exception_handlers.get_mut(&region_id) {
                    owner_handlers.retain(|handler| !split_handlers.contains(handler));
                }
            }
            for (source, split) in rewrite.splits {
                for regions in exception_region_map.values_mut() {
                    if regions.contains(&source) {
                        regions.push(split);
                        regions.sort_unstable();
                        regions.dedup();
                    }
                }
                if let Some(handlers) = exception_handlers.get(&source).cloned() {
                    exception_handlers.insert(split, handlers);
                }
            }
            let removed = rewrite.removed;
            for mapped in exception_region_map.values_mut().flatten() {
                if removed.contains(mapped) {
                    *mapped = region_id;
                }
            }
            let inherited = removed
                .iter()
                .filter_map(|removed| exception_handlers.remove(removed))
                .flatten()
                .collect::<Vec<_>>();
            if !inherited.is_empty() {
                exception_handlers
                    .entry(region_id)
                    .or_default()
                    .extend(inherited);
            }
            for handlers in exception_handlers.values_mut() {
                for handler in handlers.iter_mut() {
                    if removed.contains(handler) {
                        *handler = region_id;
                    }
                }
                handlers.sort();
                handlers.dedup();
            }
            elisions.insert_source_equivalent(fact.enter_origin);
            elisions.extend_source_equivalent(fact.release_origins);
        }
        ExceptionRegionRelaminarizer::new(
            analysis,
            cfg,
            &envelope_cfg,
            &envelope_flow,
            &cleanup_representatives,
        )
        .apply(
            &mut tree,
            &mut exception_region_map,
            &mut exception_handlers,
        )?;
        ExceptionRegionCanonicalizer::apply(
            analysis,
            cfg,
            &mut tree,
            &mut exception_region_map,
            &mut exception_handlers,
        )?;
        tree.cover_method(cfg)?;
        tree.canonicalize_nesting()?;
        tree.remove_control_regions()?;
        LexicalOwnershipClosure::apply(cfg, &control_flow, &exception_handlers, &mut tree)?;
        tree.canonicalize_nesting()?;
        control_regions.apply_loops_with_handlers(&mut tree, &exception_handlers)?;
        control_regions.apply_switches(&mut tree)?;
        tree.canonicalize_nesting()?;
        tree.cover_method(cfg)?;
        tree.close_ancestor_ownership()?;
        tree.verify(cfg)?;

        let block_owners = tree.block_owners(cfg)?;
        let implicit_cleanup_completions = ImplicitCleanupCompletions::analyze(&tree, analysis);
        let handler_adapters = analysis.handler_adapters.clone();
        let exits = RegionExitAnalysis::new(
            cfg,
            &tree,
            &elisions,
            &control_flow,
            &cleanup_representatives,
            &exception_handlers,
        )
        .analyze()?;
        let mut edge_leaves = BTreeMap::new();
        for (index, resolved) in exits.leaves.iter().enumerate() {
            let Some(edge) = resolved.leave.edge else {
                continue;
            };
            if edge_leaves.insert(edge, index).is_some() {
                return Err(RegionInvariantError::DuplicateLeaveEdge(edge));
            }
        }
        let graph = RegionGraph {
            tree,
            control_flow,
            exception_region_map,
            exception_handlers,
            handler_adapters,
            cleanup_representatives,
            cleanup_value_bindings: analysis.cleanup_value_bindings.clone(),
            implicit_cleanup_completions,
            exceptional_contractions: exceptional_cleanup.contractions,
            exceptional_rethrow_sources: exceptional_cleanup.rethrow_sources,
            block_owners,
            transfers: exits.transfers,
            leaves: exits.leaves,
            edge_leaves,
            elisions,
        };
        graph.verify(cfg)?;
        Ok(graph)
    }
}

struct ImplicitCleanupCompletions;

impl ImplicitCleanupCompletions {
    fn analyze(
        tree: &RegionTree,
        analysis: &ExceptionAnalysis,
    ) -> BTreeMap<RegionId, BTreeSet<crate::ir::BlockId>> {
        let finally_regions = tree
            .regions()
            .filter(|region| matches!(&region.kind, RegionKind::Finally))
            .collect::<Vec<_>>();
        let mut completions = BTreeMap::<RegionId, BTreeSet<_>>::new();
        for handler in analysis
            .regions
            .iter()
            .flat_map(|region| &region.handlers)
            .filter(|handler| handler.kind == HandlerKind::Finally)
        {
            let candidates = finally_regions
                .iter()
                .filter(|region| region.entry == Some(handler.semantic_entry))
                .map(|region| region.id)
                .collect::<Vec<_>>();
            let [region] = candidates.as_slice() else {
                continue;
            };
            completions
                .entry(*region)
                .or_default()
                .extend(handler.rethrow_blocks.iter().copied());
        }
        completions
    }
}

/// Projects a synthetic cleanup handler onto the exceptional continuations
/// reached after it rethrows. The exception analysis already proves which
/// blocks preserve and rethrow the caught value, so this relation is derived
/// from dataflow facts rather than rediscovering bytecode shapes.
struct ExceptionalCleanupFlow {
    contractions: Vec<(crate::ir::BlockId, crate::ir::BlockId)>,
    rethrow_sources: BTreeMap<crate::ir::BlockId, BTreeSet<crate::ir::BlockId>>,
}

impl ExceptionalCleanupFlow {
    fn analyze(cfg: &CFG, analysis: &ExceptionAnalysis) -> Self {
        let mut relations = BTreeSet::new();
        let mut rethrow_sources =
            BTreeMap::<crate::ir::BlockId, BTreeSet<crate::ir::BlockId>>::new();
        let predecessors = cfg.predecessor_snapshot();
        for handler in analysis
            .regions
            .iter()
            .flat_map(|region| &region.handlers)
            .filter(|handler| matches!(handler.kind, HandlerKind::Cleanup | HandlerKind::Finally))
        {
            let component = Self::component(handler);
            let sources = component
                .iter()
                .flat_map(|entry| cfg.incoming_edges(*entry))
                .filter(|(source, kind)| {
                    *kind == EdgeKind::Exception && !component.contains(source)
                })
                .map(|(source, _)| source)
                .collect::<BTreeSet<_>>();
            for rethrow in &handler.rethrow_blocks {
                let continuations = cfg
                    .successors_with_kind(*rethrow)
                    .into_iter()
                    .filter(|(_, kind)| *kind == EdgeKind::Exception)
                    .map(|(target, _)| *target)
                    .filter(|target| !component.contains(target))
                    .collect::<BTreeSet<_>>();
                if continuations.is_empty() {
                    continue;
                }
                if !sources.is_empty() {
                    rethrow_sources
                        .entry(*rethrow)
                        .or_default()
                        .extend(sources.iter().copied());
                }
                let slice = Self::reverse_slice(*rethrow, &component, &predecessors);
                for block in slice {
                    relations.extend(
                        continuations
                            .iter()
                            .map(|continuation| (block, *continuation)),
                    );
                }
            }
        }
        Self {
            contractions: relations.into_iter().collect(),
            rethrow_sources: Self::resolve_rethrow_sources(rethrow_sources),
        }
    }

    fn resolve_rethrow_sources(
        sources: BTreeMap<crate::ir::BlockId, BTreeSet<crate::ir::BlockId>>,
    ) -> BTreeMap<crate::ir::BlockId, BTreeSet<crate::ir::BlockId>> {
        sources
            .keys()
            .copied()
            .map(|rethrow| {
                let mut resolved = BTreeSet::new();
                let mut visited = BTreeSet::new();
                let mut pending = sources
                    .get(&rethrow)
                    .into_iter()
                    .flatten()
                    .copied()
                    .collect::<Vec<_>>();
                while let Some(source) = pending.pop() {
                    if !visited.insert(source) {
                        continue;
                    }
                    if let Some(nested) = sources.get(&source) {
                        pending.extend(nested.iter().copied());
                    } else {
                        resolved.insert(source);
                    }
                }
                (rethrow, resolved)
            })
            .collect()
    }

    fn component(handler: &crate::ir::exception::CatchHandler) -> BTreeSet<crate::ir::BlockId> {
        let mut component = handler.entry_blocks.clone();
        component.extend(handler.adapter_blocks.iter().copied());
        component.extend(handler.blocks.iter().copied());
        component.extend(handler.semantic_blocks.iter().copied());
        component.extend(handler.rethrow_blocks.iter().copied());
        component.insert(handler.handler_block);
        component.insert(handler.semantic_entry);
        component.insert(handler.canonical_entry);
        component
    }

    fn reverse_slice(
        rethrow: crate::ir::BlockId,
        component: &BTreeSet<crate::ir::BlockId>,
        predecessors: &BTreeMap<crate::ir::BlockId, Vec<crate::ir::BlockId>>,
    ) -> BTreeSet<crate::ir::BlockId> {
        let mut slice = BTreeSet::new();
        let mut pending = vec![rethrow];
        while let Some(block) = pending.pop() {
            if !component.contains(&block) || !slice.insert(block) {
                continue;
            }
            pending.extend(predecessors.get(&block).into_iter().flatten().copied());
        }
        slice
    }
}

struct ContractedControlFlow<'a> {
    cfg: &'a CFG,
    representatives: &'a BTreeMap<crate::ir::BlockId, crate::ir::BlockId>,
}

impl<'a> ContractedControlFlow<'a> {
    fn new(
        cfg: &'a CFG,
        representatives: &'a BTreeMap<crate::ir::BlockId, crate::ir::BlockId>,
    ) -> Self {
        Self {
            cfg,
            representatives,
        }
    }

    fn build(&self) -> CFG {
        let redirects = self
            .cfg
            .graph_node_ids()
            .into_iter()
            .filter(|source| !self.representatives.contains_key(source))
            .flat_map(|source| {
                self.cfg
                    .successors_with_kind(source)
                    .iter()
                    .filter(|(_, kind)| *kind != EdgeKind::Exception)
                    .filter_map(move |(target, kind)| {
                        self.representatives
                            .get(target)
                            .copied()
                            .map(|completion| (source, completion, *kind))
                    })
            })
            .collect::<Vec<_>>();

        let mut normalized = self.cfg.clone();
        for block in self.representatives.keys().copied() {
            normalized.remove_block(block);
        }
        for (source, completion, kind) in redirects {
            if normalized.block(source).is_some() && normalized.block(completion).is_some() {
                normalized.add_edge(source, completion, kind);
            }
        }
        Self::retain_reachable(&mut normalized);
        normalized
    }

    fn retain_reachable(cfg: &mut CFG) {
        let reachable = cfg.reachable();
        let unreachable = cfg
            .block_ids()
            .into_iter()
            .filter(|block| !reachable.contains(block))
            .collect::<Vec<_>>();
        for block in unreachable {
            cfg.remove_block(block);
        }
    }
}

struct SynchronizationCandidate {
    owner: RegionId,
    source_regions: Vec<RegionId>,
    fact: SynchronizationFact,
}

impl SynchronizationCandidate {
    fn handlers(&self, handlers: &BTreeMap<RegionId, Vec<RegionId>>) -> Vec<RegionId> {
        let mut regions = self
            .source_regions
            .iter()
            .chain(std::iter::once(&self.owner))
            .flat_map(|region| handlers.get(region).into_iter().flatten().copied())
            .collect::<Vec<_>>();
        regions.sort_unstable();
        regions.dedup();
        regions
    }

    /// Region rewrites are destructive: recovering an outer monitor first can
    /// consume the try envelope that owns a nested monitor. Apply lexical
    /// scopes from the inside out so every candidate is placed while its
    /// exception-region owner is still live.
    fn schedule(mut candidates: Vec<Self>) -> Vec<Self> {
        candidates.sort_by_key(|candidate| {
            (
                candidate.fact.scope_blocks.len(),
                candidate.fact.enter_origin.block,
                candidate.fact.body_entry,
            )
        });
        candidates
    }

    fn from_release_ownership(
        analysis: &ExceptionAnalysis,
        tree: &RegionTree,
        region_map: &BTreeMap<u32, Vec<RegionId>>,
        fact: SynchronizationFact,
    ) -> Result<Self, RegionInvariantError> {
        let source_regions = analysis
            .regions
            .iter()
            .filter(|source| {
                source.handlers.iter().any(|handler| {
                    fact.release_entries.contains(&handler.handler_block)
                        || fact.release_entries.contains(&handler.semantic_entry)
                        || fact.release_entries.contains(&handler.canonical_entry)
                        || !fact.release_entries.is_disjoint(&handler.entry_blocks)
                })
            })
            .flat_map(|source| region_map.get(&source.id).into_iter().flatten().copied())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let lexical_owner = tree.owner(fact.body_entry)?;
        let owner = source_regions
            .iter()
            .copied()
            .filter(|region| {
                tree.region(*region).is_some_and(|region| {
                    region.owns_block(fact.body_entry) || region.owns_block(fact.enter_origin.block)
                })
            })
            .min_by_key(|region| {
                tree.region(*region)
                    .map(|region| region.blocks.len())
                    .unwrap_or(usize::MAX)
            })
            .or_else(|| source_regions.first().copied())
            .unwrap_or(lexical_owner);
        Ok(Self {
            owner,
            source_regions,
            fact,
        })
    }

    fn canonicalize(
        analysis: &SynchronizationAnalysis<'_>,
        tree: &RegionTree,
        candidates: Vec<Self>,
    ) -> Result<Vec<Self>, RegionInvariantError> {
        let mut groups = BTreeMap::<crate::ir::StatementOrigin, Vec<Self>>::new();
        for candidate in candidates {
            groups
                .entry(candidate.fact.enter_origin.clone())
                .or_default()
                .push(candidate);
        }
        groups
            .into_values()
            .map(|group| {
                let enter = group[0].fact.enter_origin.clone();
                let fact = analysis
                    .canonical_fact(group.iter().map(|candidate| &candidate.fact))
                    .ok_or_else(|| RegionInvariantError::ConflictingSynchronizationFacts {
                        enter: enter.clone(),
                    })?;
                let owner = group
                    .iter()
                    .filter(|candidate| fact.scope_blocks.is_subset(&candidate.fact.scope_blocks))
                    .min_by_key(|candidate| candidate.fact.scope_blocks.len())
                    .map(|candidate| candidate.owner)
                    .ok_or_else(|| RegionInvariantError::ConflictingSynchronizationFacts {
                        enter: enter.clone(),
                    })?;
                let source_regions = group
                    .iter()
                    .flat_map(|candidate| candidate.source_regions.iter().copied())
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect::<Vec<_>>();
                tree.region(owner)
                    .ok_or(RegionInvariantError::UnknownRegion(owner))?;
                Ok(Self {
                    owner,
                    source_regions,
                    fact,
                })
            })
            .collect()
    }

    fn release_segments(
        &self,
        cfg: &CFG,
        tree: &RegionTree,
        handlers: &BTreeMap<RegionId, Vec<RegionId>>,
    ) -> BTreeSet<RegionId> {
        self.source_regions
            .iter()
            .copied()
            .filter(|region| *region != self.owner)
            .filter(|region| {
                tree.region(*region).is_some_and(|region| {
                    matches!(&region.kind, RegionKind::Try)
                        && region
                            .blocks
                            .difference(&self.fact.scope_blocks)
                            .all(|block| Self::is_non_throwing(cfg, *block))
                })
            })
            .filter(|region| {
                handlers.get(region).is_some_and(|handlers| {
                    !handlers.is_empty()
                        && handlers.iter().all(|handler| {
                            tree.region(*handler).is_some_and(|handler| {
                                handler
                                    .entry
                                    .is_some_and(|entry| self.fact.release_entries.contains(&entry))
                            })
                        })
                })
            })
            .collect()
    }

    fn is_non_throwing(cfg: &CFG, block: crate::ir::BlockId) -> bool {
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
}
