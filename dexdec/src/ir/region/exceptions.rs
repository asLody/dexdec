//! Construction of exception-owned region hierarchy.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::analysis::ControlFlowFacts;
use crate::ir::exception::{CatchHandler, CleanupProofOutcome, ExceptionAnalysis, HandlerKind};
use crate::ir::{Block, BlockId, StatementOrigin, CFG};

use super::{CatchRegion, RegionId, RegionInvariantError, RegionKind, RegionPlacement, RegionTree};

pub(super) struct ExceptionRegionTreeBuilder<'a> {
    analysis: &'a ExceptionAnalysis,
    cfg: &'a CFG,
    facts: &'a ControlFlowFacts,
    envelope_cfg: &'a CFG,
    envelope_facts: &'a ControlFlowFacts,
    cleanup_representatives: &'a BTreeMap<BlockId, BlockId>,
    tree: RegionTree,
    mapping: BTreeMap<u32, Vec<RegionId>>,
    handlers: BTreeMap<RegionId, Vec<RegionId>>,
    handler_regions: BTreeMap<BlockId, Vec<RegionId>>,
    handler_domains: BTreeMap<RegionId, BTreeSet<BlockId>>,
}

pub(super) struct ExceptionRegionCanonicalizer;

impl ExceptionRegionCanonicalizer {
    pub(super) fn apply(
        analysis: &ExceptionAnalysis,
        cfg: &CFG,
        tree: &mut RegionTree,
        mapping: &mut BTreeMap<u32, Vec<RegionId>>,
        handlers: &mut BTreeMap<RegionId, Vec<RegionId>>,
    ) -> Result<(), RegionInvariantError> {
        Self::coalesce_finally_families(analysis, cfg, tree, handlers)?;
        for regions in mapping.values_mut() {
            regions.sort_unstable();
            regions.dedup();
            let members = regions.iter().copied().collect::<BTreeSet<_>>();
            let mut redundant = Vec::new();
            for region in members.iter().copied() {
                let chain = tree.parent_chain(region)?;
                if chain.iter().skip(1).any(|ancestor| {
                    members.contains(ancestor)
                        && Self::equivalent_try_owner(tree, handlers, region, *ancestor)
                }) {
                    redundant.push((chain.len(), region));
                }
            }
            redundant.sort_by_key(|(depth, _)| std::cmp::Reverse(*depth));
            for (_, region) in &redundant {
                tree.remove_region_promoting_children(*region)?;
                handlers.remove(region);
            }
            let removed = redundant
                .into_iter()
                .map(|(_, region)| region)
                .collect::<BTreeSet<_>>();
            regions.retain(|region| !removed.contains(region));
        }
        Ok(())
    }

    /// DEX cannot overlap protected intervals, so javac/d8 split one lexical
    /// try/finally around nested catches and their handler bodies. When those
    /// intervals share one proven source-finally handler, recover the outer
    /// scope before semantic reduction. The proven normal cleanup copy is the
    /// lexical exit and must remain outside the recovered try body.
    fn coalesce_finally_families(
        analysis: &ExceptionAnalysis,
        cfg: &CFG,
        tree: &mut RegionTree,
        handlers: &mut BTreeMap<RegionId, Vec<RegionId>>,
    ) -> Result<(), RegionInvariantError> {
        let finally_regions = tree
            .regions()
            .filter(|region| matches!(&region.kind, RegionKind::Finally))
            .map(|region| region.id)
            .collect::<Vec<_>>();
        for finally in finally_regions {
            let Some(finally_entry) = tree
                .region(finally)
                .ok_or(RegionInvariantError::UnknownRegion(finally))?
                .entry
            else {
                continue;
            };
            let sources = analysis
                .regions
                .iter()
                .filter_map(|source| {
                    let cleanup = source.handlers.iter().find(|handler| {
                        handler.kind != HandlerKind::Catch
                            && handler.semantic_entry == finally_entry
                    })?;
                    Some((source, cleanup))
                })
                .collect::<Vec<_>>();
            if sources.len() < 2 {
                continue;
            }

            let mut owners = handlers
                .iter()
                .filter_map(|(owner, owned)| owned.contains(&finally).then_some(*owner))
                .collect::<BTreeSet<_>>();
            if owners.len() < 2 {
                continue;
            }
            let normal_exits = analysis
                .cleanup_proofs
                .iter()
                .filter(|proof| proof.outcome == CleanupProofOutcome::Proven)
                .filter(|proof| {
                    sources.iter().any(|(source, cleanup)| {
                        source.id == proof.region && cleanup.id == proof.handler
                    })
                })
                .map(|proof| proof.normal_entry)
                .collect::<BTreeSet<_>>();
            if normal_exits.is_empty() {
                continue;
            }
            let final_component = sources
                .iter()
                .flat_map(|(_, handler)| {
                    handler
                        .entry_blocks
                        .iter()
                        .chain(&handler.adapter_blocks)
                        .chain(&handler.blocks)
                        .chain(&handler.semantic_blocks)
                        .chain(&handler.rethrow_blocks)
                        .copied()
                        .chain([
                            handler.handler_block,
                            handler.semantic_entry,
                            handler.canonical_entry,
                        ])
                })
                .collect::<BTreeSet<_>>();

            while owners.len() > 1 {
                let Some(start) = owners
                    .iter()
                    .copied()
                    .filter_map(|owner| {
                        let entry = tree.region(owner)?.entry?;
                        let offset = cfg
                            .block(entry)
                            .map(|block| block.offset)
                            .unwrap_or(u32::MAX);
                        Some((offset, entry, owner))
                    })
                    .min()
                else {
                    break;
                };
                let (_, entry, first_owner) = start;
                let mut domain = BTreeSet::new();
                let mut pending = vec![entry];
                while let Some(block) = pending.pop() {
                    if normal_exits.contains(&block)
                        || final_component.contains(&block)
                        || !domain.insert(block)
                    {
                        continue;
                    }
                    pending.extend(
                        cfg.successors_with_kind(block)
                            .iter()
                            .map(|(target, _)| *target),
                    );
                }
                let members = owners
                    .iter()
                    .copied()
                    .filter(|owner| {
                        tree.region(*owner)
                            .and_then(|region| region.entry)
                            .is_some_and(|entry| domain.contains(&entry))
                    })
                    .collect::<BTreeSet<_>>();
                if members.len() < 2 {
                    owners.remove(&first_owner);
                    continue;
                }
                domain = tree.laminar_closure(&domain);
                if !normal_exits.is_disjoint(&domain) || !final_component.is_disjoint(&domain) {
                    owners.remove(&first_owner);
                    continue;
                }
                let synthetic = match tree.insert_laminar_region(RegionKind::Try, entry, domain)? {
                    RegionPlacement::Inserted(region) => region,
                    RegionPlacement::Residual => {
                        owners.remove(&first_owner);
                        continue;
                    }
                };
                handlers.insert(synthetic, vec![finally]);
                for member in &members {
                    if let Some(owned) = handlers.get_mut(member) {
                        owned.retain(|handler| *handler != finally);
                    }
                }
                owners.retain(|owner| !members.contains(owner));
            }
        }
        Ok(())
    }

    fn equivalent_try_owner(
        tree: &RegionTree,
        handlers: &BTreeMap<RegionId, Vec<RegionId>>,
        region: RegionId,
        ancestor: RegionId,
    ) -> bool {
        matches!(
            (
                tree.region(region).map(|region| &region.kind),
                tree.region(ancestor).map(|region| &region.kind),
            ),
            (Some(RegionKind::Try), Some(RegionKind::Try))
        ) && handlers.get(&region) == handlers.get(&ancestor)
    }
}

#[derive(Debug)]
struct TryScope {
    region: RegionId,
    entry: BlockId,
    blocks: BTreeSet<BlockId>,
    depth: usize,
}

struct TryRegionEnvelope {
    entry: BlockId,
    blocks: BTreeSet<BlockId>,
}

/// Proves that adding a throwing block to a lexical try envelope does not
/// expose it to the envelope's handlers. This is true when every exceptional
/// transfer is already intercepted inside the candidate domain by a nested
/// exception scope.
struct ExceptionalContainment<'cfg> {
    cfg: &'cfg CFG,
    handlers: &'cfg BTreeSet<BlockId>,
}

impl<'cfg> ExceptionalContainment<'cfg> {
    fn new(cfg: &'cfg CFG, handlers: &'cfg BTreeSet<BlockId>) -> Self {
        Self { cfg, handlers }
    }

    fn is_internal(&self, block: BlockId, domain: &BTreeSet<BlockId>) -> bool {
        let targets = self
            .cfg
            .successors_with_kind(block)
            .iter()
            .filter_map(|(target, kind)| kind.is_exception().then_some(*target))
            .collect::<Vec<_>>();
        !targets.is_empty()
            && targets
                .iter()
                .all(|target| domain.contains(target) || self.handlers.contains(target))
    }
}

#[derive(Debug)]
enum TryEnvelopeRejection {
    MissingEntry,
    EntryOutsideProtection(BlockId),
    ThrowingExpansion(BTreeSet<BlockId>),
    ExternalEntries(BTreeMap<BlockId, Vec<BlockId>>),
    Undominated(BTreeSet<BlockId>),
}

enum TryEnvelopeProof {
    Proven(TryRegionEnvelope),
    Rejected(Vec<TryEnvelopeRejection>),
}

impl TryEnvelopeProof {
    fn proven(self) -> Option<TryRegionEnvelope> {
        match self {
            Self::Proven(envelope) => Some(envelope),
            Self::Rejected(_) => None,
        }
    }
}

struct TryRegionEnvelopeAnalysis<'a> {
    analysis: &'a ExceptionAnalysis,
    source_cfg: &'a CFG,
    cfg: &'a CFG,
    facts: &'a ControlFlowFacts,
    representatives: &'a BTreeMap<BlockId, BlockId>,
    tree: &'a RegionTree,
}

impl<'a> TryRegionEnvelopeAnalysis<'a> {
    fn new(
        analysis: &'a ExceptionAnalysis,
        source_cfg: &'a CFG,
        cfg: &'a CFG,
        facts: &'a ControlFlowFacts,
        representatives: &'a BTreeMap<BlockId, BlockId>,
        tree: &'a RegionTree,
    ) -> Self {
        Self {
            analysis,
            source_cfg,
            cfg,
            facts,
            representatives,
            tree,
        }
    }

    fn analyze(
        &self,
        source: &crate::ir::exception::TryRegion,
    ) -> Result<TryEnvelopeProof, RegionInvariantError> {
        let mut protected = source.blocks.iter().copied().collect::<BTreeSet<_>>();
        protected.extend(self.nested_handlers(source)?);
        protected.extend(self.lexical_exit_suffixes(source));
        protected.retain(|block| self.cfg.block(*block).is_some());
        let Some(range_entry) = self.range_entry(source) else {
            return Ok(TryEnvelopeProof::Rejected(vec![
                TryEnvelopeRejection::MissingEntry,
            ]));
        };
        let entry = self.lexical_entry(range_entry, &protected);
        let source_handlers = source
            .handlers
            .iter()
            .flat_map(|handler| {
                handler
                    .blocks
                    .iter()
                    .copied()
                    .chain(handler.entry_blocks.iter().copied())
                    .chain(handler.adapter_blocks.iter().copied())
            })
            .collect::<BTreeSet<_>>();
        let mut rejected = Vec::new();
        let mut blocks = protected.clone();
        blocks.extend(self.normal_connectors(&protected)?);
        blocks.extend(self.entry_connectors(entry, &protected, &source_handlers)?);
        match self.prove(source, entry, blocks, &protected, &source_handlers)? {
            TryEnvelopeProof::Proven(envelope) => {
                return Ok(TryEnvelopeProof::Proven(envelope));
            }
            TryEnvelopeProof::Rejected(reasons) => rejected.extend(reasons),
        }

        let mut lexical = self.range_blocks(source);
        lexical.extend(protected.iter().copied());
        lexical.extend(self.entry_connectors(entry, &protected, &source_handlers)?);
        match self.prove(source, entry, lexical, &protected, &source_handlers)? {
            TryEnvelopeProof::Proven(envelope) => Ok(TryEnvelopeProof::Proven(envelope)),
            TryEnvelopeProof::Rejected(reasons) => {
                rejected.extend(reasons);
                Ok(TryEnvelopeProof::Rejected(rejected))
            }
        }
    }

    fn prove(
        &self,
        source: &crate::ir::exception::TryRegion,
        entry: BlockId,
        mut blocks: BTreeSet<BlockId>,
        protected: &BTreeSet<BlockId>,
        handlers: &BTreeSet<BlockId>,
    ) -> Result<TryEnvelopeProof, RegionInvariantError> {
        let mut rejected = Vec::new();
        if let Some(throwing) = self.throwing_additions(&blocks, protected, handlers)? {
            rejected.push(TryEnvelopeRejection::ThrowingExpansion(throwing));
        } else if let Some(throwing) =
            self.close_control_regions(source, &mut blocks, protected, handlers)?
        {
            rejected.push(TryEnvelopeRejection::ThrowingExpansion(throwing));
        }
        if !blocks.contains(&entry) {
            rejected.push(TryEnvelopeRejection::EntryOutsideProtection(entry));
        }
        let external = self.external_entries(entry, &blocks);
        if !external.is_empty() {
            rejected.push(TryEnvelopeRejection::ExternalEntries(external));
        }
        let undominated = self.undominated(entry, &blocks);
        if !undominated.is_empty() {
            rejected.push(TryEnvelopeRejection::Undominated(undominated));
        }
        if rejected.is_empty() {
            Ok(TryEnvelopeProof::Proven(TryRegionEnvelope {
                entry,
                blocks,
            }))
        } else {
            Ok(TryEnvelopeProof::Rejected(rejected))
        }
    }

    fn range_entry(&self, source: &crate::ir::exception::TryRegion) -> Option<BlockId> {
        let entry = self.source_cfg.block_ids().into_iter().find(|block| {
            self.source_cfg
                .block(*block)
                .is_some_and(|block| block.offset == source.start_offset)
        })?;
        let entry = self.representatives.get(&entry).copied().unwrap_or(entry);
        self.cfg.block(entry).map(|_| entry)
    }

    /// DEX protects only instructions that can throw, so the encoded range may
    /// begin below a non-throwing branch or a nested cleanup that is part of the
    /// source `try`. Recover the lexical entry as the nearest common dominator
    /// of the complete protected domain, including nested handler bodies.
    fn lexical_entry(&self, range_entry: BlockId, protected: &BTreeSet<BlockId>) -> BlockId {
        let dominators = self.facts.semantic_dominators();
        let method_entry = self.cfg.entry;
        let mut members = protected
            .iter()
            .copied()
            .filter(|block| dominators.dominates(method_entry, *block))
            .collect::<Vec<_>>();
        if dominators.dominates(method_entry, range_entry) {
            members.push(range_entry);
        }
        members.sort_unstable();
        members.dedup();

        let Some(mut candidate) = members.first().copied() else {
            return range_entry;
        };
        while !members
            .iter()
            .all(|member| dominators.dominates(candidate, *member))
        {
            let Some(parent) = dominators.idom(candidate) else {
                return range_entry;
            };
            if parent == BlockId::INVALID {
                return range_entry;
            }
            candidate = parent;
        }
        candidate
    }

    fn nested_handlers(
        &self,
        source: &crate::ir::exception::TryRegion,
    ) -> Result<BTreeSet<BlockId>, RegionInvariantError> {
        let lexical = HandlerLexicalAnalysis::new(self.cfg);
        let mut blocks = BTreeSet::new();
        let mut pending = source.children.clone();
        let mut visited = BTreeSet::new();
        while let Some(child) = pending.pop() {
            if !visited.insert(child) {
                continue;
            }
            let child = self
                .analysis
                .region(child)
                .ok_or(RegionInvariantError::MissingExceptionRegion(child))?;
            for handler in &child.handlers {
                blocks.extend(lexical.analyze(std::iter::once(handler))?);
            }
            pending.extend(child.children.iter().copied());
        }
        Ok(blocks)
    }

    fn lexical_exit_suffixes(&self, source: &crate::ir::exception::TryRegion) -> BTreeSet<BlockId> {
        let cleanup_entries = self
            .analysis
            .cleanup_contractions
            .iter()
            .map(|contraction| contraction.entry)
            .collect::<BTreeSet<_>>();
        let mut suffixes = BTreeSet::new();
        for exit in &source.normal_exit_blocks {
            for successor in self.source_cfg.normal_successors(*exit) {
                let mut current = successor;
                let mut corridor = BTreeSet::new();
                let mut visited = BTreeSet::new();
                while visited.insert(current) {
                    if cleanup_entries.contains(&current) {
                        suffixes.extend(corridor);
                        break;
                    }
                    if source.blocks.contains(&current) {
                        break;
                    }
                    let Some(block) = self.source_cfg.block(current) else {
                        break;
                    };
                    if block
                        .insns
                        .iter()
                        .any(|instruction| instruction.can_throw())
                        || self
                            .source_cfg
                            .successors_with_kind(current)
                            .iter()
                            .any(|(_, kind)| kind.is_exception())
                    {
                        break;
                    }
                    let successors = self
                        .source_cfg
                        .normal_successors(current)
                        .collect::<Vec<_>>();
                    let [next] = successors.as_slice() else {
                        break;
                    };
                    let representative = self
                        .representatives
                        .get(&current)
                        .copied()
                        .unwrap_or(current);
                    if self.cfg.block(representative).is_none() {
                        break;
                    }
                    corridor.insert(representative);
                    current = *next;
                }
            }
        }
        suffixes
    }

    fn range_blocks(&self, source: &crate::ir::exception::TryRegion) -> BTreeSet<BlockId> {
        self.source_cfg
            .block_ids()
            .into_iter()
            .filter(|block| {
                self.source_cfg.block(*block).is_some_and(|block| {
                    source.start_offset <= block.offset && block.offset < source.end_offset
                })
            })
            .map(|block| self.representatives.get(&block).copied().unwrap_or(block))
            .filter(|block| self.cfg.block(*block).is_some())
            .collect()
    }

    fn close_control_regions(
        &self,
        source: &crate::ir::exception::TryRegion,
        blocks: &mut BTreeSet<BlockId>,
        protected: &BTreeSet<BlockId>,
        handlers: &BTreeSet<BlockId>,
    ) -> Result<Option<BTreeSet<BlockId>>, RegionInvariantError> {
        let mut closure = self.tree.control_entry_closure(blocks);
        closure = self
            .tree
            .laminar_closure(&closure)
            .into_iter()
            .filter(|block| self.cfg.block(*block).is_some())
            .collect::<BTreeSet<_>>();
        self.close_exception_scopes(source, &mut closure)?;
        closure = self
            .tree
            .laminar_closure(&closure)
            .into_iter()
            .filter(|block| self.cfg.block(*block).is_some())
            .collect();
        if let Some(throwing) = self.throwing_additions(&closure, protected, handlers)? {
            return Ok(Some(throwing));
        }
        *blocks = closure;
        Ok(None)
    }

    /// DEX try items cannot overlap, so a source-nested try may appear as a
    /// sibling physical scope. Once a candidate lexical envelope contains the
    /// complete protected domain, include that scope's handlers and let the
    /// exceptional-edge proof decide whether the larger envelope is sound.
    fn close_exception_scopes(
        &self,
        source: &crate::ir::exception::TryRegion,
        blocks: &mut BTreeSet<BlockId>,
    ) -> Result<(), RegionInvariantError> {
        let lexical = HandlerLexicalAnalysis::new(self.cfg);
        loop {
            let mut additions = BTreeSet::new();
            for nested in self
                .analysis
                .regions
                .iter()
                .filter(|nested| nested.id != source.id)
            {
                let protected = nested
                    .blocks
                    .iter()
                    .map(|block| self.representatives.get(block).copied().unwrap_or(*block))
                    .filter(|block| self.cfg.block(*block).is_some())
                    .collect::<BTreeSet<_>>();
                if protected.is_empty() || !protected.is_subset(blocks) {
                    continue;
                }
                additions.extend(
                    lexical
                        .analyze(&nested.handlers)?
                        .into_iter()
                        .map(|block| self.representatives.get(&block).copied().unwrap_or(block))
                        .filter(|block| self.cfg.block(*block).is_some()),
                );
            }
            additions.retain(|block| !blocks.contains(block));
            if additions.is_empty() {
                return Ok(());
            }
            blocks.extend(additions);
        }
    }

    fn throwing_additions(
        &self,
        blocks: &BTreeSet<BlockId>,
        protected: &BTreeSet<BlockId>,
        handlers: &BTreeSet<BlockId>,
    ) -> Result<Option<BTreeSet<BlockId>>, RegionInvariantError> {
        let containment = ExceptionalContainment::new(self.cfg, handlers);
        let mut throwing = BTreeSet::new();
        for block in blocks.difference(protected) {
            let block = self
                .cfg
                .block(*block)
                .ok_or(RegionInvariantError::MissingBlock(*block))?;
            if self.effective_block_can_throw(block) && !containment.is_internal(block.id, blocks) {
                throwing.insert(block.id);
            }
        }
        Ok((!throwing.is_empty()).then_some(throwing))
    }

    fn external_entries(
        &self,
        entry: BlockId,
        blocks: &BTreeSet<BlockId>,
    ) -> BTreeMap<BlockId, Vec<BlockId>> {
        blocks
            .iter()
            .copied()
            .filter(|block| *block != entry)
            .filter_map(|block| {
                let predecessors = self
                    .facts
                    .predecessors(block)
                    .into_iter()
                    .flatten()
                    .copied()
                    .filter(|predecessor| {
                        !blocks.contains(predecessor)
                            && !self
                                .facts
                                .semantic_dominators()
                                .dominates(entry, *predecessor)
                    })
                    .collect::<Vec<_>>();
                (!predecessors.is_empty()).then_some((block, predecessors))
            })
            .collect()
    }

    fn undominated(&self, entry: BlockId, blocks: &BTreeSet<BlockId>) -> BTreeSet<BlockId> {
        blocks
            .iter()
            .copied()
            .filter(|block| !self.facts.semantic_dominators().dominates(entry, *block))
            .collect()
    }

    fn normal_connectors(
        &self,
        protected: &BTreeSet<BlockId>,
    ) -> Result<BTreeSet<BlockId>, RegionInvariantError> {
        let candidates = self
            .cfg
            .block_ids()
            .into_iter()
            .filter(|block| !protected.contains(block))
            .map(|block| {
                let body = self
                    .cfg
                    .block(block)
                    .ok_or(RegionInvariantError::MissingBlock(block))?;
                Ok((!self.effective_block_can_throw(body)).then_some(block))
            })
            .collect::<Result<Vec<_>, RegionInvariantError>>()?
            .into_iter()
            .flatten()
            .collect::<BTreeSet<_>>();

        let mut forward = BTreeSet::new();
        let mut pending = protected
            .iter()
            .flat_map(|block| self.cfg.normal_successors(*block))
            .collect::<Vec<_>>();
        while let Some(block) = pending.pop() {
            if !candidates.contains(&block) || !forward.insert(block) {
                continue;
            }
            pending.extend(self.cfg.normal_successors(block));
        }

        let predecessors = self.cfg.normal_predecessor_snapshot();
        let mut backward = BTreeSet::new();
        let mut pending = protected
            .iter()
            .flat_map(|block| predecessors.get(block).into_iter().flatten().copied())
            .collect::<Vec<_>>();
        while let Some(block) = pending.pop() {
            if !candidates.contains(&block) || !backward.insert(block) {
                continue;
            }
            pending.extend(predecessors.get(&block).into_iter().flatten().copied());
        }
        Ok(forward.intersection(&backward).copied().collect())
    }

    fn effective_block_can_throw(&self, block: &Block) -> bool {
        block.insns.iter().any(|instruction| {
            instruction.can_throw()
                && !(instruction.id.is_valid()
                    && self
                        .analysis
                        .elided_instructions
                        .contains(&StatementOrigin {
                            block: block.id,
                            instruction: instruction.id,
                        }))
        })
    }

    /// Collects the lexical prefix between a recovered entry and the encoded
    /// protected blocks. Exceptional edges are included because nested
    /// handlers and cleanup rethrows are part of that prefix. Backward
    /// reachability and the source-handler boundary keep the closure bounded;
    /// `prove` subsequently checks every added throwing instruction.
    fn entry_connectors(
        &self,
        entry: BlockId,
        protected: &BTreeSet<BlockId>,
        excluded: &BTreeSet<BlockId>,
    ) -> Result<BTreeSet<BlockId>, RegionInvariantError> {
        if protected.contains(&entry) {
            return Ok(BTreeSet::new());
        }
        let candidates = self
            .cfg
            .block_ids()
            .into_iter()
            .filter(|block| !protected.contains(block) && !excluded.contains(block))
            .collect::<BTreeSet<_>>();
        if !candidates.contains(&entry) {
            return Ok(BTreeSet::new());
        }

        let predecessors = self.cfg.predecessor_snapshot();
        let mut backward = BTreeSet::new();
        let mut pending = protected
            .iter()
            .flat_map(|block| predecessors.get(block).into_iter().flatten().copied())
            .collect::<Vec<_>>();
        while let Some(block) = pending.pop() {
            if !candidates.contains(&block) || !backward.insert(block) {
                continue;
            }
            pending.extend(predecessors.get(&block).into_iter().flatten().copied());
        }
        if !backward.contains(&entry) {
            return Ok(BTreeSet::new());
        }

        let mut connectors = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if protected.contains(&block) {
                continue;
            }
            if !backward.contains(&block) || !connectors.insert(block) {
                continue;
            }
            pending.extend(
                self.cfg
                    .successors_with_kind(block)
                    .iter()
                    .map(|(target, _)| *target),
            );
        }
        Ok(connectors)
    }
}

/// Recovers a lexical single-entry scope without changing DEX exception
/// coverage. Compilers routinely leave non-throwing dispatch blocks outside a
/// try item; those blocks may be owned lexically by the try because entering it
/// cannot add an exceptional transfer.
pub(super) struct LexicalTryAnalysis<'a> {
    cfg: &'a CFG,
    facts: &'a ControlFlowFacts,
    reachable: BTreeSet<BlockId>,
}

struct HandlerLexicalAnalysis<'a> {
    cfg: &'a CFG,
    predecessors: BTreeMap<BlockId, Vec<BlockId>>,
}

impl<'a> HandlerLexicalAnalysis<'a> {
    fn new(cfg: &'a CFG) -> Self {
        Self {
            cfg,
            predecessors: cfg.normal_predecessor_snapshot(),
        }
    }

    fn analyze<'b>(
        &self,
        handlers: impl IntoIterator<Item = &'b CatchHandler>,
    ) -> Result<BTreeSet<BlockId>, RegionInvariantError> {
        let mut blocks = handlers
            .into_iter()
            .flat_map(|handler| {
                let continuation = handler.continuation;
                handler
                    .lexical_blocks
                    .iter()
                    .copied()
                    .chain(handler.blocks.iter().copied())
                    .chain(handler.entry_blocks.iter().copied())
                    .chain(
                        (handler.kind != HandlerKind::Catch)
                            .then_some(handler.adapter_blocks.iter().copied())
                            .into_iter()
                            .flatten(),
                    )
                    .filter(move |block| Some(*block) != continuation)
            })
            .collect::<BTreeSet<_>>();
        loop {
            let additions = blocks
                .iter()
                .copied()
                .flat_map(|block| self.cfg.normal_successors(block))
                .filter(|block| !blocks.contains(block))
                .filter_map(|block| self.is_private_non_throwing(block, &blocks).transpose())
                .collect::<Result<BTreeSet<_>, RegionInvariantError>>()?;
            if additions.is_empty() {
                return Ok(blocks);
            }
            blocks.extend(additions);
        }
    }

    fn is_private_non_throwing(
        &self,
        block: BlockId,
        scope: &BTreeSet<BlockId>,
    ) -> Result<Option<BlockId>, RegionInvariantError> {
        let body = self
            .cfg
            .block(block)
            .ok_or(RegionInvariantError::MissingBlock(block))?;
        if body.insns.iter().any(|instruction| instruction.can_throw()) {
            return Ok(None);
        }
        let predecessors = self
            .predecessors
            .get(&block)
            .into_iter()
            .flatten()
            .copied()
            .collect::<BTreeSet<_>>();
        Ok((!predecessors.is_empty() && predecessors.is_subset(scope)).then_some(block))
    }
}

pub(super) struct ExceptionRegionRelaminarizer<'a> {
    analysis: &'a ExceptionAnalysis,
    source_cfg: &'a CFG,
    cfg: &'a CFG,
    facts: &'a ControlFlowFacts,
    representatives: &'a BTreeMap<BlockId, BlockId>,
}

impl<'a> ExceptionRegionRelaminarizer<'a> {
    pub(super) fn new(
        analysis: &'a ExceptionAnalysis,
        source_cfg: &'a CFG,
        cfg: &'a CFG,
        facts: &'a ControlFlowFacts,
        representatives: &'a BTreeMap<BlockId, BlockId>,
    ) -> Self {
        Self {
            analysis,
            source_cfg,
            cfg,
            facts,
            representatives,
        }
    }

    pub(super) fn apply(
        &self,
        tree: &mut RegionTree,
        mapping: &mut BTreeMap<u32, Vec<RegionId>>,
        handlers: &mut BTreeMap<RegionId, Vec<RegionId>>,
    ) -> Result<(), RegionInvariantError> {
        for source in &self.analysis.regions {
            let Some(mapped) = mapping.get(&source.id) else {
                continue;
            };
            let mapped = mapped
                .iter()
                .copied()
                .filter(|region| {
                    tree.region(*region)
                        .is_some_and(|region| matches!(region.kind, RegionKind::Try))
                })
                .collect::<Vec<_>>();
            if mapped.len() < 2 {
                continue;
            }
            let Some(TryRegionEnvelope { entry, blocks }) = TryRegionEnvelopeAnalysis::new(
                self.analysis,
                self.source_cfg,
                self.cfg,
                self.facts,
                self.representatives,
                tree,
            )
            .analyze(source)?
            .proven() else {
                continue;
            };
            if mapped.iter().any(|region| {
                tree.region(*region).is_some_and(|region| {
                    matches!(region.kind, RegionKind::Try)
                        && region.entry == Some(entry)
                        && region.blocks == blocks
                })
            }) {
                continue;
            }
            let handler_set = mapped
                .iter()
                .flat_map(|region| handlers.get(region).into_iter().flatten().copied())
                .collect::<BTreeSet<_>>();
            let RegionPlacement::Inserted(envelope) =
                tree.insert_laminar_region(RegionKind::Try, entry, blocks)?
            else {
                continue;
            };
            mapping.entry(source.id).or_default().push(envelope);
            if !handler_set.is_empty() {
                handlers.insert(envelope, handler_set.into_iter().collect());
            }
        }
        Ok(())
    }
}

impl<'a> LexicalTryAnalysis<'a> {
    pub(super) fn new(cfg: &'a CFG, facts: &'a ControlFlowFacts) -> Self {
        Self {
            cfg,
            facts,
            reachable: Self::normal_reachable(cfg),
        }
    }

    pub(super) fn apply(
        &self,
        tree: &mut RegionTree,
        mapping: &BTreeMap<u32, Vec<RegionId>>,
    ) -> Result<(), RegionInvariantError> {
        let mut scopes = mapping
            .values()
            .flatten()
            .copied()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .filter_map(|region| self.scope(tree, region).transpose())
            .collect::<Result<Vec<_>, _>>()?;
        let mut conflicts = BTreeSet::new();
        for (index, left) in scopes.iter().enumerate() {
            for right in scopes.iter().skip(index + 1) {
                let nested = tree.is_ancestor(left.region, right.region)?
                    || tree.is_ancestor(right.region, left.region)?;
                if !nested && !left.blocks.is_disjoint(&right.blocks) {
                    conflicts.insert(left.region);
                    conflicts.insert(right.region);
                }
            }
        }
        scopes.retain(|scope| !conflicts.contains(&scope.region));
        scopes.retain(|scope| {
            let Some(region) = tree.region(scope.region) else {
                return false;
            };
            let expanded = region
                .blocks
                .union(&scope.blocks)
                .copied()
                .collect::<BTreeSet<_>>();
            tree.regions()
                .filter(|other| other.id != scope.region)
                .all(|other| {
                    expanded.is_disjoint(&other.blocks)
                        || expanded.is_subset(&other.blocks)
                        || other.blocks.is_subset(&expanded)
                })
        });
        scopes.sort_by_key(|scope| scope.depth);
        for scope in scopes {
            let region = tree
                .region_mut(scope.region)
                .ok_or(RegionInvariantError::UnknownRegion(scope.region))?;
            region.blocks.extend(scope.blocks);
            region.entry = Some(scope.entry);
        }
        Ok(())
    }

    fn scope(
        &self,
        tree: &RegionTree,
        region: RegionId,
    ) -> Result<Option<TryScope>, RegionInvariantError> {
        let protected = tree
            .region(region)
            .ok_or(RegionInvariantError::UnknownRegion(region))?
            .blocks
            .clone();
        let entries =
            protected
                .iter()
                .copied()
                .filter(|block| {
                    *block == self.cfg.entry
                        || self.facts.predecessors(*block).into_iter().flatten().any(
                            |predecessor| {
                                self.reachable.contains(predecessor)
                                    && !protected.contains(predecessor)
                            },
                        )
                })
                .collect::<Vec<_>>();
        if entries.len() < 2 {
            return Ok(None);
        }
        let Some(entry) = self.common_dominator(&entries) else {
            return Ok(None);
        };
        if entry == BlockId::INVALID || protected.contains(&entry) {
            return Ok(None);
        }

        let ancestors = tree
            .parent_chain(region)?
            .into_iter()
            .skip(1)
            .collect::<BTreeSet<_>>();
        let dominated = self.facts.dominators().dominated_by(entry);
        let mut blocks = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if !self.reachable.contains(&block)
                || !dominated.contains(&block)
                || blocks.contains(&block)
            {
                continue;
            }
            if !protected.contains(&block) {
                let owner = tree.owner(block)?;
                let body = self
                    .cfg
                    .block(block)
                    .ok_or(RegionInvariantError::MissingBlock(block))?;
                let owns_control_header = tree.region(owner).is_some_and(|region| {
                    region.entry == Some(block)
                        && matches!(&region.kind, RegionKind::Loop(_) | RegionKind::Switch(_))
                });
                if !ancestors.contains(&owner)
                    || owns_control_header
                    || body.insns.iter().any(|instruction| instruction.can_throw())
                {
                    continue;
                }
            }
            blocks.insert(block);
            pending.extend(self.cfg.normal_successors(block));
        }
        if !entries.iter().all(|block| blocks.contains(block)) {
            return Ok(None);
        }
        let additions = blocks
            .difference(&protected)
            .copied()
            .collect::<BTreeSet<_>>();
        Ok((!additions.is_empty()).then_some(TryScope {
            region,
            entry,
            blocks: additions,
            depth: tree.parent_chain(region)?.len(),
        }))
    }

    fn common_dominator(&self, entries: &[BlockId]) -> Option<BlockId> {
        let mut candidate = *entries.first()?;
        while !entries
            .iter()
            .all(|entry| self.facts.dominators().dominates(candidate, *entry))
        {
            candidate = self.facts.dominators().idom(candidate)?;
        }
        Some(candidate)
    }

    fn normal_reachable(cfg: &CFG) -> BTreeSet<BlockId> {
        let mut reachable = BTreeSet::new();
        let mut pending = vec![cfg.entry];
        while let Some(block) = pending.pop() {
            if !reachable.insert(block) {
                continue;
            }
            pending.extend(cfg.normal_successors(block));
        }
        reachable
    }
}

#[derive(Debug, Clone)]
enum ExceptionParent {
    Root,
    Try(u32),
    Handler {
        owners: BTreeSet<u32>,
        entry: BlockId,
    },
}

impl ExceptionParent {
    fn dependencies(&self) -> BTreeSet<u32> {
        match self {
            Self::Root => BTreeSet::new(),
            Self::Try(parent) => BTreeSet::from([*parent]),
            Self::Handler { owners, .. } => owners.clone(),
        }
    }
}

impl<'a> ExceptionRegionTreeBuilder<'a> {
    pub(super) fn new(
        analysis: &'a ExceptionAnalysis,
        cfg: &'a CFG,
        facts: &'a ControlFlowFacts,
        envelope_cfg: &'a CFG,
        envelope_facts: &'a ControlFlowFacts,
        cleanup_representatives: &'a BTreeMap<BlockId, BlockId>,
        tree: RegionTree,
    ) -> Self {
        Self {
            analysis,
            cfg,
            facts,
            envelope_cfg,
            envelope_facts,
            cleanup_representatives,
            tree,
            mapping: BTreeMap::new(),
            handlers: BTreeMap::new(),
            handler_regions: BTreeMap::new(),
            handler_domains: BTreeMap::new(),
        }
    }

    pub(super) fn build(
        mut self,
    ) -> Result<
        (
            RegionTree,
            BTreeMap<u32, Vec<RegionId>>,
            BTreeMap<RegionId, Vec<RegionId>>,
        ),
        RegionInvariantError,
    > {
        self.tree.cover_method(self.cfg)?;
        let sources = self
            .analysis
            .regions
            .iter()
            .map(|region| (region.id, region))
            .collect::<BTreeMap<_, _>>();
        if sources.len() != self.analysis.regions.len() {
            return Err(RegionInvariantError::DuplicateExceptionRegion);
        }

        let parents = sources
            .values()
            .map(|source| Ok((source.id, self.parent_of(source, &sources)?)))
            .collect::<Result<BTreeMap<_, _>, RegionInvariantError>>()?;
        let mut remaining = BTreeSet::new();
        for source in sources.values() {
            for parent in parents[&source.id].dependencies() {
                if !sources.contains_key(&parent) {
                    return Err(RegionInvariantError::MissingExceptionParent {
                        region: source.id,
                        parent,
                    });
                }
            }
            remaining.insert(source.id);
        }

        while !remaining.is_empty() {
            let ready = remaining
                .iter()
                .copied()
                .filter(|source| {
                    parents[source]
                        .dependencies()
                        .iter()
                        .all(|dependency| self.mapping.contains_key(dependency))
                })
                .collect::<Vec<_>>();
            if ready.is_empty() {
                break;
            }
            for source_id in ready {
                remaining.remove(&source_id);
                self.add(source_id, &parents[&source_id])?;
                self.nest_regions_in_handlers()?;
                self.tree.canonicalize_nesting()?;
            }
        }

        if !remaining.is_empty() {
            return Err(RegionInvariantError::ExceptionRegionCycle(
                remaining.into_iter().collect(),
            ));
        }
        self.partition_crossing_handler_ownership()?;
        self.nest_regions_in_handlers()?;
        self.tree.canonicalize_nesting()?;
        Ok((self.tree, self.mapping, self.handlers))
    }

    fn parent_of(
        &self,
        source: &crate::ir::exception::TryRegion,
        sources: &BTreeMap<u32, &crate::ir::exception::TryRegion>,
    ) -> Result<ExceptionParent, RegionInvariantError> {
        let blocks = Self::protected_shell(source, sources);
        let mut candidates = sources
            .values()
            .filter(|owner| owner.id != source.id)
            .flat_map(|owner| {
                owner
                    .handlers
                    .iter()
                    .map(|handler| (handler.semantic_entry, &handler.lexical_blocks))
                    .collect::<BTreeMap<_, _>>()
                    .into_iter()
                    .filter(|(_, owned)| blocks.iter().all(|block| owned.contains(block)))
                    .map(|(entry, owned)| (owned.len(), owner.id, entry))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        candidates.sort();
        let Some((minimum, _, _)) = candidates.first().copied() else {
            return Ok(source
                .parent
                .map(ExceptionParent::Try)
                .unwrap_or(ExceptionParent::Root));
        };
        if let Some(parent) = source.parent {
            let parent_size = sources
                .get(&parent)
                .ok_or(RegionInvariantError::MissingExceptionParent {
                    region: source.id,
                    parent,
                })?
                .blocks
                .len();
            if parent_size <= minimum {
                return Ok(ExceptionParent::Try(parent));
            }
        }
        let minimal = candidates
            .iter()
            .take_while(|(size, _, _)| *size == minimum)
            .map(|(_, owner, entry)| (*owner, *entry))
            .collect::<Vec<_>>();
        let entries = minimal
            .iter()
            .map(|(_, entry)| *entry)
            .collect::<BTreeSet<_>>();
        if entries.len() != 1 {
            // A protected range in a shared handler suffix can be contained
            // by several lexical catch domains with different entries. None
            // of those catches is a unique source-level owner; preserve the
            // explicit exception-table parent when one exists.
            if let Some(parent) = source.parent {
                return Ok(ExceptionParent::Try(parent));
            }
            return Err(RegionInvariantError::AmbiguousExceptionHandlerParent {
                region: source.id,
                handlers: minimal,
            });
        }
        Ok(ExceptionParent::Handler {
            owners: minimal.iter().map(|(owner, _)| *owner).collect(),
            entry: *entries.first().ok_or(
                RegionInvariantError::AmbiguousExceptionHandlerParent {
                    region: source.id,
                    handlers: minimal,
                },
            )?,
        })
    }

    fn protected_shell(
        source: &crate::ir::exception::TryRegion,
        sources: &BTreeMap<u32, &crate::ir::exception::TryRegion>,
    ) -> BTreeSet<BlockId> {
        let mut blocks = source.blocks.iter().copied().collect::<BTreeSet<_>>();
        for handler in &source.handlers {
            blocks.retain(|block| !handler.blocks.contains(block));
        }
        let mut pending = source.children.clone();
        let mut visited = BTreeSet::new();
        while let Some(child) = pending.pop() {
            if !visited.insert(child) {
                continue;
            }
            let Some(child) = sources.get(&child) else {
                continue;
            };
            for handler in &child.handlers {
                blocks.retain(|block| !handler.blocks.contains(block));
            }
            pending.extend(child.children.iter().copied());
        }
        blocks
    }

    fn add(
        &mut self,
        source_id: u32,
        semantic_parent: &ExceptionParent,
    ) -> Result<Vec<RegionId>, RegionInvariantError> {
        let source = self
            .analysis
            .region(source_id)
            .ok_or(RegionInvariantError::MissingExceptionRegion(source_id))?;
        let envelope = TryRegionEnvelopeAnalysis::new(
            self.analysis,
            self.cfg,
            self.envelope_cfg,
            self.envelope_facts,
            self.cleanup_representatives,
            &self.tree,
        )
        .analyze(source)?
        .proven();
        let mut regions = match envelope {
            Some(TryRegionEnvelope { entry, blocks }) => {
                match self
                    .tree
                    .insert_laminar_region(RegionKind::Try, entry, blocks)?
                {
                    RegionPlacement::Inserted(region) => vec![region],
                    RegionPlacement::Residual => Vec::new(),
                }
            }
            None => Vec::new(),
        };
        if regions.is_empty() {
            let fragments = self.fragment_blocks(source)?;
            if fragments.is_empty() {
                return Err(RegionInvariantError::EmptyExceptionRegion(source_id));
            }
            regions.reserve(fragments.len());
            for (parent, entry, blocks) in fragments {
                let region = self.tree.add_child(parent, RegionKind::Try, Some(entry))?;
                for block in blocks {
                    self.tree.add_block(region, block)?;
                }
                regions.push(region);
            }
        }
        self.mapping.insert(source_id, regions.clone());

        let mut handlers = Vec::<(BlockId, Vec<&CatchHandler>)>::new();
        for handler in &source.handlers {
            if let Some((_, group)) = handlers
                .iter_mut()
                .find(|(entry, _)| *entry == handler.semantic_entry)
            {
                group.push(handler);
            } else {
                handlers.push((handler.semantic_entry, vec![handler]));
            }
        }
        let canonical = regions[0];
        let mut handler_regions = Vec::with_capacity(handlers.len());
        for (entry, group) in handlers {
            let lexical_blocks =
                HandlerLexicalAnalysis::new(self.cfg).analyze(group.iter().copied())?;
            let kind = Self::handler_kind(source_id, entry, &group)?;
            let blocks = self.handler_component(
                entry,
                &lexical_blocks,
                matches!(kind, RegionKind::Catch(_)),
            )?;
            if let Some(region) = self.interned_handler(entry, &kind, &blocks)? {
                self.handler_domains
                    .entry(region)
                    .or_default()
                    .extend(lexical_blocks);
                let aliases = self.handler_regions.entry(entry).or_default();
                if !aliases.contains(&region) {
                    aliases.push(region);
                }
                handler_regions.push(region);
                continue;
            }
            let parent = if blocks.contains(&entry) {
                self.semantic_handler_parent(source_id, semantic_parent)?
                    .unwrap_or(self.tree.owner(entry)?)
            } else {
                canonical
            };
            let child =
                self.tree
                    .add_child(parent, kind, blocks.contains(&entry).then_some(entry))?;
            handler_regions.push(child);
            for block in blocks {
                self.tree.add_block(child, block)?;
            }
            self.handler_domains.insert(child, lexical_blocks);
            self.handler_regions.entry(entry).or_default().push(child);
        }
        for region in &regions {
            self.handlers.insert(*region, handler_regions.clone());
        }
        Ok(regions)
    }

    fn semantic_handler_parent(
        &self,
        source_id: u32,
        parent: &ExceptionParent,
    ) -> Result<Option<RegionId>, RegionInvariantError> {
        let ExceptionParent::Handler { owners, entry } = parent else {
            return Ok(None);
        };
        let owner_regions = owners
            .iter()
            .flat_map(|owner| self.mapping.get(owner).into_iter().flatten())
            .copied()
            .collect::<BTreeSet<_>>();
        let candidates = self
            .handler_regions
            .get(entry)
            .into_iter()
            .flatten()
            .copied()
            .filter(|handler| {
                owner_regions.iter().any(|owner| {
                    self.handlers
                        .get(owner)
                        .is_some_and(|handlers| handlers.contains(handler))
                })
            })
            .collect::<BTreeSet<_>>();
        if candidates.len() == 1 {
            return Ok(candidates.into_iter().next());
        }
        let lexical_owner = self.tree.owner(*entry)?;
        if let Some(parent) = self
            .tree
            .parent_chain(lexical_owner)?
            .into_iter()
            .find(|region| candidates.contains(region))
        {
            return Ok(Some(parent));
        }
        Err(RegionInvariantError::AmbiguousExceptionHandlerParent {
            region: source_id,
            handlers: owners.iter().map(|owner| (*owner, *entry)).collect(),
        })
    }

    /// Exception tables describe protected instruction ranges, while source
    /// handlers own a lexical body. A later protected range can therefore be
    /// fragmented across an already discovered handler domain before that
    /// handler region itself has been materialized. Close that ownership
    /// relation after all handlers exist so each fragment is reduced in its
    /// lexical handler, not as an unrelated method-level continuation.
    fn nest_regions_in_handlers(&mut self) -> Result<(), RegionInvariantError> {
        let mut fragments = self
            .tree
            .regions()
            .map(|region| region.id)
            .filter(|region| *region != self.tree.root())
            .filter(|region| !self.handler_domains.contains_key(region))
            .filter(|region| {
                self.tree
                    .region(*region)
                    .is_some_and(|region| !region.blocks.is_empty())
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        fragments.sort_by_key(|region| {
            std::cmp::Reverse(
                self.tree
                    .region(*region)
                    .map(|region| region.blocks.len())
                    .unwrap_or_default(),
            )
        });

        for fragment in fragments {
            let blocks = self
                .tree
                .region(fragment)
                .ok_or(RegionInvariantError::UnknownRegion(fragment))?
                .blocks
                .clone();
            if blocks.is_empty() {
                continue;
            }
            let current = self
                .tree
                .region(fragment)
                .and_then(|region| region.parent)
                .ok_or(RegionInvariantError::MissingRegionParent {
                    region: fragment,
                    parent: self.tree.root(),
                })?;
            let own_handlers = self.handlers.get(&fragment);
            let mut candidates = self
                .handler_domains
                .iter()
                .filter(|(handler, domain)| {
                    **handler != fragment
                        && own_handlers.is_none_or(|handlers| !handlers.contains(handler))
                        && blocks.is_subset(domain)
                        && self
                            .tree
                            .is_ancestor(fragment, **handler)
                            .is_ok_and(|contains| !contains)
                })
                .map(|(handler, domain)| {
                    self.tree
                        .parent_chain(*handler)
                        .map(|chain| (domain.len(), std::cmp::Reverse(chain.len()), *handler))
                })
                .collect::<Result<Vec<_>, _>>()?;
            candidates.sort();
            let Some((domain_size, depth, owner)) = candidates.first().copied() else {
                continue;
            };
            let equally_specific = candidates
                .iter()
                .take_while(|(candidate_size, candidate_depth, _)| {
                    *candidate_size == domain_size && *candidate_depth == depth
                })
                .map(|(_, _, handler)| *handler)
                .collect::<Vec<_>>();
            if equally_specific.len() > 1 {
                // This fragment is a suffix shared by several sibling
                // handlers, not the lexical body of whichever handler happens
                // to have the smallest RegionId. Since handlers are added
                // incrementally, undo an earlier provisional placement under
                // one of the now-tied candidates. Preserve an unrelated
                // explicit parent, which can still be more specific than the
                // handlers' common ancestor.
                let nested_in_candidate = equally_specific
                    .iter()
                    .copied()
                    .map(|handler| self.tree.is_ancestor(handler, current))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .any(|nested| nested);
                if nested_in_candidate {
                    let common = equally_specific
                        .iter()
                        .copied()
                        .skip(1)
                        .try_fold(equally_specific[0], |common, handler| {
                            self.tree.common_ancestor(common, handler)
                        })?;
                    if current != common {
                        self.tree.reparent(fragment, common)?;
                    }
                }
                continue;
            }
            if current == owner || self.tree.is_ancestor(owner, current)? {
                continue;
            }
            self.tree.reparent(fragment, owner)?;
        }
        Ok(())
    }

    /// A protected interval can cross a lexical handler boundary and be
    /// represented by multiple try fragments. When the handler-local
    /// intersection is already owned by an equivalent fragment, remove that
    /// duplicate ownership from the outer envelope. This restores a laminar
    /// region tree without changing exception coverage.
    fn partition_crossing_handler_ownership(&mut self) -> Result<(), RegionInvariantError> {
        let predecessors = self.cfg.normal_predecessor_snapshot();
        loop {
            let tries = self
                .tree
                .regions()
                .filter(|region| matches!(&region.kind, RegionKind::Try))
                .map(|region| region.id)
                .collect::<Vec<_>>();
            let lexical_handlers = self.handler_domains.keys().copied().collect::<Vec<_>>();
            let mut rewrite = None;
            'outer: for owner in &tries {
                let owner_region = self
                    .tree
                    .region(*owner)
                    .ok_or(RegionInvariantError::UnknownRegion(*owner))?;
                for handler in &lexical_handlers {
                    let handler_region = self
                        .tree
                        .region(*handler)
                        .ok_or(RegionInvariantError::UnknownRegion(*handler))?;
                    let intersection = owner_region
                        .blocks
                        .intersection(&handler_region.blocks)
                        .copied()
                        .collect::<BTreeSet<_>>();
                    if intersection.is_empty()
                        || intersection == owner_region.blocks
                        || intersection == handler_region.blocks
                    {
                        continue;
                    }
                    let equivalent = tries.iter().copied().find(|fragment| {
                        *fragment != *owner
                            && self.tree.region(*fragment).is_some_and(|region| {
                                region.blocks == intersection
                                    && self.handlers.get(fragment) == self.handlers.get(owner)
                            })
                            && self
                                .tree
                                .is_ancestor(*handler, *fragment)
                                .is_ok_and(|nested| nested)
                    });
                    if equivalent.is_none() {
                        continue;
                    }
                    let remainder = owner_region
                        .blocks
                        .difference(&intersection)
                        .copied()
                        .collect::<BTreeSet<_>>();
                    if remainder.is_empty() {
                        continue;
                    }
                    let entry = if owner_region
                        .entry
                        .is_some_and(|entry| remainder.contains(&entry))
                    {
                        owner_region.entry
                    } else {
                        let entries = remainder
                            .iter()
                            .copied()
                            .filter(|block| {
                                predecessors
                                    .get(block)
                                    .into_iter()
                                    .flatten()
                                    .any(|predecessor| !remainder.contains(predecessor))
                            })
                            .collect::<BTreeSet<_>>();
                        (entries.len() == 1)
                            .then(|| entries.first().copied())
                            .flatten()
                    };
                    let Some(entry) = entry else {
                        continue;
                    };
                    rewrite = Some((*owner, remainder, entry));
                    break 'outer;
                }
            }
            let Some((owner, blocks, entry)) = rewrite else {
                return Ok(());
            };
            let region = self
                .tree
                .region_mut(owner)
                .ok_or(RegionInvariantError::UnknownRegion(owner))?;
            region.blocks = blocks;
            region.entry = Some(entry);
        }
    }

    fn interned_handler(
        &mut self,
        entry: BlockId,
        kind: &RegionKind,
        blocks: &BTreeSet<BlockId>,
    ) -> Result<Option<RegionId>, RegionInvariantError> {
        for region in self
            .handler_regions
            .get(&entry)
            .cloned()
            .unwrap_or_default()
        {
            let merged_kind = self.tree.region(region).and_then(|existing| {
                Self::merge_handler_kind(&existing.kind, kind, existing.blocks == *blocks)
            });
            let Some(merged_kind) = merged_kind else {
                continue;
            };
            self.tree
                .region_mut(region)
                .ok_or(RegionInvariantError::UnknownRegion(region))?
                .kind = merged_kind;
            for block in blocks {
                self.tree.add_block(region, *block)?;
            }
            return Ok(Some(region));
        }

        let candidates = self
            .handler_regions
            .values()
            .flatten()
            .copied()
            .collect::<BTreeSet<_>>();
        for region in candidates {
            let merged_kind = {
                let existing = self
                    .tree
                    .region(region)
                    .ok_or(RegionInvariantError::UnknownRegion(region))?;
                (existing.blocks == *blocks)
                    .then(|| Self::merge_handler_kind(&existing.kind, kind, true))
                    .flatten()
            };
            let Some(merged_kind) = merged_kind else {
                continue;
            };
            self.tree
                .region_mut(region)
                .ok_or(RegionInvariantError::UnknownRegion(region))?
                .kind = merged_kind;
            return Ok(Some(region));
        }
        Ok(None)
    }

    fn merge_handler_kind(
        left: &RegionKind,
        right: &RegionKind,
        same_component: bool,
    ) -> Option<RegionKind> {
        match (left, right) {
            (RegionKind::Finally, RegionKind::Finally)
            | (RegionKind::Finally, RegionKind::Cleanup(_))
            | (RegionKind::Cleanup(_), RegionKind::Finally) => Some(RegionKind::Finally),
            (RegionKind::Catch(left), RegionKind::Catch(right))
                if left.exception_types == right.exception_types
                    && left.exception_value == right.exception_value =>
            {
                let continuation = match (left.continuation, right.continuation) {
                    (left, right) if left == right => left,
                    // DEX may route nested fallback catches to the same
                    // physical body. A protection-relative analysis can see
                    // the body's ordinary re-entry as a continuation for one
                    // range but not the other. Identical owned components
                    // prove that the present continuation is the shared
                    // lexical boundary rather than context-specific code.
                    (Some(continuation), None) | (None, Some(continuation)) if same_component => {
                        Some(continuation)
                    }
                    _ => return None,
                };
                let mut merged = left.clone();
                merged.continuation = continuation;
                Some(RegionKind::Catch(merged))
            }
            (RegionKind::Cleanup(left), RegionKind::Cleanup(right)) => (left.exception_types
                == right.exception_types
                && left.exception_value == right.exception_value
                && left.continuation == right.continuation)
                .then(|| RegionKind::Cleanup(left.clone())),
            _ => None,
        }
    }

    fn handler_component(
        &self,
        entry: BlockId,
        lexical_blocks: &BTreeSet<BlockId>,
        claim_ancestor_owned_suffixes: bool,
    ) -> Result<BTreeSet<BlockId>, RegionInvariantError> {
        if !lexical_blocks.contains(&entry) {
            return Ok(BTreeSet::new());
        }
        let owner = self.tree.owner(entry)?;
        let predecessors = self.cfg.normal_predecessor_snapshot();
        let mut blocks = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if !lexical_blocks.contains(&block)
                || !self.belongs_to_handler_domain(
                    block,
                    entry,
                    owner,
                    lexical_blocks,
                    claim_ancestor_owned_suffixes,
                )?
                || !blocks.insert(block)
            {
                continue;
            }
            pending.extend(
                predecessors
                    .get(&block)
                    .into_iter()
                    .flatten()
                    .copied()
                    .chain(self.cfg.normal_successors(block)),
            );
        }
        Ok(blocks)
    }

    fn belongs_to_handler_domain(
        &self,
        block: BlockId,
        entry: BlockId,
        owner: RegionId,
        lexical_blocks: &BTreeSet<BlockId>,
        claim_ancestor_owned_suffixes: bool,
    ) -> Result<bool, RegionInvariantError> {
        let block_owner = self.tree.owner(block)?;
        if block_owner == owner {
            return Ok(true);
        }
        // Catch discovery can run after an enclosing try has claimed the
        // physical handler entry but before private, non-throwing suffixes are
        // moved out of an ancestor region. HandlerLexicalAnalysis has already
        // proved that such blocks have no normal predecessor outside this
        // handler, and entry dominance distinguishes a suffix from exceptional
        // ingress adapters that merely converge on the catch. Finally and
        // cleanup handlers deliberately stay on the cleanup-contraction path:
        // claiming their normal copies here would emit the same cleanup twice.
        if claim_ancestor_owned_suffixes
            && self.tree.is_ancestor(block_owner, owner)?
            && self.facts.semantic_dominators().dominates(entry, block)
        {
            return Ok(true);
        }
        let region = self
            .tree
            .region(block_owner)
            .ok_or(RegionInvariantError::UnknownRegion(block_owner))?;
        Ok(region.blocks.is_subset(lexical_blocks) && self.tree.is_ancestor(owner, block_owner)?)
    }

    fn fragment_blocks(
        &self,
        source: &crate::ir::exception::TryRegion,
    ) -> Result<Vec<(RegionId, BlockId, BTreeSet<BlockId>)>, RegionInvariantError> {
        let mut by_owner = BTreeMap::<RegionId, BTreeSet<BlockId>>::new();
        let handler_blocks = source
            .handlers
            .iter()
            .flat_map(|handler| handler.blocks.iter().copied())
            .collect::<BTreeSet<_>>();
        let preserves_control_domain =
            source.has_finally() || source.handlers.iter().any(CatchHandler::is_catch_all);
        for block in source.blocks.iter().copied() {
            if handler_blocks.contains(&block) {
                continue;
            }
            if !self.include_fragment_block(source, block, preserves_control_domain)? {
                continue;
            }
            by_owner
                .entry(self.tree.owner(block)?)
                .or_default()
                .insert(block);
        }
        let mut fragments = Vec::new();
        for (owner, blocks) in by_owner {
            let scopes = SingleEntryTryFragments::new(self.cfg, self.facts).partition(blocks);
            fragments.extend(
                scopes
                    .into_iter()
                    .map(|(entry, blocks)| (owner, entry, blocks)),
            );
        }
        fragments.sort_by_key(|(_, entry, _)| self.block_rank(*entry));
        Ok(fragments)
    }

    fn include_fragment_block(
        &self,
        source: &crate::ir::exception::TryRegion,
        block: BlockId,
        preserves_control_domain: bool,
    ) -> Result<bool, RegionInvariantError> {
        if self.has_exception_edge(block) || source.has_finally() {
            return Ok(true);
        }
        if !preserves_control_domain {
            return Ok(false);
        }
        let owner = self.tree.owner(block)?;
        let region = self
            .tree
            .region(owner)
            .ok_or(RegionInvariantError::UnknownRegion(owner))?;
        let structural_header = region.entry == Some(block)
            && matches!(&region.kind, RegionKind::Loop(_) | RegionKind::Switch(_));
        Ok(!structural_header)
    }

    fn has_exception_edge(&self, block: BlockId) -> bool {
        self.cfg
            .successors_with_kind(block)
            .iter()
            .any(|(_, kind)| kind.is_exception())
    }

    fn block_rank(&self, block: BlockId) -> (u32, u32) {
        self.cfg
            .block(block)
            .map(|block| (block.offset, block.id.raw()))
            .unwrap_or((u32::MAX, block.raw()))
    }

    fn handler_kind(
        region: u32,
        entry: BlockId,
        group: &[&CatchHandler],
    ) -> Result<RegionKind, RegionInvariantError> {
        let handler = group[0];
        if group.iter().any(|candidate| candidate.kind != handler.kind) {
            return Err(RegionInvariantError::MixedHandlerKinds { region, entry });
        }
        let exception_values = group
            .iter()
            .filter_map(|handler| handler.exception_value.as_ref())
            .collect::<Vec<_>>();
        let identities = exception_values
            .iter()
            .map(|value| (value.reg_num, value.ssa_version))
            .collect::<BTreeSet<_>>();
        if identities.len() > 1 {
            return Err(RegionInvariantError::MixedExceptionRegisters { region, entry });
        }
        let exception_value = exception_values.first().map(|value| (*value).clone());
        Ok(match handler.kind {
            HandlerKind::Catch => {
                let mut exception_types =
                    if group.iter().any(|handler| handler.catch_type.is_none()) {
                        vec![crate::ir::ArgType::throwable()]
                    } else {
                        group
                            .iter()
                            .filter_map(|handler| handler.catch_type.clone())
                            .collect::<Vec<_>>()
                    };
                exception_types.sort();
                exception_types.dedup();
                RegionKind::Catch(CatchRegion {
                    exception_types,
                    exception_value,
                    continuation: handler.continuation,
                })
            }
            HandlerKind::Finally => RegionKind::Finally,
            HandlerKind::Cleanup => RegionKind::Cleanup(CatchRegion {
                exception_types: vec![crate::ir::ArgType::throwable()],
                exception_value,
                continuation: handler.continuation,
            }),
        })
    }
}

struct SingleEntryTryFragments<'a> {
    cfg: &'a CFG,
    facts: &'a ControlFlowFacts,
    predecessors: BTreeMap<BlockId, Vec<BlockId>>,
}

impl<'a> SingleEntryTryFragments<'a> {
    fn new(cfg: &'a CFG, facts: &'a ControlFlowFacts) -> Self {
        Self {
            cfg,
            facts,
            predecessors: cfg.normal_predecessor_snapshot(),
        }
    }

    fn partition(&self, mut remaining: BTreeSet<BlockId>) -> Vec<(BlockId, BTreeSet<BlockId>)> {
        let mut fragments = Vec::new();
        while !remaining.is_empty() {
            let mut entries = self.entries(&remaining);
            if entries.is_empty() {
                let Some(entry) = remaining
                    .iter()
                    .copied()
                    .min_by_key(|block| self.block_rank(*block))
                else {
                    break;
                };
                entries.insert(entry);
            }

            let mut frontier = entries.iter().copied().collect::<Vec<_>>();
            frontier.sort_by_key(|block| self.block_rank(*block));
            let mut claimed = BTreeSet::<BlockId>::new();
            for entry in frontier {
                let blocks = self.dominated_reach(entry, &remaining, &entries);
                claimed.extend(blocks.iter().copied());
                fragments.push((entry, blocks));
            }
            fragments.retain(|(_, blocks)| !blocks.is_empty());
            remaining.retain(|block| !claimed.contains(block));
        }
        fragments
    }

    fn entries(&self, remaining: &BTreeSet<BlockId>) -> BTreeSet<BlockId> {
        remaining
            .iter()
            .copied()
            .filter(|block| {
                *block == self.cfg.entry
                    || self
                        .predecessors
                        .get(block)
                        .into_iter()
                        .flatten()
                        .any(|predecessor| !remaining.contains(predecessor))
            })
            .collect()
    }

    fn dominated_reach(
        &self,
        entry: BlockId,
        remaining: &BTreeSet<BlockId>,
        entries: &BTreeSet<BlockId>,
    ) -> BTreeSet<BlockId> {
        let dominated = self.facts.dominators().dominated_by(entry);
        let mut blocks = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if (block != entry && entries.contains(&block))
                || !remaining.contains(&block)
                || !dominated.contains(&block)
                || !blocks.insert(block)
            {
                continue;
            }
            pending.extend(self.cfg.normal_successors(block));
        }
        blocks
    }

    fn block_rank(&self, block: BlockId) -> (u32, u32) {
        self.cfg
            .block(block)
            .map(|block| (block.offset, block.id.raw()))
            .unwrap_or((u32::MAX, block.raw()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::exception::CleanupProofDiagnostic;
    use crate::ir::{Block, EdgeKind, HandlerKind, InsnNode, InsnType};

    fn catch_handler(entry: BlockId, adapters: impl IntoIterator<Item = BlockId>) -> CatchHandler {
        CatchHandler {
            id: entry.raw(),
            catch_type: Some(crate::ir::ArgType::throwable()),
            handler_offset: entry.raw(),
            entry_blocks: BTreeSet::from([entry]),
            handler_block: entry,
            semantic_entry: entry,
            canonical_entry: entry,
            adapter_blocks: adapters.into_iter().collect(),
            blocks: vec![entry],
            semantic_blocks: vec![entry],
            lexical_blocks: vec![entry],
            continuation: None,
            exception_value: None,
            canonical_exception_value: None,
            rethrow_blocks: BTreeSet::new(),
            kind: HandlerKind::Catch,
        }
    }

    fn finally_handler(entry: BlockId) -> CatchHandler {
        let mut handler = catch_handler(entry, []);
        handler.catch_type = None;
        handler.kind = HandlerKind::Finally;
        handler
    }

    #[test]
    fn proven_split_finally_family_recovers_one_outer_try() {
        let entry = BlockId::new(0);
        let first_entry = BlockId::new(1);
        let second_entry = BlockId::new(2);
        let normal_cleanup = BlockId::new(3);
        let finally_entry = BlockId::new(4);
        let mut cfg = CFG::new("split_finally_family");
        cfg.entry = entry;
        for block in [
            entry,
            first_entry,
            second_entry,
            normal_cleanup,
            finally_entry,
        ] {
            cfg.add_block(Block::new(block));
        }
        cfg.add_edge(entry, first_entry, EdgeKind::Normal);
        cfg.add_edge(first_entry, second_entry, EdgeKind::Normal);
        cfg.add_edge(second_entry, normal_cleanup, EdgeKind::Normal);
        cfg.add_edge(first_entry, finally_entry, EdgeKind::Exception);
        cfg.add_edge(second_entry, finally_entry, EdgeKind::Exception);

        let mut tree = RegionTree::new(Some(entry));
        tree.cover_method(&cfg).expect("method ownership");
        let root = tree.root();
        let first = tree
            .add_child(root, RegionKind::Try, Some(first_entry))
            .expect("first split try");
        tree.add_block(first, first_entry).expect("first try block");
        let second = tree
            .add_child(root, RegionKind::Try, Some(second_entry))
            .expect("second split try");
        tree.add_block(second, second_entry)
            .expect("second try block");
        let finally = tree
            .add_child(root, RegionKind::Finally, Some(finally_entry))
            .expect("shared finally");
        tree.add_block(finally, finally_entry)
            .expect("finally block");

        let source = |id, block: BlockId| crate::ir::exception::TryRegion {
            id,
            start_offset: block.raw(),
            end_offset: block.raw() + 1,
            blocks: vec![block],
            handlers: vec![finally_handler(finally_entry)],
            parent: None,
            children: Vec::new(),
            normal_exit_blocks: vec![normal_cleanup],
        };
        let analysis = ExceptionAnalysis {
            regions: vec![source(10, first_entry), source(11, second_entry)],
            cleanup_proofs: vec![CleanupProofDiagnostic {
                region: 10,
                handler: finally_entry.raw(),
                normal_entry: normal_cleanup,
                candidate: normal_cleanup,
                outcome: CleanupProofOutcome::Proven,
                mismatch: None,
            }],
            ..ExceptionAnalysis::default()
        };
        let mut handlers = BTreeMap::from([(first, vec![finally]), (second, vec![finally])]);

        ExceptionRegionCanonicalizer::coalesce_finally_families(
            &analysis,
            &cfg,
            &mut tree,
            &mut handlers,
        )
        .expect("finally family coalescing");

        let synthetic = tree.region(first).unwrap().parent.unwrap();
        assert_ne!(synthetic, root);
        assert_eq!(tree.region(second).unwrap().parent, Some(synthetic));
        assert!(matches!(
            tree.region(synthetic).unwrap().kind,
            RegionKind::Try
        ));
        assert_eq!(
            tree.region(synthetic).unwrap().blocks,
            BTreeSet::from([first_entry, second_entry])
        );
        assert_eq!(handlers.get(&synthetic), Some(&vec![finally]));
        assert!(handlers.get(&first).is_some_and(Vec::is_empty));
        assert!(handlers.get(&second).is_some_and(Vec::is_empty));
    }

    #[test]
    fn handler_lexical_scope_excludes_shared_adapter() {
        let mut cfg = CFG::new("shared_handler_adapter");
        for id in 0..=4 {
            cfg.add_block(Block::new(id));
        }
        cfg.add_edge(BlockId::new(1), BlockId::new(3), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(2), BlockId::new(3), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(3), BlockId::new(4), EdgeKind::Normal);

        let handler = catch_handler(BlockId::new(1), [BlockId::new(1), BlockId::new(3)]);
        let blocks = HandlerLexicalAnalysis::new(&cfg)
            .analyze([&handler])
            .unwrap();

        assert_eq!(blocks, BTreeSet::from([BlockId::new(1)]));
    }

    #[test]
    fn handler_component_claims_a_private_ancestor_owned_suffix() {
        let method_entry = BlockId::new(0);
        let handler_entry = BlockId::new(1);
        let suffix = BlockId::new(2);
        let mut cfg = CFG::new("ancestor_owned_handler_suffix");
        cfg.entry = method_entry;
        for block in [method_entry, handler_entry, suffix] {
            cfg.add_block(Block::new(block));
        }
        cfg.add_edge(method_entry, handler_entry, EdgeKind::Normal);
        cfg.add_edge(handler_entry, suffix, EdgeKind::Normal);

        let facts = ControlFlowFacts::analyze(&cfg).expect("control-flow facts");
        let mut tree = RegionTree::new(Some(method_entry));
        tree.cover_method(&cfg).expect("method ownership");
        let root = tree.root();
        let enclosing_try = tree
            .add_child(root, RegionKind::Try, Some(handler_entry))
            .expect("enclosing try");
        tree.add_block(enclosing_try, handler_entry)
            .expect("handler entry ownership");

        let analysis = ExceptionAnalysis::default();
        let representatives = BTreeMap::new();
        let builder = ExceptionRegionTreeBuilder::new(
            &analysis,
            &cfg,
            &facts,
            &cfg,
            &facts,
            &representatives,
            tree,
        );

        assert_eq!(
            builder
                .handler_component(
                    handler_entry,
                    &BTreeSet::from([method_entry, handler_entry, suffix]),
                    true,
                )
                .expect("handler component"),
            BTreeSet::from([handler_entry, suffix])
        );

        assert_eq!(
            builder
                .handler_component(
                    handler_entry,
                    &BTreeSet::from([handler_entry, suffix]),
                    false,
                )
                .expect("cleanup component"),
            BTreeSet::from([handler_entry])
        );
    }

    #[test]
    fn explicit_try_parent_owns_a_suffix_shared_by_multiple_handlers() {
        let entry = BlockId::new(0);
        let mut cfg = CFG::new("shared_handler_suffix_parent");
        cfg.add_block(Block::new(entry.raw()));
        let facts = ControlFlowFacts::analyze(&cfg).expect("control-flow facts");

        let shared = [BlockId::new(104), BlockId::new(105)];
        let owner = |id, handler_entry| {
            let mut handler = catch_handler(handler_entry, []);
            handler.lexical_blocks = std::iter::once(handler_entry).chain(shared).collect();
            crate::ir::exception::TryRegion {
                id,
                start_offset: id,
                end_offset: id + 1,
                blocks: vec![BlockId::new(id)],
                handlers: vec![handler],
                parent: None,
                children: Vec::new(),
                normal_exit_blocks: Vec::new(),
            }
        };
        let explicit_parent = crate::ir::exception::TryRegion {
            id: 11,
            start_offset: 11,
            end_offset: 12,
            blocks: vec![
                BlockId::new(100),
                BlockId::new(101),
                BlockId::new(104),
                BlockId::new(105),
            ],
            handlers: Vec::new(),
            parent: None,
            children: vec![12],
            normal_exit_blocks: Vec::new(),
        };
        let nested = crate::ir::exception::TryRegion {
            id: 12,
            start_offset: 12,
            end_offset: 13,
            blocks: shared.to_vec(),
            handlers: Vec::new(),
            parent: Some(11),
            children: Vec::new(),
            normal_exit_blocks: Vec::new(),
        };
        let analysis = ExceptionAnalysis {
            regions: vec![
                owner(3, BlockId::new(76)),
                owner(4, BlockId::new(71)),
                owner(6, BlockId::new(66)),
                explicit_parent,
                nested,
            ],
            ..ExceptionAnalysis::default()
        };
        let sources = analysis
            .regions
            .iter()
            .map(|region| (region.id, region))
            .collect::<BTreeMap<_, _>>();
        let tree = RegionTree::new(Some(entry));
        let representatives = BTreeMap::new();
        let builder = ExceptionRegionTreeBuilder::new(
            &analysis,
            &cfg,
            &facts,
            &cfg,
            &facts,
            &representatives,
            tree,
        );

        assert!(matches!(
            builder.parent_of(sources[&12], &sources),
            Ok(ExceptionParent::Try(11))
        ));
    }

    #[test]
    fn shared_handler_suffix_is_not_owned_by_region_id_tie_breaking() {
        let entry = BlockId::new(0);
        let suffix = BTreeSet::from([BlockId::new(10), BlockId::new(11)]);
        let mut cfg = CFG::new("shared_handler_suffix_nesting");
        for block in [entry, BlockId::new(1), BlockId::new(2)]
            .into_iter()
            .chain(suffix.iter().copied())
        {
            cfg.add_block(Block::new(block.raw()));
        }
        cfg.add_edge(entry, BlockId::new(1), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(1), BlockId::new(2), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(2), BlockId::new(10), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(10), BlockId::new(11), EdgeKind::Normal);
        let facts = ControlFlowFacts::analyze(&cfg).expect("control-flow facts");
        let mut tree = RegionTree::new(Some(entry));
        tree.cover_method(&cfg).expect("method ownership");
        let root = tree.root();
        let fragment = tree
            .add_child(root, RegionKind::Try, Some(BlockId::new(10)))
            .expect("shared try fragment");
        for block in &suffix {
            tree.add_block(fragment, *block).expect("fragment block");
        }

        let analysis = ExceptionAnalysis::default();
        let representatives = BTreeMap::new();
        let mut builder = ExceptionRegionTreeBuilder::new(
            &analysis,
            &cfg,
            &facts,
            &cfg,
            &facts,
            &representatives,
            tree,
        );
        let handler_kind = || {
            RegionKind::Catch(CatchRegion {
                exception_types: vec![crate::ir::ArgType::throwable()],
                exception_value: None,
                continuation: None,
            })
        };
        let first = builder
            .tree
            .add_child(root, handler_kind(), Some(BlockId::new(1)))
            .expect("first handler");
        builder.handler_domains.insert(
            first,
            suffix.iter().copied().chain([BlockId::new(1)]).collect(),
        );
        builder
            .nest_regions_in_handlers()
            .expect("provisional nesting");
        assert_eq!(builder.tree.region(fragment).unwrap().parent, Some(first));

        let second = builder
            .tree
            .add_child(root, handler_kind(), Some(BlockId::new(2)))
            .expect("second handler");
        builder.handler_domains.insert(
            second,
            suffix.iter().copied().chain([BlockId::new(2)]).collect(),
        );
        builder
            .nest_regions_in_handlers()
            .expect("shared-suffix nesting");

        assert_eq!(builder.tree.region(fragment).unwrap().parent, Some(root));
    }

    #[test]
    fn same_catch_component_preserves_present_continuation() {
        let continuation = BlockId::new(7);
        let catch = |continuation| {
            RegionKind::Catch(CatchRegion {
                exception_types: vec![crate::ir::ArgType::object("java/lang/NoSuchFieldException")],
                exception_value: None,
                continuation,
            })
        };

        let merged = ExceptionRegionTreeBuilder::merge_handler_kind(
            &catch(Some(continuation)),
            &catch(None),
            true,
        )
        .expect("same physical catch component");
        assert!(matches!(
            merged,
            RegionKind::Catch(CatchRegion {
                continuation: Some(actual),
                ..
            }) if actual == continuation
        ));
        assert!(ExceptionRegionTreeBuilder::merge_handler_kind(
            &catch(Some(continuation)),
            &catch(None),
            false,
        )
        .is_none());
    }

    #[test]
    fn lexical_try_owns_a_non_throwing_switch_dispatch() {
        let mut cfg = CFG::new("try_switch_dispatch");
        for id in 0..=4 {
            cfg.add_block(Block::new(id));
        }
        cfg.block_mut(BlockId::new(0))
            .unwrap()
            .push(InsnNode::new(InsnType::Switch, 0));
        for id in [1, 2] {
            let block = cfg.block_mut(BlockId::new(id)).unwrap();
            block.push(InsnNode::new(InsnType::Invoke, 0));
            block.push(InsnNode::new(InsnType::Return, 0));
        }
        cfg.block_mut(BlockId::new(3))
            .unwrap()
            .push(InsnNode::new(InsnType::Return, 3));
        cfg.block_mut(BlockId::new(4))
            .unwrap()
            .push(InsnNode::new(InsnType::Return, 4));
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::SwitchCase(0));
        cfg.add_edge(BlockId::new(0), BlockId::new(2), EdgeKind::SwitchCase(1));
        cfg.add_edge(BlockId::new(0), BlockId::new(3), EdgeKind::SwitchDefault);
        cfg.add_edge(BlockId::new(1), BlockId::new(4), EdgeKind::Exception);
        cfg.add_edge(BlockId::new(2), BlockId::new(4), EdgeKind::Exception);

        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        tree.cover_method(&cfg).unwrap();
        let root = tree.root();
        let try_region = tree
            .add_child(root, RegionKind::Try, Some(BlockId::new(1)))
            .unwrap();
        tree.add_block(try_region, BlockId::new(1)).unwrap();
        tree.add_block(try_region, BlockId::new(2)).unwrap();
        let catch = tree
            .add_child(
                try_region,
                RegionKind::Catch(CatchRegion {
                    exception_types: vec![crate::ir::ArgType::throwable()],
                    exception_value: None,
                    continuation: None,
                }),
                Some(BlockId::new(4)),
            )
            .unwrap();
        tree.add_block(catch, BlockId::new(4)).unwrap();

        let facts = ControlFlowFacts::analyze(&cfg).unwrap();
        LexicalTryAnalysis::new(&cfg, &facts)
            .apply(&mut tree, &BTreeMap::from([(0, vec![try_region])]))
            .unwrap();

        let recovered = tree.region(try_region).unwrap();
        assert_eq!(recovered.entry, Some(BlockId::new(0)));
        assert_eq!(
            recovered.blocks,
            BTreeSet::from([
                BlockId::new(0),
                BlockId::new(1),
                BlockId::new(2),
                BlockId::new(3),
            ])
        );
    }
}
