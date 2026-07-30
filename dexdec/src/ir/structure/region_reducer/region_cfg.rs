use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::ir::{
    analysis::{ControlContinuations, ControlContractions},
    ArgType, Block, BlockId, EdgeKind, InsnArg, InsnType, RegionEdge, RegionExit, RegionGraph,
    RegionId, ResolvedRegionExit, SemanticNode, StatementOrigin, CFG,
};

use super::super::{continuation::BoundFlow, StructureError};

pub(super) struct RegionAnchors {
    phi_predecessors: BTreeSet<BlockId>,
    control_anchors: BTreeSet<BlockId>,
    contractions: ControlContractions,
    canonical_continuations: Arc<ControlContinuations>,
    control_continuations: ControlContinuations,
}

impl RegionAnchors {
    pub(super) fn analyze(cfg: &CFG, graph: &RegionGraph) -> Result<Self, StructureError> {
        let phi_predecessors =
            ControlContractions::for_edge_arguments(cfg, graph).phi_copy_anchors(cfg);
        // Region layout may contract only blocks that denote the same lexical
        // region node. Exceptional edge-argument contractions additionally
        // relate throw sites to cleanup destinations for Phi evaluation; using
        // those relations here would erase normal critical-edge adapters that
        // remain part of the source region's control graph.
        let contractions = ControlContractions::from_regions(graph);
        let control_anchors = graph
            .tree()
            .regions()
            .flat_map(|region| match &region.kind {
                crate::ir::RegionKind::Loop(loop_region) => loop_region
                    .latches
                    .iter()
                    .copied()
                    .chain(loop_region.follow)
                    .collect::<Vec<_>>(),
                _ => Vec::new(),
            })
            .collect();
        let canonical_continuations =
            Arc::new(ControlContinuations::preserving(cfg, &phi_predecessors));
        let control_continuations = ControlContinuations::preserving(cfg, &BTreeSet::new());
        Ok(Self {
            phi_predecessors,
            control_anchors,
            contractions,
            canonical_continuations,
            control_continuations,
        })
    }

    fn preserves(&self, block: BlockId) -> bool {
        self.phi_predecessors.contains(&block) || self.control_anchors.contains(&block)
    }

    pub(super) fn phi_copy_blocks(&self) -> &BTreeSet<BlockId> {
        &self.phi_predecessors
    }

    fn representative(&self, block: BlockId) -> BlockId {
        if self.preserves(block) {
            block
        } else {
            self.contractions.terminal(block).unwrap_or(block)
        }
    }

    fn control_continuation(&self, block: BlockId) -> BlockId {
        self.control_continuations.destination(block)
    }
}

pub(super) struct RegionEntryPorts {
    entries: BTreeMap<RegionId, BTreeSet<BlockId>>,
}

impl RegionEntryPorts {
    pub(super) fn analyze(cfg: &CFG, graph: &RegionGraph) -> Result<Self, StructureError> {
        let contractions = ControlContractions::from_regions(graph);
        let mut entries = graph
            .tree()
            .regions()
            .map(|region| (region.id, region.entry.into_iter().collect::<BTreeSet<_>>()))
            .collect::<BTreeMap<_, _>>();
        let ancestors = graph
            .tree()
            .regions()
            .map(|region| {
                let mut current = Some(region.id);
                let mut chain = BTreeSet::new();
                while let Some(candidate) = current {
                    if !chain.insert(candidate) {
                        return Err(StructureError::UnknownRegion(candidate));
                    }
                    current = graph
                        .tree()
                        .region(candidate)
                        .ok_or(StructureError::UnknownRegion(candidate))?
                        .parent;
                }
                Ok((region.id, chain))
            })
            .collect::<Result<BTreeMap<_, _>, StructureError>>()?;
        let body_reachability = RegionBodyReachability::analyze(cfg, graph)?;
        for source in cfg.block_ids() {
            if contractions.is_contracted(source) {
                continue;
            }
            let source_owner =
                graph
                    .owner_of(source)
                    .ok_or(StructureError::RegionOwnerMissing {
                        region: graph.tree().root(),
                        block: source,
                    })?;
            let source_ancestors = ancestors
                .get(&source_owner)
                .ok_or(StructureError::UnknownRegion(source_owner))?;
            for target in cfg.normal_successors(source) {
                let target = contractions.terminal(target).unwrap_or(target);
                if graph.handler_adapters().get(&source).copied() == Some(target) {
                    continue;
                }
                let target_owner =
                    graph
                        .owner_of(target)
                        .ok_or(StructureError::RegionOwnerMissing {
                            region: graph.tree().root(),
                            block: target,
                        })?;
                if source_ancestors.contains(&target_owner) {
                    let source_region = graph
                        .tree()
                        .region(source_owner)
                        .ok_or(StructureError::UnknownRegion(source_owner))?;
                    if Self::is_nested_handler_continuation(graph, target_owner, source_owner)? {
                        continue;
                    }
                    if source_owner != target_owner
                        && matches!(
                            &source_region.kind,
                            crate::ir::RegionKind::Catch(_)
                                | crate::ir::RegionKind::Finally
                                | crate::ir::RegionKind::Cleanup(_)
                        )
                        && Self::continuation_is_deferred(graph.tree(), source_owner, target_owner)?
                        && !body_reachability.is_internal_join(
                            graph,
                            target_owner,
                            source,
                            target,
                        )?
                    {
                        entries
                            .get_mut(&target_owner)
                            .ok_or(StructureError::UnknownRegion(target_owner))?
                            .insert(target);
                    }
                } else {
                    Self::record_entry_paths(
                        &mut entries,
                        graph,
                        source_ancestors,
                        target_owner,
                        target,
                        false,
                        |region| {
                            let source_is_nested = source_owner == region
                                || graph
                                    .tree()
                                    .is_ancestor(region, source_owner)
                                    .map_err(|_| StructureError::UnknownRegion(source_owner))?;
                            if !source_is_nested {
                                return Ok(true);
                            }
                            body_reachability
                                .is_internal_join(graph, region, source, target)
                                .map(|internal| !internal)
                        },
                    )?;
                }
            }
        }
        for handler in graph.tree().regions() {
            let Some(target) = handler.kind.continuation() else {
                continue;
            };
            let target = contractions.terminal(target).unwrap_or(target);
            let target_owner =
                graph
                    .owner_of(target)
                    .ok_or(StructureError::RegionOwnerMissing {
                        region: graph.tree().root(),
                        block: target,
                    })?;
            let source_ancestors = ancestors
                .get(&handler.id)
                .ok_or(StructureError::UnknownRegion(handler.id))?;
            if source_ancestors.contains(&target_owner) {
                continue;
            }
            Self::record_entry_paths(
                &mut entries,
                graph,
                source_ancestors,
                target_owner,
                target,
                true,
                |_| Ok(true),
            )?;
        }
        Self::record_owned_entries(&mut entries, graph)?;
        for (region, blocks) in &mut entries {
            let primary = graph.tree().region(*region).and_then(|region| region.entry);
            blocks.retain(|block| {
                Some(*block) == primary || !graph.is_implicit_cleanup_completion(*region, *block)
            });
        }
        Ok(Self { entries })
    }

    fn record_owned_entries(
        entries: &mut BTreeMap<RegionId, BTreeSet<BlockId>>,
        graph: &RegionGraph,
    ) -> Result<(), StructureError> {
        for region in graph.tree().regions() {
            let Some(entry) = region.entry else {
                continue;
            };
            let owner = graph
                .owner_of(entry)
                .ok_or(StructureError::RegionOwnerMissing {
                    region: region.id,
                    block: entry,
                })?;
            if owner == region.id
                || !graph
                    .tree()
                    .is_ancestor(region.id, owner)
                    .map_err(|_| StructureError::UnknownRegion(owner))?
            {
                continue;
            }
            let mut current = owner;
            loop {
                if RegionBodyReachability::belongs_to_body(graph, current, entry)? {
                    entries
                        .get_mut(&current)
                        .ok_or(StructureError::UnknownRegion(current))?
                        .insert(entry);
                }
                if current == region.id {
                    break;
                }
                current = graph
                    .tree()
                    .region(current)
                    .ok_or(StructureError::UnknownRegion(current))?
                    .parent
                    .ok_or(StructureError::UnknownRegion(current))?;
            }
        }
        Ok(())
    }

    fn record_entry_paths(
        entries: &mut BTreeMap<RegionId, BTreeSet<BlockId>>,
        graph: &RegionGraph,
        source_ancestors: &BTreeSet<RegionId>,
        target_owner: RegionId,
        target: BlockId,
        route_initial_handler_semantically: bool,
        mut records: impl FnMut(RegionId) -> Result<bool, StructureError>,
    ) -> Result<(), StructureError> {
        let mut pending = vec![(target_owner, true)];
        let mut visited = BTreeSet::new();
        while let Some((region, expose)) = pending.pop() {
            if source_ancestors.contains(&region) || !visited.insert((region, expose)) {
                continue;
            }
            if expose
                && records(region)?
                && RegionBodyReachability::belongs_to_body(graph, region, target)?
            {
                entries
                    .get_mut(&region)
                    .ok_or(StructureError::UnknownRegion(region))?
                    .insert(target);
            }
            let semantic_parents = if region == target_owner && !route_initial_handler_semantically
            {
                Vec::new()
            } else {
                graph.handler_owners(region).collect::<Vec<_>>()
            };
            if semantic_parents.is_empty() {
                if let Some(parent) = graph
                    .tree()
                    .region(region)
                    .ok_or(StructureError::UnknownRegion(region))?
                    .parent
                {
                    pending.push((parent, true));
                }
            } else {
                pending.extend(
                    semantic_parents
                        .into_iter()
                        .map(|semantic_parent| (semantic_parent, false)),
                );
            }
        }
        Ok(())
    }

    fn is_nested_handler_continuation(
        graph: &RegionGraph,
        region: RegionId,
        source: RegionId,
    ) -> Result<bool, StructureError> {
        for owner in graph.handler_owners(source) {
            if owner != region
                && graph
                    .tree()
                    .is_ancestor(region, owner)
                    .map_err(|_| StructureError::UnknownRegion(owner))?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn continuation_is_deferred(
        tree: &crate::ir::RegionTree,
        source: RegionId,
        owner: RegionId,
    ) -> Result<bool, StructureError> {
        let mut child = source;
        loop {
            let region = tree
                .region(child)
                .ok_or(StructureError::UnknownRegion(child))?;
            let parent = region.parent.ok_or(StructureError::UnknownRegion(child))?;
            if parent == owner {
                return Ok(matches!(
                    &region.kind,
                    crate::ir::RegionKind::Catch(_)
                        | crate::ir::RegionKind::Finally
                        | crate::ir::RegionKind::Cleanup(_)
                ));
            }
            child = parent;
        }
    }

    fn record_entry_path(
        entries: &mut BTreeMap<RegionId, BTreeSet<BlockId>>,
        tree: &crate::ir::RegionTree,
        source_ancestors: &BTreeSet<RegionId>,
        target_owner: RegionId,
        target: BlockId,
        mut records: impl FnMut(RegionId) -> Result<bool, StructureError>,
    ) -> Result<(), StructureError> {
        let mut current = Some(target_owner);
        while let Some(region) = current {
            if source_ancestors.contains(&region) {
                break;
            }
            if records(region)? {
                entries
                    .get_mut(&region)
                    .ok_or(StructureError::UnknownRegion(region))?
                    .insert(target);
            }
            let structured = tree
                .region(region)
                .ok_or(StructureError::UnknownRegion(region))?;
            if matches!(
                &structured.kind,
                crate::ir::RegionKind::Catch(_)
                    | crate::ir::RegionKind::Finally
                    | crate::ir::RegionKind::Cleanup(_)
            ) {
                break;
            }
            current = structured.parent;
        }
        Ok(())
    }

    pub(super) fn of(&self, region: RegionId) -> Result<&BTreeSet<BlockId>, StructureError> {
        self.entries
            .get(&region)
            .ok_or(StructureError::UnknownRegion(region))
    }
}

struct RegionBodyReachability {
    blocks: BTreeMap<RegionId, BTreeSet<BlockId>>,
}

impl RegionBodyReachability {
    fn analyze(cfg: &CFG, graph: &RegionGraph) -> Result<Self, StructureError> {
        let blocks = graph
            .tree()
            .regions()
            .map(|region| {
                let reachable = region
                    .entry
                    .map(|entry| Self::from_entry(cfg, graph, region.id, entry))
                    .transpose()?
                    .unwrap_or_default();
                Ok((region.id, reachable))
            })
            .collect::<Result<BTreeMap<_, _>, StructureError>>()?;
        Ok(Self { blocks })
    }

    fn from_entry(
        cfg: &CFG,
        graph: &RegionGraph,
        region: RegionId,
        entry: BlockId,
    ) -> Result<BTreeSet<BlockId>, StructureError> {
        let mut reachable = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if !Self::belongs_to_body(graph, region, block)? || !reachable.insert(block) {
                continue;
            }
            pending.extend(cfg.normal_successors(block));
        }
        Ok(reachable)
    }

    fn belongs_to_body(
        graph: &RegionGraph,
        region: RegionId,
        block: BlockId,
    ) -> Result<bool, StructureError> {
        let Some(mut owner) = graph.owner_of(block) else {
            return Err(StructureError::RegionOwnerMissing { region, block });
        };
        let target_owner = owner;
        loop {
            if owner == region {
                return Ok(true);
            }
            if owner == target_owner && graph.is_exception_handler(owner) {
                return Ok(false);
            }
            let Some(parent) = graph
                .tree()
                .region(owner)
                .ok_or(StructureError::UnknownRegion(owner))?
                .parent
            else {
                return Ok(false);
            };
            owner = parent;
        }
    }

    fn is_internal_join(
        &self,
        graph: &RegionGraph,
        region: RegionId,
        source: BlockId,
        target: BlockId,
    ) -> Result<bool, StructureError> {
        let entry = graph
            .tree()
            .region(region)
            .ok_or(StructureError::UnknownRegion(region))?
            .entry
            .ok_or(StructureError::MissingEntry(region))?;
        Ok(self
            .blocks
            .get(&region)
            .is_some_and(|blocks| blocks.contains(&target))
            && graph.semantic_dominates(entry, source))
    }
}

pub(super) struct RegionScope<'a> {
    graph: &'a RegionGraph,
    region: RegionId,
    children: BTreeSet<RegionId>,
    ports: &'a BTreeSet<BlockId>,
    anchors: &'a RegionAnchors,
}

impl<'a> RegionScope<'a> {
    pub(super) fn new(
        graph: &'a RegionGraph,
        region: RegionId,
        children: &[RegionId],
        ports: &'a BTreeSet<BlockId>,
        anchors: &'a RegionAnchors,
    ) -> Self {
        Self {
            graph,
            region,
            children: children.iter().copied().collect(),
            ports,
            anchors,
        }
    }

    pub(super) fn representative(&self, block: BlockId) -> Result<Option<BlockId>, StructureError> {
        // Region ports are lexical anchors. A handler-adapter contraction may
        // cross the region boundary, but it must not erase the source-side
        // representative needed to enter or leave that region.
        if self.ports.contains(&block) {
            return Ok(Some(block));
        }
        let block = self.anchors.representative(block);
        let Some(mut owner) = self.graph.owner_of(block) else {
            return Err(StructureError::RegionOwnerMissing {
                region: self.region,
                block,
            });
        };
        if self.ports.contains(&block) {
            return Ok(Some(block));
        }
        loop {
            if owner == self.region {
                return Ok(Some(block));
            }
            let current = self
                .graph
                .tree()
                .region(owner)
                .ok_or(StructureError::UnknownRegion(owner))?;
            let Some(parent) = current.parent else {
                return Ok(None);
            };
            if parent == self.region {
                let attached_handler = self
                    .graph
                    .handler_owners(owner)
                    .any(|handler_owner| self.children.contains(&handler_owner));
                if !self.children.contains(&owner) && !attached_handler {
                    return Ok(None);
                }
                return current
                    .entry
                    .map(Some)
                    .ok_or(StructureError::MissingEntry(owner));
            }
            owner = parent;
        }
    }

    pub(super) fn continuation(
        &self,
        cfg: &CFG,
        block: BlockId,
    ) -> Result<Option<BlockId>, StructureError> {
        let Some(mut current) = self.representative(block)? else {
            return Ok(None);
        };
        let mut positions = BTreeMap::new();
        let mut path = Vec::new();
        loop {
            if let Some(&cycle_start) = positions.get(&current) {
                return Ok(path[cycle_start..].iter().copied().min());
            }
            positions.insert(current, path.len());
            path.push(current);
            if self.is_child_entry(current) || !self.is_epsilon(cfg, current)? {
                return Ok(Some(current));
            }
            let successors = cfg.normal_successors(current).collect::<Vec<_>>();
            let [successor] = successors.as_slice() else {
                return Ok(Some(current));
            };
            let Some(next) = self.representative(*successor)? else {
                return Ok(Some(current));
            };
            current = next;
        }
    }

    pub(super) fn control_continuation(&self, block: BlockId) -> BlockId {
        self.anchors
            .representative(self.anchors.control_continuation(block))
    }

    fn is_child_entry(&self, block: BlockId) -> bool {
        self.ports.contains(&block)
    }

    fn is_epsilon(&self, cfg: &CFG, block: BlockId) -> Result<bool, StructureError> {
        if self.anchors.preserves(block) {
            return Ok(false);
        }
        let body = cfg
            .block(block)
            .ok_or(StructureError::MissingBlock(block))?;
        Ok(body.insns.iter().all(|instruction| {
            matches!(
                instruction.insn_type,
                InsnType::Nop | InsnType::Phi | InsnType::Goto
            ) || (instruction.id.is_valid()
                && self.graph.is_elided(&StatementOrigin {
                    block,
                    instruction: instruction.id,
                })
                && !instruction.insn_type.is_branch()
                && !instruction.insn_type.is_terminal())
        }))
    }

    fn layout(&self, cfg: &CFG) -> Result<RegionLayout, StructureError> {
        let mut mapping = BTreeMap::new();
        let mut representatives = BTreeSet::new();
        for block in cfg.block_ids() {
            if let Some(representative) = self.representative(block)? {
                mapping.insert(block, representative);
                representatives.insert(representative);
            }
        }
        let child_entries = self.ports.clone();
        Ok(RegionLayout {
            mapping,
            representatives,
            child_entries,
        })
    }
}

struct RegionLayout {
    mapping: BTreeMap<BlockId, BlockId>,
    representatives: BTreeSet<BlockId>,
    child_entries: BTreeSet<BlockId>,
}

impl RegionLayout {
    fn preserve(&mut self, block: BlockId) {
        self.mapping.insert(block, block);
        self.representatives.insert(block);
    }
}

pub(super) struct RegionCfgBuilder<'a> {
    cfg: &'a CFG,
    regions: &'a RegionGraph,
    region: RegionId,
    scope: RegionScope<'a>,
    child_flows: &'a BTreeMap<BlockId, BoundFlow>,
    entry_cuts: &'a BTreeSet<BlockId>,
    entry: Option<BlockId>,
}

impl<'a> RegionCfgBuilder<'a> {
    pub(super) fn new(
        cfg: &'a CFG,
        regions: &'a RegionGraph,
        region: RegionId,
        children: &[RegionId],
        ports: &'a BTreeSet<BlockId>,
        anchors: &'a RegionAnchors,
        child_flows: &'a BTreeMap<BlockId, BoundFlow>,
        entry_cuts: &'a BTreeSet<BlockId>,
        entry: Option<BlockId>,
    ) -> Self {
        Self {
            cfg,
            regions,
            region,
            scope: RegionScope::new(regions, region, children, ports, anchors),
            child_flows,
            entry_cuts,
            entry,
        }
    }

    pub(super) fn build(self) -> Result<RegionCfg, StructureError> {
        let mut layout = self.scope.layout(self.cfg)?;
        if let Some(entry) = self.entry {
            layout.preserve(entry);
        }
        let origin_sensitive_boundaries = self.scope.anchors.phi_copy_blocks().clone();
        let mut state = RegionCfgState::new(
            self.cfg,
            self.region,
            layout,
            origin_sensitive_boundaries,
            Arc::clone(&self.scope.anchors.canonical_continuations),
        )?;
        if state.layout.representatives.is_empty() {
            return Ok(state.finish());
        }
        let entry = self
            .entry
            .ok_or(StructureError::MissingEntry(self.region))?;
        state.connect_source_edges(self.cfg, self.regions, self.region, entry, self.entry_cuts)?;
        state.connect_child_flows(self.child_flows, entry, self.entry_cuts)?;
        Ok(state.finish())
    }
}

struct RegionCfgState {
    region: RegionId,
    cfg: CFG,
    layout: RegionLayout,
    edges: BTreeSet<(BlockId, BlockId, EdgeKind)>,
    boundaries: BTreeMap<BlockId, ResolvedRegionExit>,
    boundary_ids: BTreeMap<BoundaryKey, BlockId>,
    entry_boundaries: BTreeMap<BlockId, BlockId>,
    entry_boundary_ids: BTreeMap<BlockId, BlockId>,
    origin_sensitive_boundaries: BTreeSet<BlockId>,
    canonical_continuations: Arc<ControlContinuations>,
    next_boundary: u32,
    terminal_seeds: BTreeSet<BlockId>,
    open_flows: BTreeMap<BlockId, BTreeSet<BlockId>>,
}

impl RegionCfgState {
    fn new(
        source: &CFG,
        region: RegionId,
        layout: RegionLayout,
        origin_sensitive_boundaries: BTreeSet<BlockId>,
        canonical_continuations: Arc<ControlContinuations>,
    ) -> Result<Self, StructureError> {
        let mut cfg = source.subgraph(format!("{}::{region}", source.label()));
        for representative in &layout.representatives {
            let source_block = source
                .block(*representative)
                .ok_or(StructureError::MissingBlock(*representative))?;
            let mut block = Block::with_offset(*representative, source_block.offset);
            if layout.child_entries.contains(representative) {
                block.insns.push(crate::ir::InsnNode::nop());
            } else if let Some(terminator) = source_block.terminator() {
                block.insns.push(terminator.clone());
            }
            cfg.add_block(block);
        }
        let source_entry = source
            .block_ids()
            .into_iter()
            .map(|block| block.0)
            .max()
            .unwrap_or(0);
        let next_boundary = source_entry
            .checked_add(1)
            .ok_or(StructureError::BoundaryIdExhausted(region))?;
        Ok(Self {
            region,
            cfg,
            layout,
            edges: BTreeSet::new(),
            boundaries: BTreeMap::new(),
            boundary_ids: BTreeMap::new(),
            entry_boundaries: BTreeMap::new(),
            entry_boundary_ids: BTreeMap::new(),
            origin_sensitive_boundaries,
            canonical_continuations,
            next_boundary,
            terminal_seeds: BTreeSet::new(),
            open_flows: BTreeMap::new(),
        })
    }

    fn connect_source_edges(
        &mut self,
        source: &CFG,
        regions: &RegionGraph,
        region: RegionId,
        entry: BlockId,
        entry_cuts: &BTreeSet<BlockId>,
    ) -> Result<(), StructureError> {
        self.cfg.entry = self
            .layout
            .mapping
            .get(&entry)
            .copied()
            .ok_or(StructureError::RegionEntryMissing { region, entry })?;
        for source_block in source.block_ids() {
            let Some(&from) = self.layout.mapping.get(&source_block) else {
                continue;
            };
            // Quotient-graph edges originate only at the terminal
            // representative. Emitting edges from every contracted adapter
            // would copy its epsilon path onto the representative and can
            // manufacture self-loops or multiple successors.
            if from != source_block {
                continue;
            }
            // A contracted child entry owns the complete semantic fragment.
            // Its physical interior can contain exits to other region ports,
            // but those exits have already been summarized by BoundFlow.
            if self.layout.child_entries.contains(&from) {
                continue;
            }
            for &(target, kind) in source.successors_with_kind(source_block) {
                if kind.is_exception() {
                    continue;
                }
                if let Some(target) = self.entry_cut(target, entry, entry_cuts) {
                    let boundary = self.intern_entry_boundary(target)?;
                    self.edges.insert((from, boundary, kind));
                    continue;
                }
                let edge = RegionEdge {
                    source: source_block,
                    target,
                    kind,
                };
                if let Some(leave) = regions
                    .leave_for_edge(edge)
                    .filter(|leave| leave.leave.source == region)
                {
                    let boundary = self.intern_boundary(leave)?;
                    self.edges.insert((from, boundary, kind));
                } else {
                    if let Some(&to) = self.layout.mapping.get(&target) {
                        if from != to {
                            self.edges.insert((from, to, kind));
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn intern_boundary(&mut self, leave: &ResolvedRegionExit) -> Result<BlockId, StructureError> {
        let preserve_origin = leave
            .leave
            .source_block
            .is_some_and(|block| self.origin_sensitive_boundaries.contains(&block));
        let canonical_fallthrough = match &leave.leave.exit {
            RegionExit::FallThrough(target) => {
                Some(self.canonical_continuations.destination(*target))
            }
            _ => None,
        };
        let key = BoundaryKey::of(leave, preserve_origin, canonical_fallthrough);
        if let Some(boundary) = self.boundary_ids.get(&key) {
            return Ok(*boundary);
        }
        let boundary = BlockId::new(self.next_boundary);
        self.next_boundary = self
            .next_boundary
            .checked_add(1)
            .ok_or(StructureError::BoundaryIdExhausted(self.region))?;
        self.cfg.add_block(Block::synthetic(boundary));
        self.layout.representatives.insert(boundary);
        self.boundaries.insert(boundary, leave.clone());
        self.boundary_ids.insert(key, boundary);
        Ok(boundary)
    }

    fn intern_entry_boundary(&mut self, target: BlockId) -> Result<BlockId, StructureError> {
        if let Some(boundary) = self.entry_boundary_ids.get(&target) {
            return Ok(*boundary);
        }
        let boundary = BlockId::new(self.next_boundary);
        self.next_boundary = self
            .next_boundary
            .checked_add(1)
            .ok_or(StructureError::BoundaryIdExhausted(self.region))?;
        self.cfg.add_block(Block::synthetic(boundary));
        self.layout.representatives.insert(boundary);
        self.entry_boundaries.insert(boundary, target);
        self.entry_boundary_ids.insert(target, boundary);
        Ok(boundary)
    }

    fn connect_child_flows(
        &mut self,
        flows: &BTreeMap<BlockId, BoundFlow>,
        region_entry: BlockId,
        entry_cuts: &BTreeSet<BlockId>,
    ) -> Result<(), StructureError> {
        for (child_entry, flow) in flows {
            match flow {
                BoundFlow::Lexical(target) if child_entry != target => {
                    let target = self.partition_target(*target, region_entry, entry_cuts)?;
                    self.edges.insert((*child_entry, target, EdgeKind::Normal));
                }
                BoundFlow::Lexical(_) | BoundFlow::Terminal => {
                    self.terminal_seeds.insert(*child_entry);
                }
                BoundFlow::Leave(leave) => {
                    let boundary = self.intern_boundary(leave)?;
                    self.edges
                        .insert((*child_entry, boundary, EdgeKind::Normal));
                }
                BoundFlow::Open {
                    targets, boundary, ..
                } => {
                    let mut targets = targets
                        .iter()
                        .map(|target| self.partition_target(*target, region_entry, entry_cuts))
                        .collect::<Result<BTreeSet<_>, _>>()?;
                    if let Some(leave) = boundary {
                        targets.insert(self.intern_boundary(leave)?);
                    }
                    self.terminal_seeds.insert(*child_entry);
                    self.open_flows.insert(*child_entry, targets.clone());
                    self.edges.extend(
                        targets
                            .iter()
                            .map(|target| (*child_entry, *target, EdgeKind::Normal)),
                    );
                }
            }
        }
        Ok(())
    }

    fn partition_target(
        &mut self,
        target: BlockId,
        entry: BlockId,
        entry_cuts: &BTreeSet<BlockId>,
    ) -> Result<BlockId, StructureError> {
        let target = self.layout.mapping.get(&target).copied().unwrap_or(target);
        if let Some(target) = self.entry_cut(target, entry, entry_cuts) {
            self.intern_entry_boundary(target)
        } else {
            Ok(target)
        }
    }

    fn entry_cut(
        &self,
        target: BlockId,
        entry: BlockId,
        entry_cuts: &BTreeSet<BlockId>,
    ) -> Option<BlockId> {
        let target = self.layout.mapping.get(&target).copied().unwrap_or(target);
        let entry = self.layout.mapping.get(&entry).copied().unwrap_or(entry);
        (target != entry
            && entry_cuts
                .iter()
                .any(|cut| self.layout.mapping.get(cut).copied().unwrap_or(*cut) == target))
        .then_some(target)
    }

    fn finish(mut self) -> RegionCfg {
        for (from, to, kind) in self.edges {
            self.cfg.add_edge(from, to, kind);
        }
        self.cfg.prune_unreachable_graph_nodes();
        self.layout
            .representatives
            .retain(|block| self.cfg.is_graph_node(*block));
        self.boundaries
            .retain(|block, _| self.cfg.is_graph_node(*block));
        self.entry_boundaries
            .retain(|block, _| self.cfg.is_graph_node(*block));
        self.terminal_seeds
            .retain(|block| self.cfg.is_graph_node(*block));
        RegionCfg {
            cfg: self.cfg,
            mapping: self.layout.mapping,
            representatives: self.layout.representatives,
            boundaries: self.boundaries,
            entry_boundaries: self.entry_boundaries,
            terminal_seeds: self.terminal_seeds,
            open_flows: self.open_flows,
        }
    }
}

pub(super) struct RegionCfg {
    pub(super) cfg: CFG,
    pub(super) mapping: BTreeMap<BlockId, BlockId>,
    pub(super) representatives: BTreeSet<BlockId>,
    pub(super) boundaries: BTreeMap<BlockId, ResolvedRegionExit>,
    pub(super) entry_boundaries: BTreeMap<BlockId, BlockId>,
    pub(super) terminal_seeds: BTreeSet<BlockId>,
    pub(super) open_flows: BTreeMap<BlockId, BTreeSet<BlockId>>,
}

impl RegionCfg {
    pub(super) fn take_enclosed_body(
        &self,
        entry: BlockId,
        seeded: &mut BTreeMap<BlockId, SemanticNode>,
    ) -> Option<SemanticNode> {
        if self.representatives != BTreeSet::from([entry])
            || !self.boundaries.is_empty()
            || !self.entry_boundaries.is_empty()
            || seeded.len() != 1
            || !self.cfg.block(entry).is_some_and(|block| {
                block
                    .insns
                    .iter()
                    .all(|instruction| instruction.insn_type == InsnType::Nop)
            })
        {
            return None;
        }
        seeded.remove(&entry)
    }

    pub(super) fn reaches_any_handler(
        &self,
        source: &CFG,
        graph: &RegionGraph,
        handlers: impl Iterator<Item = RegionId>,
    ) -> bool {
        let handlers = handlers.collect::<BTreeSet<_>>();
        if handlers.is_empty() {
            return false;
        }
        self.mapping.iter().any(|(block, representative)| {
            self.representatives.contains(representative)
                && source
                    .successors_with_kind(*block)
                    .iter()
                    .filter(|(_, kind)| kind.is_exception())
                    .any(|(target, _)| {
                        std::iter::once(*target)
                            .chain(graph.handler_adapters().get(target).copied())
                            .filter_map(|entry| graph.owner_of(entry))
                            .any(|owner| {
                                handlers.iter().any(|handler| {
                                    owner == *handler
                                        || graph
                                            .tree()
                                            .is_ancestor(*handler, owner)
                                            .is_ok_and(|descendant| descendant)
                                })
                            })
                    })
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct BoundaryKey {
    exit: BoundaryExitKey,
    origin: Option<BlockId>,
    region_target: RegionId,
    target: RegionId,
    cleanup: Vec<RegionId>,
}

impl BoundaryKey {
    fn of(
        exit: &ResolvedRegionExit,
        preserve_origin: bool,
        canonical_fallthrough: Option<BlockId>,
    ) -> Self {
        Self {
            exit: BoundaryExitKey::of(&exit.leave.exit, canonical_fallthrough),
            origin: preserve_origin.then_some(exit.leave.source_block).flatten(),
            region_target: exit.leave.target,
            target: exit.leave.control_target.unwrap_or(exit.leave.target),
            cleanup: exit.cleanup_regions.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum BoundaryExitKey {
    FallThrough(BlockId),
    Return(Option<BoundaryValueKey>),
    Throw(BoundaryValueKey),
    Break,
    Continue,
}

impl BoundaryExitKey {
    fn of(exit: &RegionExit, canonical_fallthrough: Option<BlockId>) -> Self {
        match exit {
            RegionExit::FallThrough(target) => {
                Self::FallThrough(canonical_fallthrough.unwrap_or(*target))
            }
            RegionExit::Return(value) => Self::Return(value.as_ref().map(BoundaryValueKey::of)),
            RegionExit::Throw(value) => Self::Throw(BoundaryValueKey::of(value)),
            RegionExit::Break => Self::Break,
            RegionExit::Continue => Self::Continue,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum BoundaryValueKey {
    Register {
        number: u32,
        version: Option<u32>,
        variable: Option<u32>,
        ty: ArgType,
    },
    Literal {
        value: i64,
        ty: ArgType,
    },
    Wrapped(usize),
}

impl BoundaryValueKey {
    fn of(value: &InsnArg) -> Self {
        match value {
            InsnArg::Reg(register) => Self::Register {
                number: register.reg_num,
                version: register.ssa_version,
                variable: register.code_var,
                ty: register.ty.clone(),
            },
            InsnArg::Lit(literal) => Self::Literal {
                value: literal.value,
                ty: literal.ty.clone(),
            },
            InsnArg::Wrapped(instruction) => {
                Self::Wrapped(std::sync::Arc::as_ptr(instruction) as usize)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::{BoundaryExitKey, BoundaryValueKey, RegionEntryPorts};
    use crate::ir::{ArgType, BlockId, CatchRegion, InsnArg, RegionExit, RegionKind, RegionTree};

    #[test]
    fn return_boundaries_include_their_ssa_value() {
        let first = RegionExit::Return(Some(InsnArg::reg_ssa(0, 0, ArgType::BOOLEAN)));
        let second = RegionExit::Return(Some(InsnArg::reg_ssa(7, 2, ArgType::BOOLEAN)));

        assert_ne!(
            BoundaryExitKey::of(&first, None),
            BoundaryExitKey::of(&second, None)
        );
    }

    #[test]
    fn equivalent_return_boundaries_still_share_an_identity() {
        let value = InsnArg::reg_ssa(7, 2, ArgType::BOOLEAN);

        assert_eq!(
            BoundaryExitKey::of(&RegionExit::Return(Some(value.clone())), None),
            BoundaryExitKey::Return(Some(BoundaryValueKey::of(&value)))
        );
    }

    #[test]
    fn nested_entry_is_visible_through_every_crossed_region() {
        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        let root = tree.root();
        let outer = tree
            .add_child(root, RegionKind::Try, Some(BlockId::new(4)))
            .expect("outer region");
        let inner = tree
            .add_child(outer, RegionKind::Try, Some(BlockId::new(6)))
            .expect("inner region");
        let mut entries = tree
            .regions()
            .map(|region| (region.id, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        let target = BlockId::new(50);

        RegionEntryPorts::record_entry_path(
            &mut entries,
            &tree,
            &BTreeSet::from([root]),
            inner,
            target,
            |_| Ok(true),
        )
        .expect("entry path");

        assert_eq!(entries[&inner], BTreeSet::from([target]));
        assert_eq!(entries[&outer], BTreeSet::from([target]));
        assert!(entries[&root].is_empty());
    }

    #[test]
    fn nested_entry_does_not_escape_its_handler_envelope() {
        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        let root = tree.root();
        let outer = tree
            .add_child(root, RegionKind::Try, Some(BlockId::new(4)))
            .expect("outer region");
        let handler = tree
            .add_child(
                outer,
                RegionKind::Catch(CatchRegion {
                    exception_types: vec![ArgType::object("java/lang/Throwable")],
                    exception_value: None,
                    continuation: None,
                }),
                Some(BlockId::new(10)),
            )
            .expect("handler region");
        let inner = tree
            .add_child(handler, RegionKind::Try, Some(BlockId::new(12)))
            .expect("inner region");
        let mut entries = tree
            .regions()
            .map(|region| (region.id, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        let target = BlockId::new(22);

        RegionEntryPorts::record_entry_path(
            &mut entries,
            &tree,
            &BTreeSet::from([root]),
            inner,
            target,
            |_| Ok(true),
        )
        .expect("entry path");

        assert_eq!(entries[&inner], BTreeSet::from([target]));
        assert_eq!(entries[&handler], BTreeSet::from([target]));
        assert!(entries[&outer].is_empty());
    }
}
