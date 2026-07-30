use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{BlockId, EdgeKind, InsnType, RegionEdge, RegionGraph, CFG};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum NormalCopySite {
    Block(BlockId),
    Edge(RegionEdge),
}

impl NormalCopySite {
    pub fn predecessor(self) -> BlockId {
        match self {
            Self::Block(block) => block,
            Self::Edge(edge) => edge.source,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ControlContractions {
    domains: Vec<BTreeMap<BlockId, BTreeSet<BlockId>>>,
}

impl ControlContractions {
    pub fn from_regions(regions: &RegionGraph) -> Self {
        ContractionGraph::new(Self::region_relations(regions)).solve(CyclePolicy::Canonical)
    }

    pub fn for_edge_arguments(cfg: &CFG, regions: &RegionGraph) -> Self {
        let region_relations = Self::region_relations(regions);
        let exception_entries = ExceptionEntryCorridors::new(cfg, regions).relations();
        let exceptional_relations = regions.exceptional_contractions();
        ContractionGraph::new(region_relations)
            .solve(CyclePolicy::Preserve)
            .with_domain(ContractionGraph::new(exception_entries).solve(CyclePolicy::Preserve))
            .with_domain(
                ContractionGraph::new(exceptional_relations.iter().copied())
                    .solve(CyclePolicy::Preserve),
            )
    }

    fn region_relations(regions: &RegionGraph) -> Vec<(BlockId, BlockId)> {
        regions
            .handler_adapters()
            .iter()
            .map(|(block, representative)| (*block, *representative))
            .chain(
                regions
                    .cleanup_representatives()
                    .iter()
                    .map(|(block, representative)| (*block, *representative)),
            )
            .collect()
    }

    pub fn contracts_to(&self, block: BlockId, terminal: BlockId) -> bool {
        self.domains.iter().any(|domain| {
            domain
                .get(&block)
                .is_some_and(|terminals| terminals.contains(&terminal))
        })
    }

    pub fn shares_quotient_node(&self, left: BlockId, right: BlockId) -> bool {
        self.domains.iter().any(|domain| {
            let Some(left_terminals) = domain.get(&left) else {
                return false;
            };
            let Some(right_terminals) = domain.get(&right) else {
                return false;
            };
            !left_terminals.is_disjoint(right_terminals)
        })
    }

    pub fn is_contracted(&self, block: BlockId) -> bool {
        self.domains.iter().any(|domain| {
            domain
                .get(&block)
                .is_some_and(|terminals| !terminals.contains(&block))
        })
    }

    pub fn terminal(&self, block: BlockId) -> Option<BlockId> {
        let terminals = self
            .domains
            .iter()
            .filter_map(|domain| domain.get(&block))
            .flatten()
            .copied()
            .collect::<BTreeSet<_>>();
        if terminals.is_empty() {
            return Some(block);
        }
        let mut terminals = terminals.iter().copied();
        let terminal = terminals.next()?;
        terminals.next().is_none().then_some(terminal)
    }

    pub fn component(&self, terminal: BlockId) -> BTreeSet<BlockId> {
        self.domains
            .iter()
            .flat_map(|domain| domain.iter())
            .filter_map(|(block, terminals)| terminals.contains(&terminal).then_some(*block))
            .collect()
    }

    fn with_domain(mut self, other: Self) -> Self {
        self.domains.extend(other.domains);
        self
    }

    /// Finds the concrete CFG edge on which a Phi copy for a quotient-graph
    /// edge can be emitted.
    ///
    /// Cleanup contraction can turn a non-critical physical edge into a
    /// critical quotient edge. When the contracted entry has one external
    /// ingress and immediately continues inside the same component, its tail
    /// is the edge-specific copy site.
    pub fn normal_copy_site(
        &self,
        cfg: &CFG,
        predecessor: BlockId,
        entry: BlockId,
        successor: BlockId,
    ) -> Option<NormalCopySite> {
        let predecessor_targets = cfg.normal_successors(predecessor).collect::<BTreeSet<_>>();
        if predecessor_targets == BTreeSet::from([entry]) {
            return Some(NormalCopySite::Block(predecessor));
        }

        let component = self.component(successor);
        if !component.contains(&entry) {
            return None;
        }
        let external_ingress = cfg
            .incoming_edges(entry)
            .into_iter()
            .filter(|(source, kind)| !kind.is_exception() && !component.contains(source))
            .map(|(source, _)| source)
            .collect::<BTreeSet<_>>();
        if external_ingress != BTreeSet::from([predecessor]) {
            return None;
        }
        let entry_targets = cfg.normal_successors(entry).collect::<BTreeSet<_>>();
        if entry_targets.len() != 1 || !entry_targets.is_subset(&component) {
            return None;
        }
        let edge = cfg
            .successors_with_kind(predecessor)
            .iter()
            .filter(|(target, kind)| *target == entry && !kind.is_exception())
            .copied()
            .collect::<Vec<_>>();
        let [(target, kind)] = edge.as_slice() else {
            return None;
        };
        Some(NormalCopySite::Edge(RegionEdge {
            source: predecessor,
            target: *target,
            kind: *kind,
        }))
    }

    pub fn phi_copy_anchors(&self, cfg: &CFG) -> BTreeSet<BlockId> {
        let mut anchors = BTreeSet::new();
        for (&successor, block) in &cfg.blocks {
            let mut component = self.component(successor);
            component.remove(&successor);
            for phi in block
                .insns
                .iter()
                .filter(|instruction| instruction.insn_type == InsnType::Phi)
            {
                for (predecessor, edge_kind) in &phi.payload.phi_edges {
                    if *edge_kind != EdgeKind::Normal {
                        continue;
                    }
                    // SSA destruction may conservatively fall back from a
                    // contracted quotient edge to its concrete Phi inputs.
                    // Keep every normal predecessor identifiable until that
                    // decision has been made; empty identities disappear
                    // during semantic compaction.
                    anchors.insert(*predecessor);
                    if component.contains(predecessor) {
                        for entry in &component {
                            for (source, _) in
                                cfg.incoming_edges(*entry)
                                    .into_iter()
                                    .filter(|(source, kind)| {
                                        !component.contains(source) && !kind.is_exception()
                                    })
                            {
                                if let Some(site) =
                                    self.normal_copy_site(cfg, source, *entry, successor)
                                {
                                    anchors.insert(site.predecessor());
                                }
                            }
                        }
                    } else if !self.shares_quotient_node(*predecessor, successor) {
                        if let Some(site) =
                            self.normal_copy_site(cfg, *predecessor, successor, successor)
                        {
                            anchors.insert(site.predecessor());
                        }
                    }
                }
            }
        }
        anchors
    }
}

/// Finds side-effect-free transport corridors between a physical exception
/// landing pad and its semantic handler entry.
///
/// DEX may split `move-exception`, register transport, and the handler body
/// across several blocks. Contracting the complete corridor makes SSA edge
/// arguments originate at the exceptional boundary instead of at a physical
/// adapter that does not survive structural recovery.
struct ExceptionEntryCorridors<'a> {
    cfg: &'a CFG,
    handler_entries: BTreeSet<BlockId>,
}

impl<'a> ExceptionEntryCorridors<'a> {
    fn new(cfg: &'a CFG, regions: &'a RegionGraph) -> Self {
        let handler_entries = regions
            .tree()
            .regions()
            .filter(|region| regions.is_exception_handler(region.id))
            .filter_map(|region| region.entry.or_else(|| region.kind.continuation()))
            .collect();
        Self {
            cfg,
            handler_entries,
        }
    }

    fn relations(&self) -> BTreeSet<(BlockId, BlockId)> {
        self.cfg
            .block_ids()
            .into_iter()
            .filter(|block| self.is_landing(*block))
            .filter_map(|landing| self.corridor(landing))
            .flat_map(|(corridor, destination)| {
                corridor.into_iter().map(move |block| (block, destination))
            })
            .collect()
    }

    fn corridor(&self, landing: BlockId) -> Option<(Vec<BlockId>, BlockId)> {
        let incoming = self.cfg.incoming_edges(landing);
        if !incoming.iter().any(|(_, kind)| kind.is_exception())
            || incoming.iter().any(|(_, kind)| !kind.is_exception())
        {
            return None;
        }

        let mut corridor = Vec::new();
        let mut visited = BTreeSet::new();
        let mut block = landing;

        loop {
            if self.handler_entries.contains(&block) {
                return Some((corridor, block));
            }
            if !visited.insert(block) {
                return None;
            }
            corridor.push(block);

            let Some(successor) = self.transport_successor(block) else {
                return None;
            };
            block = successor;
        }
    }

    fn transport_successor(&self, block: BlockId) -> Option<BlockId> {
        let Some(body) = self.cfg.block(block) else {
            return None;
        };
        let transport = body.insns.iter().all(|instruction| {
            matches!(
                instruction.insn_type,
                InsnType::MoveException
                    | InsnType::Move
                    | InsnType::Const
                    | InsnType::ConstStr
                    | InsnType::Phi
                    | InsnType::Goto
                    | InsnType::Nop
            )
        });
        if !transport
            || self
                .cfg
                .successors_with_kind(block)
                .iter()
                .any(|(_, kind)| kind.is_exception())
        {
            return None;
        }
        let mut successors = self.cfg.normal_successors(block);
        let successor = successors.next()?;
        successors.next().is_none().then_some(successor)
    }

    fn is_landing(&self, block: BlockId) -> bool {
        self.cfg.block(block).is_some_and(|body| {
            body.insns
                .iter()
                .any(|instruction| instruction.insn_type == InsnType::MoveException)
        })
    }
}

struct ContractionGraph {
    edges: BTreeMap<BlockId, BTreeSet<BlockId>>,
}

#[derive(Clone, Copy)]
enum CyclePolicy {
    Canonical,
    Preserve,
}

impl ContractionGraph {
    fn new(relations: impl IntoIterator<Item = (BlockId, BlockId)>) -> Self {
        let mut edges = BTreeMap::<BlockId, BTreeSet<BlockId>>::new();
        for (source, target) in relations {
            edges.entry(source).or_default();
            edges.entry(target).or_default();
            if source != target {
                edges.entry(source).or_default().insert(target);
            }
        }
        Self { edges }
    }

    fn solve(&self, cycle_policy: CyclePolicy) -> ControlContractions {
        let components = StrongComponents::analyze(&self.edges);
        let component_edges = self.component_edges(&components);
        let terminals = ComponentTerminals::analyze(&components, &component_edges);
        ControlContractions {
            domains: vec![self
                .edges
                .keys()
                .map(|block| {
                    let component = components.by_block[block];
                    let terminal = if matches!(cycle_policy, CyclePolicy::Preserve)
                        && component_edges[&component].is_empty()
                        && components.members[&component].len() > 1
                    {
                        BTreeSet::from([*block])
                    } else {
                        terminals[&component].clone()
                    };
                    (*block, terminal)
                })
                .collect()],
        }
    }

    fn component_edges(&self, components: &StrongComponents) -> BTreeMap<usize, BTreeSet<usize>> {
        let mut edges = components
            .members
            .keys()
            .map(|component| (*component, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        for (source, targets) in &self.edges {
            let source_component = components.by_block[source];
            for target in targets {
                let target_component = components.by_block[target];
                if source_component != target_component {
                    edges
                        .entry(source_component)
                        .or_default()
                        .insert(target_component);
                }
            }
        }
        edges
    }
}

struct StrongComponents {
    by_block: BTreeMap<BlockId, usize>,
    members: BTreeMap<usize, BTreeSet<BlockId>>,
}

impl StrongComponents {
    fn analyze(edges: &BTreeMap<BlockId, BTreeSet<BlockId>>) -> Self {
        let order = Self::finishing_order(edges);
        let reverse = Self::reverse(edges);
        let mut by_block = BTreeMap::new();
        let mut members = BTreeMap::new();
        for root in order.into_iter().rev() {
            if by_block.contains_key(&root) {
                continue;
            }
            let component = members.len();
            let mut pending = vec![root];
            let mut component_members = BTreeSet::new();
            while let Some(block) = pending.pop() {
                if by_block.contains_key(&block) {
                    continue;
                }
                by_block.insert(block, component);
                component_members.insert(block);
                pending.extend(reverse.get(&block).into_iter().flatten().copied());
            }
            members.insert(component, component_members);
        }
        Self { by_block, members }
    }

    fn finishing_order(edges: &BTreeMap<BlockId, BTreeSet<BlockId>>) -> Vec<BlockId> {
        let mut visited = BTreeSet::new();
        let mut order = Vec::with_capacity(edges.len());
        for root in edges.keys().copied() {
            if visited.contains(&root) {
                continue;
            }
            let mut pending = vec![(root, false)];
            while let Some((block, exiting)) = pending.pop() {
                if exiting {
                    order.push(block);
                    continue;
                }
                if !visited.insert(block) {
                    continue;
                }
                pending.push((block, true));
                pending.extend(
                    edges
                        .get(&block)
                        .into_iter()
                        .flatten()
                        .rev()
                        .map(|successor| (*successor, false)),
                );
            }
        }
        order
    }

    fn reverse(
        edges: &BTreeMap<BlockId, BTreeSet<BlockId>>,
    ) -> BTreeMap<BlockId, BTreeSet<BlockId>> {
        let mut reverse = edges
            .keys()
            .map(|block| (*block, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        for (source, targets) in edges {
            for target in targets {
                reverse.entry(*target).or_default().insert(*source);
            }
        }
        reverse
    }
}

struct ComponentTerminals;

impl ComponentTerminals {
    fn analyze(
        components: &StrongComponents,
        edges: &BTreeMap<usize, BTreeSet<usize>>,
    ) -> BTreeMap<usize, BTreeSet<BlockId>> {
        let mut reverse = components
            .members
            .keys()
            .map(|component| (*component, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        let mut remaining = BTreeMap::new();
        for (source, targets) in edges {
            remaining.insert(*source, targets.len());
            for target in targets {
                reverse.entry(*target).or_default().insert(*source);
            }
        }

        let mut terminals = BTreeMap::<usize, BTreeSet<BlockId>>::new();
        let mut ready = remaining
            .iter()
            .filter_map(|(component, degree)| (*degree == 0).then_some(*component))
            .collect::<BTreeSet<_>>();
        while let Some(component) = ready.pop_first() {
            if edges[&component].is_empty() {
                let canonical = components.members[&component]
                    .iter()
                    .next()
                    .copied()
                    .expect("strong component must contain a block");
                terminals.insert(component, BTreeSet::from([canonical]));
            }
            let propagated = terminals.get(&component).cloned().unwrap_or_default();
            for predecessor in reverse[&component].iter().copied() {
                terminals
                    .entry(predecessor)
                    .or_default()
                    .extend(propagated.iter().copied());
                let degree = remaining
                    .get_mut(&predecessor)
                    .expect("component must have an outdegree");
                *degree -= 1;
                if *degree == 0 {
                    ready.insert(predecessor);
                }
            }
        }
        terminals
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{BlockId, ContractionGraph, CyclePolicy};

    #[test]
    fn contracts_acyclic_chain_to_its_sink() {
        let contractions =
            ContractionGraph::new([(BlockId(1), BlockId(2)), (BlockId(2), BlockId(3))])
                .solve(CyclePolicy::Canonical);
        assert_eq!(contractions.terminal(BlockId(1)), Some(BlockId(3)));
        assert_eq!(contractions.terminal(BlockId(2)), Some(BlockId(3)));
        assert_eq!(contractions.terminal(BlockId(3)), Some(BlockId(3)));
        assert!(contractions.shares_quotient_node(BlockId(1), BlockId(2)));
        assert!(contractions.shares_quotient_node(BlockId(2), BlockId(3)));
    }

    #[test]
    fn contracts_closed_cycle_to_stable_canonical_member() {
        let contractions =
            ContractionGraph::new([(BlockId(2), BlockId(1)), (BlockId(1), BlockId(2))])
                .solve(CyclePolicy::Canonical);
        assert_eq!(contractions.terminal(BlockId(1)), Some(BlockId(1)));
        assert_eq!(contractions.terminal(BlockId(2)), Some(BlockId(1)));
        assert!(!contractions.is_contracted(BlockId(1)));
        assert!(contractions.is_contracted(BlockId(2)));
    }

    #[test]
    fn contracts_cycle_with_exit_to_external_sink() {
        let contractions = ContractionGraph::new([
            (BlockId(1), BlockId(2)),
            (BlockId(2), BlockId(1)),
            (BlockId(2), BlockId(3)),
        ])
        .solve(CyclePolicy::Canonical);
        assert_eq!(contractions.terminal(BlockId(1)), Some(BlockId(3)));
        assert_eq!(contractions.terminal(BlockId(2)), Some(BlockId(3)));
    }

    #[test]
    fn preserves_multiple_reachable_sinks() {
        let contractions =
            ContractionGraph::new([(BlockId(1), BlockId(2)), (BlockId(1), BlockId(3))])
                .solve(CyclePolicy::Canonical);
        assert_eq!(contractions.terminal(BlockId(1)), None);
        assert!(contractions.contracts_to(BlockId(1), BlockId(2)));
        assert!(contractions.contracts_to(BlockId(1), BlockId(3)));
    }

    #[test]
    fn keeps_independent_contraction_domains() {
        let normal = ContractionGraph::new([(BlockId(1), BlockId(2))]).solve(CyclePolicy::Preserve);
        let exceptional =
            ContractionGraph::new([(BlockId(1), BlockId(3))]).solve(CyclePolicy::Preserve);
        let contractions = normal.with_domain(exceptional);

        assert!(contractions.contracts_to(BlockId(1), BlockId(2)));
        assert!(contractions.contracts_to(BlockId(1), BlockId(3)));
        assert_eq!(
            contractions.component(BlockId(2)),
            BTreeSet::from([BlockId(1), BlockId(2)])
        );
        assert_eq!(contractions.terminal(BlockId(1)), None);
    }

    #[test]
    fn keeps_converging_branches_in_distinct_components() {
        let contractions = ContractionGraph::new([
            (BlockId(1), BlockId(2)),
            (BlockId(1), BlockId(3)),
            (BlockId(4), BlockId(2)),
        ])
        .solve(CyclePolicy::Canonical);
        assert!(contractions.contracts_to(BlockId(1), BlockId(2)));
        assert!(contractions.contracts_to(BlockId(1), BlockId(3)));
        assert!(contractions.contracts_to(BlockId(4), BlockId(2)));
        assert!(!contractions.contracts_to(BlockId(4), BlockId(3)));
    }

    #[test]
    fn preserves_members_of_closed_projection_cycle() {
        let contractions =
            ContractionGraph::new([(BlockId(2), BlockId(1)), (BlockId(1), BlockId(2))])
                .solve(CyclePolicy::Preserve);
        assert_eq!(contractions.terminal(BlockId(1)), Some(BlockId(1)));
        assert_eq!(contractions.terminal(BlockId(2)), Some(BlockId(2)));
        assert!(!contractions.contracts_to(BlockId(1), BlockId(2)));
        assert!(!contractions.contracts_to(BlockId(2), BlockId(1)));
    }
}
