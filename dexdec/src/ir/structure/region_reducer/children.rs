use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    BlockId, RegionExit, RegionGraph, RegionId, RegionKind, ResolvedRegionExit, SemanticLeave,
    SemanticLeaveKind, SemanticNode, StructuredRegion, CFG,
};

use super::super::{
    continuation::{BoundFlow, ContinuationBinding},
    loop_classifier::LoopClassifier,
    switch_structurer::SwitchControlDomain,
    StructureError,
};
use super::{
    handlers::HandlerReducer,
    labels::LexicalLabels,
    region_cfg::{RegionAnchors, RegionScope},
    ReducedRegion,
};

pub(super) struct RegionChildren {
    pub(super) ordinary: Vec<RegionId>,
    pub(super) handlers: BTreeSet<RegionId>,
    pub(super) releases: BTreeSet<RegionId>,
}

impl RegionChildren {
    pub(super) fn classify(
        cfg: &CFG,
        graph: &RegionGraph,
        region: &StructuredRegion,
    ) -> Result<Self, StructureError> {
        let mut handlers = BTreeSet::new();
        for handler in graph.handlers_of(region.id).iter().copied() {
            if graph
                .tree()
                .is_ancestor(handler, region.id)
                .map_err(|_| StructureError::UnknownRegion(handler))?
            {
                continue;
            }
            handlers.insert(handler);
        }
        let mut releases = graph
            .handlers_of(region.id)
            .iter()
            .copied()
            .filter(|handler| graph.is_synchronization_release_handler(*handler))
            .collect::<BTreeSet<_>>();
        if let RegionKind::Synchronized(synchronized) = &region.kind {
            releases.extend(synchronized.release_handlers.iter().copied());
        }
        handlers.extend(releases.iter().copied());
        let handler_reducer = HandlerReducer::new(graph);
        let handler_bodies = handlers
            .iter()
            .copied()
            .map(|handler| handler_reducer.body_region(region.id, handler))
            .collect::<Result<BTreeSet<_>, _>>()?;
        let release_bodies = releases
            .iter()
            .copied()
            .map(|handler| handler_reducer.body_region(region.id, handler))
            .collect::<Result<BTreeSet<_>, _>>()?;
        let mut ordinary = Vec::new();
        for child in region.children.iter().copied() {
            if releases.contains(&child) || release_bodies.contains(&child) {
                continue;
            }
            if graph.is_exception_handler(child) {
                if graph
                    .tree()
                    .region(child)
                    .ok_or(StructureError::UnknownRegion(child))?
                    .entry
                    .is_none()
                {
                    continue;
                }
                if Self::externally_entered(cfg, graph, child)? {
                    ordinary.push(child);
                    continue;
                }
                if handlers.contains(&child) || handler_bodies.contains(&child) {
                    continue;
                }
                let mut owned_below = false;
                for owner in graph.handler_owners(child) {
                    if owner == region.id
                        || graph
                            .tree()
                            .is_ancestor(region.id, owner)
                            .map_err(|_| StructureError::UnknownRegion(owner))?
                    {
                        owned_below = true;
                        break;
                    }
                }
                if owned_below {
                    continue;
                }
            } else if handlers.contains(&child) || handler_bodies.contains(&child) {
                continue;
            }
            ordinary.push(child);
        }
        Ok(Self {
            ordinary,
            handlers,
            releases,
        })
    }

    fn externally_entered(
        cfg: &CFG,
        graph: &RegionGraph,
        handler: RegionId,
    ) -> Result<bool, StructureError> {
        let owners = graph.handler_owners(handler).collect::<Vec<_>>();
        let blocks = &graph
            .tree()
            .region(handler)
            .ok_or(StructureError::UnknownRegion(handler))?
            .blocks;
        for target in blocks {
            for (predecessor, kind) in cfg.incoming_edges(*target) {
                if kind != crate::ir::EdgeKind::Normal {
                    continue;
                }
                let Some(source) = graph.owner_of(predecessor) else {
                    continue;
                };
                if source == handler
                    || graph
                        .tree()
                        .is_ancestor(handler, source)
                        .map_err(|_| StructureError::UnknownRegion(source))?
                {
                    continue;
                }
                let mut inside_owner = false;
                for owner in &owners {
                    if source == *owner
                        || graph
                            .tree()
                            .is_ancestor(*owner, source)
                            .map_err(|_| StructureError::UnknownRegion(source))?
                    {
                        inside_owner = true;
                        break;
                    }
                }
                if !inside_owner {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }
}

pub(super) struct ChildReducer<'a> {
    cfg: &'a CFG,
    graph: &'a RegionGraph,
    owner: RegionId,
    children: &'a [RegionId],
    handler_bodies: &'a BTreeSet<RegionId>,
    anchors: &'a RegionAnchors,
    observer: &'a dyn crate::ir::AnalysisObserver,
}

impl<'a> ChildReducer<'a> {
    pub(super) fn new(
        cfg: &'a CFG,
        graph: &'a RegionGraph,
        owner: RegionId,
        children: &'a [RegionId],
        handler_bodies: &'a BTreeSet<RegionId>,
        anchors: &'a RegionAnchors,
        observer: &'a dyn crate::ir::AnalysisObserver,
    ) -> Self {
        Self {
            cfg,
            graph,
            owner,
            children,
            handler_bodies,
            anchors,
            observer,
        }
    }

    pub(super) fn reduce(
        &self,
        reduced: &mut BTreeMap<RegionId, ReducedRegion>,
    ) -> Result<ChildContraction, StructureError> {
        let ports = self
            .children
            .iter()
            .flat_map(|child| reduced.get(child).into_iter())
            .flat_map(|reduction| reduction.ports.keys().copied())
            .collect::<BTreeSet<_>>();
        let scope = RegionScope::new(self.graph, self.owner, self.children, &ports, self.anchors);
        let mut contraction = ChildContraction::default();
        for child in self.children {
            let child_region = self
                .graph
                .tree()
                .region(*child)
                .ok_or(StructureError::UnknownRegion(*child))?;
            let primary = child_region
                .entry
                .ok_or(StructureError::MissingEntry(*child))?;
            let reduction =
                if self.graph.is_exception_handler(*child) || self.handler_bodies.contains(child) {
                    reduced.get(child).cloned()
                } else {
                    reduced.remove(child)
                }
                .ok_or(StructureError::MissingReduction(*child))?;
            let exits_control = reduction
                .ports
                .values()
                .any(|port| port.continuations.exits_control(*child));
            let completion = child_region
                .kind
                .follow()
                .filter(|_| exits_control)
                .map(|follow| {
                    ChildCompletion::new(self.cfg, self.graph, &scope, self.owner, *child, follow)
                        .analyze()
                })
                .transpose()?;
            for (entry, mut reduction) in reduction.ports {
                let canonical_control = entry == primary
                    && matches!(
                        &child_region.kind,
                        RegionKind::Loop(_) | RegionKind::Switch(_)
                    );
                let port_completion = canonical_control.then(|| completion.clone()).flatten();
                let (port_normal_target, port_boundary_flow) = port_completion
                    .as_ref()
                    .map(ChildCompletionFlow::flow_parts)
                    .unwrap_or((None, None));
                let internal = reduction.continuations.in_scope(*child).collect::<Vec<_>>();
                if !internal.is_empty() {
                    let body = ContinuationBinding::defer_ports(internal, self.owner)
                        .apply(reduction.body)?;
                    reduction = super::ReducedPort::new(body);
                }
                let mut external = Vec::new();
                for port in reduction.continuations.in_scope(self.owner) {
                    if scope.continuation(self.cfg, port.target)?.is_none() {
                        external.push(port);
                    }
                }
                if !external.is_empty() {
                    let parent = self
                        .graph
                        .tree()
                        .region(self.owner)
                        .and_then(|region| region.parent)
                        .unwrap_or(self.owner);
                    let body =
                        ContinuationBinding::defer_ports(external, parent).apply(reduction.body)?;
                    reduction = super::ReducedPort::new(body);
                }
                let targets = reduction
                    .continuations
                    .in_scope(self.owner)
                    .map(|port| {
                        let target = scope.continuation(self.cfg, port.target)?.ok_or(
                            StructureError::ContinuationTargetMissing {
                                scope: self.owner,
                                target: port.target,
                            },
                        )?;
                        Ok((port.target, target))
                    })
                    .collect::<Result<BTreeMap<_, _>, StructureError>>()?;
                let binding = ContinuationBinding::analyze(
                    &reduction.continuations,
                    self.owner,
                    &targets,
                    port_normal_target,
                    (entry == primary
                        && matches!(
                            &child_region.kind,
                            RegionKind::Loop(_) | RegionKind::Switch(_)
                        ))
                    .then_some(*child),
                    port_boundary_flow.is_some(),
                )?;
                let mut flow = match (binding.flow(), port_boundary_flow) {
                    (BoundFlow::Terminal, Some(leave)) => BoundFlow::Leave(leave),
                    (
                        BoundFlow::Open {
                            targets,
                            normal_target,
                            boundary: None,
                        },
                        Some(leave),
                    ) => BoundFlow::Open {
                        targets,
                        normal_target,
                        boundary: Some(leave),
                    },
                    (flow, None) => flow,
                    _ => return Err(StructureError::ConflictingChildFlow(*child)),
                };
                let body = binding.apply(reduction.body)?;
                let body =
                    if entry == primary && matches!(&child_region.kind, RegionKind::Switch(_)) {
                        SwitchControlDomain::bind(*child, body)?
                    } else {
                        body
                    };
                Self::verify_labels(self.owner, *child, entry, "bound", &body)?;
                self.observe(*child, entry, "bound", &body);
                // A loop can expose alternate entry ports when an exception
                // handler enters its interior. Each port is a cloned
                // structured view of the same control region and must close
                // break/continue locally; otherwise the alternate view leaks
                // inactive control transfers into its parent.
                let body = if matches!(&child_region.kind, RegionKind::Loop(_)) {
                    LoopClassifier::new(*child, entry)
                        .preserve_blocks(self.anchors.phi_copy_blocks().clone())
                        .classify(body)?
                } else {
                    body
                };
                Self::verify_labels(self.owner, *child, entry, "classified", &body)?;
                self.observe(*child, entry, "classified", &body);
                if !crate::ir::semantic::SemanticCompletion::analyze(&body).can_complete_normally()
                {
                    flow = flow.close_normal_path();
                }
                let body = OpenFlowCompletion::attach(self.owner, body, &flow);
                Self::verify_labels(self.owner, *child, entry, "completed", &body)?;
                self.observe(*child, entry, "completed", &body);
                contraction.flows.insert(entry, flow);
                contraction.seeded.insert(entry, body);
            }
        }
        contraction.ports = ports;
        Ok(contraction)
    }

    fn verify_labels(
        owner: RegionId,
        child: RegionId,
        entry: BlockId,
        stage: &'static str,
        body: &SemanticNode,
    ) -> Result<(), StructureError> {
        match LexicalLabels::escaped_loop(body) {
            Some(label) => Err(StructureError::EscapedChildLabel {
                owner,
                child,
                entry,
                stage,
                label,
            }),
            None => Ok(()),
        }
    }

    fn observe(&self, child: RegionId, entry: BlockId, stage: &'static str, root: &SemanticNode) {
        self.observer
            .observe(crate::ir::AnalysisEvent::RegionChild {
                owner: self.owner,
                child,
                entry,
                stage,
                root,
            });
    }
}

#[derive(Clone)]
enum ChildCompletionFlow {
    Local(BlockId),
    Boundary(ResolvedRegionExit),
}

impl ChildCompletionFlow {
    fn flow_parts(&self) -> (Option<BlockId>, Option<ResolvedRegionExit>) {
        match self {
            Self::Local(target) => (Some(*target), None),
            Self::Boundary(exit) => (None, Some(exit.clone())),
        }
    }
}

struct ChildCompletion<'a> {
    cfg: &'a CFG,
    graph: &'a RegionGraph,
    scope: &'a RegionScope<'a>,
    owner: RegionId,
    child: RegionId,
    follow: BlockId,
}

impl<'a> ChildCompletion<'a> {
    fn new(
        cfg: &'a CFG,
        graph: &'a RegionGraph,
        scope: &'a RegionScope<'a>,
        owner: RegionId,
        child: RegionId,
        follow: BlockId,
    ) -> Self {
        Self {
            cfg,
            graph,
            scope,
            owner,
            child,
            follow,
        }
    }

    fn analyze(&self) -> Result<ChildCompletionFlow, StructureError> {
        if let Some(target) = self.scope.continuation(self.cfg, self.follow)? {
            return Ok(ChildCompletionFlow::Local(target));
        }

        let exits = self.break_exits()?;
        let first = exits
            .first()
            .cloned()
            .ok_or(StructureError::ContinuationTargetMissing {
                scope: self.owner,
                target: self.follow,
            })?;

        let local_targets = exits
            .iter()
            .map(|resolved| {
                let edge =
                    resolved
                        .leave
                        .edge
                        .ok_or(StructureError::ContinuationTargetMissing {
                            scope: self.owner,
                            target: self.follow,
                        })?;
                self.scope
                    .continuation(self.cfg, self.completion_destination(edge.target))
            })
            .collect::<Result<BTreeSet<_>, StructureError>>()?;
        if local_targets.len() == 1 {
            if let Some(target) = local_targets.first().copied().flatten() {
                return Ok(ChildCompletionFlow::Local(target));
            }
        } else {
            return Err(StructureError::ConflictingChildFlow(self.child));
        }

        let destination_block = self.scope.control_continuation(self.follow);
        let destination =
            self.graph
                .owner_of(destination_block)
                .ok_or(StructureError::RegionOwnerMissing {
                    region: self.owner,
                    block: destination_block,
                })?;
        let target = self
            .graph
            .tree()
            .common_ancestor(self.owner, destination)
            .map_err(StructureError::from)?;
        let mut boundary = first;
        boundary.leave.source = self.owner;
        boundary.leave.target = target;
        boundary.leave.exit = RegionExit::FallThrough(self.follow);
        boundary.leave.control_target = None;
        boundary.leave.source_block = None;
        boundary.leave.edge = None;
        boundary.cleanup_regions = self
            .graph
            .cleanup_chain(self.owner, boundary.leave.target)
            .map_err(StructureError::from)?;
        Ok(ChildCompletionFlow::Boundary(boundary))
    }

    fn break_exits(&self) -> Result<Vec<ResolvedRegionExit>, StructureError> {
        let mut exits = Vec::new();
        for resolved in self.graph.leaves() {
            if resolved.leave.target == self.child
                || resolved.leave.control_target != Some(self.child)
                || !matches!(resolved.leave.exit, RegionExit::Break)
            {
                continue;
            }
            if !self
                .graph
                .tree()
                .is_ancestor(self.child, resolved.leave.source)
                .map_err(|_| StructureError::UnknownRegion(resolved.leave.source))?
            {
                continue;
            }
            if resolved.leave.edge.is_some_and(|edge| {
                self.completion_destination(edge.target) == self.completion_destination(self.follow)
            }) {
                exits.push(resolved.clone());
            }
        }
        Ok(exits)
    }

    fn completion_destination(&self, block: BlockId) -> BlockId {
        // Cleanup predecessors may be preserved as physical Phi-copy anchors,
        // but they still denote the same control destination as the cleanup
        // completion. Compare that semantic destination without erasing the
        // anchors needed by later out-of-SSA lowering.
        let continuation = self.graph.control_continuation(block);
        let continuation = self
            .graph
            .cleanup_representative(continuation)
            .unwrap_or(continuation);
        self.graph.control_continuation(continuation)
    }
}

struct OpenFlowCompletion;

impl OpenFlowCompletion {
    fn attach(owner: RegionId, body: SemanticNode, flow: &BoundFlow) -> SemanticNode {
        let BoundFlow::Open {
            normal_target: Some(target),
            ..
        } = flow
        else {
            return body;
        };
        if !crate::ir::semantic::SemanticCompletion::analyze(&body).can_complete_normally() {
            return body;
        }
        SemanticNode::sequence([
            body,
            SemanticNode::Leave(SemanticLeave {
                site: None,
                condition: None,
                kind: SemanticLeaveKind::Jump(*target),
                edge: None,
                origin: None,
                source: owner,
                destination: owner,
                target: owner,
                cleanup: Vec::new(),
            }),
        ])
    }
}

#[derive(Default)]
pub(super) struct ChildContraction {
    pub(super) ports: BTreeSet<BlockId>,
    pub(super) seeded: BTreeMap<BlockId, SemanticNode>,
    pub(super) flows: BTreeMap<BlockId, BoundFlow>,
}
