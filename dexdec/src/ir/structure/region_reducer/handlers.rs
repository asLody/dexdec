use std::collections::BTreeMap;

use crate::ir::analysis::SsaVar;
use crate::ir::{
    ArgType, RegionGraph, RegionId, RegionKind, RegisterArg, SemanticCatch, SemanticExpression,
    SemanticExpressionTransform, SemanticFinally, SemanticFolder, SemanticInstructions,
    SemanticLeaveKind, SemanticNode,
};

use super::super::{
    continuation::{ContinuationBinding, ControlPort, ControlTransfer},
    StructureError,
};
use super::region_cfg::RegionCfg;
use super::{ExceptionEnvelope, ReducedPort, ReducedRegion, RegionChildren};

struct ExceptionForwarding {
    thrown: RegisterArg,
    origin: Option<crate::ir::BlockId>,
    edge: Option<crate::ir::RegionEdge>,
    caught: RegisterArg,
    body: SemanticNode,
}

impl ExceptionForwarding {
    fn collapse(
        node: SemanticNode,
        handler_exception: Option<&RegisterArg>,
    ) -> Result<SemanticNode, StructureError> {
        let Some(forwarding) = Self::analyze(&node, handler_exception) else {
            return Ok(node);
        };
        let Some(caught) = SsaVar::from_reg(&forwarding.caught) else {
            return Ok(node);
        };
        let Some(thrown) = SsaVar::from_reg(&forwarding.thrown) else {
            return Ok(node);
        };
        let mut body = forwarding.body;
        SemanticInstructions::transform(
            &mut body,
            &mut ExceptionValueSubstitution {
                caught,
                thrown: forwarding.thrown,
            },
        )?;
        let mut provenance = ForwardedThrowProvenance {
            thrown,
            origin: forwarding.origin,
            edge: forwarding.edge,
            count: 0,
        };
        body = provenance.fold_node(body)?;
        if provenance.count != 1 {
            return Ok(node);
        }
        Ok(body)
    }

    fn analyze(node: &SemanticNode, handler_exception: Option<&RegisterArg>) -> Option<Self> {
        let SemanticNode::Try {
            body,
            catches,
            finally: None,
            ..
        } = node
        else {
            return None;
        };
        let [catch] = catches.as_slice() else {
            return None;
        };
        if !catch
            .exception_types
            .iter()
            .any(|exception| exception == &ArgType::throwable())
        {
            return None;
        }
        let thrown = ForwardedException::analyze(body)?;
        let handler_exception = handler_exception?;
        if SsaVar::from_reg(&thrown.value) != SsaVar::from_reg(handler_exception) {
            return None;
        }
        Some(Self {
            thrown: thrown.value,
            origin: thrown.origin,
            edge: thrown.edge,
            caught: catch.exception_value.clone()?,
            body: catch.body.clone(),
        })
    }
}

struct ForwardedThrow {
    value: RegisterArg,
    origin: Option<crate::ir::BlockId>,
    edge: Option<crate::ir::RegionEdge>,
}

struct ForwardedException;

impl ForwardedException {
    fn analyze(node: &SemanticNode) -> Option<ForwardedThrow> {
        let nodes = match node {
            SemanticNode::Sequence(nodes) => nodes.as_slice(),
            node => std::slice::from_ref(node),
        };
        let mut thrown = None;
        for node in nodes {
            match node {
                SemanticNode::Empty => {}
                SemanticNode::BasicBlock(block) if block.statements.is_empty() => {}
                SemanticNode::Leave(leave)
                    if leave.condition.is_none()
                        && leave.cleanup.is_empty()
                        && matches!(&leave.kind, SemanticLeaveKind::Throw(_)) =>
                {
                    let SemanticLeaveKind::Throw(SemanticExpression::Register(value)) = &leave.kind
                    else {
                        return None;
                    };
                    if thrown
                        .replace(ForwardedThrow {
                            value: value.clone(),
                            origin: leave.origin,
                            edge: leave.edge,
                        })
                        .is_some()
                    {
                        return None;
                    }
                }
                _ => return None,
            }
        }
        thrown
    }
}

struct ForwardedThrowProvenance {
    thrown: SsaVar,
    origin: Option<crate::ir::BlockId>,
    edge: Option<crate::ir::RegionEdge>,
    count: usize,
}

impl SemanticFolder for ForwardedThrowProvenance {
    type Error = crate::ir::SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        let SemanticNode::Leave(mut leave) = node else {
            return Ok(node);
        };
        let SemanticLeaveKind::Throw(SemanticExpression::Register(value)) = &leave.kind else {
            return Ok(SemanticNode::Leave(leave));
        };
        if SsaVar::from_reg(value) == Some(self.thrown) {
            self.count += 1;
            leave.origin = self.origin;
            leave.edge = self.edge;
        }
        Ok(SemanticNode::Leave(leave))
    }
}

struct ExceptionValueSubstitution {
    caught: SsaVar,
    thrown: RegisterArg,
}

impl SemanticExpressionTransform for ExceptionValueSubstitution {
    fn transform_register(&mut self, register: RegisterArg) -> SemanticExpression {
        if SsaVar::from_reg(&register) == Some(self.caught) {
            SemanticExpression::Register(self.thrown.clone())
        } else {
            SemanticExpression::Register(register)
        }
    }
}

pub(super) struct HandlerContraction {
    pub(super) envelope: ExceptionEnvelope,
    pub(super) ports: BTreeMap<crate::ir::BlockId, HandlerPort>,
}

pub(super) struct HandlerPort {
    pub(super) handler: RegionId,
    pub(super) port: ReducedPort,
}

pub(super) struct HandlerReducer<'a> {
    regions: &'a RegionGraph,
}

impl<'a> HandlerReducer<'a> {
    pub(super) fn new(regions: &'a RegionGraph) -> Self {
        Self { regions }
    }

    pub(super) fn body_region(
        &self,
        owner: RegionId,
        handler: RegionId,
    ) -> Result<RegionId, StructureError> {
        let tree = self.regions.tree();
        let handler_region = tree
            .region(handler)
            .ok_or(StructureError::UnknownRegion(handler))?;
        let Some(entry) = handler_region.entry else {
            let bodies = handler_region
                .children
                .iter()
                .copied()
                .filter(|child| {
                    tree.region(*child).is_some_and(|child| {
                        child.entry.is_some() && child.blocks == handler_region.blocks
                    })
                })
                .collect::<Vec<_>>();
            if let [body] = bodies.as_slice() {
                return Ok(*body);
            }
            return Ok(handler);
        };
        let mut body = handler;
        loop {
            let current = tree
                .region(body)
                .ok_or(StructureError::UnknownRegion(body))?;
            let Some(parent) = current.parent else {
                break;
            };
            if self.regions.handlers_of(parent).contains(&handler) {
                break;
            }
            if parent == owner {
                break;
            }
            let envelope = tree
                .region(parent)
                .ok_or(StructureError::UnknownRegion(parent))?;
            if envelope.entry != Some(entry)
                || envelope.blocks != current.blocks
                || !matches!(
                    &envelope.kind,
                    RegionKind::Try
                        | RegionKind::Synchronized(_)
                        | RegionKind::Loop(_)
                        | RegionKind::Switch(_)
                )
            {
                break;
            }
            body = parent;
        }
        Ok(body)
    }

    pub(super) fn reduce(
        &self,
        owner: RegionId,
        children: &RegionChildren,
        region_cfg: &RegionCfg,
        reduced: &mut BTreeMap<RegionId, ReducedRegion>,
    ) -> Result<HandlerContraction, StructureError> {
        let parent = self
            .regions
            .tree()
            .region(owner)
            .ok_or(StructureError::UnknownRegion(owner))?
            .parent
            .unwrap_or(owner);
        let mut envelope = ExceptionEnvelope::default();
        let mut ports = BTreeMap::new();
        for child in &children.handlers {
            if children.releases.contains(child)
                || self.regions.is_synchronization_release_handler(*child)
            {
                reduced
                    .get(child)
                    .ok_or(StructureError::MissingReduction(*child))?;
                continue;
            }
            let handler = self
                .regions
                .tree()
                .region(*child)
                .ok_or(StructureError::UnknownRegion(*child))?
                .clone();
            match handler.kind {
                RegionKind::Catch(catch) => {
                    let body_region = self.body_region(owner, *child)?;
                    let (reduction, alternate) = self.reduction(reduced, body_region)?;
                    envelope.catches.push(SemanticCatch {
                        region: *child,
                        exception_types: catch.exception_types,
                        exception_value: catch.exception_value,
                        body: self.bind(owner, parent, *child, region_cfg, reduction)?,
                    });
                    self.expose(owner, parent, *child, region_cfg, alternate, &mut ports)?;
                }
                RegionKind::Finally => {
                    let body_region = self.body_region(owner, *child)?;
                    let (reduction, alternate) = self.reduction(reduced, body_region)?;
                    let body = self.bind(owner, parent, *child, region_cfg, reduction)?;
                    if let Some(existing) = &envelope.finally {
                        return Err(StructureError::MultipleFinallyRegions {
                            owner,
                            first: existing.region,
                            second: *child,
                        });
                    }
                    envelope.finally = Some(SemanticFinally {
                        region: *child,
                        body: Box::new(body),
                    });
                    self.expose(owner, parent, *child, region_cfg, alternate, &mut ports)?;
                }
                RegionKind::Cleanup(cleanup) => {
                    let source_finally = self.source_finally_body(owner, *child)?;
                    let body_region = source_finally.unwrap_or(self.body_region(owner, *child)?);
                    let (reduction, alternate) = self.reduction(reduced, body_region)?;
                    let exception_value = cleanup.exception_value;
                    let semantic_handler = source_finally.unwrap_or(*child);
                    let body = self.bind(owner, parent, semantic_handler, region_cfg, reduction)?;
                    let body = ExceptionForwarding::collapse(body, exception_value.as_ref())?;
                    if let Some(finally_region) = source_finally {
                        if let Some(existing) = &envelope.finally {
                            return Err(StructureError::MultipleFinallyRegions {
                                owner,
                                first: existing.region,
                                second: finally_region,
                            });
                        }
                        envelope.finally = Some(SemanticFinally {
                            region: finally_region,
                            body: Box::new(body),
                        });
                    } else {
                        envelope.catches.push(SemanticCatch {
                            region: *child,
                            exception_types: cleanup.exception_types,
                            exception_value,
                            body,
                        });
                    }
                    self.expose(
                        owner,
                        parent,
                        semantic_handler,
                        region_cfg,
                        alternate,
                        &mut ports,
                    )?;
                }
                _ => {
                    return Err(StructureError::InvalidHandlerRegion {
                        owner,
                        handler: *child,
                    });
                }
            }
        }
        Ok(HandlerContraction { envelope, ports })
    }

    fn source_finally_body(
        &self,
        owner: RegionId,
        cleanup: RegionId,
    ) -> Result<Option<RegionId>, StructureError> {
        if !self.regions.handlers_of(owner).contains(&cleanup) {
            return Ok(None);
        }
        let tree = self.regions.tree();
        let wrapper = tree
            .region(cleanup)
            .ok_or(StructureError::UnknownRegion(cleanup))?;
        let candidates = wrapper
            .children
            .iter()
            .copied()
            .filter(|child| {
                tree.region(*child).is_some_and(|region| {
                    matches!(region.kind, RegionKind::Finally)
                        && region.entry == wrapper.entry
                        && region.blocks.is_subset(&wrapper.blocks)
                })
            })
            .collect::<Vec<_>>();
        Ok(match candidates.as_slice() {
            [finally] => Some(*finally),
            _ => None,
        })
    }

    fn reduction(
        &self,
        reduced: &mut BTreeMap<RegionId, ReducedRegion>,
        region: RegionId,
    ) -> Result<(ReducedPort, BTreeMap<crate::ir::BlockId, ReducedPort>), StructureError> {
        let mut reduction = reduced
            .get(&region)
            .cloned()
            .ok_or(StructureError::MissingReduction(region))?;
        let entry = self
            .regions
            .tree()
            .region(region)
            .ok_or(StructureError::UnknownRegion(region))?
            .entry;
        let primary = match entry {
            Some(entry) => reduction
                .ports
                .remove(&entry)
                .ok_or(StructureError::RegionEntryMissing { region, entry }),
            None => reduction
                .detached
                .take()
                .ok_or(StructureError::MissingEntry(region)),
        }?;
        let mut alternate = BTreeMap::new();
        for (entry, port) in reduction.ports {
            if self.entry_belongs_to(region, entry)? {
                alternate.insert(entry, port);
            }
        }
        Ok((primary, alternate))
    }

    fn entry_belongs_to(
        &self,
        body: RegionId,
        entry: crate::ir::BlockId,
    ) -> Result<bool, StructureError> {
        let owner = self
            .regions
            .owner_of(entry)
            .ok_or(StructureError::RegionOwnerMissing {
                region: body,
                block: entry,
            })?;
        Ok(owner == body
            || self
                .regions
                .tree()
                .is_ancestor(body, owner)
                .map_err(|_| StructureError::UnknownRegion(owner))?)
    }

    fn expose(
        &self,
        owner: RegionId,
        parent: RegionId,
        handler: RegionId,
        region_cfg: &RegionCfg,
        alternate: BTreeMap<crate::ir::BlockId, ReducedPort>,
        ports: &mut BTreeMap<crate::ir::BlockId, HandlerPort>,
    ) -> Result<(), StructureError> {
        for (entry, port) in alternate {
            let body = self.bind(owner, parent, handler, region_cfg, port)?;
            if ports
                .insert(
                    entry,
                    HandlerPort {
                        handler,
                        port: ReducedPort::new(body),
                    },
                )
                .is_some()
            {
                return Err(StructureError::ConflictingEntryPort { owner, entry });
            }
        }
        Ok(())
    }

    fn bind(
        &self,
        scope: RegionId,
        parent: RegionId,
        handler_region: RegionId,
        region_cfg: &RegionCfg,
        handler: ReducedPort,
    ) -> Result<SemanticNode, StructureError> {
        let targets = handler
            .continuations
            .ports()
            .iter()
            .copied()
            .map(|port| {
                let target = region_cfg
                    .mapping
                    .get(&port.target)
                    .copied()
                    .unwrap_or(port.target);
                Ok((port.target, target))
            })
            .collect::<Result<BTreeMap<_, _>, StructureError>>()?;
        let control_targets = handler
            .continuations
            .controls()
            .iter()
            .copied()
            .map(|port| self.detached_control_target(scope, handler_region, port))
            .collect::<Result<Vec<_>, StructureError>>()?
            .into_iter()
            .flatten()
            .collect::<BTreeMap<_, _>>();
        ContinuationBinding::defer_handler(
            &handler.continuations,
            scope,
            parent,
            &targets,
            &control_targets,
        )?
        .apply(handler.body)
    }

    fn detached_control_target(
        &self,
        owner: RegionId,
        handler: RegionId,
        port: ControlPort,
    ) -> Result<Option<(ControlPort, crate::ir::BlockId)>, StructureError> {
        let tree = self.regions.tree();
        if tree
            .is_ancestor(handler, port.target)
            .map_err(|_| StructureError::UnknownRegion(port.target))?
            || tree
                .is_ancestor(port.target, owner)
                .map_err(|_| StructureError::UnknownRegion(port.target))?
        {
            return Ok(None);
        }
        let region = tree
            .region(port.target)
            .ok_or(StructureError::UnknownRegion(port.target))?;
        let target = match port.transfer {
            ControlTransfer::Continue => region.entry,
            ControlTransfer::Break => region.kind.follow(),
        }
        .ok_or(StructureError::MissingControlTarget(port.target))?;
        Ok(Some((port, target)))
    }
}
