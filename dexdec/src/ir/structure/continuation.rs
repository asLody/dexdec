//! Algebraic binding of cross-region lexical continuations.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    BlockId, RegionId, SemanticFoldError, SemanticFolder, SemanticLabel, SemanticLeaveKind,
    SemanticLoopKind, SemanticNode, SemanticVisitor,
};

use super::StructureError;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct ContinuationPort {
    pub(super) scope: RegionId,
    pub(super) target: BlockId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum ControlTransfer {
    Break,
    Continue,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct ControlPort {
    pub(super) target: RegionId,
    pub(super) transfer: ControlTransfer,
}

#[derive(Debug, Clone, Default)]
pub(super) struct ContinuationFacts {
    ports: BTreeSet<ContinuationPort>,
    controls: BTreeSet<ControlPort>,
    control_exits: BTreeSet<RegionId>,
    closed_controls: BTreeSet<RegionId>,
}

impl ContinuationFacts {
    pub(super) fn analyze(root: &SemanticNode) -> Self {
        let mut facts = Self::default();
        facts.visit_node(root);
        facts
            .controls
            .retain(|port| !facts.closed_controls.contains(&port.target));
        facts
    }

    pub(super) fn ports(&self) -> &BTreeSet<ContinuationPort> {
        &self.ports
    }

    pub(super) fn in_scope(&self, scope: RegionId) -> impl Iterator<Item = ContinuationPort> + '_ {
        self.ports
            .iter()
            .copied()
            .filter(move |port| port.scope == scope)
    }

    pub(super) fn controls(&self) -> &BTreeSet<ControlPort> {
        &self.controls
    }

    pub(super) fn exits_control(&self, region: RegionId) -> bool {
        self.control_exits.contains(&region)
    }
}

impl SemanticVisitor for ContinuationFacts {
    fn enter_node(&mut self, node: &SemanticNode) {
        if let SemanticNode::Loop {
            control: crate::ir::SemanticLoopControl::Region(region),
            kind,
            ..
        } = node
        {
            self.closed_controls.insert(*region);
            if !matches!(kind, SemanticLoopKind::Endless) {
                self.control_exits.insert(*region);
            }
        }
        let SemanticNode::Leave(leave) = node else {
            return;
        };
        match &leave.kind {
            SemanticLeaveKind::FallThrough(target) | SemanticLeaveKind::Jump(target) => {
                self.ports.insert(ContinuationPort {
                    scope: leave.target,
                    target: *target,
                });
            }
            SemanticLeaveKind::Break => {
                self.controls.insert(ControlPort {
                    target: leave.target,
                    transfer: ControlTransfer::Break,
                });
                self.control_exits.insert(leave.target);
            }
            SemanticLeaveKind::Continue => {
                self.controls.insert(ControlPort {
                    target: leave.target,
                    transfer: ControlTransfer::Continue,
                });
            }
            _ => {}
        }
    }
}

#[derive(Debug, Clone)]
pub(super) enum BoundFlow {
    Terminal,
    Lexical(BlockId),
    Leave(crate::ir::ResolvedRegionExit),
    Open {
        targets: BTreeSet<BlockId>,
        normal_target: Option<BlockId>,
        boundary: Option<crate::ir::ResolvedRegionExit>,
    },
}

impl BoundFlow {
    pub(super) fn close_normal_path(self) -> Self {
        match self {
            Self::Lexical(_) | Self::Leave(_) => Self::Terminal,
            Self::Open {
                mut targets,
                normal_target,
                ..
            } => {
                if let Some(normal_target) = normal_target {
                    targets.remove(&normal_target);
                }
                if targets.is_empty() {
                    Self::Terminal
                } else {
                    Self::Open {
                        targets,
                        normal_target: None,
                        boundary: None,
                    }
                }
            }
            Self::Terminal => Self::Terminal,
        }
    }
}

pub(super) struct ContinuationBinding {
    actions: BTreeMap<ContinuationPort, BindingAction>,
    control_actions: BTreeMap<ControlPort, BindingAction>,
    flow: BoundFlow,
    lexical_scope: Option<SemanticLabel>,
}

impl ContinuationBinding {
    pub(super) fn analyze(
        facts: &ContinuationFacts,
        scope: RegionId,
        targets: &BTreeMap<BlockId, BlockId>,
        normal_target: Option<BlockId>,
        lexical_control: Option<RegionId>,
        has_boundary_exit: bool,
    ) -> Result<Self, StructureError> {
        let ports = facts.in_scope(scope).collect::<Vec<_>>();
        if ports.is_empty() && normal_target.is_none() && !has_boundary_exit {
            return Ok(Self {
                actions: BTreeMap::new(),
                control_actions: BTreeMap::new(),
                flow: BoundFlow::Terminal,
                lexical_scope: None,
            });
        }

        let mut mapped_targets = BTreeSet::new();
        for port in &ports {
            mapped_targets.insert(targets.get(&port.target).copied().ok_or(
                StructureError::ContinuationTargetMissing {
                    scope,
                    target: port.target,
                },
            )?);
        }
        mapped_targets.extend(normal_target);
        let Some(target_hint) = ports.first().map(|port| port.target).or(normal_target) else {
            return Ok(Self {
                actions: BTreeMap::new(),
                control_actions: BTreeMap::new(),
                flow: BoundFlow::Terminal,
                lexical_scope: None,
            });
        };
        let has_multiple_exits = mapped_targets.len() != 1 || has_boundary_exit;
        let lexical_target = if has_multiple_exits {
            None
        } else {
            Some(mapped_targets.iter().next().copied().ok_or(
                StructureError::ContinuationTargetMissing {
                    scope,
                    target: target_hint,
                },
            )?)
        };
        let lexical_scope = lexical_target
            .filter(|_| !ports.is_empty() && lexical_control.is_none())
            .map(|target| SemanticLabel::block(scope, target));
        let flow = if let Some(target) = lexical_target {
            BoundFlow::Lexical(target)
        } else {
            BoundFlow::Open {
                targets: mapped_targets.clone(),
                normal_target,
                boundary: None,
            }
        };
        let actions = ports
            .into_iter()
            .map(|port| {
                let mapped_target = targets.get(&port.target).copied().ok_or(
                    StructureError::ContinuationTargetMissing {
                        scope,
                        target: port.target,
                    },
                )?;
                let action = if has_multiple_exits {
                    BindingAction::Jump(mapped_target)
                } else if let Some(control) = lexical_control {
                    BindingAction::Break(control)
                } else {
                    BindingAction::BreakLabel(SemanticLabel::block(scope, mapped_target))
                };
                Ok((port, action))
            })
            .collect::<Result<BTreeMap<_, _>, StructureError>>()?;
        Ok(Self {
            actions,
            control_actions: BTreeMap::new(),
            flow,
            lexical_scope,
        })
    }

    pub(super) fn flow(&self) -> BoundFlow {
        self.flow.clone()
    }

    /// Move handler continuations to the enclosing lexical region. This keeps
    /// exception handlers as ordinary open semantic fragments; the parent
    /// graph subsequently binds them using the same continuation algebra as
    /// every other child region.
    pub(super) fn defer_handler(
        facts: &ContinuationFacts,
        scope: RegionId,
        parent: RegionId,
        targets: &BTreeMap<BlockId, BlockId>,
        control_targets: &BTreeMap<ControlPort, BlockId>,
    ) -> Result<Self, StructureError> {
        let ports = facts.ports().iter().copied().collect::<Vec<_>>();
        let actions = ports
            .into_iter()
            .map(|port| {
                let target = targets.get(&port.target).copied().ok_or(
                    StructureError::ContinuationTargetMissing {
                        scope,
                        target: port.target,
                    },
                )?;
                Ok((port, BindingAction::Defer { target, parent }))
            })
            .collect::<Result<BTreeMap<_, _>, StructureError>>()?;
        let control_actions = control_targets
            .iter()
            .map(|(port, target)| {
                (
                    *port,
                    BindingAction::Defer {
                        target: *target,
                        parent,
                    },
                )
            })
            .collect();
        Ok(Self {
            actions,
            control_actions,
            flow: BoundFlow::Terminal,
            lexical_scope: None,
        })
    }

    pub(super) fn defer_ports(
        ports: impl IntoIterator<Item = ContinuationPort>,
        parent: RegionId,
    ) -> Self {
        let actions = ports
            .into_iter()
            .map(|port| {
                (
                    port,
                    BindingAction::Defer {
                        target: port.target,
                        parent,
                    },
                )
            })
            .collect();
        Self {
            actions,
            control_actions: BTreeMap::new(),
            flow: BoundFlow::Terminal,
            lexical_scope: None,
        }
    }

    pub(super) fn apply(mut self, root: SemanticNode) -> Result<SemanticNode, StructureError> {
        let lexical_scope = self.lexical_scope;
        let body = self.fold_node(root).map_err(StructureError::from)?;
        Ok(match lexical_scope {
            Some(label) => SemanticNode::Label {
                label,
                body: Box::new(body),
            },
            None => body,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BindingAction {
    Break(RegionId),
    BreakLabel(SemanticLabel),
    Jump(BlockId),
    Defer { target: BlockId, parent: RegionId },
}

impl SemanticFolder for ContinuationBinding {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        Ok(match node {
            SemanticNode::Leave(mut leave) => {
                let control = match &leave.kind {
                    SemanticLeaveKind::Break => Some(ControlPort {
                        target: leave.target,
                        transfer: ControlTransfer::Break,
                    }),
                    SemanticLeaveKind::Continue => Some(ControlPort {
                        target: leave.target,
                        transfer: ControlTransfer::Continue,
                    }),
                    _ => None,
                };
                if let Some(BindingAction::Defer { target, parent }) =
                    control.and_then(|port| self.control_actions.get(&port).copied())
                {
                    leave.kind = SemanticLeaveKind::FallThrough(target);
                    leave.target = parent;
                    return Ok(SemanticNode::Leave(leave));
                }
                let target = match &leave.kind {
                    SemanticLeaveKind::FallThrough(target) | SemanticLeaveKind::Jump(target) => {
                        *target
                    }
                    _ => return Ok(SemanticNode::Leave(leave)),
                };
                let port = ContinuationPort {
                    scope: leave.target,
                    target,
                };
                match self.actions.get(&port).copied() {
                    Some(BindingAction::Break(control)) => {
                        leave.kind = SemanticLeaveKind::Break;
                        leave.target = control;
                        SemanticNode::Leave(leave)
                    }
                    Some(BindingAction::BreakLabel(label)) => {
                        leave.kind = SemanticLeaveKind::BreakLabel(label);
                        SemanticNode::Leave(leave)
                    }
                    Some(BindingAction::Jump(target)) => {
                        leave.kind = SemanticLeaveKind::Jump(target);
                        SemanticNode::Leave(leave)
                    }
                    Some(BindingAction::Defer { target, parent }) => {
                        leave.kind = SemanticLeaveKind::FallThrough(target);
                        leave.target = parent;
                        SemanticNode::Leave(leave)
                    }
                    None => {
                        leave.kind = SemanticLeaveKind::FallThrough(target);
                        SemanticNode::Leave(leave)
                    }
                }
            }
            SemanticNode::Sequence(nodes) => SemanticNode::sequence(nodes),
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => SemanticNode::branch(
                condition.into_inner(),
                *then_node,
                else_node.map(|node| *node),
            ),
            node => node,
        })
    }
}
