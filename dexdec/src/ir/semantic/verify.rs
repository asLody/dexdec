//! Structural invariants for fully reduced Semantic IR.

use std::fmt;

use crate::ir::{
    BlockId, RegionGraph, RegionId, RegionKind, SemanticLabel, SemanticLabelKind,
    SemanticLeaveKind, SemanticNode, SemanticVisitor,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemanticInvariantError {
    UnknownRegion(RegionId),
    WrongControlRegion(RegionId),
    WrongExceptionRegion(RegionId),
    WrongHandlerRegion { owner: RegionId, handler: RegionId },
    InactiveControl(RegionId),
    InvalidContinueTarget(RegionId),
    InactiveLabel(SemanticLabel),
    DuplicateLabel(SemanticLabel),
    WrongLabelKind(SemanticLabel),
    InvalidLabelContinue(SemanticLabel),
    InvalidPredicateIdentity(u32),
    UnboundContinuation { scope: RegionId, target: BlockId },
    UnknownCleanup(RegionId),
    InactiveCleanup(RegionId),
    ScopeStackMismatch,
}

impl fmt::Display for SemanticInvariantError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownRegion(region) => {
                write!(formatter, "semantic IR references unknown {region}")
            }
            Self::WrongControlRegion(region) => {
                write!(
                    formatter,
                    "semantic control node uses incompatible {region}"
                )
            }
            Self::WrongExceptionRegion(region) => {
                write!(
                    formatter,
                    "semantic exception node uses incompatible {region}"
                )
            }
            Self::WrongHandlerRegion { owner, handler } => {
                write!(
                    formatter,
                    "semantic handler {handler} is not owned by {owner}"
                )
            }
            Self::InactiveControl(region) => {
                write!(
                    formatter,
                    "semantic leave targets inactive control {region}"
                )
            }
            Self::InvalidContinueTarget(region) => {
                write!(
                    formatter,
                    "semantic continue targets non-loop control {region}"
                )
            }
            Self::InactiveLabel(label) => write!(
                formatter,
                "semantic transfer targets inactive graph label {}:{}",
                label.region, label.block
            ),
            Self::DuplicateLabel(label) => write!(
                formatter,
                "semantic graph label {}:{} has overlapping lexical scopes",
                label.region, label.block
            ),
            Self::WrongLabelKind(label) => write!(
                formatter,
                "semantic graph label {}:{} has the wrong lexical kind",
                label.region, label.block
            ),
            Self::InvalidLabelContinue(label) => write!(
                formatter,
                "semantic continue targets non-loop graph label {}:{}",
                label.region, label.block
            ),
            Self::InvalidPredicateIdentity(offset) => {
                write!(
                    formatter,
                    "semantic predicate at {offset:#x} has no stable identity"
                )
            }
            Self::UnboundContinuation { scope, target } => {
                write!(
                    formatter,
                    "unbound continuation {scope} -> {target} remains in Semantic IR"
                )
            }
            Self::UnknownCleanup(region) => {
                write!(
                    formatter,
                    "semantic leave references unknown cleanup {region}"
                )
            }
            Self::InactiveCleanup(region) => {
                write!(
                    formatter,
                    "semantic leave cleanup {region} has no active Kotlin envelope"
                )
            }
            Self::ScopeStackMismatch => {
                formatter.write_str("semantic control scope stack is malformed")
            }
        }
    }
}

impl std::error::Error for SemanticInvariantError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ControlScope {
    region: RegionId,
    accepts_continue: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LabelScope {
    label: SemanticLabel,
    accepts_continue: bool,
}

pub(super) struct SemanticVerifier<'a> {
    regions: &'a RegionGraph,
    controls: Vec<ControlScope>,
    labels: Vec<LabelScope>,
    cleanups: Vec<RegionId>,
    error: Option<SemanticInvariantError>,
}

impl<'a> SemanticVerifier<'a> {
    pub(super) fn verify(
        root: &SemanticNode,
        regions: &'a RegionGraph,
    ) -> Result<(), SemanticInvariantError> {
        let mut verifier = Self {
            regions,
            controls: Vec::new(),
            labels: Vec::new(),
            cleanups: Vec::new(),
            error: None,
        };
        verifier.visit_node(root);
        if let Some(error) = verifier.error {
            return Err(error);
        }
        if !verifier.controls.is_empty()
            || !verifier.labels.is_empty()
            || !verifier.cleanups.is_empty()
        {
            return Err(SemanticInvariantError::ScopeStackMismatch);
        }
        Ok(())
    }

    fn fail(&mut self, error: SemanticInvariantError) {
        if self.error.is_none() {
            self.error = Some(error);
        }
    }

    fn control_scope(&self, node: &SemanticNode) -> Option<ControlScope> {
        match node {
            SemanticNode::Loop {
                control: crate::ir::SemanticLoopControl::Region(region),
                ..
            }
            | SemanticNode::For {
                control: crate::ir::SemanticLoopControl::Region(region),
                ..
            }
            | SemanticNode::ForEach {
                control: crate::ir::SemanticLoopControl::Region(region),
                ..
            } => Some(ControlScope {
                region: *region,
                accepts_continue: true,
            }),
            SemanticNode::Switch { region, .. } => region.map(|region| ControlScope {
                region,
                accepts_continue: false,
            }),
            _ => None,
        }
    }

    fn label_scope(node: &SemanticNode) -> Option<LabelScope> {
        match node {
            SemanticNode::Loop {
                control: crate::ir::SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::For {
                control: crate::ir::SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::ForEach {
                control: crate::ir::SemanticLoopControl::Label(label),
                ..
            } => Some(LabelScope {
                label: *label,
                accepts_continue: true,
            }),
            SemanticNode::Label { label, .. } => Some(LabelScope {
                label: *label,
                accepts_continue: false,
            }),
            _ => None,
        }
    }

    fn verify_control_region(&mut self, scope: ControlScope) {
        let owner = self.regions.tree().region(scope.region);
        let valid = owner.is_some_and(|region| match &region.kind {
            RegionKind::Loop(_) => scope.accepts_continue,
            RegionKind::Switch(_) => !scope.accepts_continue,
            _ => false,
        });
        if !valid {
            self.fail(if owner.is_some() {
                SemanticInvariantError::WrongControlRegion(scope.region)
            } else {
                SemanticInvariantError::UnknownRegion(scope.region)
            });
        }
    }

    fn verify_handler(&mut self, owner: RegionId, handler: RegionId, finally: bool) {
        let valid = self.regions.tree().region(handler).is_some_and(|region| {
            let direct =
                region.parent == Some(owner) || self.regions.handlers_of(owner).contains(&handler);
            let nested_cleanup = finally
                && region.parent.is_some_and(|parent| {
                    self.regions
                        .tree()
                        .region(parent)
                        .is_some_and(|parent_region| {
                            matches!(parent_region.kind, RegionKind::Cleanup(_))
                                && self.regions.handlers_of(owner).contains(&parent)
                        })
                });
            (direct || nested_cleanup)
                && if finally {
                    matches!(&region.kind, RegionKind::Finally)
                } else {
                    matches!(&region.kind, RegionKind::Catch(_) | RegionKind::Cleanup(_))
                }
        });
        if !valid {
            self.fail(SemanticInvariantError::WrongHandlerRegion { owner, handler });
        }
    }

    fn verify_protection(
        &mut self,
        owner: RegionId,
        catches: &[crate::ir::SemanticCatch],
        finally: Option<&crate::ir::SemanticFinally>,
    ) {
        let owner_valid = self.regions.tree().region(owner).is_some_and(|region| {
            matches!(&region.kind, RegionKind::Try | RegionKind::Synchronized(_))
        });
        if !owner_valid {
            self.fail(SemanticInvariantError::WrongExceptionRegion(owner));
        }
        for catch in catches {
            self.verify_handler(owner, catch.region, false);
        }
        if let Some(finally) = finally {
            self.verify_handler(owner, finally.region, true);
        }
    }

    fn cleanup_scope(node: &SemanticNode) -> Option<RegionId> {
        match node {
            SemanticNode::Try {
                finally: Some(finally),
                ..
            } => Some(finally.region),
            SemanticNode::Synchronized { region, .. } => Some(*region),
            _ => None,
        }
    }

    fn verify_leave(&mut self, leave: &crate::ir::SemanticLeave) {
        let known_path = [leave.source, leave.destination, leave.target]
            .into_iter()
            .all(|region| self.regions.tree().region(region).is_some());
        if !known_path {
            if let Some(region) = [leave.source, leave.destination, leave.target]
                .into_iter()
                .find(|region| self.regions.tree().region(*region).is_none())
            {
                self.fail(SemanticInvariantError::UnknownRegion(region));
            }
        }
        for cleanup in &leave.cleanup {
            if self.regions.tree().region(*cleanup).is_none() {
                self.fail(SemanticInvariantError::UnknownCleanup(*cleanup));
            } else if !self.cleanups.contains(cleanup) {
                self.fail(SemanticInvariantError::InactiveCleanup(*cleanup));
            }
        }
        let represented = self
            .cleanups
            .iter()
            .rev()
            .filter(|cleanup| leave.cleanup.contains(cleanup))
            .copied()
            .collect::<Vec<_>>();
        if represented != leave.cleanup {
            if let Some(cleanup) = leave
                .cleanup
                .iter()
                .find(|cleanup| !self.cleanups.contains(cleanup))
            {
                self.fail(SemanticInvariantError::InactiveCleanup(*cleanup));
            }
        }
        match &leave.kind {
            SemanticLeaveKind::FallThrough(target) | SemanticLeaveKind::Jump(target) => {
                self.fail(SemanticInvariantError::UnboundContinuation {
                    scope: leave.target,
                    target: *target,
                });
            }
            SemanticLeaveKind::BreakLabel(label) => {
                if !self.labels.iter().any(|scope| scope.label == *label) {
                    self.fail(SemanticInvariantError::InactiveLabel(*label));
                }
            }
            SemanticLeaveKind::ContinueLabel(label) => {
                match self.labels.iter().rev().find(|scope| scope.label == *label) {
                    Some(scope) if scope.accepts_continue => {}
                    Some(_) => self.fail(SemanticInvariantError::InvalidLabelContinue(*label)),
                    None => self.fail(SemanticInvariantError::InactiveLabel(*label)),
                }
            }
            SemanticLeaveKind::Break => {
                if !self
                    .controls
                    .iter()
                    .any(|scope| scope.region == leave.target)
                {
                    self.fail(SemanticInvariantError::InactiveControl(leave.target));
                }
            }
            SemanticLeaveKind::Continue => match self
                .controls
                .iter()
                .rev()
                .find(|scope| scope.region == leave.target)
            {
                Some(scope) if scope.accepts_continue => {}
                Some(_) => self.fail(SemanticInvariantError::InvalidContinueTarget(leave.target)),
                None => self.fail(SemanticInvariantError::InactiveControl(leave.target)),
            },
            SemanticLeaveKind::Return(_) | SemanticLeaveKind::Throw(_) => {}
        }
    }
}

impl SemanticVisitor for SemanticVerifier<'_> {
    fn visit_predicate(&mut self, predicate: &crate::ir::SemanticPredicate) {
        let mut pending = vec![predicate];
        while let Some(predicate) = pending.pop() {
            match predicate {
                crate::ir::SemanticPredicate::Test(instruction) => {
                    if !instruction.id.is_valid() {
                        self.fail(SemanticInvariantError::InvalidPredicateIdentity(
                            instruction.offset,
                        ));
                    }
                }
                crate::ir::SemanticPredicate::Not(inner) => pending.push(inner),
                crate::ir::SemanticPredicate::And(terms)
                | crate::ir::SemanticPredicate::Or(terms) => pending.extend(terms),
                crate::ir::SemanticPredicate::True | crate::ir::SemanticPredicate::False => {}
            }
        }
    }

    fn enter_node(&mut self, node: &SemanticNode) {
        match node {
            SemanticNode::Try {
                region,
                catches,
                finally,
                ..
            } => self.verify_protection(*region, catches, finally.as_ref()),
            SemanticNode::Synchronized { region, .. } => {
                let valid = self
                    .regions
                    .tree()
                    .region(*region)
                    .is_some_and(|owner| matches!(&owner.kind, RegionKind::Synchronized(_)));
                if !valid {
                    self.fail(SemanticInvariantError::WrongExceptionRegion(*region));
                }
            }
            _ => {}
        }
        if let Some(cleanup) = Self::cleanup_scope(node) {
            self.cleanups.push(cleanup);
        }
        if let Some(scope) = Self::label_scope(node) {
            let expected = if scope.accepts_continue {
                SemanticLabelKind::Loop
            } else {
                SemanticLabelKind::Block
            };
            if scope.label.kind != expected {
                self.fail(SemanticInvariantError::WrongLabelKind(scope.label));
            }
            if self.labels.iter().any(|active| active.label == scope.label) {
                self.fail(SemanticInvariantError::DuplicateLabel(scope.label));
            }
            self.labels.push(scope);
        }
        if let Some(scope) = self.control_scope(node) {
            self.verify_control_region(scope);
            self.controls.push(scope);
        }
        if let SemanticNode::Leave(leave) = node {
            self.verify_leave(leave);
        }
    }

    fn exit_node(&mut self, node: &SemanticNode) {
        if let Some(scope) = self.control_scope(node) {
            if self.controls.pop() != Some(scope) {
                self.fail(SemanticInvariantError::ScopeStackMismatch);
            }
        }
        if let Some(scope) = Self::label_scope(node) {
            if self.labels.pop() != Some(scope) {
                self.fail(SemanticInvariantError::ScopeStackMismatch);
            }
        }
        if let Some(cleanup) = Self::cleanup_scope(node) {
            if self.cleanups.pop() != Some(cleanup) {
                self.fail(SemanticInvariantError::ScopeStackMismatch);
            }
        }
    }
}
