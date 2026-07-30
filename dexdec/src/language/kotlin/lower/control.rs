use std::collections::BTreeSet;

use crate::ir::{
    RegionId, SemanticLabel, SemanticLabelKind, SemanticLeaveKind, SemanticLoopControl,
    SemanticNode, SemanticVisitor,
};
use crate::language::kotlin::ast::KotlinIdentifier;

use super::KotlinStructuralError;

#[derive(Default)]
pub(super) struct ControlLayout {
    regions: BTreeSet<RegionId>,
    labels: BTreeSet<SemanticLabel>,
}

impl ControlLayout {
    pub(super) fn analyze(root: &SemanticNode) -> Result<Self, KotlinStructuralError> {
        LabelAnalysis::analyze(root)
    }

    pub(super) fn label(&self, region: Option<RegionId>) -> Option<KotlinIdentifier> {
        region
            .filter(|region| self.regions.contains(region))
            .map(Self::region_identifier)
    }

    pub(super) fn loop_label(&self, control: SemanticLoopControl) -> Option<KotlinIdentifier> {
        match control {
            SemanticLoopControl::Region(region) => self
                .regions
                .contains(&region)
                .then(|| Self::region_identifier(region)),
            SemanticLoopControl::Label(label) => self
                .labels
                .contains(&label)
                .then(|| Self::label_identifier(label)),
        }
    }

    pub(super) fn leave_label(&self, region: RegionId) -> Option<KotlinIdentifier> {
        self.regions
            .contains(&region)
            .then(|| Self::region_identifier(region))
    }

    pub(super) fn label_for(&self, label: SemanticLabel) -> Option<KotlinIdentifier> {
        self.labels
            .contains(&label)
            .then(|| Self::label_identifier(label))
    }

    pub(super) fn label_identifier(label: SemanticLabel) -> KotlinIdentifier {
        let category = match label.kind {
            SemanticLabelKind::Block => "flow",
            SemanticLabelKind::Loop => "loop",
        };
        KotlinIdentifier::from_dex(&format!(
            "{}_{}_{}",
            category,
            label.region.raw(),
            label.block.raw()
        ))
    }

    fn region_identifier(region: RegionId) -> KotlinIdentifier {
        KotlinIdentifier::from_dex(&format!("region_{}", region.raw()))
    }
}

#[derive(Default)]
struct LabelAnalysis {
    active: Vec<LexicalScope>,
    regions: BTreeSet<RegionId>,
    labels: BTreeSet<SemanticLabel>,
    invalid: Option<KotlinStructuralError>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LexicalScope {
    identity: ScopeIdentity,
    accepts_break: bool,
    accepts_continue: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScopeIdentity {
    Region(RegionId),
    LoopLabel(SemanticLabel),
    BlockLabel(SemanticLabel),
}

impl LabelAnalysis {
    fn analyze(root: &SemanticNode) -> Result<ControlLayout, KotlinStructuralError> {
        let mut analysis = Self::default();
        analysis.visit_node(root);
        match analysis.invalid {
            Some(error) => Err(error),
            None if analysis.active.is_empty() => Ok(ControlLayout {
                regions: analysis.regions,
                labels: analysis.labels,
            }),
            None => Err(KotlinStructuralError::MissingControlScope),
        }
    }

    fn scope(node: &SemanticNode) -> Option<LexicalScope> {
        match node {
            SemanticNode::Loop { control, .. }
            | SemanticNode::For { control, .. }
            | SemanticNode::ForEach { control, .. } => Some(LexicalScope {
                identity: match control {
                    SemanticLoopControl::Region(region) => ScopeIdentity::Region(*region),
                    SemanticLoopControl::Label(label) => ScopeIdentity::LoopLabel(*label),
                },
                accepts_break: true,
                accepts_continue: true,
            }),
            SemanticNode::Switch {
                region: Some(region),
                ..
            } => Some(LexicalScope {
                identity: ScopeIdentity::Region(*region),
                accepts_break: true,
                accepts_continue: false,
            }),
            SemanticNode::Label { label, .. } => Some(LexicalScope {
                identity: ScopeIdentity::BlockLabel(*label),
                accepts_break: false,
                accepts_continue: false,
            }),
            _ => None,
        }
    }

    fn nearest(&self, direction: ControlDirection) -> Option<usize> {
        self.active.iter().rposition(|scope| match direction {
            ControlDirection::Break => scope.accepts_break,
            ControlDirection::Continue => scope.accepts_continue,
        })
    }

    fn record_region(&mut self, target: RegionId, direction: ControlDirection) {
        let identity = ScopeIdentity::Region(target);
        let Some(index) = self
            .active
            .iter()
            .rposition(|scope| scope.identity == identity)
        else {
            self.invalid
                .get_or_insert(KotlinStructuralError::UnknownControlTarget(target));
            return;
        };
        if self.nearest(direction) != Some(index) {
            self.regions.insert(target);
        }
    }

    fn record_label(&mut self, target: SemanticLabel, direction: ControlDirection) {
        let index = self.active.iter().rposition(|scope| {
            matches!(
                scope.identity,
                ScopeIdentity::LoopLabel(label) | ScopeIdentity::BlockLabel(label)
                    if label == target
            )
        });
        let Some(index) = index else {
            self.invalid
                .get_or_insert(KotlinStructuralError::MissingControlScope);
            return;
        };
        let scope = self.active[index];
        let can_be_unlabeled = match direction {
            ControlDirection::Break => scope.accepts_break,
            ControlDirection::Continue => scope.accepts_continue,
        };
        if !can_be_unlabeled || self.nearest(direction) != Some(index) {
            self.labels.insert(target);
        }
    }

    fn record_leave(&mut self, node: &SemanticNode) {
        let SemanticNode::Leave(leave) = node else {
            return;
        };
        match &leave.kind {
            SemanticLeaveKind::Break => self.record_region(leave.target, ControlDirection::Break),
            SemanticLeaveKind::Continue => {
                self.record_region(leave.target, ControlDirection::Continue)
            }
            SemanticLeaveKind::BreakLabel(label) => {
                self.record_label(*label, ControlDirection::Break)
            }
            SemanticLeaveKind::ContinueLabel(label) => {
                self.record_label(*label, ControlDirection::Continue)
            }
            SemanticLeaveKind::FallThrough(target) | SemanticLeaveKind::Jump(target) => {
                self.invalid
                    .get_or_insert(KotlinStructuralError::UnboundContinuation {
                        scope: leave.target,
                        target: *target,
                    });
            }
            SemanticLeaveKind::Return(_) | SemanticLeaveKind::Throw(_) => {}
        }
    }
}

impl SemanticVisitor for LabelAnalysis {
    fn enter_node(&mut self, node: &SemanticNode) {
        self.record_leave(node);
        if let Some(scope) = Self::scope(node) {
            self.active.push(scope);
        }
    }

    fn exit_node(&mut self, node: &SemanticNode) {
        let Some(scope) = Self::scope(node) else {
            return;
        };
        if self.active.pop() != Some(scope) {
            self.invalid
                .get_or_insert(KotlinStructuralError::MissingControlScope);
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum ControlDirection {
    Break,
    Continue,
}
