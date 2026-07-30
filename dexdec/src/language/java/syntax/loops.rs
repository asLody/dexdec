//! Proven Java loop syntax over typed Semantic IR.

mod boundary;
mod condition;
mod continuation;
mod entry;
mod facts;
mod forms;
mod guard;

use crate::ir::{
    analysis::TypeHierarchy, SemanticFolder, SemanticLoopControl, SemanticLoopKind, SemanticNode,
};

use self::{
    boundary::StatementBoundary,
    condition::{LoopConditionInlining, LoopRotation, LoopTestCycle},
    facts::LoopSyntaxProof,
    forms::LoopForm,
    guard::LoopGuardCondition,
};

pub(super) struct JavaLoopSyntax<'a> {
    hierarchy: &'a dyn TypeHierarchy,
    method_facts: crate::ir::SemanticExpressionFacts,
    changed: bool,
}

impl<'a> JavaLoopSyntax<'a> {
    pub(super) fn new(hierarchy: &'a dyn TypeHierarchy) -> Self {
        Self {
            hierarchy,
            method_facts: crate::ir::SemanticExpressionFacts::default(),
            changed: false,
        }
    }

    pub(super) fn apply(
        &mut self,
        root: &mut SemanticNode,
    ) -> Result<bool, crate::ir::SemanticFoldError> {
        let before = crate::ir::semantic::SemanticCompletion::analyze(root);
        self.method_facts = crate::ir::SemanticExpressionFacts::of_node(root);
        self.changed = false;
        let body = std::mem::replace(root, SemanticNode::Empty);
        *root = self.fold_node(body)?;
        let after = crate::ir::semantic::SemanticCompletion::analyze(root);
        if before != after {
            return Err(crate::ir::SemanticFoldError::CompletionChanged {
                transform: "java-loop-syntax",
            });
        }
        Ok(self.changed)
    }
}

impl SemanticFolder for JavaLoopSyntax<'_> {
    type Error = crate::ir::SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        let node = Self::reclassify(node)?;
        let node = LoopGuardCondition::apply(node);
        let node = LoopRotation::recover_post_test(node);
        let node = LoopConditionInlining::apply(node, &self.method_facts)?;
        let node = LoopTestCycle::apply(node);
        let node = LoopRotation::recover_pre_test(node);
        let node = match node {
            SemanticNode::Sequence(children) => SemanticNode::sequence(children),
            node => node,
        };
        let SemanticNode::Sequence(mut children) = node else {
            return Ok(node);
        };
        let mut index = 1;
        while index < children.len() {
            let mut start = index;
            while start != 0 {
                let candidate = start - 1;
                if StatementBoundary::linear(&children[candidate]).is_none() {
                    break;
                }
                start = candidate;
                if !StatementBoundary::is_reorderable(&children[candidate]) {
                    break;
                }
            }
            if start == index {
                index += 1;
                continue;
            }
            let previous = SemanticNode::sequence(children[start..index].iter().cloned());
            let Some(fact) =
                LoopSyntaxProof::new(self.hierarchy).prove(&previous, &children[index])
            else {
                index += 1;
                continue;
            };
            let local_facts =
                crate::ir::SemanticExpressionFacts::of_node(&SemanticNode::sequence([
                    previous.clone(),
                    children[index].clone(),
                ]));
            if fact.escapes(&self.method_facts, &local_facts) {
                index += 1;
                continue;
            }
            let Some((previous, loop_node)) =
                LoopForm::apply(fact, previous, children[index].clone())
            else {
                index += 1;
                continue;
            };
            children.splice(start..=index, [previous, loop_node]);
            self.changed = true;
            index = start + 2;
        }
        Ok(SemanticNode::sequence(children))
    }
}

impl JavaLoopSyntax<'_> {
    fn reclassify(node: SemanticNode) -> Result<SemanticNode, crate::ir::SemanticFoldError> {
        let SemanticNode::Loop {
            control: SemanticLoopControl::Region(region),
            header: Some(header),
            kind: SemanticLoopKind::Endless,
            body,
            ..
        } = node
        else {
            return Ok(node);
        };
        crate::ir::structure::LoopClassifier::new(region, header).classify(*body)
    }
}
