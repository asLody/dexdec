use crate::ir::{
    InstructionId, SemanticFoldError, SemanticFolder, SemanticLeaveKind, SemanticLoopControl,
    SemanticNode,
};

use super::boundary::{Boundary, StatementBoundary};

/// Proves and removes structural replicas of a counted-loop update that run
/// immediately before a local continue. The update remains at the lexical loop
/// tail and becomes the Java `for` update clause.
pub(super) struct ContinuationUpdate {
    control: SemanticLoopControl,
    instruction: InstructionId,
    variable: u32,
    updates: usize,
    continues: usize,
    removed: usize,
    valid: bool,
}

impl ContinuationUpdate {
    pub(super) fn new(
        control: SemanticLoopControl,
        instruction: InstructionId,
        variable: u32,
    ) -> Self {
        Self {
            control,
            instruction,
            variable,
            updates: 0,
            continues: 0,
            removed: 0,
            valid: true,
        }
    }

    pub(super) fn prove(
        control: SemanticLoopControl,
        instruction: InstructionId,
        variable: u32,
        body: &SemanticNode,
    ) -> bool {
        let mut candidate = body.clone();
        let mut update = Self::new(control, instruction, variable);
        update.apply(&mut candidate) && update.is_valid()
    }

    pub(super) fn apply(&mut self, body: &mut SemanticNode) -> bool {
        let root = std::mem::replace(body, SemanticNode::Empty);
        match self.fold_node(root) {
            Ok(root) => {
                *body = root;
                true
            }
            Err(_) => false,
        }
    }

    pub(super) fn is_valid(&self) -> bool {
        self.valid
            && self.updates != 0
            && self.continues == self.removed
            && self.updates == self.removed.saturating_add(1)
    }

    fn is_local_continue(&self, node: &SemanticNode) -> bool {
        let SemanticNode::Leave(leave) = node else {
            return false;
        };
        match self.control {
            SemanticLoopControl::Region(region) => {
                matches!(leave.kind, SemanticLeaveKind::Continue) && leave.target == region
            }
            SemanticLoopControl::Label(label) => {
                matches!(leave.kind, SemanticLeaveKind::ContinueLabel(target) if target == label)
            }
        }
    }
}

impl SemanticFolder for ContinuationUpdate {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, mut node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        let is_local_continue = self.is_local_continue(&node);
        match &mut node {
            SemanticNode::BasicBlock(block) => {
                for statement in &block.statements {
                    if self.is_update(statement) {
                        self.updates += 1;
                    }
                }
            }
            SemanticNode::Leave(_) if is_local_continue => {
                self.continues += 1;
            }
            SemanticNode::Sequence(nodes) => {
                for index in 1..nodes.len() {
                    if !self.is_local_continue(&nodes[index]) {
                        continue;
                    }
                    let previous = &mut nodes[index - 1];
                    let matches_update = StatementBoundary::last(previous)
                        .is_some_and(|statement| self.is_update(statement));
                    if matches_update && StatementBoundary::take(previous, Boundary::Last).is_some()
                    {
                        self.removed += 1;
                    } else {
                        self.valid = false;
                    }
                }
            }
            _ => {}
        }
        Ok(match node {
            SemanticNode::Sequence(nodes) => SemanticNode::sequence(nodes),
            node => node,
        })
    }
}

impl ContinuationUpdate {
    fn is_update(&self, statement: &crate::ir::SemanticStatement) -> bool {
        if statement.id() != self.instruction {
            return false;
        }
        let result = statement.result().and_then(|result| result.code_var);
        let target = statement
            .instruction_ref()
            .and_then(|operation| operation.compound_target())
            .and_then(crate::ir::SemanticExpression::as_register)
            .and_then(|target| target.code_var);
        result.or(target) == Some(self.variable)
    }
}
