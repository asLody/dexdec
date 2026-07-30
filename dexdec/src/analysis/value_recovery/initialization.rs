//! Definite-value recovery at source-variable merge points.
//!
//! Phi lowering must sometimes materialize an edge copy even when the value is
//! already implied by the only normally completing path through the opposite
//! edge. This module proves that implication over Semantic IR and moves the
//! synthetic initialization to the common dominator.

use std::collections::BTreeMap;

use crate::ir::{
    IfOp, InsnType, SemanticExpression, SemanticExpressionFacts, SemanticFoldError, SemanticFolder,
    SemanticNode, SemanticPredicate, SemanticStatement, SemanticStatementKind,
};

use super::ValueRecoveryError;

pub(super) struct SourceInitializationRecovery {
    changed: bool,
}

impl SourceInitializationRecovery {
    pub(super) fn apply(root: &mut SemanticNode) -> Result<bool, ValueRecoveryError> {
        let original = std::mem::replace(root, SemanticNode::Empty);
        let before = crate::ir::semantic::SemanticCompletion::analyze(&original);
        let mut recovery = Self { changed: false };
        let rewritten = recovery.fold_node(original)?;
        let after = crate::ir::semantic::SemanticCompletion::analyze(&rewritten);
        if !before.same_control_outcomes(&after) {
            return Err(SemanticFoldError::CompletionChanged {
                transform: "source-initialization",
            }
            .into());
        }
        *root = rewritten;
        Ok(recovery.changed)
    }

    fn recover_branch(&mut self, node: SemanticNode) -> SemanticNode {
        let SemanticNode::If {
            condition,
            then_node,
            else_node,
        } = node
        else {
            return node;
        };

        let then_initializer = LeadingInitializer::from_node(&then_node);
        let else_initializer = else_node.as_deref().and_then(LeadingInitializer::from_node);
        let direction = match (then_initializer, else_initializer) {
            (Some(initializer), None)
                if Self::can_hoist(&condition, else_node.as_deref(), initializer.value) =>
            {
                InitializationEdge::Then
            }
            (None, Some(initializer))
                if Self::can_hoist(&condition, Some(&then_node), initializer.value) =>
            {
                InitializationEdge::Else
            }
            _ => {
                return SemanticNode::If {
                    condition,
                    then_node,
                    else_node,
                };
            }
        };

        self.changed = true;
        match direction {
            InitializationEdge::Then => {
                let (initializer, remainder) = LeadingInitializer::split(*then_node)
                    .expect("checked then initializer is no longer present");
                let branch = SemanticNode::If {
                    condition,
                    then_node: Box::new(remainder),
                    else_node,
                };
                SemanticNode::sequence([initializer, branch])
            }
            InitializationEdge::Else => {
                let branch_node =
                    else_node.expect("checked initialization edge is missing its node");
                let (initializer, remainder) = LeadingInitializer::split(*branch_node)
                    .expect("checked else initializer is no longer present");
                let branch = SemanticNode::If {
                    condition,
                    then_node,
                    else_node: Some(Box::new(remainder)),
                };
                SemanticNode::sequence([initializer, branch])
            }
        }
    }

    fn can_hoist(
        condition: &crate::ir::SemanticOperand<SemanticPredicate>,
        opposite: Option<&SemanticNode>,
        initializer: EdgeInitializer,
    ) -> bool {
        let empty = SemanticNode::Empty;
        let opposite = opposite.unwrap_or(&empty);
        !SemanticExpressionFacts::of_predicate(condition).uses(initializer.variable)
            && (DefiniteAssignment::holds(opposite, initializer.variable)
                || DefiniteValues::normal_exit(opposite).is_some_and(|facts| {
                    facts.get(initializer.variable) == Some(initializer.value)
                }))
    }
}

impl SemanticFolder for SourceInitializationRecovery {
    type Error = ValueRecoveryError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        Ok(self.recover_branch(node))
    }
}

#[derive(Clone, Copy)]
struct EdgeInitializer {
    variable: u32,
    value: i64,
}

impl EdgeInitializer {
    fn from_node(node: &SemanticNode) -> Option<Self> {
        let SemanticNode::BasicBlock(block) = node else {
            return None;
        };
        let [statement] = block.statements.as_slice() else {
            return None;
        };
        let SemanticStatementKind::Instruction(operation) = &statement.kind else {
            return None;
        };
        if operation.insn_type != InsnType::Move
            || !operation.payload.edge_copy
            || !operation.effects_ignoring_edge_copy().is_pure()
            || operation.compound_target().is_some()
        {
            return None;
        }
        let variable = operation.result.as_ref()?.code_var?;
        let [value] = operation.operands() else {
            return None;
        };
        Some(Self {
            variable,
            value: value.literal_value()?,
        })
    }
}

#[derive(Clone, Copy)]
struct LeadingInitializer {
    value: EdgeInitializer,
}

impl LeadingInitializer {
    fn from_node(node: &SemanticNode) -> Option<Self> {
        let candidate = match node {
            SemanticNode::Sequence(children) => children.first()?,
            node => node,
        };
        Some(Self {
            value: EdgeInitializer::from_node(candidate)?,
        })
    }

    fn split(node: SemanticNode) -> Option<(SemanticNode, SemanticNode)> {
        match node {
            node @ SemanticNode::BasicBlock(_) => {
                EdgeInitializer::from_node(&node)?;
                Some((node, SemanticNode::Empty))
            }
            SemanticNode::Sequence(mut children) => {
                EdgeInitializer::from_node(children.first()?)?;
                let initializer = children.remove(0);
                Some((initializer, SemanticNode::sequence(children)))
            }
            _ => None,
        }
    }
}

#[derive(Clone, Copy)]
enum InitializationEdge {
    Then,
    Else,
}

#[derive(Clone, Default)]
struct DefiniteValues {
    values: BTreeMap<u32, i64>,
}

impl DefiniteValues {
    fn normal_exit(node: &SemanticNode) -> Option<Self> {
        Self::default().interpret(node)
    }

    fn get(&self, variable: u32) -> Option<i64> {
        self.values.get(&variable).copied()
    }

    fn interpret(mut self, node: &SemanticNode) -> Option<Self> {
        match node {
            SemanticNode::Empty => Some(self),
            SemanticNode::BasicBlock(block) => {
                for statement in &block.statements {
                    self.transfer_statement(statement);
                }
                Some(self)
            }
            SemanticNode::Sequence(children) => {
                let mut state = Some(self);
                for child in children {
                    state = state.and_then(|facts| facts.interpret(child));
                }
                state
            }
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => {
                let then_facts = self
                    .clone()
                    .assume(condition, true)
                    .and_then(|facts| facts.interpret(then_node));
                let else_facts = self.assume(condition, false).and_then(|facts| {
                    facts.interpret(else_node.as_deref().unwrap_or(&SemanticNode::Empty))
                });
                Self::intersect(then_facts, else_facts)
            }
            SemanticNode::Label { body, .. } | SemanticNode::Synchronized { body, .. } => {
                self.interpret(body)
            }
            SemanticNode::Leave(leave) => {
                let Some(condition) = &leave.condition else {
                    return None;
                };
                self.assume(condition, false)
            }
            node => {
                if !crate::ir::semantic::SemanticCompletion::analyze(node).can_complete_normally() {
                    return None;
                }
                for variable in SemanticExpressionFacts::of_node(node).defined_variables() {
                    self.values.remove(&variable);
                }
                Some(self)
            }
        }
    }

    fn transfer_statement(&mut self, statement: &SemanticStatement) {
        let Some(variable) = statement.result().and_then(|result| result.code_var) else {
            return;
        };
        let value = match &statement.kind {
            SemanticStatementKind::Definition { value, .. } => value.literal_value(),
            SemanticStatementKind::Instruction(operation)
                if matches!(operation.insn_type, InsnType::Const | InsnType::Move) =>
            {
                operation
                    .operands()
                    .first()
                    .and_then(SemanticExpression::literal_value)
            }
            SemanticStatementKind::Instruction(_) => None,
        };
        match value {
            Some(value) => {
                self.values.insert(variable, value);
            }
            None => {
                self.values.remove(&variable);
            }
        }
    }

    fn assume(mut self, predicate: &SemanticPredicate, truth: bool) -> Option<Self> {
        if self.apply_assumption(predicate, truth) {
            Some(self)
        } else {
            None
        }
    }

    fn apply_assumption(&mut self, predicate: &SemanticPredicate, truth: bool) -> bool {
        match predicate {
            SemanticPredicate::True => truth,
            SemanticPredicate::False => !truth,
            SemanticPredicate::Not(inner) => self.apply_assumption(inner, !truth),
            SemanticPredicate::And(terms) if truth => {
                terms.iter().all(|term| self.apply_assumption(term, true))
            }
            SemanticPredicate::Or(terms) if !truth => {
                terms.iter().all(|term| self.apply_assumption(term, false))
            }
            SemanticPredicate::Test(test) => {
                let Some((variable, value, equality)) = PredicateEquality::extract(test) else {
                    return true;
                };
                let equals = if truth { equality } else { !equality };
                match (equals, self.values.get(&variable).copied()) {
                    (true, Some(known)) => known == value,
                    (true, None) => {
                        self.values.insert(variable, value);
                        true
                    }
                    (false, Some(known)) => known != value,
                    (false, None) => true,
                }
            }
            SemanticPredicate::And(_) | SemanticPredicate::Or(_) => true,
        }
    }

    fn intersect(left: Option<Self>, right: Option<Self>) -> Option<Self> {
        match (left, right) {
            (None, None) => None,
            (Some(facts), None) | (None, Some(facts)) => Some(facts),
            (Some(mut left), Some(right)) => {
                left.values
                    .retain(|variable, value| right.values.get(variable) == Some(value));
                Some(left)
            }
        }
    }
}

struct PredicateEquality;

impl PredicateEquality {
    fn extract(operation: &crate::ir::SemanticOperation) -> Option<(u32, i64, bool)> {
        if operation.insn_type != InsnType::If {
            return None;
        }
        let equality = match operation.payload.if_op? {
            IfOp::Eq => true,
            IfOp::Ne => false,
            IfOp::Lt | IfOp::Ge | IfOp::Gt | IfOp::Le => return None,
        };
        let [left, right] = operation.operands() else {
            return None;
        };
        Self::register_literal(left, right)
            .or_else(|| Self::register_literal(right, left))
            .map(|(variable, value)| (variable, value, equality))
    }

    fn register_literal(
        register: &SemanticExpression,
        literal: &SemanticExpression,
    ) -> Option<(u32, i64)> {
        Some((register.as_register()?.code_var?, literal.literal_value()?))
    }
}

struct DefiniteAssignment;

impl DefiniteAssignment {
    fn holds(node: &SemanticNode, variable: u32) -> bool {
        matches!(Self::interpret(node, variable, false), Ok(Some(true)))
    }

    fn interpret(
        node: &SemanticNode,
        variable: u32,
        mut defined: bool,
    ) -> Result<Option<bool>, ()> {
        match node {
            SemanticNode::Empty => Ok(Some(defined)),
            SemanticNode::BasicBlock(block) => {
                for statement in &block.statements {
                    let uses_variable = match &statement.kind {
                        SemanticStatementKind::Definition { value, .. } => {
                            SemanticExpressionFacts::of_expression(value).uses(variable)
                        }
                        SemanticStatementKind::Instruction(operation) => {
                            SemanticExpressionFacts::of_operation(operation).uses(variable)
                        }
                    };
                    if !defined && uses_variable {
                        return Err(());
                    }
                    if statement.result().and_then(|result| result.code_var) == Some(variable) {
                        defined = true;
                    }
                }
                Ok(Some(defined))
            }
            SemanticNode::Sequence(children) => {
                let mut state = Some(defined);
                for child in children {
                    state = match state {
                        Some(defined) => Self::interpret(child, variable, defined)?,
                        None => None,
                    };
                }
                Ok(state)
            }
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => {
                if !defined && SemanticExpressionFacts::of_predicate(condition).uses(variable) {
                    return Err(());
                }
                let then_state = Self::interpret(then_node, variable, defined)?;
                let else_state = Self::interpret(
                    else_node.as_deref().unwrap_or(&SemanticNode::Empty),
                    variable,
                    defined,
                )?;
                Ok(match (then_state, else_state) {
                    (None, None) => None,
                    (Some(state), None) | (None, Some(state)) => Some(state),
                    (Some(left), Some(right)) => Some(left && right),
                })
            }
            SemanticNode::Leave(leave) => {
                let facts = SemanticExpressionFacts::of_node(node);
                if !defined && facts.uses(variable) {
                    return Err(());
                }
                if leave.condition.is_some() {
                    Ok(Some(defined))
                } else {
                    Ok(None)
                }
            }
            SemanticNode::Label { body, .. } => Self::interpret(body, variable, defined),
            node => {
                let facts = SemanticExpressionFacts::of_node(node);
                if facts.uses(variable) || facts.definition_count(variable) != 0 {
                    Err(())
                } else if crate::ir::semantic::SemanticCompletion::analyze(node)
                    .can_complete_normally()
                {
                    Ok(Some(defined))
                } else {
                    Ok(None)
                }
            }
        }
    }
}
