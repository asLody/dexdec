//! Reusable value facts over Semantic IR.

use std::collections::BTreeMap;

use crate::ir::{analysis::SsaVar, RegisterArg, SemanticExpression, SemanticOperation};

use super::{
    visit, SemanticBindingKind, SemanticLeaveKind, SemanticNode, SemanticPredicate,
    SemanticStatement, SemanticVisitor,
};

#[derive(Debug, Clone, Default)]
pub struct SemanticExpressionFacts {
    definitions: BTreeMap<u32, usize>,
    uses: BTreeMap<u32, usize>,
    ssa_definitions: BTreeMap<SsaVar, usize>,
    ssa_uses: BTreeMap<SsaVar, usize>,
    has_root_continue: bool,
    loop_depth: usize,
}

impl SemanticExpressionFacts {
    pub fn of_node(node: &SemanticNode) -> Self {
        let mut facts = Self::default();
        facts.visit_node(node);
        facts
    }

    pub fn of_predicate(predicate: &SemanticPredicate) -> Self {
        let mut facts = Self::default();
        facts.visit_predicate(predicate);
        facts
    }

    pub fn of_operation(operation: &SemanticOperation) -> Self {
        let mut facts = Self::default();
        facts.visit_operation(operation);
        facts
    }

    pub fn of_expression(expression: &SemanticExpression) -> Self {
        let mut facts = Self::default();
        facts.visit_expression(expression);
        facts
    }

    pub fn definition_count(&self, variable: u32) -> usize {
        self.definitions.get(&variable).copied().unwrap_or(0)
    }

    pub fn uses(&self, variable: u32) -> bool {
        self.use_count(variable) != 0
    }

    pub fn use_count(&self, variable: u32) -> usize {
        self.uses.get(&variable).copied().unwrap_or(0)
    }

    pub fn ssa_definition_count(&self, variable: SsaVar) -> usize {
        self.ssa_definitions.get(&variable).copied().unwrap_or(0)
    }

    pub fn ssa_use_count(&self, variable: SsaVar) -> usize {
        self.ssa_uses.get(&variable).copied().unwrap_or(0)
    }

    pub fn ssa_escapes(&self, scope: &Self, variable: SsaVar) -> bool {
        let local_definitions = scope.ssa_definition_count(variable);
        let global_definitions = self.ssa_definition_count(variable);
        let local_uses = scope.ssa_use_count(variable);
        let global_uses = self.ssa_use_count(variable);
        if local_definitions == 0 || global_definitions < local_definitions {
            return global_uses != local_uses;
        }
        global_uses.checked_mul(local_definitions) != local_uses.checked_mul(global_definitions)
    }

    pub fn variable_escapes(&self, scope: &Self, variable: u32) -> bool {
        let local_definitions = scope.definition_count(variable);
        let global_definitions = self.definition_count(variable);
        let local_uses = scope.use_count(variable);
        let global_uses = self.use_count(variable);
        if local_definitions == 0 || global_definitions < local_definitions {
            return global_uses != local_uses;
        }
        global_uses.checked_mul(local_definitions) != local_uses.checked_mul(global_definitions)
    }

    pub fn defined_variables(&self) -> impl Iterator<Item = u32> + '_ {
        self.definitions.keys().copied()
    }

    pub fn used_variables(&self) -> impl Iterator<Item = u32> + '_ {
        self.uses.keys().copied()
    }

    pub fn defined_ssa_variables(&self) -> impl Iterator<Item = SsaVar> + '_ {
        self.ssa_definitions.keys().copied()
    }

    pub fn used_ssa_variables(&self) -> impl Iterator<Item = SsaVar> + '_ {
        self.ssa_uses.keys().copied()
    }

    pub fn has_root_continue(&self) -> bool {
        self.has_root_continue
    }

    pub fn merge(&mut self, other: &Self) {
        for (variable, count) in &other.definitions {
            *self.definitions.entry(*variable).or_default() += count;
        }
        for (variable, count) in &other.uses {
            *self.uses.entry(*variable).or_default() += count;
        }
        for (variable, count) in &other.ssa_definitions {
            *self.ssa_definitions.entry(*variable).or_default() += count;
        }
        for (variable, count) in &other.ssa_uses {
            *self.ssa_uses.entry(*variable).or_default() += count;
        }
        self.has_root_continue |= other.has_root_continue;
    }
}

impl SemanticVisitor for SemanticExpressionFacts {
    fn enter_node(&mut self, node: &SemanticNode) {
        if let SemanticNode::Leave(leave) = node {
            if matches!(&leave.kind, SemanticLeaveKind::Continue) && self.loop_depth == 0 {
                self.has_root_continue = true;
            }
        }
        let nested_loop = matches!(
            node,
            SemanticNode::Loop { .. } | SemanticNode::For { .. } | SemanticNode::ForEach { .. }
        );
        self.loop_depth += usize::from(nested_loop);
    }

    fn exit_node(&mut self, node: &SemanticNode) {
        let nested_loop = matches!(
            node,
            SemanticNode::Loop { .. } | SemanticNode::For { .. } | SemanticNode::ForEach { .. }
        );
        self.loop_depth -= usize::from(nested_loop);
    }

    fn visit_statement(&mut self, statement: &SemanticStatement) {
        if let Some(variable) = statement.result().and_then(|result| result.code_var) {
            *self.definitions.entry(variable).or_default() += 1;
        }
        if let Some(variable) = statement.result().and_then(SsaVar::from_reg) {
            *self.ssa_definitions.entry(variable).or_default() += 1;
        }
        visit::walk_statement(self, statement);
    }

    fn visit_register(&mut self, register: &RegisterArg) {
        if let Some(variable) = register.code_var {
            *self.uses.entry(variable).or_default() += 1;
        }
        if let Some(variable) = SsaVar::from_reg(register) {
            *self.ssa_uses.entry(variable).or_default() += 1;
        }
    }

    fn visit_binding(&mut self, _kind: SemanticBindingKind, register: &RegisterArg) {
        if let Some(variable) = register.code_var {
            *self.definitions.entry(variable).or_default() += 1;
        }
        if let Some(variable) = SsaVar::from_reg(register) {
            *self.ssa_definitions.entry(variable).or_default() += 1;
        }
    }
}
