use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    InsnType, RegisterArg, SemanticExpression, SemanticNode, SemanticOperation, SemanticPredicate,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct SourceVariable(u32);

impl SourceVariable {
    pub(super) fn new(value: u32) -> Self {
        Self(value)
    }

    pub(super) fn raw(self) -> u32 {
        self.0
    }

    pub(super) fn of(register: &RegisterArg) -> Result<Self, DeclarationError> {
        register
            .code_var
            .map(Self)
            .ok_or(DeclarationError::MissingSourceVariable(register.reg_num))
    }
}

#[derive(Debug, Clone)]
pub(super) enum DeclarationError {
    MissingSourceVariable(u32),
    MalformedConstructor(u32),
}

impl std::fmt::Display for DeclarationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingSourceVariable(register) => {
                write!(
                    formatter,
                    "register v{register} has no source variable identity"
                )
            }
            Self::MalformedConstructor(offset) => {
                write!(formatter, "constructor at {offset:#x} has no receiver")
            }
        }
    }
}

impl std::error::Error for DeclarationError {}

#[derive(Debug, Clone, Copy)]
struct Point {
    scope: u32,
    event: usize,
}

#[derive(Debug, Default)]
struct LocalFacts {
    definitions: Vec<Point>,
    uses: Vec<Point>,
}

#[derive(Debug, Default)]
pub(super) struct DeclarationFacts {
    inline_variables: BTreeSet<SourceVariable>,
    catch_storage: BTreeSet<SourceVariable>,
}

impl DeclarationFacts {
    pub(super) fn inline_variables(&self) -> &BTreeSet<SourceVariable> {
        &self.inline_variables
    }

    pub(super) fn catch_requires_storage(&self, variable: SourceVariable) -> bool {
        self.catch_storage.contains(&variable)
    }
}

#[derive(Debug, Default)]
pub(super) struct DeclarationAnalysis {
    facts: BTreeMap<SourceVariable, LocalFacts>,
    scope_parents: BTreeMap<u32, u32>,
    catch_scopes: BTreeMap<SourceVariable, BTreeSet<u32>>,
    scope: u32,
    next_scope: u32,
    event: usize,
}

impl DeclarationAnalysis {
    pub(super) fn analyze(
        mut self,
        root: &SemanticNode,
    ) -> Result<DeclarationFacts, DeclarationError> {
        self.visit(root)?;
        let mut inline_variables = self
            .facts
            .iter()
            .filter_map(|(key, facts)| {
                let [definition] = facts.definitions.as_slice() else {
                    return None;
                };
                facts
                    .uses
                    .iter()
                    .all(|usage| {
                        self.scope_contains(definition.scope, usage.scope)
                            && usage.event >= definition.event
                    })
                    .then_some(*key)
            })
            .collect::<BTreeSet<_>>();
        inline_variables.retain(|variable| !self.catch_scopes.contains_key(variable));

        let catch_storage = self
            .catch_scopes
            .iter()
            .filter_map(|(variable, binding_scopes)| {
                let escapes = self.facts.get(variable).is_some_and(|facts| {
                    facts.uses.iter().any(|usage| {
                        !binding_scopes
                            .iter()
                            .any(|scope| self.scope_contains(*scope, usage.scope))
                    })
                });
                escapes.then_some(*variable)
            })
            .collect();

        Ok(DeclarationFacts {
            inline_variables,
            catch_storage,
        })
    }

    fn visit(&mut self, root: &SemanticNode) -> Result<(), DeclarationError> {
        let mut pending = vec![DeclarationTask::Node(root, self.scope)];
        while let Some(task) = pending.pop() {
            match task {
                DeclarationTask::Node(node, scope) => {
                    self.scope = scope;
                    self.schedule_node(node, scope, &mut pending)?;
                }
                DeclarationTask::Statement(statement, scope) => {
                    self.scope = scope;
                    self.statement(statement)?;
                }
                DeclarationTask::Predicate(predicate, scope) => {
                    self.scope = scope;
                    let point = self.point();
                    self.predicate(predicate, point)?;
                }
            }
        }
        Ok(())
    }

    fn schedule_node<'a>(
        &mut self,
        node: &'a SemanticNode,
        scope: u32,
        pending: &mut Vec<DeclarationTask<'a>>,
    ) -> Result<(), DeclarationError> {
        match node {
            SemanticNode::Empty => {}
            SemanticNode::BasicBlock(block) => pending.extend(
                block
                    .statements
                    .iter()
                    .rev()
                    .map(|statement| DeclarationTask::Statement(statement, scope)),
            ),
            SemanticNode::Sequence(children) => pending.extend(
                children
                    .iter()
                    .rev()
                    .map(|child| DeclarationTask::Node(child, scope)),
            ),
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => {
                let point = self.point();
                self.predicate(condition, point)?;
                if let Some(else_node) = else_node {
                    let child_scope = self.new_scope(scope);
                    pending.push(DeclarationTask::Node(else_node, child_scope));
                }
                let child_scope = self.new_scope(scope);
                pending.push(DeclarationTask::Node(then_node, child_scope));
            }
            SemanticNode::Loop {
                kind, test, body, ..
            } => {
                let body_scope = self.new_scope(scope);
                match kind {
                    crate::ir::SemanticLoopKind::PreTested => {
                        pending.push(DeclarationTask::Node(body, body_scope));
                        pending.push(DeclarationTask::Predicate(&test.condition, scope));
                        pending.push(DeclarationTask::Node(&test.setup, body_scope));
                    }
                    crate::ir::SemanticLoopKind::PostTested => {
                        pending.push(DeclarationTask::Predicate(&test.condition, scope));
                        pending.push(DeclarationTask::Node(&test.setup, body_scope));
                        pending.push(DeclarationTask::Node(body, body_scope));
                    }
                    crate::ir::SemanticLoopKind::Endless => {
                        pending.push(DeclarationTask::Node(body, body_scope));
                        pending.push(DeclarationTask::Node(&test.setup, body_scope));
                    }
                }
            }
            SemanticNode::For {
                init,
                condition,
                update,
                body,
                ..
            } => {
                let loop_scope = self.new_scope(scope);
                self.scope = loop_scope;
                self.statement(init)?;
                let point = self.point();
                self.predicate(condition, point)?;
                pending.push(DeclarationTask::Statement(update, loop_scope));
                let child_scope = self.new_scope(loop_scope);
                pending.push(DeclarationTask::Node(body, child_scope));
            }
            SemanticNode::ForEach { iterable, body, .. } => {
                let point = self.point();
                self.expression(iterable, point)?;
                let child_scope = self.new_scope(scope);
                pending.push(DeclarationTask::Node(body, child_scope));
            }
            SemanticNode::Switch {
                selector, cases, ..
            } => {
                let point = self.point();
                self.expression(selector, point)?;
                for case in cases.iter().rev() {
                    let child_scope = self.new_scope(scope);
                    pending.push(DeclarationTask::Node(&case.body, child_scope));
                }
            }
            SemanticNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                if let Some(finally) = finally {
                    let child_scope = self.new_scope(scope);
                    pending.push(DeclarationTask::Node(&finally.body, child_scope));
                }
                for catch in catches.iter().rev() {
                    let child_scope = self.new_scope(scope);
                    if let Some(value) = &catch.exception_value {
                        self.catch_scopes
                            .entry(SourceVariable::of(value)?)
                            .or_default()
                            .insert(child_scope);
                    }
                    pending.push(DeclarationTask::Node(&catch.body, child_scope));
                }
                let child_scope = self.new_scope(scope);
                pending.push(DeclarationTask::Node(body, child_scope));
            }
            SemanticNode::Synchronized { lock, body, .. } => {
                let point = self.point();
                self.expression(lock, point)?;
                let child_scope = self.new_scope(scope);
                pending.push(DeclarationTask::Node(body, child_scope));
            }
            SemanticNode::Label { body, .. } => {
                let child_scope = self.new_scope(scope);
                pending.push(DeclarationTask::Node(body, child_scope));
            }
            SemanticNode::Leave(leave) => {
                let point = self.point();
                if let Some(condition) = &leave.condition {
                    self.predicate(condition, point)?;
                }
                if let Some(value) = leave.value() {
                    self.expression(value, point)?;
                }
            }
        }
        Ok(())
    }

    fn new_scope(&mut self, parent: u32) -> u32 {
        self.next_scope += 1;
        self.scope_parents.insert(self.next_scope, parent);
        self.next_scope
    }

    fn scope_contains(&self, ancestor: u32, mut scope: u32) -> bool {
        loop {
            if scope == ancestor {
                return true;
            }
            let Some(parent) = self.scope_parents.get(&scope) else {
                return false;
            };
            scope = *parent;
        }
    }

    fn statement(
        &mut self,
        statement: &crate::ir::SemanticStatement,
    ) -> Result<(), DeclarationError> {
        let point = self.point();
        match &statement.kind {
            crate::ir::SemanticStatementKind::Definition { value, .. } => {
                self.semantic_value(value, point)?;
            }
            crate::ir::SemanticStatementKind::Instruction(instruction) => {
                for argument in Self::semantic_arguments(instruction)? {
                    self.expression(argument, point)?;
                }
                if let Some(target) = instruction.compound_target() {
                    self.expression(target, point)?;
                }
            }
        }
        if let Some(result) = statement.result() {
            self.facts
                .entry(SourceVariable::of(result)?)
                .or_default()
                .definitions
                .push(point);
        }
        Ok(())
    }

    fn semantic_value(
        &mut self,
        value: &crate::ir::SemanticExpression,
        point: Point,
    ) -> Result<(), DeclarationError> {
        match value {
            SemanticExpression::Register(register) => {
                self.facts
                    .entry(SourceVariable::of(register)?)
                    .or_default()
                    .uses
                    .push(point);
                Ok(())
            }
            SemanticExpression::Literal(_) => Ok(()),
            SemanticExpression::Operation(operation) => {
                for operand in Self::semantic_arguments(operation)? {
                    self.expression(operand, point)?;
                }
                if let Some(target) = operation.compound_target() {
                    self.expression(target, point)?;
                }
                Ok(())
            }
            crate::ir::SemanticExpression::Select {
                condition,
                when_true,
                when_false,
            } => {
                self.predicate(condition, point)?;
                self.semantic_value(when_true, point)?;
                self.semantic_value(when_false, point)
            }
        }
    }

    fn point(&mut self) -> Point {
        let point = Point {
            scope: self.scope,
            event: self.event,
        };
        self.event += 1;
        point
    }

    fn predicate(
        &mut self,
        predicate: &SemanticPredicate,
        point: Point,
    ) -> Result<(), DeclarationError> {
        let mut pending = vec![predicate];
        while let Some(predicate) = pending.pop() {
            match predicate {
                SemanticPredicate::Test(insn) => {
                    for argument in insn.operands() {
                        self.expression(argument, point)?;
                    }
                    if let Some(target) = insn.compound_target() {
                        self.expression(target, point)?;
                    }
                }
                SemanticPredicate::Not(inner) => pending.push(inner),
                SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                    pending.extend(terms.iter().rev());
                }
                SemanticPredicate::True | SemanticPredicate::False => {}
            }
        }
        Ok(())
    }

    fn expression(
        &mut self,
        expression: &SemanticExpression,
        point: Point,
    ) -> Result<(), DeclarationError> {
        self.semantic_value(expression, point)
    }

    fn semantic_arguments(
        instruction: &SemanticOperation,
    ) -> Result<&[SemanticExpression], DeclarationError> {
        if instruction.insn_type != InsnType::Constructor {
            return Ok(instruction.operands());
        }
        instruction
            .operands()
            .get(1..)
            .ok_or(DeclarationError::MalformedConstructor(instruction.offset))
    }
}

enum DeclarationTask<'a> {
    Node(&'a SemanticNode, u32),
    Statement(&'a crate::ir::SemanticStatement, u32),
    Predicate(&'a SemanticPredicate, u32),
}
