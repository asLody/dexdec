use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    ArgType, ArithOp, InsnType, InstructionId, MemberReference, PrimitiveType, RegisterArg,
    SemanticBindingKind, SemanticExpression, SemanticNode, SemanticOperation, SemanticPredicate,
    SemanticStatement, SemanticStatementKind, SemanticVisitor,
};

use super::SourceTypeEnvironment;

#[derive(Debug, Clone)]
pub struct VariableSemanticGraph {
    variables: BTreeMap<u32, VariableNode>,
    operations: BTreeMap<InstructionId, OperationNode>,
    edges: Vec<VariableEdge>,
}

impl VariableSemanticGraph {
    pub fn analyze(root: &SemanticNode, types: &SourceTypeEnvironment) -> Self {
        let mut builder = VariableSemanticGraphBuilder::new(types);
        builder.visit_node(root);
        builder.finish()
    }

    pub fn variables(&self) -> impl Iterator<Item = &VariableNode> {
        self.variables.values()
    }

    pub fn variable(&self, identity: u32) -> Option<&VariableNode> {
        self.variables.get(&identity)
    }

    pub fn operation(&self, identity: InstructionId) -> Option<&OperationNode> {
        self.operations.get(&identity)
    }

    pub fn edges_for(&self, variable: u32) -> impl Iterator<Item = &VariableEdge> {
        self.edges
            .iter()
            .filter(move |edge| edge.variable == variable)
    }
}

#[derive(Debug, Clone)]
pub struct VariableNode {
    identity: u32,
    ty: ArgType,
    definitions: usize,
    uses: usize,
    source_binding: bool,
}

impl VariableNode {
    pub fn identity(&self) -> u32 {
        self.identity
    }

    pub fn ty(&self) -> &ArgType {
        &self.ty
    }

    pub fn definitions(&self) -> usize {
        self.definitions
    }

    pub fn uses(&self) -> usize {
        self.uses
    }

    pub fn is_source_binding(&self) -> bool {
        self.source_binding
    }

    fn can_be_integral(&self) -> bool {
        match &self.ty {
            ArgType::Primitive(
                PrimitiveType::Byte
                | PrimitiveType::Short
                | PrimitiveType::Char
                | PrimitiveType::Int,
            ) => true,
            ArgType::Unknown(possible) => {
                !possible.is_empty()
                    && possible.iter().all(|ty| {
                        matches!(
                            ty,
                            PrimitiveType::Byte
                                | PrimitiveType::Short
                                | PrimitiveType::Char
                                | PrimitiveType::Int
                        )
                    })
            }
            _ => false,
        }
    }

    fn can_be_reference(&self) -> bool {
        match &self.ty {
            ArgType::Object(_) | ArgType::Array(_) => true,
            ArgType::Unknown(possible) => {
                !possible.is_empty()
                    && possible
                        .iter()
                        .all(|ty| matches!(ty, PrimitiveType::Object | PrimitiveType::Array))
            }
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct OperationNode {
    identity: InstructionId,
    kind: InsnType,
    reference: Option<MemberReference>,
    operands: Vec<OperationOperand>,
    loop_depth: usize,
}

impl OperationNode {
    pub fn identity(&self) -> InstructionId {
        self.identity
    }

    pub fn kind(&self) -> InsnType {
        self.kind
    }

    pub fn reference(&self) -> Option<&MemberReference> {
        self.reference.as_ref()
    }

    pub fn operands(&self) -> &[OperationOperand] {
        &self.operands
    }

    pub fn loop_depth(&self) -> usize {
        self.loop_depth
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OperationOperand {
    ty: Option<ArgType>,
    literal: Option<i64>,
    reference: Option<MemberReference>,
}

impl OperationOperand {
    pub fn ty(&self) -> Option<&ArgType> {
        self.ty.as_ref()
    }

    pub fn literal(&self) -> Option<i64> {
        self.literal
    }

    pub fn reference(&self) -> Option<&MemberReference> {
        self.reference.as_ref()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariableEdge {
    variable: u32,
    operation: Option<InstructionId>,
    kind: VariableEdgeKind,
}

impl VariableEdge {
    pub fn variable(&self) -> u32 {
        self.variable
    }

    pub fn operation(&self) -> Option<InstructionId> {
        self.operation
    }

    pub fn kind(&self) -> &VariableEdgeKind {
        &self.kind
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VariableEdgeKind {
    Definition,
    Operand(usize),
    Predicate,
    LoopIndex,
    LoopBound,
    LoopValue,
    RecurrenceStep,
    Return,
    Throw,
    Lock,
    Selector,
    ArrayIndex,
    ArrayValue,
    Dimension,
    FieldValue,
    Binding(SemanticBindingKind),
    Recurrence(RecurrenceKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecurrenceKind {
    Increment,
    Decrement,
    Other,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum VariableRole {
    Exception,
    Element,
    Index,
    Limit,
    Size,
    Counter,
    Remaining,
    Step,
    Value,
    Accumulator,
    Condition,
    Result,
    Lock,
    Selector,
    Iterator,
}

#[derive(Debug, Clone, Default)]
pub struct VariableRoleScores {
    scores: BTreeMap<u32, BTreeMap<VariableRole, u16>>,
}

impl VariableRoleScores {
    pub fn score(&self, variable: u32, role: VariableRole) -> u16 {
        self.scores
            .get(&variable)
            .and_then(|roles| roles.get(&role))
            .copied()
            .unwrap_or_default()
    }

    pub fn roles(&self, variable: u32) -> impl Iterator<Item = (VariableRole, u16)> + '_ {
        self.scores
            .get(&variable)
            .into_iter()
            .flat_map(|roles| roles.iter().map(|(role, score)| (*role, *score)))
    }

    fn add(&mut self, variable: u32, role: VariableRole, score: u16) {
        let current = self
            .scores
            .entry(variable)
            .or_default()
            .entry(role)
            .or_default();
        *current = current.saturating_add(score);
    }
}

pub trait VariableRoleAnalysis {
    fn analyze(&self, graph: &VariableSemanticGraph) -> VariableRoleScores;
}

#[derive(Debug, Clone, Copy, Default)]
pub struct StructuralVariableRoleAnalysis;

impl VariableRoleAnalysis for StructuralVariableRoleAnalysis {
    fn analyze(&self, graph: &VariableSemanticGraph) -> VariableRoleScores {
        let mut scores = VariableRoleScores::default();
        let return_variables = graph
            .edges
            .iter()
            .filter_map(|edge| {
                matches!(edge.kind(), VariableEdgeKind::Return).then_some(edge.variable())
            })
            .collect::<BTreeSet<_>>();
        for variable in graph.variables() {
            if variable.ty() == &ArgType::BOOLEAN {
                scores.add(variable.identity(), VariableRole::Condition, 20);
            }
            if variable.ty() == &ArgType::object("java/util/Iterator") {
                scores.add(variable.identity(), VariableRole::Iterator, 80);
            }
            for edge in graph.edges_for(variable.identity()) {
                let role = match edge.kind() {
                    VariableEdgeKind::Binding(SemanticBindingKind::Catch) => {
                        Some((VariableRole::Exception, 100))
                    }
                    VariableEdgeKind::Throw if variable.can_be_reference() => {
                        Some((VariableRole::Exception, 100))
                    }
                    VariableEdgeKind::Binding(SemanticBindingKind::ForEach) => {
                        Some((VariableRole::Element, 100))
                    }
                    VariableEdgeKind::LoopIndex if variable.can_be_integral() => {
                        Some((VariableRole::Index, 100))
                    }
                    VariableEdgeKind::LoopBound if variable.can_be_integral() => {
                        Some((VariableRole::Limit, 80))
                    }
                    VariableEdgeKind::LoopValue => Some((VariableRole::Value, 70)),
                    VariableEdgeKind::RecurrenceStep => Some((VariableRole::Step, 75)),
                    VariableEdgeKind::ArrayIndex if variable.can_be_integral() => {
                        Some((VariableRole::Index, 100))
                    }
                    VariableEdgeKind::Dimension if variable.can_be_integral() => {
                        Some((VariableRole::Size, 90))
                    }
                    VariableEdgeKind::Predicate if variable.ty() == &ArgType::BOOLEAN => {
                        Some((VariableRole::Condition, 70))
                    }
                    VariableEdgeKind::Return if return_variables.len() == 1 => {
                        Some((VariableRole::Result, 35))
                    }
                    VariableEdgeKind::Lock if variable.can_be_reference() => {
                        Some((VariableRole::Lock, 100))
                    }
                    VariableEdgeKind::Selector => Some((VariableRole::Selector, 80)),
                    VariableEdgeKind::Recurrence(
                        RecurrenceKind::Increment | RecurrenceKind::Decrement,
                    ) => {
                        let indexes_values = graph.edges_for(variable.identity()).any(|edge| {
                            matches!(
                                edge.kind(),
                                VariableEdgeKind::ArrayIndex | VariableEdgeKind::LoopIndex
                            )
                        });
                        Some(if indexes_values {
                            (VariableRole::Index, 90)
                        } else {
                            match edge.kind() {
                                VariableEdgeKind::Recurrence(RecurrenceKind::Increment) => {
                                    (VariableRole::Counter, 70)
                                }
                                VariableEdgeKind::Recurrence(RecurrenceKind::Decrement) => {
                                    (VariableRole::Remaining, 70)
                                }
                                _ => unreachable!(),
                            }
                        })
                    }
                    VariableEdgeKind::Recurrence(RecurrenceKind::Other) => {
                        Some((VariableRole::Accumulator, 70))
                    }
                    VariableEdgeKind::Definition => edge
                        .operation()
                        .and_then(|operation| graph.operation(operation))
                        .and_then(|operation| {
                            (operation.kind() == InsnType::ArrayLength)
                                .then_some((VariableRole::Size, 100))
                                .or_else(|| {
                                    (operation.kind() == InsnType::Aget
                                        && operation.loop_depth() != 0)
                                        .then_some((VariableRole::Element, 65))
                                })
                        }),
                    VariableEdgeKind::ArrayIndex
                    | VariableEdgeKind::Dimension
                    | VariableEdgeKind::Throw
                    | VariableEdgeKind::Lock
                    | VariableEdgeKind::LoopIndex
                    | VariableEdgeKind::LoopBound
                    | VariableEdgeKind::LoopValue
                    | VariableEdgeKind::RecurrenceStep
                    | VariableEdgeKind::Operand(_)
                    | VariableEdgeKind::ArrayValue
                    | VariableEdgeKind::FieldValue
                    | VariableEdgeKind::Predicate
                    | VariableEdgeKind::Return => None,
                };
                if let Some((role, weight)) = role {
                    scores.add(variable.identity(), role, weight);
                }
            }
        }
        scores
    }
}

struct VariableSemanticGraphBuilder<'a> {
    types: &'a SourceTypeEnvironment,
    graph: VariableSemanticGraph,
    loop_depth: usize,
}

impl<'a> VariableSemanticGraphBuilder<'a> {
    fn new(types: &'a SourceTypeEnvironment) -> Self {
        Self {
            types,
            graph: VariableSemanticGraph {
                variables: BTreeMap::new(),
                operations: BTreeMap::new(),
                edges: Vec::new(),
            },
            loop_depth: 0,
        }
    }

    fn finish(self) -> VariableSemanticGraph {
        self.graph
    }

    fn ensure_variable(&mut self, register: &RegisterArg) -> Option<u32> {
        let identity = register.code_var?;
        let ty = self
            .types
            .register_type(register)
            .unwrap_or(&register.ty)
            .clone();
        self.graph
            .variables
            .entry(identity)
            .and_modify(|variable| {
                if !variable.ty.is_known() && ty.is_known() {
                    variable.ty = ty.clone();
                }
            })
            .or_insert(VariableNode {
                identity,
                ty,
                definitions: 0,
                uses: 0,
                source_binding: false,
            });
        Some(identity)
    }

    fn expression_type(&self, expression: &SemanticExpression) -> Option<ArgType> {
        match expression {
            SemanticExpression::Register(register) => Some(
                self.types
                    .register_type(register)
                    .unwrap_or(&register.ty)
                    .clone(),
            ),
            SemanticExpression::Literal(literal) => Some(literal.ty.clone()),
            SemanticExpression::Operation(operation) => operation.result.as_ref().map(|result| {
                self.types
                    .register_type(result)
                    .unwrap_or(&result.ty)
                    .clone()
            }),
            SemanticExpression::Select { when_true, .. } => self.expression_type(when_true),
        }
    }

    fn operation_operands(&self, operation: &SemanticOperation) -> Vec<OperationOperand> {
        operation
            .operands()
            .iter()
            .map(|operand| OperationOperand {
                ty: self.expression_type(operand),
                literal: operand.literal_value(),
                reference: Self::expression_reference(operand),
            })
            .collect()
    }

    fn expression_reference(expression: &SemanticExpression) -> Option<MemberReference> {
        let mut expression = expression;
        loop {
            let SemanticExpression::Operation(operation) = expression else {
                return None;
            };
            if matches!(operation.insn_type, InsnType::Move | InsnType::CheckCast)
                && operation.operands().len() == 1
            {
                expression = &operation.operands()[0];
                continue;
            }
            return operation.payload.reference.clone();
        }
    }

    fn source_binding(&mut self, register: &RegisterArg) {
        let Some(variable) = self.ensure_variable(register) else {
            return;
        };
        self.graph
            .variables
            .get_mut(&variable)
            .unwrap()
            .source_binding = true;
    }

    fn definition(&mut self, register: &RegisterArg, operation: Option<InstructionId>) {
        let Some(variable) = self.ensure_variable(register) else {
            return;
        };
        self.graph.variables.get_mut(&variable).unwrap().definitions += 1;
        self.edge(variable, operation, VariableEdgeKind::Definition);
    }

    fn edge(&mut self, variable: u32, operation: Option<InstructionId>, kind: VariableEdgeKind) {
        let edge = VariableEdge {
            variable,
            operation,
            kind,
        };
        if !self.graph.edges.contains(&edge) {
            self.graph.edges.push(edge);
        }
    }

    fn expression_edges(
        &mut self,
        expression: &SemanticExpression,
        operation: Option<InstructionId>,
        kind: VariableEdgeKind,
    ) {
        for variable in VariableReferences::expression(expression) {
            self.edge(variable, operation, kind.clone());
        }
    }

    fn expression_root_edge(
        &mut self,
        expression: &SemanticExpression,
        operation: Option<InstructionId>,
        kind: VariableEdgeKind,
    ) {
        if let Some(variable) = VariableReferences::expression_root(expression) {
            self.edge(variable, operation, kind);
        }
    }

    fn predicate_edges(&mut self, predicate: &SemanticPredicate) {
        for variable in VariableReferences::predicate(predicate) {
            self.edge(variable, None, VariableEdgeKind::Predicate);
        }
    }

    fn for_loop_edges(&mut self, update: &SemanticStatement, condition: &SemanticPredicate) {
        let Some(index) = Self::statement_definition(update) else {
            return;
        };
        if !Self::statement_uses_variable(update, index) {
            self.edge(
                index,
                Self::statement_value_operation(update),
                VariableEdgeKind::LoopValue,
            );
            return;
        }
        self.edge(index, None, VariableEdgeKind::LoopIndex);
        for bound in VariableReferences::predicate_roots(condition) {
            if bound != index {
                self.edge(bound, None, VariableEdgeKind::LoopBound);
            }
        }
    }

    fn statement_definition(statement: &SemanticStatement) -> Option<u32> {
        match &statement.kind {
            SemanticStatementKind::Instruction(operation) => operation
                .result
                .as_ref()
                .and_then(|result| result.code_var)
                .or_else(|| {
                    operation
                        .compound_target()
                        .and_then(VariableReferences::expression_root)
                }),
            SemanticStatementKind::Definition { result, .. } => result.code_var,
        }
    }

    fn statement_uses_variable(statement: &SemanticStatement, variable: u32) -> bool {
        match &statement.kind {
            SemanticStatementKind::Instruction(operation) => operation
                .operands()
                .iter()
                .chain(operation.compound_target())
                .any(|expression| VariableReferences::expression(expression).contains(&variable)),
            SemanticStatementKind::Definition { value, .. } => {
                VariableReferences::expression(value).contains(&variable)
            }
        }
    }

    fn statement_value_operation(statement: &SemanticStatement) -> Option<InstructionId> {
        let expression_operation = |expression: &SemanticExpression| {
            expression.as_operation().map(|operation| operation.id)
        };
        match &statement.kind {
            SemanticStatementKind::Instruction(operation) => (operation.insn_type
                == InsnType::Invoke)
                .then_some(operation.id)
                .or_else(|| operation.operands().first().and_then(expression_operation)),
            SemanticStatementKind::Definition { value, .. } => expression_operation(value),
        }
    }

    fn recurrence(&mut self, operation: &SemanticOperation) {
        if self.loop_depth == 0 || operation.insn_type != InsnType::Arith {
            return;
        }
        let Some(variable) = operation.result.as_ref().and_then(|result| result.code_var) else {
            return;
        };
        let operands = operation.operands();
        if !operands
            .iter()
            .any(|operand| VariableReferences::expression(operand).contains(&variable))
        {
            return;
        }
        let literal = operands.iter().find_map(|operand| operand.literal_value());
        let kind = match (operation.payload.arith_op, literal) {
            (Some(ArithOp::Add), Some(1)) | (Some(ArithOp::Sub), Some(-1)) => {
                RecurrenceKind::Increment
            }
            (Some(ArithOp::Add), Some(-1)) | (Some(ArithOp::Sub), Some(1)) => {
                RecurrenceKind::Decrement
            }
            _ => RecurrenceKind::Other,
        };
        for step in operands
            .iter()
            .filter_map(VariableReferences::expression_root)
            .filter(|step| *step != variable)
        {
            self.edge(step, Some(operation.id), VariableEdgeKind::RecurrenceStep);
        }
        self.edge(
            variable,
            Some(operation.id),
            VariableEdgeKind::Recurrence(kind),
        );
    }

    fn visit_predicate_tests(&mut self, predicate: &SemanticPredicate) {
        let mut pending = vec![predicate];
        while let Some(predicate) = pending.pop() {
            match predicate {
                SemanticPredicate::Test(operation) => self.visit_operation(operation),
                SemanticPredicate::Not(inner) => pending.push(inner),
                SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                    pending.extend(terms.iter().rev())
                }
                SemanticPredicate::True | SemanticPredicate::False => {}
            }
        }
    }
}

impl SemanticVisitor for VariableSemanticGraphBuilder<'_> {
    fn enter_node(&mut self, node: &SemanticNode) {
        let nested_loop = matches!(
            node,
            SemanticNode::Loop { .. } | SemanticNode::For { .. } | SemanticNode::ForEach { .. }
        );
        self.loop_depth += usize::from(nested_loop);
        match node {
            SemanticNode::Synchronized { lock, .. } => {
                self.expression_root_edge(lock, None, VariableEdgeKind::Lock)
            }
            SemanticNode::Switch { selector, .. } => {
                self.expression_root_edge(selector, None, VariableEdgeKind::Selector)
            }
            SemanticNode::For {
                update, condition, ..
            } => self.for_loop_edges(update, condition),
            SemanticNode::Leave(leave) => match &leave.kind {
                crate::ir::SemanticLeaveKind::Return(Some(value)) => {
                    self.expression_root_edge(value, None, VariableEdgeKind::Return)
                }
                crate::ir::SemanticLeaveKind::Throw(value) => {
                    self.expression_root_edge(value, None, VariableEdgeKind::Throw)
                }
                _ => {}
            },
            _ => {}
        }
    }

    fn exit_node(&mut self, node: &SemanticNode) {
        let nested_loop = matches!(
            node,
            SemanticNode::Loop { .. } | SemanticNode::For { .. } | SemanticNode::ForEach { .. }
        );
        self.loop_depth -= usize::from(nested_loop);
    }

    fn visit_statement(&mut self, statement: &SemanticStatement) {
        match &statement.kind {
            SemanticStatementKind::Instruction(operation) => {
                if let Some(result) = &operation.result {
                    self.source_binding(result);
                }
                self.visit_operation(operation);
            }
            SemanticStatementKind::Definition { result, value, .. } => {
                self.source_binding(result);
                self.definition(result, Some(statement.id()));
                self.visit_expression(value);
            }
        }
    }

    fn visit_predicate(&mut self, predicate: &SemanticPredicate) {
        self.predicate_edges(predicate);
        self.visit_predicate_tests(predicate);
    }

    fn visit_operation(&mut self, operation: &SemanticOperation) {
        let operands = self.operation_operands(operation);
        self.graph
            .operations
            .entry(operation.id)
            .or_insert_with(|| OperationNode {
                identity: operation.id,
                kind: operation.insn_type,
                reference: operation.payload.reference.clone(),
                operands,
                loop_depth: self.loop_depth,
            });
        if let Some(result) = &operation.result {
            self.definition(result, Some(operation.id));
        }
        if matches!(operation.insn_type, InsnType::Iput | InsnType::Sput) {
            if let Some(variable) = operation
                .operands()
                .first()
                .and_then(VariableReferences::expression_root)
            {
                self.edge(variable, Some(operation.id), VariableEdgeKind::FieldValue);
            }
        }
        for (index, operand) in operation.operands().iter().enumerate() {
            self.expression_edges(
                operand,
                Some(operation.id),
                VariableEdgeKind::Operand(index),
            );
            let contextual = match (operation.insn_type, index) {
                (InsnType::Aget, 1) | (InsnType::Aput, 2) => Some(VariableEdgeKind::ArrayIndex),
                (InsnType::Aput, 0) => Some(VariableEdgeKind::ArrayValue),
                (InsnType::NewArray, 0) => Some(VariableEdgeKind::Dimension),
                (InsnType::MonitorEnter | InsnType::MonitorExit, 0) => Some(VariableEdgeKind::Lock),
                _ => None,
            };
            if let Some(kind) = contextual {
                self.expression_edges(operand, Some(operation.id), kind);
            }
            self.visit_expression(operand);
        }
        if let Some(target) = operation.compound_target() {
            self.visit_expression(target);
        }
        self.recurrence(operation);
    }

    fn visit_register(&mut self, register: &RegisterArg) {
        let Some(variable) = self.ensure_variable(register) else {
            return;
        };
        self.graph.variables.get_mut(&variable).unwrap().uses += 1;
    }

    fn visit_binding(&mut self, kind: SemanticBindingKind, register: &RegisterArg) {
        let Some(variable) = self.ensure_variable(register) else {
            return;
        };
        self.graph.variables.get_mut(&variable).unwrap().definitions += 1;
        self.graph
            .variables
            .get_mut(&variable)
            .unwrap()
            .source_binding = true;
        self.edge(variable, None, VariableEdgeKind::Binding(kind));
    }
}

#[derive(Default)]
struct VariableReferences {
    variables: BTreeSet<u32>,
}

impl VariableReferences {
    fn expression(expression: &SemanticExpression) -> BTreeSet<u32> {
        let mut collector = Self::default();
        collector.visit_expression(expression);
        collector.variables
    }

    fn predicate(predicate: &SemanticPredicate) -> BTreeSet<u32> {
        let mut collector = Self::default();
        collector.visit_predicate(predicate);
        collector.variables
    }

    fn predicate_roots(predicate: &SemanticPredicate) -> BTreeSet<u32> {
        let mut variables = BTreeSet::new();
        let mut pending = vec![predicate];
        while let Some(predicate) = pending.pop() {
            match predicate {
                SemanticPredicate::Test(operation) => {
                    variables.extend(
                        operation
                            .operands()
                            .iter()
                            .filter_map(Self::expression_root),
                    );
                }
                SemanticPredicate::Not(inner) => pending.push(inner),
                SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                    pending.extend(terms)
                }
                SemanticPredicate::True | SemanticPredicate::False => {}
            }
        }
        variables
    }

    fn expression_root(expression: &SemanticExpression) -> Option<u32> {
        match expression {
            SemanticExpression::Register(register) => register.code_var,
            SemanticExpression::Operation(operation) => {
                operation.result.as_ref().and_then(|result| result.code_var)
            }
            SemanticExpression::Literal(_) | SemanticExpression::Select { .. } => None,
        }
    }
}

impl SemanticVisitor for VariableReferences {
    fn visit_register(&mut self, register: &RegisterArg) {
        if let Some(variable) = register.code_var {
            self.variables.insert(variable);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn graph_with_edge(ty: ArgType, kind: VariableEdgeKind) -> VariableSemanticGraph {
        VariableSemanticGraph {
            variables: BTreeMap::from([(
                1,
                VariableNode {
                    identity: 1,
                    ty,
                    definitions: 1,
                    uses: 1,
                    source_binding: true,
                },
            )]),
            operations: BTreeMap::new(),
            edges: vec![VariableEdge {
                variable: 1,
                operation: None,
                kind,
            }],
        }
    }

    #[test]
    fn array_index_requires_an_integral_variable() {
        let reference = graph_with_edge(ArgType::unknown_object(), VariableEdgeKind::ArrayIndex);
        let index = graph_with_edge(ArgType::INT, VariableEdgeKind::ArrayIndex);

        let analysis = StructuralVariableRoleAnalysis;
        assert_eq!(
            analysis.analyze(&reference).score(1, VariableRole::Index),
            0
        );
        assert_eq!(analysis.analyze(&index).score(1, VariableRole::Index), 100);
    }

    #[test]
    fn predicate_role_requires_a_boolean_variable() {
        let integer = graph_with_edge(ArgType::INT, VariableEdgeKind::Predicate);
        let boolean = graph_with_edge(ArgType::BOOLEAN, VariableEdgeKind::Predicate);

        let analysis = StructuralVariableRoleAnalysis;
        assert_eq!(
            analysis.analyze(&integer).score(1, VariableRole::Condition),
            0
        );
        assert_eq!(
            analysis.analyze(&boolean).score(1, VariableRole::Condition),
            90
        );
    }
}
