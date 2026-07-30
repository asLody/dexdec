//! Kotlin expression syntax proven over recovered value trees.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    analysis::SourceTypeEnvironment, ArgType, ArithOp, CmpBias, IfOp, InsnType, MemberReference,
    PrimitiveType, SemanticExpression, SemanticExpressionTransform, SemanticFolder,
    SemanticInstructions, SemanticNode, SemanticOperation, SemanticPredicate, SemanticStatement,
    SemanticStatementKind, SemanticVisitor, StringBuilderProtocol, UnaryOp,
};

use super::primitives::PrimitiveOperationDomain;

trait ExpressionProof {
    fn prove(
        &self,
        expression: &SemanticOperation,
        facts: &ExpressionFacts<'_>,
    ) -> Option<ExpressionFact>;
}

struct ExpressionFacts<'a> {
    types: &'a SourceTypeEnvironment,
    boolean_variables: &'a BTreeSet<u32>,
}

impl ExpressionFacts<'_> {
    fn intrinsic_boolean_operation(operation: &SemanticOperation) -> bool {
        operation
            .result
            .as_ref()
            .is_some_and(|result| result.ty == ArgType::BOOLEAN)
            || operation
                .payload
                .reference
                .as_ref()
                .is_some_and(|reference| match reference {
                    MemberReference::Method(method) => {
                        method.descriptor.return_type == ArgType::BOOLEAN
                    }
                    MemberReference::Field(field) => field.field_type == ArgType::BOOLEAN,
                })
            || operation.insn_type == InsnType::InstanceOf
    }

    fn is_boolean(&self, expression: &SemanticExpression) -> bool {
        match expression {
            SemanticExpression::Register(register) => {
                register
                    .code_var
                    .is_some_and(|variable| self.boolean_variables.contains(&variable))
                    || register.ty == ArgType::BOOLEAN
                    || self.types.register_type(register).ok() == Some(&ArgType::BOOLEAN)
            }
            SemanticExpression::Literal(literal) => literal.ty == ArgType::BOOLEAN,
            SemanticExpression::Operation(operation) => {
                if operation
                    .result
                    .as_ref()
                    .and_then(|result| result.code_var)
                    .is_some_and(|variable| self.boolean_variables.contains(&variable))
                    || operation
                        .result
                        .as_ref()
                        .is_some_and(|result| result.ty == ArgType::BOOLEAN)
                    || operation.result.as_ref().is_some_and(|result| {
                        self.types.register_type(result).ok() == Some(&ArgType::BOOLEAN)
                    })
                    || Self::intrinsic_boolean_operation(operation)
                {
                    return true;
                }
                if matches!(operation.insn_type, InsnType::Const | InsnType::Move)
                    && operation.operands().len() == 1
                {
                    return self.is_boolean(&operation.operands()[0]);
                }
                operation.insn_type == InsnType::Arith
                    && matches!(
                        operation.payload.arith_op,
                        Some(ArithOp::And | ArithOp::Or | ArithOp::Xor)
                    )
                    && operation
                        .operands()
                        .iter()
                        .all(|operand| self.is_boolean(operand))
            }
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                let materialized = when_true
                    .literal_value()
                    .zip(when_false.literal_value())
                    .is_some_and(|(when_true, when_false)| {
                        matches!(when_true, 0 | 1)
                            && matches!(when_false, 0 | 1)
                            && when_true != when_false
                    });
                materialized || (self.is_boolean(when_true) && self.is_boolean(when_false))
            }
        }
    }
}

enum ExpressionFact {
    BooleanNot(SemanticExpression),
    Comparison {
        operator: IfOp,
        left: SemanticExpression,
        right: SemanticExpression,
    },
    Operands(Vec<SemanticExpression>),
    StringConcat(Vec<SemanticExpression>),
}

impl ExpressionFact {
    fn rewrite(self, source: &SemanticOperation) -> Option<SemanticOperation> {
        match self {
            Self::BooleanNot(operand) => {
                let mut negation = source.clone().rewrite_kind(InsnType::Not, vec![operand]);
                negation.set_result_type(ArgType::BOOLEAN).then_some(())?;
                negation.set_unary_operator(UnaryOp::Not);
                Some(negation)
            }
            Self::Comparison {
                operator,
                left,
                right,
            } => {
                let mut comparison = source.clone().rewrite_kind(InsnType::If, vec![left, right]);
                comparison.set_comparison_operator(operator);
                Some(comparison)
            }
            Self::Operands(operands) => {
                Some(source.clone().rewrite_kind(source.insn_type, operands))
            }
            Self::StringConcat(terms) => source
                .result
                .as_ref()
                .map(|_| source.clone().rewrite_kind(InsnType::StringConcat, terms)),
        }
    }
}

pub(super) struct ExpressionSyntax {
    proofs: Vec<Box<dyn ExpressionProof>>,
}

impl Default for ExpressionSyntax {
    fn default() -> Self {
        Self {
            proofs: vec![
                Box::new(CmpConditionProof),
                Box::new(BooleanXorProof),
                Box::new(NumericDomainNormalizationProof),
                Box::new(StringConcatProof),
            ],
        }
    }
}

struct CmpConditionProof;

impl ExpressionProof for CmpConditionProof {
    fn prove(
        &self,
        expression: &SemanticOperation,
        _facts: &ExpressionFacts<'_>,
    ) -> Option<ExpressionFact> {
        Self::analyze(expression)
    }
}

impl CmpConditionProof {
    fn analyze(condition: &SemanticOperation) -> Option<ExpressionFact> {
        (condition.insn_type == InsnType::If).then_some(())?;
        let operator = condition.payload.if_op?;
        let [left, right] = condition.operands() else {
            return None;
        };
        let (comparison, operator) = if right.literal_value() == Some(0) {
            (left.as_operation()?, operator)
        } else if left.literal_value() == Some(0) {
            (right.as_operation()?, Self::swap(operator))
        } else {
            return None;
        };
        (comparison.insn_type == InsnType::Cmp).then_some(())?;
        let [left, right] = comparison.operands() else {
            return None;
        };
        let operator = Self::recovered_operator(comparison.payload.cmp_bias?, operator)?;
        Some(ExpressionFact::Comparison {
            operator,
            left: left.clone(),
            right: right.clone(),
        })
    }

    fn swap(operator: IfOp) -> IfOp {
        match operator {
            IfOp::Eq => IfOp::Eq,
            IfOp::Ne => IfOp::Ne,
            IfOp::Lt => IfOp::Gt,
            IfOp::Ge => IfOp::Le,
            IfOp::Gt => IfOp::Lt,
            IfOp::Le => IfOp::Ge,
        }
    }

    fn recovered_operator(bias: CmpBias, operator: IfOp) -> Option<IfOp> {
        match (bias, operator) {
            (CmpBias::None, operator)
            | (CmpBias::Lt | CmpBias::Gt, operator @ (IfOp::Eq | IfOp::Ne)) => Some(operator),
            (CmpBias::Gt, operator @ (IfOp::Lt | IfOp::Le))
            | (CmpBias::Lt, operator @ (IfOp::Ge | IfOp::Gt)) => Some(operator),
            (CmpBias::Lt, IfOp::Lt | IfOp::Le) | (CmpBias::Gt, IfOp::Ge | IfOp::Gt) => None,
        }
    }
}

impl ExpressionSyntax {
    pub(super) fn apply(
        &self,
        root: &mut SemanticNode,
        types: &SourceTypeEnvironment,
    ) -> Result<ExpressionRecovery, crate::ir::SemanticFoldError> {
        let boolean_variables = BooleanValueAnalysis::analyze(root, types);
        let mut rewriter = ExpressionRewriter {
            proofs: &self.proofs,
            types,
            changed: false,
            boolean_variables,
        };
        SemanticInstructions::transform(root, &mut rewriter)?;
        let mut identities = BooleanIdentityEliminator {
            types,
            proven: &rewriter.boolean_variables,
            changed: false,
        };
        let body = std::mem::replace(root, SemanticNode::Empty);
        *root = identities.fold_node(body)?;
        Ok(ExpressionRecovery {
            changed: rewriter.changed || identities.changed,
            boolean_variables: rewriter.boolean_variables,
        })
    }
}

struct BooleanIdentityEliminator<'a> {
    types: &'a SourceTypeEnvironment,
    proven: &'a BTreeSet<u32>,
    changed: bool,
}

impl BooleanIdentityEliminator<'_> {
    fn redundant_definition(
        &self,
        result: &crate::ir::RegisterArg,
        value: &SemanticExpression,
    ) -> bool {
        let Some(variable) = result.code_var else {
            return false;
        };
        if !self.proven.contains(&variable)
            && self.types.register_type(result).ok() != Some(&ArgType::BOOLEAN)
        {
            return false;
        }
        BooleanIdentityProof::normalized_variable(value) == Some(variable)
    }
}

impl SemanticFolder for BooleanIdentityEliminator<'_> {
    type Error = crate::ir::SemanticFoldError;

    fn finish_node(&mut self, mut node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        let SemanticNode::BasicBlock(block) = &mut node else {
            return Ok(node);
        };
        let before = block.statements.len();
        block.statements.retain(|statement| {
            let SemanticStatementKind::Definition { result, value, .. } = &statement.kind else {
                return true;
            };
            !self.redundant_definition(result, value)
        });
        self.changed |= block.statements.len() != before;
        Ok(node)
    }
}

struct BooleanIdentityProof;

impl BooleanIdentityProof {
    fn normalized_variable(value: &SemanticExpression) -> Option<u32> {
        let SemanticExpression::Select {
            condition,
            when_true,
            when_false,
        } = Self::canonical(value)
        else {
            return None;
        };
        let (variable, predicate_matches_source) = Self::predicate_variable(condition)?;
        let true_value = Self::boolean_literal(when_true)?;
        let false_value = Self::boolean_literal(when_false)?;
        (true_value != false_value
            && predicate_matches_source == true_value
            && predicate_matches_source != false_value)
            .then_some(variable)
    }

    fn predicate_variable(predicate: &SemanticPredicate) -> Option<(u32, bool)> {
        match predicate {
            SemanticPredicate::Test(test) => Self::test_variable(test),
            SemanticPredicate::Not(inner) => {
                let (variable, matches_source) = Self::predicate_variable(inner)?;
                Some((variable, !matches_source))
            }
            SemanticPredicate::True
            | SemanticPredicate::False
            | SemanticPredicate::And(_)
            | SemanticPredicate::Or(_) => None,
        }
    }

    fn test_variable(test: &SemanticOperation) -> Option<(u32, bool)> {
        (test.insn_type == InsnType::If).then_some(())?;
        let matches_source = match test.payload.if_op? {
            IfOp::Ne => true,
            IfOp::Eq => false,
            IfOp::Lt | IfOp::Ge | IfOp::Gt | IfOp::Le => return None,
        };
        let [left, right] = test.operands() else {
            return None;
        };
        let value = if Self::boolean_literal(right) == Some(false) {
            left
        } else if Self::boolean_literal(left) == Some(false) {
            right
        } else {
            return None;
        };
        Some((Self::direct_variable(value)?, matches_source))
    }

    fn direct_variable(value: &SemanticExpression) -> Option<u32> {
        match Self::canonical(value) {
            SemanticExpression::Register(register) => register.code_var,
            SemanticExpression::Literal(_)
            | SemanticExpression::Operation(_)
            | SemanticExpression::Select { .. } => None,
        }
    }

    fn boolean_literal(value: &SemanticExpression) -> Option<bool> {
        match Self::canonical(value) {
            SemanticExpression::Literal(literal) => match literal.value {
                0 => Some(false),
                1 => Some(true),
                _ => None,
            },
            SemanticExpression::Register(_)
            | SemanticExpression::Operation(_)
            | SemanticExpression::Select { .. } => None,
        }
    }

    fn canonical(mut value: &SemanticExpression) -> &SemanticExpression {
        while let SemanticExpression::Operation(operation) = value {
            if !matches!(operation.insn_type, InsnType::Const | InsnType::Move)
                || operation.operands().len() != 1
            {
                break;
            }
            value = &operation.operands()[0];
        }
        value
    }
}

#[derive(Default)]
struct BooleanValueAnalysis<'a> {
    types: Option<&'a SourceTypeEnvironment>,
    definitions: BTreeMap<u32, Vec<BooleanFormula>>,
    result_types: BTreeMap<u32, ArgType>,
    predicate_uses: BTreeSet<u32>,
    value_uses: BTreeSet<u32>,
    consumers: BTreeMap<u32, BTreeSet<u32>>,
}

#[derive(Default)]
struct BooleanFormula {
    dependencies: BTreeSet<u32>,
    valid: bool,
}

impl BooleanFormula {
    fn valid() -> Self {
        Self {
            dependencies: BTreeSet::new(),
            valid: true,
        }
    }

    fn dependency(variable: u32) -> Self {
        Self {
            dependencies: BTreeSet::from([variable]),
            valid: true,
        }
    }

    fn merge(left: Self, right: Self) -> Self {
        let mut dependencies = left.dependencies;
        dependencies.extend(right.dependencies);
        Self {
            dependencies,
            valid: left.valid && right.valid,
        }
    }
}

impl<'a> BooleanValueAnalysis<'a> {
    fn analyze(root: &SemanticNode, types: &'a SourceTypeEnvironment) -> BTreeSet<u32> {
        let mut analysis = Self {
            types: Some(types),
            ..Self::default()
        };
        analysis.visit_node(root);
        analysis.solve()
    }

    fn types(&self) -> &SourceTypeEnvironment {
        self.types.expect("boolean value analysis requires types")
    }

    fn solve(self) -> BTreeSet<u32> {
        let mut candidates = self
            .definitions
            .iter()
            .filter(|(variable, definitions)| {
                self.result_types.get(*variable) == Some(&ArgType::INT)
                    && !self.value_uses.contains(*variable)
                    && !definitions.is_empty()
                    && definitions.iter().all(|definition| definition.valid)
            })
            .map(|(variable, _)| *variable)
            .collect::<BTreeSet<_>>();
        loop {
            let retained = candidates
                .iter()
                .copied()
                .filter(|variable| {
                    let dependencies_are_boolean = self
                        .definitions
                        .get(variable)
                        .into_iter()
                        .flatten()
                        .flat_map(|definition| &definition.dependencies)
                        .all(|dependency| {
                            dependency == variable || candidates.contains(dependency)
                        });
                    let consumers_are_boolean = self
                        .consumers
                        .get(variable)
                        .into_iter()
                        .flatten()
                        .all(|consumer| {
                            candidates.contains(consumer)
                                || self.result_types.get(consumer) == Some(&ArgType::BOOLEAN)
                        });
                    dependencies_are_boolean && consumers_are_boolean
                })
                .collect::<BTreeSet<_>>();
            if retained == candidates {
                break;
            }
            candidates = retained;
        }
        let mut proven = BTreeSet::new();
        let mut pending = self
            .predicate_uses
            .intersection(&candidates)
            .copied()
            .collect::<Vec<_>>();
        pending.extend(
            self.definitions
                .iter()
                .filter(|(variable, _)| self.result_types.get(*variable) == Some(&ArgType::BOOLEAN))
                .flat_map(|(_, definitions)| definitions)
                .filter(|definition| definition.valid)
                .flat_map(|definition| &definition.dependencies)
                .filter(|dependency| candidates.contains(dependency))
                .copied(),
        );
        while let Some(variable) = pending.pop() {
            if !proven.insert(variable) {
                continue;
            }
            pending.extend(
                self.definitions
                    .get(&variable)
                    .into_iter()
                    .flatten()
                    .flat_map(|definition| &definition.dependencies)
                    .filter(|dependency| candidates.contains(dependency))
                    .copied(),
            );
        }
        proven
    }

    fn record_definition(&mut self, result: &crate::ir::RegisterArg, value: &SemanticExpression) {
        let Some(variable) = result.code_var else {
            return;
        };
        let ty = self
            .types()
            .register_type(result)
            .cloned()
            .unwrap_or_else(|_| result.ty.clone());
        self.result_types.entry(variable).or_insert(ty);
        let formula = self.formula(value);
        self.record_select_predicates(value);
        if formula.valid {
            for dependency in &formula.dependencies {
                self.consumers
                    .entry(*dependency)
                    .or_default()
                    .insert(variable);
            }
        } else {
            self.record_value_expression(value);
        }
        self.definitions.entry(variable).or_default().push(formula);
    }

    fn formula(&self, value: &SemanticExpression) -> BooleanFormula {
        match value {
            SemanticExpression::Literal(literal) => {
                if matches!(literal.value, 0 | 1) {
                    BooleanFormula::valid()
                } else {
                    BooleanFormula::default()
                }
            }
            SemanticExpression::Register(register) => {
                match self.types().register_type(register).ok() {
                    Some(&ArgType::Primitive(PrimitiveType::Boolean)) => BooleanFormula::valid(),
                    Some(&ArgType::Primitive(PrimitiveType::Int)) => register
                        .code_var
                        .map(BooleanFormula::dependency)
                        .unwrap_or_default(),
                    _ => BooleanFormula::default(),
                }
            }
            SemanticExpression::Operation(operation)
                if matches!(operation.insn_type, InsnType::Const | InsnType::Move)
                    && operation.operands().len() == 1 =>
            {
                self.formula(&operation.operands()[0])
            }
            SemanticExpression::Operation(operation)
                if operation.insn_type == InsnType::Arith
                    && matches!(
                        operation.payload.arith_op,
                        Some(ArithOp::And | ArithOp::Or | ArithOp::Xor)
                    ) =>
            {
                let [left, right] = operation.operands() else {
                    return BooleanFormula::default();
                };
                BooleanFormula::merge(self.formula(left), self.formula(right))
            }
            SemanticExpression::Operation(operation)
                if ExpressionFacts::intrinsic_boolean_operation(operation) =>
            {
                BooleanFormula::valid()
            }
            SemanticExpression::Operation(operation)
                if self
                    .operation_type(operation)
                    .is_some_and(|ty| ty == &ArgType::BOOLEAN) =>
            {
                BooleanFormula::valid()
            }
            SemanticExpression::Operation(_) => BooleanFormula::default(),
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => BooleanFormula::merge(self.formula(when_true), self.formula(when_false)),
        }
    }

    fn operation_type<'b>(&'b self, operation: &'b SemanticOperation) -> Option<&'b ArgType> {
        operation
            .result
            .as_ref()
            .and_then(|result| self.types().register_type(result).ok())
    }

    fn record_select_predicates(&mut self, value: &SemanticExpression) {
        let mut pending = vec![value];
        while let Some(value) = pending.pop() {
            match value {
                SemanticExpression::Select {
                    condition,
                    when_true,
                    when_false,
                } => {
                    self.record_predicate(condition);
                    pending.push(when_false);
                    pending.push(when_true);
                }
                SemanticExpression::Operation(operation) => {
                    pending.extend(operation.operands());
                    pending.extend(operation.compound_target());
                }
                SemanticExpression::Register(_) | SemanticExpression::Literal(_) => {}
            }
        }
    }

    fn record_predicate(&mut self, predicate: &SemanticPredicate) {
        let mut pending = vec![predicate];
        while let Some(predicate) = pending.pop() {
            match predicate {
                SemanticPredicate::Test(test) => self.record_test(test),
                SemanticPredicate::Not(inner) => pending.push(inner),
                SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                    pending.extend(terms)
                }
                SemanticPredicate::True | SemanticPredicate::False => {}
            }
        }
    }

    fn record_test(&mut self, test: &SemanticOperation) {
        let operands = test.operands();
        if test.insn_type == InsnType::If && matches!(test.payload.if_op, Some(IfOp::Eq | IfOp::Ne))
        {
            if let [left, right] = operands {
                let left = self.formula(left);
                let right = self.formula(right);
                if left.valid && right.valid {
                    self.predicate_uses.extend(left.dependencies);
                    self.predicate_uses.extend(right.dependencies);
                    for operand in operands {
                        self.record_select_predicates(operand);
                    }
                    return;
                }
            }
        }
        let boolean_operand = (test.insn_type == InsnType::If
            && matches!(test.payload.if_op, Some(IfOp::Eq | IfOp::Ne)))
        .then(|| match operands {
            [value, zero] if zero.literal_value() == Some(0) => Self::direct_variable(value),
            [zero, value] if zero.literal_value() == Some(0) => Self::direct_variable(value),
            _ => None,
        })
        .flatten();
        if let Some(variable) = boolean_operand {
            self.predicate_uses.insert(variable);
            for operand in operands {
                if Self::direct_variable(operand) != Some(variable) {
                    self.record_value_expression(operand);
                }
            }
            return;
        }
        for operand in operands {
            self.record_value_expression(operand);
        }
        if let Some(target) = test.compound_target() {
            self.record_value_expression(target);
        }
    }

    fn direct_variable(value: &SemanticExpression) -> Option<u32> {
        let mut value = value;
        loop {
            match value {
                SemanticExpression::Register(register) => return register.code_var,
                SemanticExpression::Operation(operation)
                    if matches!(operation.insn_type, InsnType::Const | InsnType::Move)
                        && operation.operands().len() == 1 =>
                {
                    value = &operation.operands()[0];
                }
                SemanticExpression::Literal(_)
                | SemanticExpression::Operation(_)
                | SemanticExpression::Select { .. } => return None,
            }
        }
    }

    fn record_value_expression(&mut self, value: &SemanticExpression) {
        let mut pending = vec![value];
        while let Some(value) = pending.pop() {
            match value {
                SemanticExpression::Register(register) => {
                    self.value_uses.extend(register.code_var);
                }
                SemanticExpression::Operation(operation) => {
                    pending.extend(operation.operands());
                    pending.extend(operation.compound_target());
                }
                SemanticExpression::Select {
                    condition,
                    when_true,
                    when_false,
                } => {
                    self.record_predicate(condition);
                    pending.push(when_false);
                    pending.push(when_true);
                }
                SemanticExpression::Literal(_) => {}
            }
        }
    }
}

impl SemanticVisitor for BooleanValueAnalysis<'_> {
    fn visit_statement(&mut self, statement: &SemanticStatement) {
        match &statement.kind {
            SemanticStatementKind::Definition { result, value, .. } => {
                self.record_definition(result, value)
            }
            SemanticStatementKind::Instruction(operation) => {
                if let Some(result) = &operation.result {
                    self.record_definition(
                        result,
                        &SemanticExpression::Operation(Box::new(operation.clone())),
                    );
                } else {
                    for operand in operation.operands() {
                        self.record_value_expression(operand);
                    }
                }
                if let Some(target) = operation.compound_target() {
                    self.record_value_expression(target);
                }
            }
        }
    }

    fn visit_predicate(&mut self, predicate: &SemanticPredicate) {
        self.record_predicate(predicate);
    }

    fn visit_expression(&mut self, expression: &SemanticExpression) {
        self.record_value_expression(expression);
    }
}

pub(super) struct ExpressionRecovery {
    #[allow(dead_code)]
    pub(super) changed: bool,
    pub(super) boolean_variables: std::collections::BTreeSet<u32>,
}

struct ExpressionRewriter<'a> {
    proofs: &'a [Box<dyn ExpressionProof>],
    types: &'a SourceTypeEnvironment,
    changed: bool,
    boolean_variables: std::collections::BTreeSet<u32>,
}

impl SemanticExpressionTransform for ExpressionRewriter<'_> {
    fn transform_operation(&mut self, instruction: SemanticOperation) -> SemanticExpression {
        let facts = ExpressionFacts {
            types: self.types,
            boolean_variables: &self.boolean_variables,
        };
        for proof in self.proofs {
            let Some(fact) = proof.prove(&instruction, &facts) else {
                continue;
            };
            let Some(replacement) = fact.rewrite(&instruction) else {
                continue;
            };
            self.changed = true;
            if replacement.insn_type == InsnType::Not {
                self.boolean_variables.extend(
                    replacement
                        .result
                        .as_ref()
                        .and_then(|result| result.code_var),
                );
            }
            return SemanticExpression::Operation(Box::new(replacement));
        }
        SemanticExpression::Operation(Box::new(instruction))
    }
}

struct BooleanXorProof;

impl ExpressionProof for BooleanXorProof {
    fn prove(
        &self,
        expression: &SemanticOperation,
        facts: &ExpressionFacts<'_>,
    ) -> Option<ExpressionFact> {
        (expression.insn_type == InsnType::Arith
            && expression.payload.arith_op == Some(ArithOp::Xor))
        .then_some(())?;
        expression.result.as_ref()?;
        let [left, right] = expression.operands() else {
            return None;
        };
        Self::operand(left, right, facts)
            .or_else(|| Self::operand(right, left, facts))
            .map(ExpressionFact::BooleanNot)
    }
}

impl BooleanXorProof {
    fn operand(
        literal: &SemanticExpression,
        value: &SemanticExpression,
        facts: &ExpressionFacts<'_>,
    ) -> Option<SemanticExpression> {
        (literal.literal_value()? == 1 && facts.is_boolean(value)).then(|| value.clone())
    }
}

/// Normalizes explicit widening conversions already represented by the
/// enclosing DEX arithmetic domain.
///
/// Lowering later materializes the conversions Kotlin requires at the typed
/// expression boundary. Here we retain the minimum IR needed to prove the
/// operation domain, choosing the largest removable cast subset whose result
/// still equals that domain.
struct NumericDomainNormalizationProof;

impl ExpressionProof for NumericDomainNormalizationProof {
    fn prove(
        &self,
        expression: &SemanticOperation,
        facts: &ExpressionFacts<'_>,
    ) -> Option<ExpressionFact> {
        let types = facts.types;
        (matches!(expression.insn_type, InsnType::Arith | InsnType::If)
            && !(expression.insn_type == InsnType::Arith
                && matches!(
                    expression.payload.arith_op,
                    Some(ArithOp::Shl | ArithOp::Shr | ArithOp::Ushr)
                )))
        .then_some(())?;
        let [left, right] = expression.operands() else {
            return None;
        };
        let target = if expression.insn_type == InsnType::Arith {
            PrimitiveOperationDomain::numeric(Self::operation_type(expression, types)?)?
        } else {
            PrimitiveOperationDomain::binary_numeric_promotion(
                Self::expression_type(left, types)?,
                Self::expression_type(right, types)?,
            )?
        };

        let operands = [left, right];
        let removable = operands.map(|operand| Self::widening_cast(operand, types));
        let mut selected = None::<(u32, u32)>;
        for mask in 1u32..4 {
            if (0..2).any(|index| mask & (1 << index) != 0 && removable[index].is_none()) {
                continue;
            }
            let promoted = PrimitiveOperationDomain::binary_numeric_promotion(
                Self::operand_type(operands[0], removable[0], mask & 1 != 0, types)?,
                Self::operand_type(operands[1], removable[1], mask & 2 != 0, types)?,
            )?;
            if promoted != target {
                continue;
            }
            let removed = mask.count_ones();
            if selected.is_none_or(|(count, current)| {
                removed > count || (removed == count && mask < current)
            }) {
                selected = Some((removed, mask));
            }
        }
        let (_, mask) = selected?;
        Some(ExpressionFact::Operands(
            operands
                .into_iter()
                .enumerate()
                .map(|(index, operand)| {
                    if mask & (1 << index) == 0 {
                        return operand.clone();
                    }
                    removable[index]
                        .and_then(|cast| cast.operands().first())
                        .cloned()
                        .unwrap_or_else(|| operand.clone())
                })
                .collect(),
        ))
    }
}

impl NumericDomainNormalizationProof {
    fn operation_type(
        operation: &SemanticOperation,
        types: &SourceTypeEnvironment,
    ) -> Option<PrimitiveType> {
        operation
            .result
            .as_ref()
            .and_then(|result| types.register_type(result).ok())
            .or_else(|| operation.result.as_ref().map(|result| &result.ty))
            .and_then(ArgType::as_primitive)
    }

    fn expression_type(
        expression: &SemanticExpression,
        types: &SourceTypeEnvironment,
    ) -> Option<PrimitiveType> {
        match expression {
            SemanticExpression::Register(register) => types
                .register_type(register)
                .ok()
                .or(Some(&register.ty))
                .and_then(ArgType::as_primitive),
            SemanticExpression::Literal(literal) => literal.ty.as_primitive(),
            SemanticExpression::Operation(operation) => operation
                .conversion_type()
                .or_else(|| {
                    operation
                        .result
                        .as_ref()
                        .and_then(|result| types.register_type(result).ok())
                })
                .or_else(|| operation.result.as_ref().map(|result| &result.ty))
                .and_then(ArgType::as_primitive),
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                let left = Self::expression_type(when_true, types)?;
                (Self::expression_type(when_false, types)? == left).then_some(left)
            }
        }
    }

    fn widening_cast<'a>(
        expression: &'a SemanticExpression,
        types: &SourceTypeEnvironment,
    ) -> Option<&'a SemanticOperation> {
        let cast = expression.as_operation()?;
        (cast.insn_type == InsnType::Cast && cast.operands().len() == 1).then_some(())?;
        let source = Self::expression_type(&cast.operands()[0], types)?;
        let target = cast.conversion_type()?.as_primitive()?;
        PrimitiveOperationDomain::is_widening(source, target).then_some(cast)
    }

    fn operand_type(
        original: &SemanticExpression,
        cast: Option<&SemanticOperation>,
        remove: bool,
        types: &SourceTypeEnvironment,
    ) -> Option<PrimitiveType> {
        if remove {
            Self::expression_type(cast?.operands().first()?, types)
        } else {
            Self::expression_type(original, types)
        }
    }
}

struct StringConcatProof;

impl ExpressionProof for StringConcatProof {
    fn prove(
        &self,
        expression: &SemanticOperation,
        _facts: &ExpressionFacts<'_>,
    ) -> Option<ExpressionFact> {
        let terms = StringBuilderProtocol::terms(expression)?;
        (terms.len() >= 2).then_some(ExpressionFact::StringConcat(terms))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::{BooleanFormula, BooleanValueAnalysis, CmpConditionProof};
    use crate::ir::{ArgType, CmpBias, IfOp};

    #[test]
    fn cmp_rewrite_preserves_nan_semantics() {
        let exact = [
            (CmpBias::Lt, IfOp::Eq),
            (CmpBias::Lt, IfOp::Ne),
            (CmpBias::Lt, IfOp::Ge),
            (CmpBias::Lt, IfOp::Gt),
            (CmpBias::Gt, IfOp::Eq),
            (CmpBias::Gt, IfOp::Ne),
            (CmpBias::Gt, IfOp::Lt),
            (CmpBias::Gt, IfOp::Le),
        ];
        for (bias, operator) in exact {
            assert_eq!(
                CmpConditionProof::recovered_operator(bias, operator),
                Some(operator)
            );
        }

        let inexact = [
            (CmpBias::Lt, IfOp::Lt),
            (CmpBias::Lt, IfOp::Le),
            (CmpBias::Gt, IfOp::Ge),
            (CmpBias::Gt, IfOp::Gt),
        ];
        for (bias, operator) in inexact {
            assert_eq!(CmpConditionProof::recovered_operator(bias, operator), None);
        }
    }

    #[test]
    fn known_boolean_result_proves_integer_dependencies() {
        let definitions = BTreeMap::from([
            (16, vec![BooleanFormula::valid()]),
            (20, vec![BooleanFormula::valid()]),
            (
                18,
                vec![BooleanFormula::merge(
                    BooleanFormula::dependency(16),
                    BooleanFormula::dependency(20),
                )],
            ),
        ]);
        let analysis = BooleanValueAnalysis {
            definitions,
            result_types: BTreeMap::from([
                (16, ArgType::INT),
                (18, ArgType::BOOLEAN),
                (20, ArgType::INT),
            ]),
            predicate_uses: BTreeSet::from([18]),
            consumers: BTreeMap::from([(16, BTreeSet::from([18])), (20, BTreeSet::from([18]))]),
            ..BooleanValueAnalysis::default()
        };

        assert_eq!(analysis.solve(), BTreeSet::from([16, 20]));
    }
}
