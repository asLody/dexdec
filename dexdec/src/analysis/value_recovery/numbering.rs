//! Global value numbering over pure semantic expressions.

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    sync::Arc,
};

use crate::ir::analysis::SsaVar;
use crate::ir::{
    ArgType, ArithOp, CmpBias, InsnArg, InsnType, RegisterArg, SemanticExpression,
    SemanticOperation, UnaryOp, Utf16String,
};

use super::domain::{ControlDomain, DomainLogic};
use super::flow::{DefinitionFact, ValueIdentity};
use super::ValueRecoveryError;

pub(super) trait ValueAvailability {
    fn supports(
        &self,
        source: crate::ir::analysis::SemanticFlowPoint,
        target: crate::ir::analysis::SemanticFlowPoint,
    ) -> bool;

    fn unchanged(
        &self,
        value: SsaVar,
        source: crate::ir::analysis::SemanticFlowPoint,
        target: crate::ir::analysis::SemanticFlowPoint,
    ) -> bool;
}

#[derive(Debug, Clone)]
pub(super) struct SyntheticUse {
    pub(super) representative: SsaVar,
    pub(super) eliminated: SsaVar,
}

#[derive(Debug, Default)]
pub(super) struct ValueNumberingResult {
    pub(super) replacements: BTreeMap<SsaVar, InsnArg>,
    pub(super) synthetic_uses: Vec<SyntheticUse>,
}

pub(super) struct ValueNumbering<'a> {
    identity: ValueIdentity,
    logic: &'a DomainLogic,
    canonical_values: &'a BTreeMap<SsaVar, InsnArg>,
    availability: Option<&'a dyn ValueAvailability>,
    aliases: BTreeMap<SsaVar, SsaVar>,
    classes: HashMap<ValueExpression, Vec<NumberedDefinition>>,
}

impl<'a> ValueNumbering<'a> {
    pub(super) fn analyze(
        identity: ValueIdentity,
        logic: &'a DomainLogic,
        definitions: impl IntoIterator<Item = &'a DefinitionFact<'a>>,
        canonical_values: &'a BTreeMap<SsaVar, InsnArg>,
        availability: Option<&'a dyn ValueAvailability>,
    ) -> Result<ValueNumberingResult, ValueRecoveryError> {
        let mut definitions = definitions.into_iter().collect::<Vec<_>>();
        definitions.sort_by_key(|definition| definition.event);
        let mut numbering = Self {
            identity,
            logic,
            canonical_values,
            availability,
            aliases: BTreeMap::new(),
            classes: HashMap::new(),
        };
        let mut result = ValueNumberingResult::default();
        for definition in definitions {
            numbering.record_alias(definition);
            let Some(operation) = definition.operation() else {
                continue;
            };
            if matches!(
                operation.insn_type,
                InsnType::Const | InsnType::ConstStr | InsnType::Move
            ) {
                continue;
            }
            let Some(expression) = numbering.expression(operation) else {
                continue;
            };
            let mut representative = None;
            for candidate in numbering
                .classes
                .get(&expression)
                .into_iter()
                .flatten()
                .rev()
            {
                if numbering.available(candidate, definition, &expression)? {
                    representative = Some(candidate.clone());
                    break;
                }
            }
            if let Some(representative) = representative {
                result.replacements.insert(
                    definition.key,
                    InsnArg::Reg(representative.register.clone()),
                );
                result.synthetic_uses.push(SyntheticUse {
                    representative: representative.key,
                    eliminated: definition.key,
                });
                numbering.aliases.insert(definition.key, representative.key);
                continue;
            }
            numbering
                .classes
                .entry(expression)
                .or_default()
                .push(NumberedDefinition {
                    key: definition.key,
                    register: (*definition.result).clone(),
                    domain: definition.domain,
                    scope: definition.scope.clone(),
                    event: definition.event,
                    repetitive: definition.repetitive,
                    site: definition.site,
                });
        }
        Ok(result)
    }

    fn record_alias(&mut self, definition: &DefinitionFact) {
        let Some(operation) = definition.operation() else {
            return;
        };
        if operation.insn_type != InsnType::Move {
            return;
        }
        let Some(source) = operation
            .operands()
            .first()
            .and_then(SemanticExpression::as_register)
            .and_then(|register| self.key(register))
        else {
            return;
        };
        let source = self.root(source);
        self.aliases.insert(definition.key, source);
    }

    fn available(
        &self,
        candidate: &NumberedDefinition,
        current: &DefinitionFact,
        expression: &ValueExpression,
    ) -> Result<bool, ValueRecoveryError> {
        if !(candidate.event < current.event
            && current.scope.starts_with(&candidate.scope)
            && (!candidate.repetitive || current.repetitive)
            && self.logic.implies(current.domain, candidate.domain)?)
        {
            return Ok(false);
        }
        if self.identity == ValueIdentity::Ssa {
            return Ok(true);
        }
        let Some(availability) = self.availability else {
            return Ok(false);
        };
        let (Some(candidate_site), Some(current_site)) = (candidate.site, current.site) else {
            return Ok(false);
        };
        let candidate_input = crate::ir::analysis::SemanticFlowPoint::before(candidate_site);
        let candidate_result = crate::ir::analysis::SemanticFlowPoint::after(candidate_site);
        let current_input = crate::ir::analysis::SemanticFlowPoint::before(current_site);
        if !availability.supports(candidate_input, current_input)
            || !availability.supports(candidate_result, current_input)
            || !availability.unchanged(candidate.key, candidate_result, current_input)
        {
            return Ok(false);
        }
        Ok(expression
            .variables()
            .all(|value| availability.unchanged(value, candidate_input, current_input)))
    }

    fn expression(&self, instruction: &SemanticOperation) -> Option<ValueExpression> {
        if !instruction.effects().is_pure()
            || !matches!(
                instruction.insn_type,
                InsnType::Const
                    | InsnType::ConstStr
                    | InsnType::Arith
                    | InsnType::Neg
                    | InsnType::Not
                    | InsnType::Cast
                    | InsnType::Cmp
                    | InsnType::InstanceOf
            )
        {
            return None;
        }
        let mut pending = vec![ExpressionTask::Operation(instruction.clone())];
        let mut values = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                ExpressionTask::Operation(instruction) => {
                    if !instruction.effects().is_pure() || !Self::numberable(instruction.insn_type)
                    {
                        return None;
                    }
                    let frame = ExpressionFrame::of(&instruction)?;
                    pending.push(ExpressionTask::Build(frame));
                    pending.extend(
                        instruction
                            .operands()
                            .iter()
                            .cloned()
                            .into_iter()
                            .rev()
                            .map(ExpressionTask::Expression),
                    );
                }
                ExpressionTask::Expression(SemanticExpression::Register(register)) => {
                    let mut visited = BTreeSet::new();
                    loop {
                        let value = self.root(self.key(&register)?);
                        if !visited.insert(value) {
                            values.push(ValueOperand::Register(value));
                            break;
                        }
                        let Some(canonical) = self.canonical_values.get(&value) else {
                            values.push(ValueOperand::Register(value));
                            break;
                        };
                        pending.push(ExpressionTask::Canonical(canonical.clone()));
                        break;
                    }
                }
                ExpressionTask::Expression(SemanticExpression::Literal(literal)) => {
                    values.push(ValueOperand::Literal {
                        value: literal.value,
                        ty: literal.ty,
                    });
                }
                ExpressionTask::Expression(SemanticExpression::Operation(operation)) => {
                    pending.push(ExpressionTask::Operation(*operation));
                }
                ExpressionTask::Expression(SemanticExpression::Select { .. }) => return None,
                ExpressionTask::Canonical(mut argument) => {
                    let mut visited = BTreeSet::new();
                    loop {
                        match argument {
                            InsnArg::Lit(literal) => {
                                values.push(ValueOperand::Literal {
                                    value: literal.value,
                                    ty: literal.ty.clone(),
                                });
                                break;
                            }
                            InsnArg::Wrapped(instruction) => {
                                pending.push(ExpressionTask::Operation(
                                    SemanticOperation::from_instruction((*instruction).clone())
                                        .ok()?,
                                ));
                                break;
                            }
                            InsnArg::Reg(register) => {
                                let value = self.root(self.key(&register)?);
                                if !visited.insert(value) {
                                    values.push(ValueOperand::Register(value));
                                    break;
                                }
                                let Some(canonical) = self.canonical_values.get(&value) else {
                                    values.push(ValueOperand::Register(value));
                                    break;
                                };
                                argument = canonical.clone();
                            }
                        }
                    }
                }
                ExpressionTask::Build(frame) => {
                    let start = values.len().checked_sub(frame.argument_count)?;
                    let arguments = values.drain(start..).collect();
                    values.push(ValueOperand::Expression(Box::new(frame.build(arguments))));
                }
            }
        }
        let [ValueOperand::Expression(expression)] = values.as_slice() else {
            return None;
        };
        Some((**expression).clone())
    }

    fn numberable(instruction: InsnType) -> bool {
        matches!(
            instruction,
            InsnType::Const
                | InsnType::ConstStr
                | InsnType::Arith
                | InsnType::Neg
                | InsnType::Not
                | InsnType::Cast
                | InsnType::Cmp
                | InsnType::InstanceOf
        )
    }

    fn root(&self, mut value: SsaVar) -> SsaVar {
        let mut visited = BTreeSet::new();
        while visited.insert(value) {
            let Some(parent) = self.aliases.get(&value).copied() else {
                break;
            };
            value = parent;
        }
        value
    }

    fn key(&self, register: &RegisterArg) -> Option<SsaVar> {
        self.identity.key(register)
    }
}

#[derive(Debug, Clone)]
struct NumberedDefinition {
    key: SsaVar,
    register: RegisterArg,
    domain: ControlDomain,
    scope: Arc<[u32]>,
    event: usize,
    repetitive: bool,
    site: Option<crate::ir::SemanticSiteId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ValueExpression {
    instruction: InsnType,
    result_type: ArgType,
    arithmetic: Option<ArithOp>,
    unary: Option<UnaryOp>,
    comparison_bias: Option<CmpBias>,
    cast_type: Option<ArgType>,
    class_type: Option<ArgType>,
    type_index: Option<u32>,
    string_value: Option<Utf16String>,
    arguments: Vec<ValueOperand>,
}

impl ValueExpression {
    fn variables(&self) -> impl Iterator<Item = SsaVar> + '_ {
        let mut pending = self.arguments.iter().collect::<Vec<_>>();
        let mut variables = BTreeSet::new();
        while let Some(operand) = pending.pop() {
            match operand {
                ValueOperand::Register(value) => {
                    variables.insert(*value);
                }
                ValueOperand::Expression(expression) => {
                    pending.extend(expression.arguments.iter());
                }
                ValueOperand::Literal { .. } => {}
            }
        }
        variables.into_iter()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ValueOperand {
    Register(SsaVar),
    Literal { value: i64, ty: ArgType },
    Expression(Box<ValueExpression>),
}

struct ExpressionFrame {
    instruction: InsnType,
    result_type: ArgType,
    arithmetic: Option<ArithOp>,
    unary: Option<UnaryOp>,
    comparison_bias: Option<CmpBias>,
    cast_type: Option<ArgType>,
    class_type: Option<ArgType>,
    type_index: Option<u32>,
    string_value: Option<Utf16String>,
    argument_count: usize,
}

impl ExpressionFrame {
    fn of(instruction: &SemanticOperation) -> Option<Self> {
        Some(Self {
            instruction: instruction.insn_type,
            result_type: instruction.result.as_ref()?.ty.clone(),
            arithmetic: instruction.payload.arith_op,
            unary: instruction.payload.unary_op,
            comparison_bias: instruction.payload.cmp_bias,
            cast_type: instruction.payload.cast_type.clone(),
            class_type: instruction.payload.class_type.clone(),
            type_index: instruction.payload.type_index,
            string_value: instruction.payload.string_value.clone(),
            argument_count: instruction.operands().len(),
        })
    }

    fn build(self, arguments: Vec<ValueOperand>) -> ValueExpression {
        ValueExpression {
            instruction: self.instruction,
            result_type: self.result_type,
            arithmetic: self.arithmetic,
            unary: self.unary,
            comparison_bias: self.comparison_bias,
            cast_type: self.cast_type,
            class_type: self.class_type,
            type_index: self.type_index,
            string_value: self.string_value,
            arguments,
        }
    }
}

enum ExpressionTask {
    Operation(SemanticOperation),
    Expression(SemanticExpression),
    Canonical(InsnArg),
    Build(ExpressionFrame),
}
