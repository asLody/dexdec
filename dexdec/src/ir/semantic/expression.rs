//! Expressions owned by structured Semantic IR.
//!
//! Low-level `InsnArg::Wrapped` trees end at `SemanticFactory`.  From that
//! boundary onward every value, including control-dependent selections, uses
//! this representation.

use crate::ir::{
    analysis::{InstructionEffects, SourceEvaluationError},
    ArgType, InsnArg, InsnNode, InsnPayload, InsnType, InstructionEquivalence, InstructionId,
    LiteralArg, MemberReference, RegisterArg,
};

use super::{SemanticFoldError, SemanticPredicate};

#[derive(Debug, Clone)]
pub enum SemanticExpression {
    Register(RegisterArg),
    Literal(LiteralArg),
    Operation(Box<SemanticOperation>),
    Select {
        condition: SemanticPredicate,
        when_true: Box<SemanticExpression>,
        when_false: Box<SemanticExpression>,
    },
}

/// One source-level operation with semantic expressions as its operands.
///
/// `instruction.args` and `instruction.payload.compound_target` are always
/// empty. Keeping the opcode payload separate from operands makes it
/// impossible for later stages to accidentally reintroduce wrapped CFG trees.
#[derive(Debug, Clone)]
pub struct SemanticOperation {
    pub id: InstructionId,
    pub insn_type: InsnType,
    pub result: Option<RegisterArg>,
    pub offset: u32,
    pub payload: InsnPayload,
    operands: Vec<SemanticExpression>,
    compound_target: Option<Box<SemanticExpression>>,
}

impl SemanticExpression {
    pub fn from_argument(argument: InsnArg) -> Result<Self, SemanticFoldError> {
        let mut pending = vec![ExpressionTask::Argument(argument)];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                ExpressionTask::Argument(InsnArg::Reg(register)) => {
                    results.push(Self::Register(register));
                }
                ExpressionTask::Argument(InsnArg::Lit(literal)) => {
                    results.push(Self::Literal(literal));
                }
                ExpressionTask::Argument(InsnArg::Wrapped(instruction)) => {
                    Self::schedule_operation((*instruction).clone(), &mut pending);
                }
                ExpressionTask::Operation {
                    instruction,
                    operand_count,
                    has_compound_target,
                } => {
                    let child_count = operand_count + usize::from(has_compound_target);
                    let start = results
                        .len()
                        .checked_sub(child_count)
                        .ok_or(SemanticFoldError::MalformedWorkStack)?;
                    let (operands, compound_target) = {
                        let mut children = results.drain(start..);
                        let operands = children.by_ref().take(operand_count).collect();
                        let compound_target = has_compound_target
                            .then(|| children.next().map(Box::new))
                            .flatten();
                        (operands, compound_target)
                    };
                    if has_compound_target && compound_target.is_none() {
                        return Err(SemanticFoldError::MalformedWorkStack);
                    }
                    results.push(Self::Operation(Box::new(SemanticOperation::from_parts(
                        instruction,
                        operands,
                        compound_target.map(|target| *target),
                    ))));
                }
            }
        }
        if results.len() != 1 {
            return Err(SemanticFoldError::MalformedWorkStack);
        }
        results.pop().ok_or(SemanticFoldError::MalformedWorkStack)
    }

    pub fn operation(instruction: InsnNode) -> Result<Self, SemanticFoldError> {
        let mut pending = Vec::new();
        Self::schedule_operation(instruction, &mut pending);
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                ExpressionTask::Argument(argument) => {
                    results.push(Self::from_argument(argument)?);
                }
                ExpressionTask::Operation {
                    instruction,
                    operand_count,
                    has_compound_target,
                } => {
                    let child_count = operand_count + usize::from(has_compound_target);
                    let start = results
                        .len()
                        .checked_sub(child_count)
                        .ok_or(SemanticFoldError::MalformedWorkStack)?;
                    let (operands, compound_target) = {
                        let mut children = results.drain(start..);
                        let operands = children.by_ref().take(operand_count).collect();
                        let compound_target = has_compound_target
                            .then(|| children.next().map(Box::new))
                            .flatten();
                        (operands, compound_target)
                    };
                    if has_compound_target && compound_target.is_none() {
                        return Err(SemanticFoldError::MalformedWorkStack);
                    }
                    results.push(Self::Operation(Box::new(SemanticOperation::from_parts(
                        instruction,
                        operands,
                        compound_target.map(|target| *target),
                    ))));
                }
            }
        }
        if results.len() != 1 {
            return Err(SemanticFoldError::MalformedWorkStack);
        }
        results.pop().ok_or(SemanticFoldError::MalformedWorkStack)
    }

    fn schedule_operation(instruction: InsnNode, pending: &mut Vec<ExpressionTask>) {
        let mut instruction = instruction;
        let operands = std::mem::take(&mut instruction.args);
        let compound_target = instruction.payload.compound_target.take();
        pending.push(ExpressionTask::Operation {
            instruction,
            operand_count: operands.len(),
            has_compound_target: compound_target.is_some(),
        });
        pending.extend(
            operands
                .into_iter()
                .chain(compound_target)
                .rev()
                .map(ExpressionTask::Argument),
        );
    }

    pub fn select(
        condition: SemanticPredicate,
        when_true: SemanticExpression,
        when_false: SemanticExpression,
    ) -> Self {
        Self::Select {
            condition,
            when_true: Box::new(when_true),
            when_false: Box::new(when_false),
        }
    }

    pub fn declared_type(&self) -> Option<&ArgType> {
        match self {
            Self::Register(register) => Some(&register.ty),
            Self::Literal(literal) => Some(&literal.ty),
            Self::Operation(operation) => operation.result.as_ref().map(|result| &result.ty),
            Self::Select { when_true, .. } => when_true.declared_type(),
        }
    }

    pub fn as_register(&self) -> Option<&RegisterArg> {
        match self {
            Self::Register(register) => Some(register),
            Self::Literal(_) | Self::Operation(_) | Self::Select { .. } => None,
        }
    }

    pub fn as_operation(&self) -> Option<&SemanticOperation> {
        match self {
            Self::Operation(operation) => Some(operation),
            Self::Register(_) | Self::Literal(_) | Self::Select { .. } => None,
        }
    }

    pub fn literal_value(&self) -> Option<i64> {
        let mut current = self;
        loop {
            match current {
                Self::Literal(literal) => return Some(literal.value),
                Self::Operation(operation)
                    if matches!(
                        operation.insn_type,
                        crate::ir::InsnType::Const | crate::ir::InsnType::Move
                    ) && operation.operands.len() == 1 =>
                {
                    current = &operation.operands[0];
                }
                Self::Register(_) | Self::Operation(_) | Self::Select { .. } => return None,
            }
        }
    }

    fn stable_leaf(&self) -> &Self {
        let mut expression = self;
        while let Self::Operation(operation) = expression {
            if !matches!(
                operation.insn_type,
                crate::ir::InsnType::Const | crate::ir::InsnType::Move
            ) || operation.operands.len() != 1
            {
                break;
            }
            expression = &operation.operands[0];
        }
        expression
    }

    pub fn same_stable_value(&self, other: &Self) -> bool {
        match (self.stable_leaf(), other.stable_leaf()) {
            (Self::Register(left), Self::Register(right)) => {
                match (left.code_var, right.code_var) {
                    (Some(left), Some(right)) => left == right,
                    _ => left.reg_num == right.reg_num && left.ssa_version == right.ssa_version,
                }
            }
            (Self::Literal(left), Self::Literal(right)) => left == right,
            _ => false,
        }
    }

    pub fn effects(&self) -> InstructionEffects {
        let mut effects = InstructionEffects::PURE;
        let mut pending = vec![self];
        while let Some(expression) = pending.pop() {
            match expression {
                Self::Register(_) | Self::Literal(_) => {}
                Self::Operation(operation) => {
                    effects = effects.join(operation.direct_effects());
                    pending.extend(operation.compound_target.iter().map(Box::as_ref));
                    pending.extend(operation.operands.iter().rev());
                }
                Self::Select {
                    condition,
                    when_true,
                    when_false,
                } => {
                    effects = effects.join(condition.effects());
                    pending.push(when_false);
                    pending.push(when_true);
                }
            }
        }
        effects
    }
}

impl SemanticOperation {
    pub(crate) fn string_literal(value: impl Into<crate::ir::Utf16String>) -> Self {
        let mut instruction = InsnNode::new(InsnType::ConstStr, 0);
        instruction.payload.string_value = Some(value.into());
        Self {
            id: instruction.id,
            insn_type: instruction.insn_type,
            result: instruction.result,
            offset: instruction.offset,
            payload: instruction.payload,
            operands: Vec::new(),
            compound_target: None,
        }
    }
    pub fn from_instruction(instruction: InsnNode) -> Result<Self, SemanticFoldError> {
        match SemanticExpression::operation(instruction)? {
            SemanticExpression::Operation(operation) => Ok(*operation),
            _ => Err(SemanticFoldError::MalformedWorkStack),
        }
    }

    pub fn operands(&self) -> &[SemanticExpression] {
        &self.operands
    }

    pub fn operands_mut(&mut self) -> &mut [SemanticExpression] {
        &mut self.operands
    }

    pub fn compound_target(&self) -> Option<&SemanticExpression> {
        self.compound_target.as_deref()
    }

    pub fn compound_target_mut(&mut self) -> Option<&mut SemanticExpression> {
        self.compound_target.as_deref_mut()
    }

    pub fn operation_equivalent(&self, other: &Self) -> bool {
        self.instruction_with_arguments(Vec::new())
            .operation_equivalent(&other.instruction_with_arguments(Vec::new()))
    }

    pub fn discard_result(&mut self) {
        self.result = None;
    }

    pub(crate) fn rewrite_kind(
        mut self,
        kind: InsnType,
        operands: Vec<SemanticExpression>,
    ) -> Self {
        self.insn_type = kind;
        self.operands = operands;
        self.compound_target = None;
        self
    }

    pub(crate) fn set_result_type(&mut self, ty: ArgType) -> bool {
        let Some(result) = &mut self.result else {
            return false;
        };
        result.ty = ty;
        true
    }

    pub(crate) fn set_unary_operator(&mut self, operator: crate::ir::UnaryOp) {
        self.payload.unary_op = Some(operator);
    }

    pub(crate) fn set_comparison_operator(&mut self, operator: crate::ir::IfOp) {
        self.payload.if_op = Some(operator);
    }

    pub fn effects(&self) -> InstructionEffects {
        let mut effects = self.direct_effects();
        for operand in &self.operands {
            effects = effects.join(operand.effects());
        }
        if let Some(target) = &self.compound_target {
            effects = effects.join(target.effects());
        }
        effects
    }

    pub fn effects_ignoring_edge_copy(&self) -> InstructionEffects {
        let mut instruction = self.instruction_with_arguments(Vec::new());
        instruction.payload.edge_copy = false;
        let mut effects = InstructionEffects::of(&instruction);
        for operand in &self.operands {
            effects = effects.join(operand.effects());
        }
        if let Some(target) = &self.compound_target {
            effects = effects.join(target.effects());
        }
        effects
    }

    pub fn direct_effects(&self) -> InstructionEffects {
        InstructionEffects::of(&self.instruction_with_arguments(Vec::new()))
    }

    pub fn conversion_type(&self) -> Option<&ArgType> {
        match self.insn_type {
            InsnType::Cast => self.payload.cast_type.as_ref(),
            InsnType::CheckCast => self
                .payload
                .class_type
                .as_ref()
                .or(self.payload.cast_type.as_ref()),
            _ => None,
        }
        .or_else(|| self.result.as_ref().map(|result| &result.ty))
    }

    /// Runtime class allocated by a recovered constructor operation.
    ///
    /// Optimizers may replace an empty subclass initializer with a direct call
    /// to its superclass initializer. The invoked method owner therefore does
    /// not necessarily identify the object produced by `new-instance`.
    pub fn allocation_type(&self) -> Option<&ArgType> {
        if self.insn_type != InsnType::Constructor {
            return None;
        }
        self.payload
            .class_type
            .as_ref()
            .or_else(|| self.result.as_ref().map(|result| &result.ty))
            .or_else(|| match self.payload.reference.as_ref() {
                Some(MemberReference::Method(method)) => Some(&method.owner),
                _ => None,
            })
    }

    pub fn evaluation_operands(&self) -> Result<Vec<&SemanticExpression>, SourceEvaluationError> {
        let arity = || SourceEvaluationError::InvalidArity {
            instruction: self.insn_type,
            offset: self.offset,
            actual: self.operands.len(),
        };
        Ok(match self.insn_type {
            InsnType::Constructor => self
                .operands
                .get(1..)
                .ok_or(SourceEvaluationError::MalformedConstructor(self.offset))?
                .iter()
                .collect(),
            InsnType::Iput => {
                if self.operands.len() != 2 {
                    return Err(arity());
                }
                vec![&self.operands[1], &self.operands[0]]
            }
            InsnType::Aput => {
                if self.operands.len() != 3 {
                    return Err(arity());
                }
                vec![&self.operands[1], &self.operands[2], &self.operands[0]]
            }
            InsnType::CompoundAssign => vec![
                self.compound_target.as_deref().ok_or_else(arity)?,
                self.operands.last().ok_or_else(arity)?,
            ],
            _ => self
                .operands
                .iter()
                .chain(self.compound_target.iter().map(Box::as_ref))
                .collect(),
        })
    }

    pub fn effects_before(
        &self,
        target: crate::ir::InstructionId,
    ) -> Result<Option<InstructionEffects>, SourceEvaluationError> {
        if self.id == target {
            return Ok(Some(InstructionEffects::PURE));
        }
        let mut effects = InstructionEffects::PURE;
        let mut pending = vec![EvaluationTask::Effect(self)];
        pending.extend(
            self.evaluation_operands()?
                .into_iter()
                .rev()
                .map(EvaluationTask::Expression),
        );
        while let Some(task) = pending.pop() {
            match task {
                EvaluationTask::Expression(SemanticExpression::Operation(operation)) => {
                    if operation.id == target {
                        return Ok(Some(effects));
                    }
                    pending.push(EvaluationTask::Effect(operation));
                    pending.extend(
                        operation
                            .evaluation_operands()?
                            .into_iter()
                            .rev()
                            .map(EvaluationTask::Expression),
                    );
                }
                EvaluationTask::Expression(SemanticExpression::Select { .. }) => return Ok(None),
                EvaluationTask::Expression(
                    SemanticExpression::Register(_) | SemanticExpression::Literal(_),
                ) => {}
                EvaluationTask::Effect(operation) => {
                    effects = effects.join(operation.direct_effects());
                }
            }
        }
        Ok(None)
    }

    pub(crate) fn from_parts(
        instruction: InsnNode,
        operands: Vec<SemanticExpression>,
        compound_target: Option<SemanticExpression>,
    ) -> Self {
        debug_assert!(instruction.args.is_empty());
        debug_assert!(instruction.payload.compound_target.is_none());
        Self {
            id: instruction.id,
            insn_type: instruction.insn_type,
            result: instruction.result,
            offset: instruction.offset,
            payload: instruction.payload,
            operands,
            compound_target: compound_target.map(Box::new),
        }
    }

    pub(crate) fn into_parts(
        self,
    ) -> (
        InsnNode,
        Vec<SemanticExpression>,
        Option<SemanticExpression>,
    ) {
        (
            self.instruction_with_arguments(Vec::new()),
            self.operands,
            self.compound_target.map(|target| *target),
        )
    }

    pub(crate) fn instruction_with_arguments(&self, arguments: Vec<InsnArg>) -> InsnNode {
        InsnNode {
            id: self.id,
            insn_type: self.insn_type,
            result: self.result.clone(),
            args: arguments,
            offset: self.offset,
            payload: self.payload.clone(),
        }
    }
}

enum ExpressionTask {
    Argument(InsnArg),
    Operation {
        instruction: InsnNode,
        operand_count: usize,
        has_compound_target: bool,
    },
}

enum EvaluationTask<'a> {
    Expression(&'a SemanticExpression),
    Effect(&'a SemanticOperation),
}
