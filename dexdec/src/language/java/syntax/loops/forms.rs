use crate::ir::{
    analysis::SsaVar, InsnType, InstructionId, RegisterArg, SemanticExpression,
    SemanticExpressionFacts, SemanticExpressionTransform, SemanticInstructions, SemanticLoopKind,
    SemanticNode, SemanticOperation,
};

use super::{
    boundary::{Boundary, StatementBoundary},
    continuation::ContinuationUpdate,
    facts::LoopSyntaxFact,
};

pub(super) struct LoopForm;

impl LoopForm {
    pub(super) fn apply(
        fact: LoopSyntaxFact,
        mut previous: SemanticNode,
        loop_node: SemanticNode,
    ) -> Option<(SemanticNode, SemanticNode)> {
        let init = StatementBoundary::take_site(&mut previous, fact.init())?;
        let SemanticNode::Loop {
            control,
            kind: SemanticLoopKind::PreTested,
            test,
            mut body,
            ..
        } = loop_node
        else {
            return None;
        };
        let loop_form = match fact {
            LoopSyntaxFact::Counted {
                update,
                update_operation,
                variable,
                ..
            } => {
                (!test.has_setup()).then_some(())?;
                (StatementBoundary::last(&body)?.site == Some(update)).then_some(())?;
                let mut continuation = ContinuationUpdate::new(control, update_operation, variable);
                continuation.apply(&mut body).then_some(())?;
                continuation.is_valid().then_some(())?;
                let update_statement = StatementBoundary::take(&mut body, Boundary::Last)?;
                SemanticNode::For {
                    control,
                    init,
                    condition: test.condition,
                    update: update_statement,
                    body,
                }
            }
            LoopSyntaxFact::ForEach {
                variable,
                iterable,
                advance,
                advance_is_statement,
                ..
            } => {
                (!test.has_setup()).then_some(())?;
                if advance_is_statement {
                    StatementBoundary::take(&mut body, Boundary::First)?;
                } else {
                    SemanticInstructions::transform(
                        &mut body,
                        &mut AdvanceUseRewrite {
                            instruction: advance,
                            variable: variable.clone(),
                        },
                    )
                    .ok()?;
                }
                let variable = IterationVariable::refine(&mut body, variable);
                SemanticNode::ForEach {
                    control,
                    variable,
                    iterable: crate::ir::SemanticOperand::new(iterable),
                    body,
                }
            }
        };
        Some((previous, loop_form))
    }
}

struct IterationVariable;

impl IterationVariable {
    fn refine(body: &mut SemanticNode, variable: RegisterArg) -> RegisterArg {
        let Some(value) = SsaVar::from_reg(&variable) else {
            return variable;
        };
        let Some(cast) = StatementBoundary::first(body)
            .and_then(|statement| statement.instruction_ref())
            .filter(|instruction| instruction.insn_type == InsnType::CheckCast)
        else {
            return variable;
        };
        let [SemanticExpression::Register(operand)] = cast.operands() else {
            return variable;
        };
        if SsaVar::from_reg(operand) != Some(value)
            || SemanticExpressionFacts::of_node(body).ssa_use_count(value) != 1
        {
            return variable;
        }
        let Some(result) = cast.result.clone() else {
            return variable;
        };
        if StatementBoundary::take(body, Boundary::First).is_none() {
            return variable;
        }
        result
    }
}

struct AdvanceUseRewrite {
    instruction: InstructionId,
    variable: crate::ir::RegisterArg,
}

impl SemanticExpressionTransform for AdvanceUseRewrite {
    fn transform_operation(&mut self, operation: SemanticOperation) -> SemanticExpression {
        if operation.id == self.instruction {
            SemanticExpression::Register(self.variable.clone())
        } else {
            SemanticExpression::Operation(Box::new(operation))
        }
    }
}
