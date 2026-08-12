use crate::ir::{
    analysis::{SubtypeRelation, TypeHierarchy},
    ArgType, IfOp, InsnType, InstructionId, MemberReference, MethodReference, SemanticExpression,
    SemanticExpressionFacts, SemanticLoopControl, SemanticNode, SemanticOperation,
    SemanticPredicate, SemanticSiteId, SemanticStatement,
};

use super::{boundary::StatementBoundary, continuation::ContinuationUpdate, entry::IterationEntry};

#[derive(Debug)]
pub(super) enum LoopSyntaxFact {
    Counted {
        init: SemanticSiteId,
        update: SemanticSiteId,
        update_operation: InstructionId,
        variable: u32,
    },
    ForEach {
        init: SemanticSiteId,
        variable: crate::ir::RegisterArg,
        variable_value: crate::ir::analysis::SsaVar,
        iterator_value: crate::ir::analysis::SsaVar,
        iterable: SemanticExpression,
        advance: InstructionId,
        advance_is_statement: bool,
    },
}

impl LoopSyntaxFact {
    pub(super) fn init(&self) -> SemanticSiteId {
        match self {
            Self::Counted { init, .. } | Self::ForEach { init, .. } => *init,
        }
    }

    pub(super) fn escapes(
        &self,
        method: &SemanticExpressionFacts,
        local: &SemanticExpressionFacts,
    ) -> bool {
        match self {
            Self::Counted { variable, .. } => {
                method.use_count(*variable) != local.use_count(*variable)
            }
            Self::ForEach {
                variable,
                variable_value,
                iterator_value,
                ..
            } => {
                method.ssa_escapes(local, *variable_value)
                    || method.ssa_escapes(local, *iterator_value)
                    || variable
                        .code_var
                        // For-each removes the iterator-advance definition. A phi may use a
                        // different SSA value coalesced into the same source variable after
                        // the loop, so compare uses directly instead of definition/use ratios.
                        .is_some_and(|source| method.use_count(source) != local.use_count(source))
            }
        }
    }
}

pub(super) struct LoopSyntaxProof<'a> {
    hierarchy: &'a dyn TypeHierarchy,
}

impl<'a> LoopSyntaxProof<'a> {
    pub(super) fn new(hierarchy: &'a dyn TypeHierarchy) -> Self {
        Self { hierarchy }
    }

    pub(super) fn prove(
        &self,
        previous: &SemanticNode,
        loop_node: &SemanticNode,
    ) -> Option<LoopSyntaxFact> {
        let SemanticNode::Loop {
            control,
            kind: crate::ir::SemanticLoopKind::PreTested,
            test,
            body,
            ..
        } = loop_node
        else {
            return None;
        };
        let statements = StatementBoundary::linear(previous)?;
        for (index, init) in statements.iter().enumerate().rev() {
            let fact = IteratorLoopProof::new(self.hierarchy)
                .prove(init, test, body)
                .or_else(|| {
                    (!test.has_setup())
                        .then(|| CountedLoopProof::prove(init, *control, &test.condition, body))
                        .flatten()
                });
            if fact.is_some() && Self::can_schedule_before(init, &statements[index + 1..]) {
                return fact;
            }
        }
        None
    }

    fn can_schedule_before(init: &SemanticStatement, trailing: &[&SemanticStatement]) -> bool {
        let Some(init_instruction) = init.instruction_ref() else {
            return false;
        };
        if trailing.iter().any(|statement| {
            statement
                .instruction_ref()
                .is_none_or(|instruction| !instruction.effects().is_pure())
        }) {
            return false;
        }
        let init = SemanticExpressionFacts::of_operation(init_instruction);
        let mut suffix = SemanticExpressionFacts::default();
        for statement in trailing {
            let Some(instruction) = statement.instruction_ref() else {
                return false;
            };
            suffix.merge(&SemanticExpressionFacts::of_operation(instruction));
        }
        let source_conflict = init
            .defined_variables()
            .any(|variable| suffix.uses(variable) || suffix.definition_count(variable) != 0)
            || suffix
                .defined_variables()
                .any(|variable| init.uses(variable) || init.definition_count(variable) != 0);
        let ssa_conflict = init.defined_ssa_variables().any(|variable| {
            suffix.ssa_use_count(variable) != 0 || suffix.ssa_definition_count(variable) != 0
        }) || suffix.defined_ssa_variables().any(|variable| {
            init.ssa_use_count(variable) != 0 || init.ssa_definition_count(variable) != 0
        });
        !source_conflict && !ssa_conflict
    }
}

struct CountedLoopProof;

impl CountedLoopProof {
    fn prove(
        init: &SemanticStatement,
        control: SemanticLoopControl,
        condition: &SemanticPredicate,
        body: &SemanticNode,
    ) -> Option<LoopSyntaxFact> {
        Self::analyze(init, control, condition, body).ok()
    }

    fn analyze(
        init: &SemanticStatement,
        control: SemanticLoopControl,
        condition: &SemanticPredicate,
        body: &SemanticNode,
    ) -> Result<LoopSyntaxFact, CountedLoopRejection> {
        let init_instruction = init
            .instruction_ref()
            .ok_or(CountedLoopRejection::NonInstructionInit)?;
        let variable = init_instruction
            .result
            .as_ref()
            .and_then(|result| result.code_var)
            .ok_or(CountedLoopRejection::MissingInitVariable)?;
        let update = InductionUpdate::analyze(
            StatementBoundary::last(body).ok_or(CountedLoopRejection::MissingUpdate)?,
            variable,
        )?;
        SemanticExpressionFacts::of_predicate(condition)
            .uses(variable)
            .then_some(())
            .ok_or(CountedLoopRejection::ConditionDoesNotUseVariable)?;
        SemanticExpressionFacts::of_operation(update.value)
            .uses(variable)
            .then_some(())
            .ok_or(CountedLoopRejection::UpdateDoesNotUseVariable)?;
        ContinuationUpdate::prove(control, update.statement.id(), variable, body)
            .then_some(())
            .ok_or(CountedLoopRejection::InvalidContinuationUpdates)?;
        Ok(LoopSyntaxFact::Counted {
            init: init.site.ok_or(CountedLoopRejection::MissingInitSite)?,
            update: update
                .statement
                .site
                .ok_or(CountedLoopRejection::MissingUpdateSite)?,
            update_operation: update.statement.id(),
            variable,
        })
    }
}

struct InductionUpdate<'a> {
    statement: &'a SemanticStatement,
    value: &'a SemanticOperation,
}

impl<'a> InductionUpdate<'a> {
    fn analyze(
        statement: &'a SemanticStatement,
        variable: u32,
    ) -> Result<Self, CountedLoopRejection> {
        let operation = statement
            .instruction_ref()
            .ok_or(CountedLoopRejection::NonInstructionUpdate)?;
        (Self::target_variable(operation) == Some(variable))
            .then_some(())
            .ok_or(CountedLoopRejection::DifferentUpdateVariable)?;
        let value = Self::canonical_value(operation);
        matches!(value.insn_type, InsnType::Arith | InsnType::CompoundAssign)
            .then_some(())
            .ok_or(CountedLoopRejection::UnsupportedUpdate)?;
        Ok(Self { statement, value })
    }

    fn target_variable(operation: &SemanticOperation) -> Option<u32> {
        operation
            .result
            .as_ref()
            .and_then(|result| result.code_var)
            .or_else(|| {
                operation
                    .compound_target()
                    .and_then(SemanticExpression::as_register)
                    .and_then(|target| target.code_var)
            })
    }

    fn canonical_value(mut operation: &SemanticOperation) -> &SemanticOperation {
        while operation.insn_type == InsnType::Move && operation.operands().len() == 1 {
            let Some(inner) = operation.operands()[0].as_operation() else {
                break;
            };
            operation = inner;
        }
        operation
    }
}

#[derive(Debug)]
enum CountedLoopRejection {
    NonInstructionInit,
    MissingInitVariable,
    MissingUpdate,
    NonInstructionUpdate,
    DifferentUpdateVariable,
    UnsupportedUpdate,
    ConditionDoesNotUseVariable,
    UpdateDoesNotUseVariable,
    InvalidContinuationUpdates,
    MissingInitSite,
    MissingUpdateSite,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{BlockId, InsnArg, InsnNode, RegisterArg, SemanticBlock, SemanticStatement};

    fn register(reg_num: u32, version: u32, variable: u32) -> RegisterArg {
        let mut register = RegisterArg::new(reg_num, ArgType::object("java/lang/Object"));
        register.ssa_version = Some(version);
        register.code_var = Some(variable);
        register
    }

    fn block(id: u32, statements: Vec<SemanticStatement>) -> SemanticNode {
        SemanticNode::BasicBlock(SemanticBlock {
            id: BlockId::new(id),
            statements,
        })
    }

    fn move_statement(result: RegisterArg, source: InsnArg) -> SemanticStatement {
        SemanticStatement::instruction(InsnNode::mov(result, source))
            .expect("move should produce a semantic statement")
    }

    #[test]
    fn foreach_rejects_a_phi_coalesced_advance_used_after_the_loop() {
        let advance = register(0, 4, 4);
        let iteration_value = register(1, 2, 8);
        let phi_value = register(0, 6, 4);
        let consumer = register(0, 7, 6);
        let iterator = register(8, 4, 30);
        let local = block(
            1,
            vec![
                move_statement(
                    advance.clone(),
                    InsnArg::lit(0, ArgType::object("java/lang/Object")),
                ),
                move_statement(iteration_value, InsnArg::Reg(advance.clone())),
            ],
        );
        let continuation = block(
            2,
            vec![
                move_statement(
                    phi_value.clone(),
                    InsnArg::lit(0, ArgType::object("java/lang/Object")),
                ),
                move_statement(consumer, InsnArg::Reg(phi_value)),
            ],
        );
        let method = SemanticNode::sequence([local.clone(), continuation]);
        let method_facts = SemanticExpressionFacts::of_node(&method);
        let local_facts = SemanticExpressionFacts::of_node(&local);
        assert!(!method_facts.variable_escapes(&local_facts, 4));

        let fact = LoopSyntaxFact::ForEach {
            init: SemanticSiteId(1),
            variable_value: crate::ir::analysis::SsaVar::from_reg(&advance)
                .expect("advance should have an SSA identity"),
            iterator_value: crate::ir::analysis::SsaVar::from_reg(&iterator)
                .expect("iterator should have an SSA identity"),
            variable: advance,
            iterable: SemanticExpression::Register(iterator),
            advance: InstructionId::new(1),
            advance_is_statement: true,
        };
        assert!(fact.escapes(&method_facts, &local_facts));
    }
}

struct IteratorLoopProof<'a> {
    hierarchy: &'a dyn TypeHierarchy,
}

impl<'a> IteratorLoopProof<'a> {
    fn new(hierarchy: &'a dyn TypeHierarchy) -> Self {
        Self { hierarchy }
    }

    fn prove(
        &self,
        init: &SemanticStatement,
        test: &crate::ir::SemanticLoopTest,
        body: &SemanticNode,
    ) -> Option<LoopSyntaxFact> {
        let init_instruction = init.instruction_ref()?;
        (!test.has_setup()).then_some(())?;
        let iterator_value =
            crate::ir::analysis::SsaVar::from_reg(init_instruction.result.as_ref()?)?;
        let iterable = IteratorProtocol::iterator_source(self.hierarchy, init_instruction)?;
        IteratorProtocol::is_has_next(&test.condition, iterator_value).then_some(())?;
        let entry = IterationEntry::find(body)?;
        let advance = IteratorProtocol::advance(entry.instruction, iterator_value)?;
        entry
            .instruction
            .effects_before(advance.instruction)
            .ok()??
            .is_pure()
            .then_some(())?;
        let variable = advance.variable;
        let variable_value = crate::ir::analysis::SsaVar::from_reg(&variable)?;
        (SemanticExpressionFacts::of_node(body).ssa_use_count(iterator_value) == 1).then_some(())?;
        Some(LoopSyntaxFact::ForEach {
            init: init.site?,
            variable,
            variable_value,
            iterator_value,
            iterable,
            advance: advance.instruction,
            advance_is_statement: entry
                .statement
                .is_some_and(|statement| advance.instruction == statement.id()),
        })
    }
}

struct IteratorProtocol;

impl IteratorProtocol {
    fn advance(
        instruction: &SemanticOperation,
        receiver: crate::ir::analysis::SsaVar,
    ) -> Option<IteratorAdvance> {
        let mut candidates = Vec::new();
        let mut pending = vec![instruction];
        while let Some(instruction) = pending.pop() {
            if Self::is_next_definition(instruction, receiver) {
                candidates.push(IteratorAdvance {
                    instruction: instruction.id,
                    variable: instruction.result.clone()?,
                });
                continue;
            }
            pending.extend(
                instruction
                    .operands()
                    .iter()
                    .chain(instruction.compound_target())
                    .filter_map(SemanticExpression::as_operation),
            );
        }
        let [advance] = candidates.as_slice() else {
            return None;
        };
        Some(advance.clone())
    }

    fn iterator_source(
        hierarchy: &dyn TypeHierarchy,
        instruction: &SemanticOperation,
    ) -> Option<SemanticExpression> {
        let method = Self::method(instruction)?;
        (method.name == "iterator"
            && method.descriptor.parameters.is_empty()
            && method.descriptor.return_type == ArgType::object("java/util/Iterator")
            && instruction.insn_type == InsnType::Invoke
            && instruction.operands().len() == 1
            && method.owner.as_object().is_some_and(|owner| {
                hierarchy.subtype_relation(owner, "java/lang/Iterable") != SubtypeRelation::No
            }))
        .then(|| instruction.operands()[0].clone())
    }

    fn is_has_next(predicate: &SemanticPredicate, receiver: crate::ir::analysis::SsaVar) -> bool {
        Self::is_boolean_call(predicate, "hasNext", receiver, true)
    }

    fn is_next_definition(
        instruction: &SemanticOperation,
        receiver: crate::ir::analysis::SsaVar,
    ) -> bool {
        if Self::is_call(
            instruction,
            "next",
            &ArgType::object("java/lang/Object"),
            receiver,
        ) {
            return true;
        }
        instruction.insn_type == InsnType::CheckCast
            && instruction.operands().len() == 1
            && instruction
                .operands()
                .first()
                .and_then(SemanticExpression::as_operation)
                .is_some_and(|call| {
                    Self::is_call(call, "next", &ArgType::object("java/lang/Object"), receiver)
                })
    }

    fn is_boolean_call(
        predicate: &SemanticPredicate,
        name: &str,
        receiver: crate::ir::analysis::SsaVar,
        expected: bool,
    ) -> bool {
        match predicate {
            SemanticPredicate::Test(test) => Self::is_boolean_test(test, name, receiver, expected),
            SemanticPredicate::Not(inner) => {
                Self::is_boolean_call(inner, name, receiver, !expected)
            }
            SemanticPredicate::And(_)
            | SemanticPredicate::Or(_)
            | SemanticPredicate::True
            | SemanticPredicate::False => false,
        }
    }

    fn is_boolean_test(
        test: &SemanticOperation,
        name: &str,
        receiver: crate::ir::analysis::SsaVar,
        expected: bool,
    ) -> bool {
        let Some(op @ (IfOp::Eq | IfOp::Ne)) = test.payload.if_op else {
            return false;
        };
        let [left, right] = test.operands() else {
            return false;
        };
        let (call, literal) = if let Some(call) = left.as_operation() {
            (call, right)
        } else if let Some(call) = right.as_operation() {
            (call, left)
        } else {
            return false;
        };
        let Some(value) = literal.literal_value() else {
            return false;
        };
        matches!(value, 0 | 1)
            && Self::is_call(call, name, &ArgType::BOOLEAN, receiver)
            && ((op == IfOp::Eq) == (value == 1)) == expected
    }

    fn is_call(
        instruction: &SemanticOperation,
        name: &str,
        return_type: &ArgType,
        receiver: crate::ir::analysis::SsaVar,
    ) -> bool {
        Self::method(instruction).is_some_and(|method| {
            method.name == name
                && method.descriptor.parameters.is_empty()
                && method.descriptor.return_type == *return_type
                && instruction.operands().len() == 1
                && instruction.operands().first().is_some_and(|argument| {
                    argument
                        .as_register()
                        .and_then(crate::ir::analysis::SsaVar::from_reg)
                        == Some(receiver)
                })
        })
    }

    fn method(instruction: &SemanticOperation) -> Option<&MethodReference> {
        (instruction.insn_type == InsnType::Invoke).then_some(())?;
        let MemberReference::Method(method) = instruction.payload.reference.as_ref()? else {
            return None;
        };
        Some(method)
    }
}

#[derive(Clone)]
struct IteratorAdvance {
    instruction: InstructionId,
    variable: crate::ir::RegisterArg,
}
