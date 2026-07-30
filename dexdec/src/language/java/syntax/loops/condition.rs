//! Inlining of loop-test setup values into Java condition expressions.

use crate::ir::{
    analysis::SsaVar, ArgType, SemanticExpression, SemanticExpressionFacts,
    SemanticExpressionTransform, SemanticFoldError, SemanticInstructions, SemanticLoopControl,
    SemanticLoopKind, SemanticLoopTest, SemanticNode, SemanticOperation, SemanticStatement,
};

/// Reverse loop rotation when the complete iteration lives in the condition
/// setup. This is the canonical post-tested loop produced by CFGs whose latch
/// owns the branch and whose loop body has no separate region node.
pub(super) struct LoopRotation;

impl LoopRotation {
    pub(super) fn recover_post_test(node: SemanticNode) -> SemanticNode {
        let SemanticNode::Loop {
            control,
            header,
            kind: SemanticLoopKind::PreTested,
            test,
            body,
        } = node
        else {
            return node;
        };
        if !matches!(body.as_ref(), SemanticNode::Empty)
            || !test.has_setup()
            || Self::has_local_continue(control, &test.setup)
        {
            return SemanticNode::Loop {
                control,
                header,
                kind: SemanticLoopKind::PreTested,
                test,
                body,
            };
        }
        let SemanticLoopTest { setup, condition } = test;
        SemanticNode::Loop {
            control,
            header,
            kind: SemanticLoopKind::PostTested,
            test: SemanticLoopTest {
                setup: Box::new(SemanticNode::Empty),
                condition,
            },
            body: setup,
        }
    }

    /// Rotates a side-effecting loop header into Java's pre-tested form:
    ///
    /// `loop { setup; if (!condition) break; body; }`
    /// becomes `setup; while (condition) { body; setup; }`.
    ///
    /// A local continue would bypass the duplicated setup in Java, so such a
    /// loop is retained in its explicit endless form.
    pub(super) fn recover_pre_test(node: SemanticNode) -> SemanticNode {
        let SemanticNode::Loop {
            control,
            header,
            kind: SemanticLoopKind::PreTested,
            test,
            body,
        } = node
        else {
            return node;
        };
        if !test.has_setup()
            || matches!(body.as_ref(), SemanticNode::Empty)
            || !crate::ir::semantic::SemanticCompletion::analyze(&test.setup).is_transfer_free()
            || Self::has_local_continue(control, &body)
        {
            return SemanticNode::Loop {
                control,
                header,
                kind: SemanticLoopKind::PreTested,
                test,
                body,
            };
        }

        let SemanticLoopTest { setup, condition } = test;
        let initial = (*setup).clone();
        let body = SemanticNode::sequence([*body, *setup]);
        SemanticNode::sequence([
            initial,
            SemanticNode::Loop {
                control,
                header,
                kind: SemanticLoopKind::PreTested,
                test: SemanticLoopTest {
                    setup: Box::new(SemanticNode::Empty),
                    condition,
                },
                body: Box::new(body),
            },
        ])
    }

    fn has_local_continue(control: SemanticLoopControl, setup: &SemanticNode) -> bool {
        let completion = crate::ir::semantic::SemanticCompletion::analyze(setup);
        match control {
            SemanticLoopControl::Region(region) => completion.has_continue_to_region(region),
            SemanticLoopControl::Label(label) => completion.has_continue_to_label(label),
        }
    }
}

pub(super) struct LoopConditionInlining;

impl LoopConditionInlining {
    pub(super) fn apply(
        node: SemanticNode,
        method: &SemanticExpressionFacts,
    ) -> Result<SemanticNode, SemanticFoldError> {
        let local = SemanticExpressionFacts::of_node(&node);
        let SemanticNode::Loop {
            control,
            header,
            kind: SemanticLoopKind::PreTested,
            mut test,
            body,
        } = node
        else {
            return Ok(node);
        };
        let Some(fact) =
            LoopConditionFact::prove(&test.setup, &test.condition, &body, method, &local)
        else {
            return Ok(SemanticNode::Loop {
                control,
                header,
                kind: SemanticLoopKind::PreTested,
                test,
                body,
            });
        };
        SemanticInstructions::transform_predicate(
            &mut test.condition,
            &mut ConditionValueInlining {
                value: fact.value,
                expression: Some(fact.expression),
            },
        )?;
        test.setup = Box::new(SemanticNode::Empty);
        Ok(SemanticNode::Loop {
            control,
            header,
            kind: SemanticLoopKind::PreTested,
            test,
            body,
        })
    }
}

/// Java `for` is the direct syntax for a pre-tested semantic loop whose test
/// has one setup evaluation. The initializer performs the first evaluation;
/// the update performs every later evaluation, including after `continue`.
pub(super) struct LoopTestCycle;

impl LoopTestCycle {
    pub(super) fn apply(node: SemanticNode) -> SemanticNode {
        let SemanticNode::Loop {
            control,
            header,
            kind: SemanticLoopKind::PreTested,
            test,
            body,
        } = node
        else {
            return node;
        };
        let Some(statement) = SingleStatement::of(&test.setup)
            .filter(|statement| {
                statement
                    .instruction_ref()
                    .is_some_and(|instruction| instruction.result.is_some())
            })
            .cloned()
        else {
            return SemanticNode::Loop {
                control,
                header,
                kind: SemanticLoopKind::PreTested,
                test,
                body,
            };
        };
        SemanticNode::For {
            control,
            init: statement.clone(),
            condition: test.condition,
            update: statement,
            body,
        }
    }
}

struct LoopConditionFact {
    value: SsaVar,
    expression: SemanticOperation,
}

impl LoopConditionFact {
    fn prove(
        setup: &SemanticNode,
        condition: &crate::ir::SemanticPredicate,
        body: &SemanticNode,
        method: &SemanticExpressionFacts,
        local: &SemanticExpressionFacts,
    ) -> Option<Self> {
        let statement = SingleStatement::of(setup)?;
        let instruction = statement.instruction_ref()?;
        let result = instruction.result.as_ref()?;
        (result.ty == ArgType::BOOLEAN).then_some(())?;
        let value = SsaVar::from_reg(result)?;
        (SemanticExpressionFacts::of_node(setup).ssa_definition_count(value) == 1
            && SemanticExpressionFacts::of_predicate(condition).ssa_use_count(value) == 1
            && SemanticExpressionFacts::of_node(body).ssa_use_count(value) == 0
            && !method.ssa_escapes(local, value))
        .then_some(Self {
            value,
            expression: instruction.clone(),
        })
    }
}

struct ConditionValueInlining {
    value: SsaVar,
    expression: Option<SemanticOperation>,
}

impl SemanticExpressionTransform for ConditionValueInlining {
    fn transform_register(&mut self, register: crate::ir::RegisterArg) -> SemanticExpression {
        if SsaVar::from_reg(&register) == Some(self.value) {
            self.expression
                .take()
                .map(|operation| SemanticExpression::Operation(Box::new(operation)))
                .unwrap_or(SemanticExpression::Register(register))
        } else {
            SemanticExpression::Register(register)
        }
    }
}

struct SingleStatement;

impl SingleStatement {
    fn of(node: &SemanticNode) -> Option<&SemanticStatement> {
        let mut found = None;
        let mut pending = vec![node];
        while let Some(node) = pending.pop() {
            match node {
                SemanticNode::Empty => {}
                SemanticNode::BasicBlock(block) => {
                    for statement in &block.statements {
                        if found.replace(statement).is_some() {
                            return None;
                        }
                    }
                }
                SemanticNode::Sequence(children) => pending.extend(children.iter().rev()),
                _ => return None,
            }
        }
        found
    }
}
