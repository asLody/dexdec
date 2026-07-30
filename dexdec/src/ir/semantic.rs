//! Structured semantic IR.
//!
//! Control-flow recovery ends at this layer.  Nodes own their statements and
//! all non-local transfers are explicit; later value recovery must not inspect
//! CFG edges or rediscover control-flow intent from instruction shapes.

#[path = "semantic/completion.rs"]
mod completion;
#[path = "semantic/dce.rs"]
mod dce;
#[path = "semantic/expression.rs"]
mod expression;
#[path = "semantic/factory.rs"]
mod factory;
#[path = "semantic/facts.rs"]
mod facts;
#[path = "semantic/instructions.rs"]
mod instructions;
#[path = "semantic/normalize.rs"]
mod normalize;
#[path = "semantic/sites.rs"]
mod sites;
mod string_building;
#[path = "semantic/verify.rs"]
mod verify;
#[path = "semantic/visit.rs"]
mod visit;

pub(crate) use completion::{
    CompletionDomain, CompletionInterpreter, SemanticCompletion, SemanticControlTopology,
    SemanticTransfer,
};
pub use dce::SemanticDeadCodeElimination;
pub use expression::{SemanticExpression, SemanticOperation};
pub use factory::SemanticBuildError;
pub(crate) use factory::SemanticFactory;
pub use facts::SemanticExpressionFacts;
pub use instructions::{SemanticExpressionTransform, SemanticInstructions};
pub(crate) use sites::SemanticSiteNumbering;
pub use string_building::{StringBuilderProtocol, StringBuildingRecovery};
pub use verify::SemanticInvariantError;
pub use visit::{
    SemanticBindingKind, SemanticFoldControl, SemanticFoldError, SemanticFolder, SemanticVisitor,
};

use std::collections::{BTreeMap, BTreeSet};

use super::{
    analysis::{InstructionEffects, SsaValueGraph},
    BlockId, BoolExpr, BoolVariable, IfOp, InsnArg, InsnNode, InsnType, RegionEdge, RegionGraph,
    RegionId, RegisterArg,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct StatementOrigin {
    pub block: BlockId,
    pub instruction: super::InstructionId,
}

#[derive(Debug, Clone)]
pub struct SemanticStatement {
    pub site: Option<SemanticSiteId>,
    pub origin: Option<StatementOrigin>,
    pub kind: SemanticStatementKind,
}

#[derive(Debug, Clone)]
pub enum SemanticStatementKind {
    Instruction(SemanticOperation),
    Definition {
        id: super::InstructionId,
        result: RegisterArg,
        value: SemanticExpression,
    },
}

impl SemanticStatement {
    pub fn instruction(instruction: InsnNode) -> Result<Self, SemanticFoldError> {
        Ok(Self {
            site: None,
            origin: None,
            kind: SemanticStatementKind::Instruction(SemanticOperation::from_instruction(
                instruction,
            )?),
        })
    }

    pub fn definition(
        id: super::InstructionId,
        result: RegisterArg,
        value: SemanticExpression,
    ) -> Self {
        Self {
            site: None,
            origin: None,
            kind: SemanticStatementKind::Definition { id, result, value },
        }
    }

    pub fn instruction_ref(&self) -> Option<&SemanticOperation> {
        match &self.kind {
            SemanticStatementKind::Instruction(instruction) => Some(instruction),
            SemanticStatementKind::Definition { .. } => None,
        }
    }

    pub fn instruction_mut(&mut self) -> Option<&mut SemanticOperation> {
        match &mut self.kind {
            SemanticStatementKind::Instruction(instruction) => Some(instruction),
            SemanticStatementKind::Definition { .. } => None,
        }
    }

    pub fn value(&self) -> Option<&SemanticExpression> {
        match &self.kind {
            SemanticStatementKind::Definition { value, .. } => Some(value),
            SemanticStatementKind::Instruction(_) => None,
        }
    }

    pub fn value_mut(&mut self) -> Option<&mut SemanticExpression> {
        match &mut self.kind {
            SemanticStatementKind::Definition { value, .. } => Some(value),
            SemanticStatementKind::Instruction(_) => None,
        }
    }

    pub fn result(&self) -> Option<&RegisterArg> {
        match &self.kind {
            SemanticStatementKind::Instruction(instruction) => instruction.result.as_ref(),
            SemanticStatementKind::Definition { result, .. } => Some(result),
        }
    }

    pub fn result_mut(&mut self) -> Option<&mut RegisterArg> {
        match &mut self.kind {
            SemanticStatementKind::Instruction(instruction) => instruction.result.as_mut(),
            SemanticStatementKind::Definition { result, .. } => Some(result),
        }
    }

    pub fn id(&self) -> super::InstructionId {
        match &self.kind {
            SemanticStatementKind::Instruction(instruction) => instruction.id,
            SemanticStatementKind::Definition { id, .. } => *id,
        }
    }

    pub fn effects(&self) -> InstructionEffects {
        match &self.kind {
            SemanticStatementKind::Instruction(instruction) => instruction.effects(),
            SemanticStatementKind::Definition { value, .. } => value.effects(),
        }
    }
}

/// Instructions owned by one original CFG block.
///
/// Block identity lets edge analyses place Phi copies after sparse SSA
/// recovery without reconstructing topology from statement shapes.
#[derive(Debug, Clone)]
pub struct SemanticBlock {
    pub id: BlockId,
    pub statements: Vec<SemanticStatement>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemanticLoopKind {
    PreTested,
    PostTested,
    Endless,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SemanticLoopControl {
    Region(RegionId),
    Label(SemanticLabel),
}

#[derive(Debug, Clone)]
pub struct SemanticLoopTest {
    pub setup: Box<SemanticNode>,
    pub condition: SemanticOperand<SemanticPredicate>,
}

impl SemanticLoopTest {
    pub fn new(setup: SemanticNode, condition: SemanticPredicate) -> Self {
        Self {
            setup: Box::new(setup),
            condition: SemanticOperand::new(condition),
        }
    }

    pub fn pure(condition: SemanticPredicate) -> Self {
        Self::new(SemanticNode::Empty, condition)
    }

    pub fn has_setup(&self) -> bool {
        !matches!(self.setup.as_ref(), SemanticNode::Empty)
    }
}

#[derive(Debug, Clone)]
pub enum SemanticLeaveKind {
    /// An unresolved lexical continuation. Region reduction must either bind
    /// it to the sole normal successor or retain it in semantic graph reduction.
    FallThrough(BlockId),
    /// An unresolved jump in the current region-local graph. Graph structuring
    /// must bind this before Semantic IR leaves the structure layer.
    Jump(BlockId),
    /// A forward transfer represented by a lexical Kotlin label.
    BreakLabel(SemanticLabel),
    /// A loop back-edge represented by a lexical Kotlin loop label.
    ContinueLabel(SemanticLabel),
    Return(Option<SemanticExpression>),
    Throw(SemanticExpression),
    Break,
    Continue,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SemanticLabelKind {
    Block,
    Loop,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SemanticLabel {
    pub region: RegionId,
    pub block: BlockId,
    pub kind: SemanticLabelKind,
}

impl SemanticLabel {
    pub const fn block(region: RegionId, block: BlockId) -> Self {
        Self {
            region,
            block,
            kind: SemanticLabelKind::Block,
        }
    }

    pub const fn loop_(region: RegionId, block: BlockId) -> Self {
        Self {
            region,
            block,
            kind: SemanticLabelKind::Loop,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SemanticSiteId(pub u64);

#[derive(Debug, Clone)]
pub struct SemanticOperand<T> {
    pub site: Option<SemanticSiteId>,
    pub value: T,
}

impl<T> SemanticOperand<T> {
    pub fn new(value: T) -> Self {
        Self { site: None, value }
    }

    pub fn into_inner(self) -> T {
        self.value
    }
}

impl<T> std::ops::Deref for SemanticOperand<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> std::ops::DerefMut for SemanticOperand<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

#[derive(Debug, Clone)]
pub struct SemanticLeave {
    pub site: Option<SemanticSiteId>,
    pub condition: Option<SemanticPredicate>,
    pub kind: SemanticLeaveKind,
    /// Physical CFG edge represented by this transfer, when one exists.
    pub edge: Option<RegionEdge>,
    /// CFG predecessor whose edge produced this semantic transfer.
    pub origin: Option<BlockId>,
    pub source: RegionId,
    pub destination: RegionId,
    pub target: RegionId,
    pub cleanup: Vec<RegionId>,
}

impl SemanticLeave {
    pub fn value(&self) -> Option<&SemanticExpression> {
        match &self.kind {
            SemanticLeaveKind::Return(value) => value.as_ref(),
            SemanticLeaveKind::Throw(value) => Some(value),
            SemanticLeaveKind::FallThrough(_)
            | SemanticLeaveKind::Jump(_)
            | SemanticLeaveKind::BreakLabel(_)
            | SemanticLeaveKind::ContinueLabel(_)
            | SemanticLeaveKind::Break
            | SemanticLeaveKind::Continue => None,
        }
    }

    pub fn value_mut(&mut self) -> Option<&mut SemanticExpression> {
        match &mut self.kind {
            SemanticLeaveKind::Return(value) => value.as_mut(),
            SemanticLeaveKind::Throw(value) => Some(value),
            SemanticLeaveKind::FallThrough(_)
            | SemanticLeaveKind::Jump(_)
            | SemanticLeaveKind::BreakLabel(_)
            | SemanticLeaveKind::ContinueLabel(_)
            | SemanticLeaveKind::Break
            | SemanticLeaveKind::Continue => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct SemanticCatch {
    pub region: RegionId,
    pub exception_types: Vec<super::ArgType>,
    pub exception_value: Option<super::RegisterArg>,
    pub body: SemanticNode,
}

#[derive(Debug, Clone)]
pub struct SemanticFinally {
    pub region: RegionId,
    pub body: Box<SemanticNode>,
}

#[derive(Debug, Clone)]
pub struct SemanticSwitchCase {
    pub values: Vec<i32>,
    pub is_default: bool,
    pub body: SemanticNode,
}

#[derive(Debug)]
pub enum SemanticPredicate {
    True,
    False,
    Test(SemanticOperation),
    Not(Box<SemanticPredicate>),
    And(Vec<SemanticPredicate>),
    Or(Vec<SemanticPredicate>),
}

impl Clone for SemanticPredicate {
    fn clone(&self) -> Self {
        enum Task<'a> {
            Visit(&'a SemanticPredicate),
            Not,
            Junction { count: usize, conjunction: bool },
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(Self::True) => results.push(Self::True),
                Task::Visit(Self::False) => results.push(Self::False),
                Task::Visit(Self::Test(test)) => results.push(Self::Test(test.clone())),
                Task::Visit(Self::Not(inner)) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(inner));
                }
                Task::Visit(Self::And(terms)) => {
                    tasks.push(Task::Junction {
                        count: terms.len(),
                        conjunction: true,
                    });
                    tasks.extend(terms.iter().rev().map(Task::Visit));
                }
                Task::Visit(Self::Or(terms)) => {
                    tasks.push(Task::Junction {
                        count: terms.len(),
                        conjunction: false,
                    });
                    tasks.extend(terms.iter().rev().map(Task::Visit));
                }
                Task::Not => {
                    let inner = results
                        .pop()
                        .expect("semantic predicate clone stack is malformed");
                    results.push(Self::Not(Box::new(inner)));
                }
                Task::Junction { count, conjunction } => {
                    let start = results
                        .len()
                        .checked_sub(count)
                        .expect("semantic predicate clone arity is malformed");
                    let terms = results.drain(start..).collect();
                    results.push(if conjunction {
                        Self::And(terms)
                    } else {
                        Self::Or(terms)
                    });
                }
            }
        }
        assert_eq!(results.len(), 1, "semantic predicate clone is malformed");
        results
            .pop()
            .expect("semantic predicate clone result is missing")
    }
}

impl SemanticPredicate {
    pub fn negate(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Not(inner) => *inner,
            predicate => Self::Not(Box::new(predicate)),
        }
    }

    pub fn domain(&self) -> Result<BoolExpr, SemanticFoldError> {
        let mut pending = vec![PredicateDomainTask::Visit(self)];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                PredicateDomainTask::Visit(predicate) => match predicate {
                    Self::True => results.push(BoolExpr::True),
                    Self::False => results.push(BoolExpr::False),
                    Self::Test(insn) => results.push(BoolExpr::instruction(insn.id)),
                    Self::Not(inner) => {
                        pending.push(PredicateDomainTask::CombineNot);
                        pending.push(PredicateDomainTask::Visit(inner));
                    }
                    Self::And(terms) | Self::Or(terms) => {
                        pending.push(PredicateDomainTask::Combine {
                            count: terms.len(),
                            conjunction: matches!(predicate, Self::And(_)),
                        });
                        pending.extend(terms.iter().rev().map(PredicateDomainTask::Visit));
                    }
                },
                PredicateDomainTask::CombineNot => {
                    let inner = results.pop().ok_or(SemanticFoldError::MalformedWorkStack)?;
                    results.push(BoolExpr::not(inner));
                }
                PredicateDomainTask::Combine { count, conjunction } => {
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(SemanticFoldError::MalformedWorkStack)?;
                    let terms = results.drain(start..).collect();
                    results.push(if conjunction {
                        BoolExpr::and(terms)
                    } else {
                        BoolExpr::or(terms)
                    });
                }
            }
        }
        if results.len() != 1 {
            return Err(SemanticFoldError::MalformedWorkStack);
        }
        results.pop().ok_or(SemanticFoldError::MalformedWorkStack)
    }

    pub fn symbols(&self) -> std::collections::BTreeSet<BoolVariable> {
        let mut symbols = std::collections::BTreeSet::new();
        let mut pending = vec![self];
        while let Some(predicate) = pending.pop() {
            match predicate {
                Self::Test(instruction) => {
                    symbols.insert(BoolVariable::Instruction(instruction.id));
                }
                Self::Not(inner) => pending.push(inner),
                Self::And(terms) | Self::Or(terms) => pending.extend(terms),
                Self::True | Self::False => {}
            }
        }
        symbols
    }

    pub fn effects(&self) -> InstructionEffects {
        let mut effects = InstructionEffects::PURE;
        let mut pending = vec![self];
        while let Some(predicate) = pending.pop() {
            match predicate {
                Self::Test(operation) => {
                    effects = effects.join(operation.direct_effects().without_control());
                    for operand in operation.operands() {
                        effects = effects.join(operand.effects());
                    }
                    if let Some(target) = operation.compound_target() {
                        effects = effects.join(target.effects());
                    }
                }
                Self::Not(inner) => pending.push(inner),
                Self::And(terms) | Self::Or(terms) => pending.extend(terms),
                Self::True | Self::False => {}
            }
        }
        effects
    }
}

enum PredicateDomainTask<'a> {
    Visit(&'a SemanticPredicate),
    CombineNot,
    Combine { count: usize, conjunction: bool },
}

#[derive(Debug)]
pub enum SemanticNode {
    Empty,
    Sequence(Vec<SemanticNode>),
    BasicBlock(SemanticBlock),
    If {
        condition: SemanticOperand<SemanticPredicate>,
        then_node: Box<SemanticNode>,
        else_node: Option<Box<SemanticNode>>,
    },
    Loop {
        control: SemanticLoopControl,
        header: Option<BlockId>,
        kind: SemanticLoopKind,
        test: SemanticLoopTest,
        body: Box<SemanticNode>,
    },
    For {
        control: SemanticLoopControl,
        init: SemanticStatement,
        condition: SemanticOperand<SemanticPredicate>,
        update: SemanticStatement,
        body: Box<SemanticNode>,
    },
    ForEach {
        control: SemanticLoopControl,
        variable: RegisterArg,
        iterable: SemanticOperand<SemanticExpression>,
        body: Box<SemanticNode>,
    },
    Switch {
        region: Option<RegionId>,
        selector: SemanticOperand<SemanticExpression>,
        cases: Vec<SemanticSwitchCase>,
    },
    Try {
        region: RegionId,
        body: Box<SemanticNode>,
        catches: Vec<SemanticCatch>,
        finally: Option<SemanticFinally>,
    },
    Synchronized {
        region: RegionId,
        lock: SemanticOperand<SemanticExpression>,
        method: bool,
        body: Box<SemanticNode>,
    },
    Label {
        label: SemanticLabel,
        body: Box<SemanticNode>,
    },
    Leave(SemanticLeave),
}

impl Clone for SemanticNode {
    fn clone(&self) -> Self {
        let mut tasks = vec![SemanticCloneTask::Visit(self)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                SemanticCloneTask::Visit(Self::Empty) => results.push(Self::Empty),
                SemanticCloneTask::Visit(Self::BasicBlock(block)) => {
                    results.push(Self::BasicBlock(block.clone()));
                }
                SemanticCloneTask::Visit(Self::Leave(leave)) => {
                    results.push(Self::Leave(leave.clone()));
                }
                SemanticCloneTask::Visit(Self::Sequence(children)) => {
                    tasks.push(SemanticCloneTask::Rebuild(SemanticCloneFrame::Sequence(
                        children.len(),
                    )));
                    tasks.extend(children.iter().rev().map(SemanticCloneTask::Visit));
                }
                SemanticCloneTask::Visit(Self::If {
                    condition,
                    then_node,
                    else_node,
                }) => {
                    tasks.push(SemanticCloneTask::Rebuild(SemanticCloneFrame::If {
                        condition: condition.clone(),
                        has_else: else_node.is_some(),
                    }));
                    if let Some(else_node) = else_node {
                        tasks.push(SemanticCloneTask::Visit(else_node));
                    }
                    tasks.push(SemanticCloneTask::Visit(then_node));
                }
                SemanticCloneTask::Visit(Self::Loop {
                    control,
                    header,
                    kind,
                    test,
                    body,
                }) => {
                    tasks.push(SemanticCloneTask::Rebuild(SemanticCloneFrame::Loop {
                        control: *control,
                        header: *header,
                        kind: *kind,
                        condition: test.condition.clone(),
                    }));
                    tasks.push(SemanticCloneTask::Visit(body));
                    tasks.push(SemanticCloneTask::Visit(&test.setup));
                }
                SemanticCloneTask::Visit(Self::For {
                    control,
                    init,
                    condition,
                    update,
                    body,
                }) => {
                    tasks.push(SemanticCloneTask::Rebuild(SemanticCloneFrame::For {
                        control: *control,
                        init: init.clone(),
                        condition: condition.clone(),
                        update: update.clone(),
                    }));
                    tasks.push(SemanticCloneTask::Visit(body));
                }
                SemanticCloneTask::Visit(Self::ForEach {
                    control,
                    variable,
                    iterable,
                    body,
                }) => {
                    tasks.push(SemanticCloneTask::Rebuild(SemanticCloneFrame::ForEach {
                        control: *control,
                        variable: variable.clone(),
                        iterable: iterable.clone(),
                    }));
                    tasks.push(SemanticCloneTask::Visit(body));
                }
                SemanticCloneTask::Visit(Self::Switch {
                    region,
                    selector,
                    cases,
                }) => {
                    tasks.push(SemanticCloneTask::Rebuild(SemanticCloneFrame::Switch {
                        region: *region,
                        selector: selector.clone(),
                        metadata: cases
                            .iter()
                            .map(|case| (case.values.clone(), case.is_default))
                            .collect(),
                    }));
                    tasks.extend(
                        cases
                            .iter()
                            .rev()
                            .map(|case| SemanticCloneTask::Visit(&case.body)),
                    );
                }
                SemanticCloneTask::Visit(Self::Try {
                    region,
                    body,
                    catches,
                    finally,
                }) => {
                    tasks.push(SemanticCloneTask::Rebuild(SemanticCloneFrame::Try {
                        region: *region,
                        catches: catches
                            .iter()
                            .map(|catch| {
                                (
                                    catch.region,
                                    catch.exception_types.clone(),
                                    catch.exception_value.clone(),
                                )
                            })
                            .collect(),
                        finally: finally.as_ref().map(|finally| finally.region),
                    }));
                    if let Some(finally) = finally {
                        tasks.push(SemanticCloneTask::Visit(&finally.body));
                    }
                    tasks.extend(
                        catches
                            .iter()
                            .rev()
                            .map(|catch| SemanticCloneTask::Visit(&catch.body)),
                    );
                    tasks.push(SemanticCloneTask::Visit(body));
                }
                SemanticCloneTask::Visit(Self::Synchronized {
                    region,
                    lock,
                    method,
                    body,
                }) => {
                    tasks.push(SemanticCloneTask::Rebuild(
                        SemanticCloneFrame::Synchronized {
                            region: *region,
                            lock: lock.clone(),
                            method: *method,
                        },
                    ));
                    tasks.push(SemanticCloneTask::Visit(body));
                }
                SemanticCloneTask::Visit(Self::Label { label, body }) => {
                    tasks.push(SemanticCloneTask::Rebuild(SemanticCloneFrame::Label(
                        *label,
                    )));
                    tasks.push(SemanticCloneTask::Visit(body));
                }
                SemanticCloneTask::Rebuild(frame) => frame.rebuild(&mut results),
            }
        }
        assert_eq!(results.len(), 1, "semantic node clone is malformed");
        results
            .pop()
            .expect("semantic node clone result is missing")
    }
}

enum SemanticCloneTask<'a> {
    Visit(&'a SemanticNode),
    Rebuild(SemanticCloneFrame),
}

enum SemanticCloneFrame {
    Sequence(usize),
    If {
        condition: SemanticOperand<SemanticPredicate>,
        has_else: bool,
    },
    Loop {
        control: SemanticLoopControl,
        header: Option<BlockId>,
        kind: SemanticLoopKind,
        condition: SemanticOperand<SemanticPredicate>,
    },
    For {
        control: SemanticLoopControl,
        init: SemanticStatement,
        condition: SemanticOperand<SemanticPredicate>,
        update: SemanticStatement,
    },
    ForEach {
        control: SemanticLoopControl,
        variable: RegisterArg,
        iterable: SemanticOperand<SemanticExpression>,
    },
    Switch {
        region: Option<RegionId>,
        selector: SemanticOperand<SemanticExpression>,
        metadata: Vec<(Vec<i32>, bool)>,
    },
    Try {
        region: RegionId,
        catches: Vec<(RegionId, Vec<super::ArgType>, Option<RegisterArg>)>,
        finally: Option<RegionId>,
    },
    Synchronized {
        region: RegionId,
        lock: SemanticOperand<SemanticExpression>,
        method: bool,
    },
    Label(SemanticLabel),
}

impl SemanticCloneFrame {
    fn child_count(&self) -> usize {
        match self {
            Self::Sequence(count) => *count,
            Self::If { has_else, .. } => 1 + usize::from(*has_else),
            Self::Loop { .. } => 2,
            Self::For { .. }
            | Self::ForEach { .. }
            | Self::Synchronized { .. }
            | Self::Label(_) => 1,
            Self::Switch { metadata, .. } => metadata.len(),
            Self::Try {
                catches, finally, ..
            } => 1 + catches.len() + usize::from(finally.is_some()),
        }
    }

    fn rebuild(self, results: &mut Vec<SemanticNode>) {
        let count = self.child_count();
        let start = results
            .len()
            .checked_sub(count)
            .expect("semantic node clone arity is malformed");
        let mut children = results.drain(start..);
        let node = match self {
            Self::Sequence(_) => SemanticNode::Sequence(children.by_ref().collect()),
            Self::If {
                condition,
                has_else,
            } => SemanticNode::If {
                condition,
                then_node: Box::new(Self::child(&mut children)),
                else_node: has_else.then(|| Box::new(Self::child(&mut children))),
            },
            Self::Loop {
                control,
                header,
                kind,
                condition,
            } => SemanticNode::Loop {
                control,
                header,
                kind,
                test: SemanticLoopTest {
                    setup: Box::new(Self::child(&mut children)),
                    condition,
                },
                body: Box::new(Self::child(&mut children)),
            },
            Self::For {
                control,
                init,
                condition,
                update,
            } => SemanticNode::For {
                control,
                init,
                condition,
                update,
                body: Box::new(Self::child(&mut children)),
            },
            Self::ForEach {
                control,
                variable,
                iterable,
            } => SemanticNode::ForEach {
                control,
                variable,
                iterable,
                body: Box::new(Self::child(&mut children)),
            },
            Self::Switch {
                region,
                selector,
                metadata,
            } => SemanticNode::Switch {
                region,
                selector,
                cases: metadata
                    .into_iter()
                    .map(|(values, is_default)| SemanticSwitchCase {
                        values,
                        is_default,
                        body: Self::child(&mut children),
                    })
                    .collect(),
            },
            Self::Try {
                region,
                catches,
                finally,
            } => {
                let body = Self::child(&mut children);
                let catches = catches
                    .into_iter()
                    .map(|(region, exception_types, exception_value)| SemanticCatch {
                        region,
                        exception_types,
                        exception_value,
                        body: Self::child(&mut children),
                    })
                    .collect();
                let finally = finally.map(|region| SemanticFinally {
                    region,
                    body: Box::new(Self::child(&mut children)),
                });
                SemanticNode::Try {
                    region,
                    body: Box::new(body),
                    catches,
                    finally,
                }
            }
            Self::Synchronized {
                region,
                lock,
                method,
            } => SemanticNode::Synchronized {
                region,
                lock,
                method,
                body: Box::new(Self::child(&mut children)),
            },
            Self::Label(label) => SemanticNode::Label {
                label,
                body: Box::new(Self::child(&mut children)),
            },
        };
        assert!(
            children.next().is_none(),
            "semantic node clone frame left children"
        );
        drop(children);
        results.push(node);
    }

    fn child(children: &mut impl Iterator<Item = SemanticNode>) -> SemanticNode {
        children
            .next()
            .expect("semantic node clone child is missing")
    }
}

impl SemanticPredicate {
    pub fn constant_value(&self) -> Option<bool> {
        enum Task<'a> {
            Visit(&'a SemanticPredicate),
            Not,
            Junction { count: usize, conjunction: bool },
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(Self::True) => values.push(Some(true)),
                Task::Visit(Self::False) => values.push(Some(false)),
                Task::Visit(Self::Test(test)) => values.push(Self::constant_test(test)),
                Task::Visit(Self::Not(inner)) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(inner));
                }
                Task::Visit(Self::And(terms)) => {
                    tasks.push(Task::Junction {
                        count: terms.len(),
                        conjunction: true,
                    });
                    tasks.extend(terms.iter().rev().map(Task::Visit));
                }
                Task::Visit(Self::Or(terms)) => {
                    tasks.push(Task::Junction {
                        count: terms.len(),
                        conjunction: false,
                    });
                    tasks.extend(terms.iter().rev().map(Task::Visit));
                }
                Task::Not => {
                    let value = values.pop()?;
                    values.push(value.map(|value| !value));
                }
                Task::Junction { count, conjunction } => {
                    let start = values.len().checked_sub(count)?;
                    let terms = values.drain(start..).collect::<Vec<_>>();
                    values.push(terms.into_iter().collect::<Option<Vec<_>>>().map(|terms| {
                        if conjunction {
                            terms.into_iter().all(|term| term)
                        } else {
                            terms.into_iter().any(|term| term)
                        }
                    }));
                }
            }
        }
        (values.len() == 1)
            .then(|| values.pop())
            .flatten()
            .flatten()
    }

    fn constant_test(test: &SemanticOperation) -> Option<bool> {
        if test.insn_type != InsnType::If {
            return None;
        }
        let [left, right] = test.operands() else {
            return None;
        };
        if left.same_stable_value(right) {
            return Some(match test.payload.if_op? {
                IfOp::Eq | IfOp::Ge | IfOp::Le => true,
                IfOp::Ne | IfOp::Lt | IfOp::Gt => false,
            });
        }
        let left = left.literal_value()?;
        let right = right.literal_value()?;
        Some(match test.payload.if_op? {
            IfOp::Eq => left == right,
            IfOp::Ne => left != right,
            IfOp::Lt => (left as i32) < (right as i32),
            IfOp::Ge => (left as i32) >= (right as i32),
            IfOp::Gt => (left as i32) > (right as i32),
            IfOp::Le => (left as i32) <= (right as i32),
        })
    }
}

impl SemanticNode {
    pub fn sequence(nodes: impl IntoIterator<Item = SemanticNode>) -> Self {
        let mut flattened = Vec::new();
        for node in nodes {
            match node {
                Self::Empty => {}
                Self::Sequence(children) => flattened.extend(children),
                other => flattened.push(other),
            }
        }
        match flattened.len() {
            0 => Self::Empty,
            1 => flattened.into_iter().next().unwrap_or(Self::Empty),
            _ => Self::Sequence(flattened),
        }
    }

    pub fn guard(condition: SemanticPredicate, node: SemanticNode) -> Self {
        if condition.constant_value() == Some(true) || matches!(node, Self::Empty) {
            node
        } else if condition.constant_value() == Some(false) {
            Self::Empty
        } else {
            Self::If {
                condition: SemanticOperand::new(condition),
                then_node: Box::new(node),
                else_node: None,
            }
        }
    }

    pub fn branch(
        condition: SemanticPredicate,
        then_node: SemanticNode,
        else_node: Option<SemanticNode>,
    ) -> Self {
        match condition.constant_value() {
            Some(true) => return then_node,
            Some(false) => return else_node.unwrap_or(Self::Empty),
            None => {}
        }
        match (then_node, else_node) {
            (Self::Empty, None | Some(Self::Empty)) => Self::Empty,
            (Self::Empty, Some(else_node)) => Self::guard(condition.negate(), else_node),
            (then_node, None | Some(Self::Empty)) => Self::guard(condition, then_node),
            (then_node, Some(else_node)) => Self::If {
                condition: SemanticOperand::new(condition),
                then_node: Box::new(then_node),
                else_node: Some(Box::new(else_node)),
            },
        }
    }
}

#[derive(Debug, Clone)]
pub struct SsaSemantics {
    values: SsaValueGraph,
    regions: RegionGraph,
}

#[derive(Debug, Clone)]
pub struct ValueSemantics {
    values: SsaValueGraph,
    constants: BTreeMap<super::analysis::SsaVar, InsnArg>,
    recovered_phis: BTreeSet<super::analysis::SsaVar>,
    regions: RegionGraph,
}

#[derive(Debug, Clone)]
pub struct SourceSemantics {
    types: super::analysis::SourceTypeEnvironment,
    regions: RegionGraph,
}

#[derive(Debug, Clone)]
pub struct SourceSyntaxSemantics {
    types: super::analysis::SourceTypeEnvironment,
    regions: RegionGraph,
}

pub trait SemanticContext {
    fn regions(&self) -> &RegionGraph;
}

/// Typestates whose registers carry stable source-level `code_var` identity.
pub trait SourceVariableContext: SemanticContext {}

#[derive(Debug, Clone)]
pub struct SemanticMethod<State> {
    body: SemanticNode,
    state: State,
}

impl SsaSemantics {
    pub fn values(&self) -> &SsaValueGraph {
        &self.values
    }

    pub fn regions(&self) -> &RegionGraph {
        &self.regions
    }
}

impl ValueSemantics {
    pub fn values(&self) -> &SsaValueGraph {
        &self.values
    }

    pub fn constants(&self) -> &BTreeMap<super::analysis::SsaVar, InsnArg> {
        &self.constants
    }

    pub fn recovered_phis(&self) -> &BTreeSet<super::analysis::SsaVar> {
        &self.recovered_phis
    }

    pub fn regions(&self) -> &RegionGraph {
        &self.regions
    }

    pub(crate) fn into_regions(self) -> RegionGraph {
        self.regions
    }
}

impl SourceSemantics {
    pub fn types(&self) -> &super::analysis::SourceTypeEnvironment {
        &self.types
    }

    pub(crate) fn types_mut(&mut self) -> &mut super::analysis::SourceTypeEnvironment {
        &mut self.types
    }

    pub fn regions(&self) -> &RegionGraph {
        &self.regions
    }
}

impl SourceSyntaxSemantics {
    pub fn types(&self) -> &super::analysis::SourceTypeEnvironment {
        &self.types
    }

    pub fn regions(&self) -> &RegionGraph {
        &self.regions
    }
}

impl SemanticContext for SsaSemantics {
    fn regions(&self) -> &RegionGraph {
        &self.regions
    }
}

impl SemanticContext for ValueSemantics {
    fn regions(&self) -> &RegionGraph {
        &self.regions
    }
}

impl SemanticContext for SourceSemantics {
    fn regions(&self) -> &RegionGraph {
        &self.regions
    }
}

impl SemanticContext for SourceSyntaxSemantics {
    fn regions(&self) -> &RegionGraph {
        &self.regions
    }
}

impl SourceVariableContext for SourceSemantics {}

impl SourceVariableContext for SourceSyntaxSemantics {}

impl<State> SemanticMethod<State> {
    pub fn body(&self) -> &SemanticNode {
        &self.body
    }

    pub(crate) fn body_mut(&mut self) -> &mut SemanticNode {
        &mut self.body
    }

    pub fn state(&self) -> &State {
        &self.state
    }

    pub(crate) fn state_mut(&mut self) -> &mut State {
        &mut self.state
    }

    pub(crate) fn parts_mut(&mut self) -> (&mut SemanticNode, &mut State) {
        (&mut self.body, &mut self.state)
    }

    pub(crate) fn into_parts(self) -> (SemanticNode, State) {
        (self.body, self.state)
    }
}

impl<State: SemanticContext> SemanticMethod<State> {
    pub fn verify(&self) -> Result<(), SemanticInvariantError> {
        verify::SemanticVerifier::verify(&self.body, self.state.regions())
    }
}
