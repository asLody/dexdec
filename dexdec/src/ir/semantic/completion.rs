//! Completion algebra for structured semantic IR.
//!
//! This is the single source of truth for normal and abrupt control outcomes.
//! Consumers must not infer reachability from rendered shapes or instruction
//! patterns.

use std::collections::BTreeSet;

use crate::ir::{BlockId, BoolExpr, RegionId};

use super::{
    SemanticBlock, SemanticLabel, SemanticLeave, SemanticLeaveKind, SemanticLoopControl,
    SemanticLoopKind, SemanticNode, SemanticPredicate, SemanticVisitor,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum AbruptCompletion {
    FallThrough {
        block: BlockId,
        source: RegionId,
        destination: RegionId,
        target: RegionId,
        cleanup: Vec<RegionId>,
    },
    Jump {
        block: BlockId,
        source: RegionId,
        destination: RegionId,
        target: RegionId,
        cleanup: Vec<RegionId>,
    },
    BreakLabel {
        label: SemanticLabel,
        source: RegionId,
        destination: RegionId,
        target: RegionId,
        cleanup: Vec<RegionId>,
    },
    ContinueLabel {
        label: SemanticLabel,
        source: RegionId,
        destination: RegionId,
        target: RegionId,
        cleanup: Vec<RegionId>,
    },
    Return {
        source: RegionId,
        destination: RegionId,
        target: RegionId,
        cleanup: Vec<RegionId>,
    },
    Throw {
        source: RegionId,
        destination: RegionId,
        target: RegionId,
        cleanup: Vec<RegionId>,
    },
    NoReturnCall,
    Break {
        source: RegionId,
        destination: RegionId,
        target: RegionId,
        cleanup: Vec<RegionId>,
    },
    Continue {
        source: RegionId,
        destination: RegionId,
        target: RegionId,
        cleanup: Vec<RegionId>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum SemanticTransfer {
    FallThrough(BlockId, RegionId),
    Jump(BlockId, RegionId),
    BreakLabel(SemanticLabel),
    ContinueLabel(SemanticLabel),
    Return,
    Throw,
    Break(RegionId),
    Continue(RegionId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SemanticControlTopology {
    tokens: Vec<ControlToken>,
}

impl SemanticControlTopology {
    pub(crate) fn analyze(root: &SemanticNode) -> Self {
        let mut topology = Self { tokens: Vec::new() };
        topology.visit_node(root);
        topology
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ControlToken {
    Empty,
    Block(BlockId),
    Sequence(usize),
    If(bool),
    Loop(SemanticLoopControl, Option<BlockId>, SemanticLoopKind),
    For(SemanticLoopControl),
    ForEach(SemanticLoopControl),
    Switch(Option<RegionId>, Vec<bool>),
    Try(RegionId, Vec<RegionId>, Option<RegionId>),
    Synchronized(RegionId, bool),
    Label(SemanticLabel),
    Leave(AbruptCompletion, bool),
    End,
}

impl SemanticVisitor for SemanticControlTopology {
    fn enter_node(&mut self, node: &SemanticNode) {
        self.tokens.push(match node {
            SemanticNode::Empty => ControlToken::Empty,
            SemanticNode::BasicBlock(block) => ControlToken::Block(block.id),
            SemanticNode::Sequence(children) => ControlToken::Sequence(children.len()),
            SemanticNode::If { else_node, .. } => ControlToken::If(else_node.is_some()),
            SemanticNode::Loop {
                control,
                header,
                kind,
                ..
            } => ControlToken::Loop(*control, *header, *kind),
            SemanticNode::For { control, .. } => ControlToken::For(*control),
            SemanticNode::ForEach { control, .. } => ControlToken::ForEach(*control),
            SemanticNode::Switch { region, cases, .. } => {
                ControlToken::Switch(*region, cases.iter().map(|case| case.is_default).collect())
            }
            SemanticNode::Try {
                region,
                catches,
                finally,
                ..
            } => ControlToken::Try(
                *region,
                catches.iter().map(|catch| catch.region).collect(),
                finally.as_ref().map(|finally| finally.region),
            ),
            SemanticNode::Synchronized { region, method, .. } => {
                ControlToken::Synchronized(*region, *method)
            }
            SemanticNode::Label { label, .. } => ControlToken::Label(*label),
            SemanticNode::Leave(leave) => ControlToken::Leave(
                AbruptCompletion::from_leave(leave),
                leave.condition.is_some(),
            ),
        });
    }

    fn exit_node(&mut self, node: &SemanticNode) {
        if matches!(
            node,
            SemanticNode::Sequence(_)
                | SemanticNode::If { .. }
                | SemanticNode::Loop { .. }
                | SemanticNode::For { .. }
                | SemanticNode::ForEach { .. }
                | SemanticNode::Switch { .. }
                | SemanticNode::Try { .. }
                | SemanticNode::Synchronized { .. }
                | SemanticNode::Label { .. }
        ) {
            self.tokens.push(ControlToken::End);
        }
    }
}

impl AbruptCompletion {
    fn from_leave(leave: &SemanticLeave) -> Self {
        let source = leave.source;
        let destination = leave.destination;
        let target = leave.target;
        let cleanup = leave.cleanup.clone();
        match &leave.kind {
            SemanticLeaveKind::FallThrough(block) => Self::FallThrough {
                block: *block,
                source,
                destination,
                target,
                cleanup,
            },
            SemanticLeaveKind::Jump(block) => Self::Jump {
                block: *block,
                source,
                destination,
                target,
                cleanup,
            },
            SemanticLeaveKind::BreakLabel(label) => Self::BreakLabel {
                label: *label,
                source,
                destination,
                target,
                cleanup,
            },
            SemanticLeaveKind::ContinueLabel(label) => Self::ContinueLabel {
                label: *label,
                source,
                destination,
                target,
                cleanup,
            },
            SemanticLeaveKind::Return(_) => Self::Return {
                source,
                destination,
                target,
                cleanup,
            },
            SemanticLeaveKind::Throw(_) => Self::Throw {
                source,
                destination,
                target,
                cleanup,
            },
            SemanticLeaveKind::Break => Self::Break {
                source,
                destination,
                target,
                cleanup,
            },
            SemanticLeaveKind::Continue => Self::Continue {
                source,
                destination,
                target,
                cleanup,
            },
        }
    }

    pub(crate) fn is_open(&self) -> bool {
        matches!(self, Self::FallThrough { .. } | Self::Jump { .. })
    }

    fn is_open_to(&self, scope: RegionId) -> bool {
        matches!(
            self,
            Self::FallThrough { target, .. } | Self::Jump { target, .. } if *target == scope
        )
    }

    fn is_break_for_region(&self, region: RegionId) -> bool {
        matches!(self, Self::Break { target, .. } if *target == region)
    }

    fn is_continue_for_region(&self, region: RegionId) -> bool {
        matches!(self, Self::Continue { target, .. } if *target == region)
    }

    fn is_break_for_label(&self, expected: SemanticLabel) -> bool {
        matches!(self, Self::BreakLabel { label, .. } if *label == expected)
    }

    fn is_continue_for_label(&self, expected: SemanticLabel) -> bool {
        matches!(self, Self::ContinueLabel { label, .. } if *label == expected)
    }

    fn exits_loop(&self, region: RegionId, label: Option<SemanticLabel>) -> bool {
        match self {
            Self::Return { .. } | Self::Throw { .. } | Self::NoReturnCall => true,
            Self::FallThrough { target, .. }
            | Self::Jump { target, .. }
            | Self::Break { target, .. }
            | Self::Continue { target, .. } => *target != region,
            Self::BreakLabel { label: target, .. } | Self::ContinueLabel { label: target, .. } => {
                Some(*target) != label
            }
        }
    }

    fn transfer(&self) -> SemanticTransfer {
        match self {
            Self::FallThrough { block, target, .. } => {
                SemanticTransfer::FallThrough(*block, *target)
            }
            Self::Jump { block, target, .. } => SemanticTransfer::Jump(*block, *target),
            Self::BreakLabel { label, .. } => SemanticTransfer::BreakLabel(*label),
            Self::ContinueLabel { label, .. } => SemanticTransfer::ContinueLabel(*label),
            Self::Return { .. } => SemanticTransfer::Return,
            Self::Throw { .. } => SemanticTransfer::Throw,
            Self::NoReturnCall => SemanticTransfer::Throw,
            Self::Break { target, .. } => SemanticTransfer::Break(*target),
            Self::Continue { target, .. } => SemanticTransfer::Continue(*target),
        }
    }
}

impl SemanticTransfer {
    pub(crate) fn from_leave(leave: &SemanticLeave) -> Self {
        match &leave.kind {
            SemanticLeaveKind::FallThrough(block) => Self::FallThrough(*block, leave.target),
            SemanticLeaveKind::Jump(block) => Self::Jump(*block, leave.target),
            SemanticLeaveKind::BreakLabel(label) => Self::BreakLabel(*label),
            SemanticLeaveKind::ContinueLabel(label) => Self::ContinueLabel(*label),
            SemanticLeaveKind::Return(_) => Self::Return,
            SemanticLeaveKind::Throw(_) => Self::Throw,
            SemanticLeaveKind::Break => Self::Break(leave.target),
            SemanticLeaveKind::Continue => Self::Continue(leave.target),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SemanticCompletion {
    normal: bool,
    abrupt: BTreeSet<AbruptCompletion>,
}

impl SemanticCompletion {
    pub(crate) fn analyze(root: &SemanticNode) -> Self {
        match CompletionInterpreter::analyze(root, &SemanticCompletionDomain) {
            Ok(completion) => completion,
            Err(error) => match error {},
        }
    }

    pub(crate) fn can_complete_normally(&self) -> bool {
        self.normal
    }

    pub(crate) fn has_open_transfer(&self) -> bool {
        self.abrupt.iter().any(AbruptCompletion::is_open)
    }

    pub(crate) fn has_open_transfer_to(&self, scope: RegionId) -> bool {
        self.abrupt
            .iter()
            .any(|completion| completion.is_open_to(scope))
    }

    pub(crate) fn has_closed_transfer(&self) -> bool {
        self.abrupt.iter().any(|completion| !completion.is_open())
    }

    pub(crate) fn is_transfer_free(&self) -> bool {
        self.abrupt.is_empty()
    }

    pub(crate) fn same_control_outcomes(&self, other: &Self) -> bool {
        self.normal == other.normal
            && self
                .abrupt
                .iter()
                .map(AbruptCompletion::transfer)
                .collect::<BTreeSet<_>>()
                == other
                    .abrupt
                    .iter()
                    .map(AbruptCompletion::transfer)
                    .collect::<BTreeSet<_>>()
    }

    pub(crate) fn same_void_method_outcomes(&self, other: &Self) -> bool {
        fn outcomes(completion: &SemanticCompletion) -> BTreeSet<SemanticTransfer> {
            let mut outcomes = completion
                .abrupt
                .iter()
                .map(AbruptCompletion::transfer)
                .collect::<BTreeSet<_>>();
            if completion.normal {
                outcomes.insert(SemanticTransfer::Return);
            }
            outcomes
        }
        outcomes(self) == outcomes(other)
    }

    pub(crate) fn has_break_to_region(&self, region: RegionId) -> bool {
        self.abrupt
            .iter()
            .any(|completion| completion.is_break_for_region(region))
    }

    pub(crate) fn has_break_to_label(&self, label: SemanticLabel) -> bool {
        self.abrupt
            .iter()
            .any(|completion| completion.is_break_for_label(label))
    }

    pub(crate) fn is_continue_to_region(&self, region: RegionId) -> bool {
        !self.normal
            && self.abrupt.len() == 1
            && self
                .abrupt
                .iter()
                .all(|completion| completion.is_continue_for_region(region))
    }

    pub(crate) fn has_continue_to_region(&self, region: RegionId) -> bool {
        self.abrupt
            .iter()
            .any(|completion| completion.is_continue_for_region(region))
    }

    pub(crate) fn has_continue_to_label(&self, label: SemanticLabel) -> bool {
        self.abrupt
            .iter()
            .any(|completion| completion.is_continue_for_label(label))
    }

    pub(crate) fn exits_loop(&self, region: RegionId, label: Option<SemanticLabel>) -> bool {
        !self.normal
            && !self.abrupt.is_empty()
            && self
                .abrupt
                .iter()
                .all(|completion| completion.exits_loop(region, label))
    }

    fn normal() -> Self {
        Self {
            normal: true,
            abrupt: BTreeSet::new(),
        }
    }

    fn abrupt(completion: AbruptCompletion) -> Self {
        Self {
            normal: false,
            abrupt: BTreeSet::from([completion]),
        }
    }

    fn sequence(children: impl IntoIterator<Item = Self>) -> Self {
        let mut result = Self::normal();
        for child in children {
            if !result.normal {
                break;
            }
            result.normal = child.normal;
            result.abrupt.extend(child.abrupt);
        }
        result
    }

    fn alternatives(children: impl IntoIterator<Item = Self>) -> Self {
        let mut result = Self {
            normal: false,
            abrupt: BTreeSet::new(),
        };
        for child in children {
            result.normal |= child.normal;
            result.abrupt.extend(child.abrupt);
        }
        result
    }

    fn consume_region_loop(mut self, region: Option<RegionId>) -> (Self, bool, bool) {
        let Some(region) = region else {
            return (self, false, false);
        };
        let has_break = self
            .abrupt
            .iter()
            .any(|completion| completion.is_break_for_region(region));
        let has_continue = self
            .abrupt
            .iter()
            .any(|completion| completion.is_continue_for_region(region));
        self.abrupt.retain(|completion| {
            !completion.is_break_for_region(region) && !completion.is_continue_for_region(region)
        });
        (self, has_break, has_continue)
    }

    fn consume_labeled_loop(mut self, label: SemanticLabel) -> (Self, bool, bool) {
        let has_break = self
            .abrupt
            .iter()
            .any(|completion| completion.is_break_for_label(label));
        let has_continue = self
            .abrupt
            .iter()
            .any(|completion| completion.is_continue_for_label(label));
        self.abrupt.retain(|completion| {
            !completion.is_break_for_label(label) && !completion.is_continue_for_label(label)
        });
        (self, has_break, has_continue)
    }

    fn consume_loop(self, control: SemanticLoopControl) -> (Self, bool, bool) {
        match control {
            SemanticLoopControl::Region(region) => self.consume_region_loop(Some(region)),
            SemanticLoopControl::Label(label) => self.consume_labeled_loop(label),
        }
    }

    fn consume_label(mut self, label: SemanticLabel) -> Self {
        let has_break = self
            .abrupt
            .iter()
            .any(|completion| completion.is_break_for_label(label));
        self.abrupt
            .retain(|completion| !completion.is_break_for_label(label));
        self.normal |= has_break;
        self
    }
}

fn block_has_no_return_call(block: &SemanticBlock) -> bool {
    block.statements.iter().any(|statement| {
        statement
            .instruction_ref()
            .is_some_and(|operation| operation.payload.no_return)
    })
}

struct SemanticCompletionDomain;

impl CompletionDomain for SemanticCompletionDomain {
    type State = SemanticCompletion;
    type Error = std::convert::Infallible;

    fn normal(&self) -> Result<Self::State, Self::Error> {
        Ok(SemanticCompletion::normal())
    }

    fn no_return_call(&self) -> Result<Self::State, Self::Error> {
        Ok(SemanticCompletion::abrupt(AbruptCompletion::NoReturnCall))
    }

    fn leave(&self, leave: &SemanticLeave) -> Result<Self::State, Self::Error> {
        Ok(SemanticCompletion::abrupt(AbruptCompletion::from_leave(
            leave,
        )))
    }

    fn sequence(&self, children: Vec<Self::State>) -> Result<Self::State, Self::Error> {
        Ok(SemanticCompletion::sequence(children))
    }

    fn branch(
        &self,
        condition: &SemanticPredicate,
        then_state: Self::State,
        else_state: Option<Self::State>,
    ) -> Result<Self::State, Self::Error> {
        Ok(match condition.constant_value() {
            Some(true) => then_state,
            Some(false) => else_state.unwrap_or_else(SemanticCompletion::normal),
            None => SemanticCompletion::alternatives([
                then_state,
                else_state.unwrap_or_else(SemanticCompletion::normal),
            ]),
        })
    }

    fn loop_node(
        &self,
        control: SemanticLoopControl,
        kind: SemanticLoopKind,
        condition: &SemanticPredicate,
        setup: Self::State,
        body: Self::State,
    ) -> Result<Self::State, Self::Error> {
        let (mut body, has_break, has_continue) = body.consume_loop(control);
        let condition_true = condition.constant_value() == Some(true);
        let condition_false = condition.constant_value() == Some(false);
        let reaches_test = body.normal || has_continue;
        if matches!(kind, SemanticLoopKind::PostTested) {
            if reaches_test {
                body.abrupt.extend(setup.abrupt);
            }
            body.normal = has_break || (reaches_test && setup.normal && !condition_true);
            return Ok(body);
        }

        if !setup.normal {
            return Ok(setup);
        }
        if matches!(kind, SemanticLoopKind::PreTested) && condition_false {
            return Ok(setup);
        }
        body.abrupt.extend(setup.abrupt);
        body.normal = match kind {
            SemanticLoopKind::PreTested => !condition_true || has_break,
            SemanticLoopKind::Endless => has_break,
            SemanticLoopKind::PostTested => unreachable!(),
        };
        Ok(body)
    }

    fn for_node(
        &self,
        control: SemanticLoopControl,
        condition: &SemanticPredicate,
        body: Self::State,
    ) -> Result<Self::State, Self::Error> {
        let (mut body, has_break, _) = body.consume_loop(control);
        body.normal = condition.constant_value() != Some(true) || has_break;
        Ok(body)
    }

    fn for_each_node(
        &self,
        control: SemanticLoopControl,
        body: Self::State,
    ) -> Result<Self::State, Self::Error> {
        let (mut body, _, _) = body.consume_loop(control);
        body.normal = true;
        Ok(body)
    }

    fn switch_node(
        &self,
        region: Option<RegionId>,
        has_default: bool,
        cases: Vec<Self::State>,
    ) -> Result<Self::State, Self::Error> {
        let mut result = SemanticCompletion::alternatives(cases);
        if let Some(region) = region {
            let has_break = result
                .abrupt
                .iter()
                .any(|completion| completion.is_break_for_region(region));
            result
                .abrupt
                .retain(|completion| !completion.is_break_for_region(region));
            result.normal |= has_break;
        }
        result.normal |= !has_default;
        Ok(result)
    }

    fn try_node(
        &self,
        catches: usize,
        has_finally: bool,
        mut children: Vec<Self::State>,
    ) -> Result<Self::State, Self::Error> {
        let finally = has_finally.then(|| children.pop().expect("finally child"));
        let protected = SemanticCompletion::alternatives(children.drain(..=catches));
        let Some(finally) = finally else {
            return Ok(protected);
        };
        let mut result = SemanticCompletion {
            normal: protected.normal && finally.normal,
            abrupt: finally.abrupt,
        };
        if finally.normal {
            result.abrupt.extend(protected.abrupt);
        }
        Ok(result)
    }

    fn synchronized(&self, body: Self::State) -> Result<Self::State, Self::Error> {
        Ok(body)
    }

    fn label(&self, label: SemanticLabel, body: Self::State) -> Result<Self::State, Self::Error> {
        Ok(body.consume_label(label))
    }
}

pub(crate) trait CompletionDomain {
    type State;
    type Error;

    fn normal(&self) -> Result<Self::State, Self::Error>;
    fn basic_block(&self, _block: &SemanticBlock) -> Result<Self::State, Self::Error> {
        self.normal()
    }
    fn no_return_call(&self) -> Result<Self::State, Self::Error> {
        self.normal()
    }
    fn leave(&self, leave: &SemanticLeave) -> Result<Self::State, Self::Error>;
    fn sequence(&self, children: Vec<Self::State>) -> Result<Self::State, Self::Error>;
    fn branch(
        &self,
        condition: &SemanticPredicate,
        then_state: Self::State,
        else_state: Option<Self::State>,
    ) -> Result<Self::State, Self::Error>;
    fn loop_node(
        &self,
        control: SemanticLoopControl,
        kind: SemanticLoopKind,
        condition: &SemanticPredicate,
        setup: Self::State,
        body: Self::State,
    ) -> Result<Self::State, Self::Error>;
    fn for_node(
        &self,
        control: SemanticLoopControl,
        condition: &SemanticPredicate,
        body: Self::State,
    ) -> Result<Self::State, Self::Error>;
    fn for_each_node(
        &self,
        control: SemanticLoopControl,
        body: Self::State,
    ) -> Result<Self::State, Self::Error>;
    fn switch_node(
        &self,
        region: Option<RegionId>,
        has_default: bool,
        cases: Vec<Self::State>,
    ) -> Result<Self::State, Self::Error>;
    fn try_node(
        &self,
        catches: usize,
        has_finally: bool,
        children: Vec<Self::State>,
    ) -> Result<Self::State, Self::Error>;
    fn synchronized(&self, body: Self::State) -> Result<Self::State, Self::Error>;
    fn label(&self, label: SemanticLabel, body: Self::State) -> Result<Self::State, Self::Error>;
}

enum CompletionTask<'a> {
    Visit(&'a SemanticNode),
    Combine(&'a SemanticNode, CompletionFrame),
}

enum CompletionFrame {
    Sequence(usize),
    If {
        condition: SemanticPredicate,
        has_else: bool,
    },
    Loop {
        control: SemanticLoopControl,
        kind: SemanticLoopKind,
        condition: SemanticPredicate,
    },
    For {
        control: SemanticLoopControl,
        condition: SemanticPredicate,
    },
    ForEach {
        control: SemanticLoopControl,
    },
    Switch {
        region: Option<RegionId>,
        cases: usize,
        has_default: bool,
    },
    Try {
        catches: usize,
        has_finally: bool,
    },
    Synchronized,
    Label(SemanticLabel),
}

impl CompletionFrame {
    fn child_count(&self) -> usize {
        match self {
            Self::Sequence(count) => *count,
            Self::If { has_else, .. } => usize::from(*has_else) + 1,
            Self::Loop { .. } => 2,
            Self::For { .. } | Self::ForEach { .. } | Self::Synchronized | Self::Label(_) => 1,
            Self::Switch { cases, .. } => *cases,
            Self::Try {
                catches,
                has_finally,
            } => 1 + *catches + usize::from(*has_finally),
        }
    }
}

pub(crate) struct CompletionInterpreter;

impl CompletionInterpreter {
    pub(crate) fn analyze<D: CompletionDomain>(
        root: &SemanticNode,
        domain: &D,
    ) -> Result<D::State, D::Error> {
        Self::analyze_with(root, domain, |_, _| {})
    }

    pub(crate) fn analyze_facts<D: CompletionDomain>(
        root: &SemanticNode,
        domain: &D,
    ) -> Result<std::collections::BTreeMap<usize, D::State>, D::Error>
    where
        D::State: Clone,
    {
        let mut facts = std::collections::BTreeMap::new();
        Self::analyze_with(root, domain, |node, state| {
            facts.insert(std::ptr::from_ref(node).addr(), state.clone());
        })?;
        Ok(facts)
    }

    fn analyze_with<D: CompletionDomain>(
        root: &SemanticNode,
        domain: &D,
        mut record: impl FnMut(&SemanticNode, &D::State),
    ) -> Result<D::State, D::Error> {
        let mut tasks = vec![CompletionTask::Visit(root)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CompletionTask::Visit(node) => {
                    Self::schedule(node, domain, &mut tasks, &mut results, &mut record)?
                }
                CompletionTask::Combine(node, frame) => {
                    let count = frame.child_count();
                    let children = results.split_off(results.len().saturating_sub(count));
                    let state = Self::combine(frame, children, domain)?;
                    record(node, &state);
                    results.push(state);
                }
            }
        }
        match results.pop() {
            Some(result) => Ok(result),
            None => domain.normal(),
        }
    }

    fn schedule<'a, D: CompletionDomain>(
        node: &'a SemanticNode,
        domain: &D,
        tasks: &mut Vec<CompletionTask<'a>>,
        results: &mut Vec<D::State>,
        record: &mut impl FnMut(&SemanticNode, &D::State),
    ) -> Result<(), D::Error> {
        match node {
            SemanticNode::Empty => {
                let state = domain.normal()?;
                record(node, &state);
                results.push(state);
            }
            SemanticNode::BasicBlock(block) => {
                let state = if block_has_no_return_call(block) {
                    domain.no_return_call()?
                } else {
                    domain.basic_block(block)?
                };
                record(node, &state);
                results.push(state);
            }
            SemanticNode::Leave(leave) => {
                let state = domain.leave(leave)?;
                record(node, &state);
                results.push(state);
            }
            SemanticNode::Sequence(children) => {
                tasks.push(CompletionTask::Combine(
                    node,
                    CompletionFrame::Sequence(children.len()),
                ));
                tasks.extend(children.iter().rev().map(CompletionTask::Visit));
            }
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => {
                tasks.push(CompletionTask::Combine(
                    node,
                    CompletionFrame::If {
                        condition: condition.value.clone(),
                        has_else: else_node.is_some(),
                    },
                ));
                if let Some(else_node) = else_node {
                    tasks.push(CompletionTask::Visit(else_node));
                }
                tasks.push(CompletionTask::Visit(then_node));
            }
            SemanticNode::Loop {
                control,
                kind,
                test,
                body,
                ..
            } => {
                tasks.push(CompletionTask::Combine(
                    node,
                    CompletionFrame::Loop {
                        control: *control,
                        kind: *kind,
                        condition: test.condition.value.clone(),
                    },
                ));
                tasks.push(CompletionTask::Visit(body));
                tasks.push(CompletionTask::Visit(&test.setup));
            }
            SemanticNode::For {
                control,
                condition,
                body,
                ..
            } => {
                tasks.push(CompletionTask::Combine(
                    node,
                    CompletionFrame::For {
                        control: *control,
                        condition: condition.value.clone(),
                    },
                ));
                tasks.push(CompletionTask::Visit(body));
            }
            SemanticNode::ForEach { control, body, .. } => {
                tasks.push(CompletionTask::Combine(
                    node,
                    CompletionFrame::ForEach { control: *control },
                ));
                tasks.push(CompletionTask::Visit(body));
            }
            SemanticNode::Switch { region, cases, .. } => {
                tasks.push(CompletionTask::Combine(
                    node,
                    CompletionFrame::Switch {
                        region: *region,
                        cases: cases.len(),
                        has_default: cases.iter().any(|case| case.is_default),
                    },
                ));
                tasks.extend(
                    cases
                        .iter()
                        .rev()
                        .map(|case| CompletionTask::Visit(&case.body)),
                );
            }
            SemanticNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                tasks.push(CompletionTask::Combine(
                    node,
                    CompletionFrame::Try {
                        catches: catches.len(),
                        has_finally: finally.is_some(),
                    },
                ));
                if let Some(finally) = finally {
                    tasks.push(CompletionTask::Visit(&finally.body));
                }
                tasks.extend(
                    catches
                        .iter()
                        .rev()
                        .map(|catch| CompletionTask::Visit(&catch.body)),
                );
                tasks.push(CompletionTask::Visit(body));
            }
            SemanticNode::Synchronized { body, .. } => {
                tasks.push(CompletionTask::Combine(node, CompletionFrame::Synchronized));
                tasks.push(CompletionTask::Visit(body));
            }
            SemanticNode::Label { label, body } => {
                tasks.push(CompletionTask::Combine(
                    node,
                    CompletionFrame::Label(*label),
                ));
                tasks.push(CompletionTask::Visit(body));
            }
        }
        Ok(())
    }

    fn combine<D: CompletionDomain>(
        frame: CompletionFrame,
        mut children: Vec<D::State>,
        domain: &D,
    ) -> Result<D::State, D::Error> {
        match frame {
            CompletionFrame::Sequence(_) => domain.sequence(children),
            CompletionFrame::If {
                condition,
                has_else,
            } => {
                let then_state = children.remove(0);
                let else_state = has_else.then(|| children.remove(0));
                domain.branch(&condition, then_state, else_state)
            }
            CompletionFrame::Loop {
                control,
                kind,
                condition,
            } => domain.loop_node(
                control,
                kind,
                &condition,
                children.remove(0),
                children.remove(0),
            ),
            CompletionFrame::For { control, condition } => {
                domain.for_node(control, &condition, children.remove(0))
            }
            CompletionFrame::ForEach { control } => {
                domain.for_each_node(control, children.remove(0))
            }
            CompletionFrame::Switch {
                region,
                has_default,
                ..
            } => domain.switch_node(region, has_default, children),
            CompletionFrame::Try {
                catches,
                has_finally,
            } => domain.try_node(catches, has_finally, children),
            CompletionFrame::Synchronized => domain.synchronized(children.remove(0)),
            CompletionFrame::Label(label) => domain.label(label, children.remove(0)),
        }
    }
}

/// Reaching predicate for normal fallthrough through structured code.
///
/// Acyclic decisions are exact. Constructs whose finite syntax cannot encode
/// all dynamic exits conservatively return an over-approximation, so consumers
/// may lose an optimization proof but never remove a reachable path.
pub(crate) struct SemanticFallthrough;

impl SemanticFallthrough {
    pub(crate) fn analyze(root: &SemanticNode) -> Result<BoolExpr, super::SemanticFoldError> {
        CompletionInterpreter::analyze(root, &FallthroughDomain)
    }
}

struct FallthroughDomain;

impl CompletionDomain for FallthroughDomain {
    type State = BoolExpr;
    type Error = super::SemanticFoldError;

    fn normal(&self) -> Result<Self::State, Self::Error> {
        Ok(BoolExpr::True)
    }

    fn no_return_call(&self) -> Result<Self::State, Self::Error> {
        Ok(BoolExpr::False)
    }

    fn leave(&self, _leave: &SemanticLeave) -> Result<Self::State, Self::Error> {
        Ok(BoolExpr::False)
    }

    fn sequence(&self, children: Vec<Self::State>) -> Result<Self::State, Self::Error> {
        Ok(BoolExpr::and(children))
    }

    fn branch(
        &self,
        condition: &SemanticPredicate,
        then_state: Self::State,
        else_state: Option<Self::State>,
    ) -> Result<Self::State, Self::Error> {
        let condition = condition.domain()?;
        Ok(BoolExpr::or(vec![
            BoolExpr::and(vec![condition.clone(), then_state]),
            BoolExpr::and(vec![
                BoolExpr::not(condition),
                else_state.unwrap_or(BoolExpr::True),
            ]),
        ]))
    }

    fn loop_node(
        &self,
        _control: SemanticLoopControl,
        kind: SemanticLoopKind,
        _condition: &SemanticPredicate,
        setup: Self::State,
        _body: Self::State,
    ) -> Result<Self::State, Self::Error> {
        Ok(match kind {
            SemanticLoopKind::PreTested | SemanticLoopKind::Endless => setup,
            SemanticLoopKind::PostTested => BoolExpr::True,
        })
    }

    fn for_node(
        &self,
        _control: SemanticLoopControl,
        _condition: &SemanticPredicate,
        _body: Self::State,
    ) -> Result<Self::State, Self::Error> {
        Ok(BoolExpr::True)
    }

    fn for_each_node(
        &self,
        _control: SemanticLoopControl,
        _body: Self::State,
    ) -> Result<Self::State, Self::Error> {
        Ok(BoolExpr::True)
    }

    fn switch_node(
        &self,
        _region: Option<RegionId>,
        _has_default: bool,
        _cases: Vec<Self::State>,
    ) -> Result<Self::State, Self::Error> {
        Ok(BoolExpr::True)
    }

    fn try_node(
        &self,
        _catches: usize,
        _has_finally: bool,
        _children: Vec<Self::State>,
    ) -> Result<Self::State, Self::Error> {
        Ok(BoolExpr::True)
    }

    fn synchronized(&self, body: Self::State) -> Result<Self::State, Self::Error> {
        Ok(body)
    }

    fn label(&self, _label: SemanticLabel, _body: Self::State) -> Result<Self::State, Self::Error> {
        Ok(BoolExpr::True)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{BlockId, RegionId, SemanticSwitchCase};

    fn leave(kind: SemanticLeaveKind, target: RegionId) -> SemanticNode {
        SemanticNode::Leave(SemanticLeave {
            site: None,
            condition: None,
            kind,
            edge: None,
            origin: None,
            source: target,
            destination: target,
            target,
            cleanup: Vec::new(),
        })
    }

    #[test]
    fn label_break_completes_the_owned_label() {
        let region = RegionId::new(1);
        let label = SemanticLabel::block(region, BlockId::new(2));
        let node = SemanticNode::Label {
            label,
            body: Box::new(leave(SemanticLeaveKind::BreakLabel(label), region)),
        };

        assert!(SemanticCompletion::analyze(&node).can_complete_normally());
    }

    #[test]
    fn exhaustive_terminal_switch_does_not_complete_normally() {
        let region = RegionId::new(1);
        let node = SemanticNode::Switch {
            region: Some(region),
            selector: super::super::SemanticOperand::new(crate::ir::SemanticExpression::Literal(
                crate::ir::LiteralArg::new(0, crate::ir::ArgType::INT),
            )),
            cases: vec![
                SemanticSwitchCase {
                    values: vec![0],
                    is_default: false,
                    body: leave(SemanticLeaveKind::Return(None), region),
                },
                SemanticSwitchCase {
                    values: Vec::new(),
                    is_default: true,
                    body: leave(
                        SemanticLeaveKind::Throw(crate::ir::SemanticExpression::Literal(
                            crate::ir::LiteralArg::new(0, crate::ir::ArgType::INT),
                        )),
                        region,
                    ),
                },
            ],
        };

        assert!(!SemanticCompletion::analyze(&node).can_complete_normally());
    }

    #[test]
    fn switch_without_default_keeps_the_unmatched_path() {
        let region = RegionId::new(1);
        let node = SemanticNode::Switch {
            region: Some(region),
            selector: super::super::SemanticOperand::new(crate::ir::SemanticExpression::Literal(
                crate::ir::LiteralArg::new(0, crate::ir::ArgType::INT),
            )),
            cases: vec![SemanticSwitchCase {
                values: vec![0],
                is_default: false,
                body: leave(SemanticLeaveKind::Return(None), region),
            }],
        };

        assert!(SemanticCompletion::analyze(&node).can_complete_normally());
    }
}
