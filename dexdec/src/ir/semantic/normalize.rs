use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    analysis::{SsaValueGraph, SsaVar},
    InsnArg, LiteralArg, RegionGraph, SemanticExpression, SemanticExpressionTransform,
    SemanticFoldError, SemanticFolder, SemanticInstructions, SemanticLabel, SemanticLeaveKind,
    SemanticOperation, SemanticPredicate, SemanticStatement, SemanticVisitor,
};

use super::{
    SemanticMethod, SemanticNode, SourceSemantics, SourceSyntaxSemantics, SourceVariableContext,
    SsaSemantics, ValueSemantics,
};

impl SemanticMethod<SsaSemantics> {
    pub(crate) fn from_ssa(
        body: SemanticNode,
        regions: RegionGraph,
        values: SsaValueGraph,
    ) -> Self {
        Self {
            body,
            state: SsaSemantics { values, regions },
        }
    }

    pub(crate) fn into_values(
        self,
        constants: BTreeMap<SsaVar, InsnArg>,
        recovered_phis: BTreeSet<SsaVar>,
    ) -> SemanticMethod<ValueSemantics> {
        let (body, state) = self.into_parts();
        SemanticMethod {
            body,
            state: ValueSemantics {
                values: state.values,
                constants,
                recovered_phis,
                regions: state.regions,
            },
        }
    }
}

impl SemanticMethod<SourceSemantics> {
    pub(crate) fn from_source(
        body: SemanticNode,
        types: crate::ir::analysis::SourceTypeEnvironment,
        regions: RegionGraph,
    ) -> Self {
        Self {
            body,
            state: SourceSemantics { types, regions },
        }
    }

    pub(crate) fn into_source_syntax(self) -> SemanticMethod<SourceSyntaxSemantics> {
        let (body, state) = self.into_parts();
        SemanticMethod {
            body,
            state: SourceSyntaxSemantics {
                types: state.types,
                regions: state.regions,
            },
        }
    }
}

impl<State> SemanticMethod<State> {
    pub(crate) fn normalize(&mut self) -> Result<(), SemanticFoldError> {
        self.normalize_with(ReachabilityMode::PruneUnreachable)
    }

    pub(crate) fn normalize_before_phi_lowering(&mut self) -> Result<(), SemanticFoldError> {
        self.normalize_with(ReachabilityMode::PreserveCfgTopology)
    }

    fn normalize_with(&mut self, reachability: ReachabilityMode) -> Result<(), SemanticFoldError> {
        let required_cfg = reachability
            .preserves_cfg_topology()
            .then(|| SemanticCfgIdentity::collect(&self.body));
        let body = std::mem::replace(&mut self.body, SemanticNode::Empty);
        self.body = if reachability.preserves_cfg_topology() {
            CompletionPreservingRewrite::apply("semantic-normalize", body, |body| {
                SemanticNormalization::new(reachability).rewrite(body)
            })?
        } else {
            CompletionPreservingRewrite::apply_control("terminal-label-compose", body, |body| {
                SemanticNormalization::new(reachability).rewrite(body)
            })?
        };
        if required_cfg.is_some_and(|required| required != SemanticCfgIdentity::collect(&self.body))
        {
            return Err(SemanticFoldError::CfgIdentityChanged {
                transform: "semantic-normalize-before-phi",
            });
        }
        Ok(())
    }

    pub(crate) fn normalize_void_method_completion(&mut self) -> Result<(), SemanticFoldError> {
        let body = std::mem::replace(&mut self.body, SemanticNode::Empty);
        self.body = CompletionPreservingRewrite::apply_void_method(
            "void-method-completion",
            body,
            |body| TerminalCompletionRewrite::rewrite(body, TerminalCompletionTarget::Method),
        )?;
        Ok(())
    }
}

impl<State: SourceVariableContext> SemanticMethod<State> {
    pub(crate) fn normalize_source(&mut self) -> Result<(), SemanticFoldError> {
        let body = std::mem::replace(&mut self.body, SemanticNode::Empty);
        self.body = CompletionPreservingRewrite::apply_control(
            "source-semantic-normalize",
            body,
            |body| {
                let body =
                    SemanticNormalization::new(ReachabilityMode::PruneUnreachable).rewrite(body)?;
                SourceSemanticNormalizer.fold_node(body)
            },
        )?;
        Ok(())
    }

    pub(crate) fn normalize_source_variables(&mut self) -> Result<(), SemanticFoldError> {
        let body = std::mem::replace(&mut self.body, SemanticNode::Empty);
        self.body =
            CompletionPreservingRewrite::apply("source-semantic-normalize", body, |body| {
                SourceSemanticNormalizer.fold_node(body)
            })?;
        Ok(())
    }
}

impl SemanticMethod<SourceSyntaxSemantics> {
    pub(crate) fn compact(&mut self) -> Result<(), SemanticFoldError> {
        let body = std::mem::replace(&mut self.body, SemanticNode::Empty);
        self.body = CompletionPreservingRewrite::apply("kotlin-semantic-compact", body, |body| {
            SourceSemanticNormalizer.fold_node(body)
        })?;
        Ok(())
    }
}

struct CompletionPreservingRewrite;

impl CompletionPreservingRewrite {
    fn apply<F>(
        name: &'static str,
        body: SemanticNode,
        rewrite: F,
    ) -> Result<SemanticNode, SemanticFoldError>
    where
        F: FnOnce(SemanticNode) -> Result<SemanticNode, SemanticFoldError>,
    {
        let before = crate::profile_scope!(
            "semantic.completion.before",
            super::SemanticCompletion::analyze(&body)
        );
        let rewritten = rewrite(body)?;
        let after = crate::profile_scope!(
            "semantic.completion.after",
            super::SemanticCompletion::analyze(&rewritten)
        );
        if before != after {
            return Err(SemanticFoldError::CompletionChanged { transform: name });
        }
        Ok(rewritten)
    }

    fn apply_control<F>(
        name: &'static str,
        body: SemanticNode,
        rewrite: F,
    ) -> Result<SemanticNode, SemanticFoldError>
    where
        F: FnOnce(SemanticNode) -> Result<SemanticNode, SemanticFoldError>,
    {
        let before = crate::profile_scope!(
            "semantic.completion.before",
            super::SemanticCompletion::analyze(&body)
        );
        let rewritten = rewrite(body)?;
        let after = crate::profile_scope!(
            "semantic.completion.after",
            super::SemanticCompletion::analyze(&rewritten)
        );
        if !before.same_control_outcomes(&after) {
            return Err(SemanticFoldError::CompletionChanged { transform: name });
        }
        Ok(rewritten)
    }

    fn apply_void_method<F>(
        name: &'static str,
        body: SemanticNode,
        rewrite: F,
    ) -> Result<SemanticNode, SemanticFoldError>
    where
        F: FnOnce(SemanticNode) -> Result<SemanticNode, SemanticFoldError>,
    {
        let before = crate::profile_scope!(
            "semantic.completion.before",
            super::SemanticCompletion::analyze(&body)
        );
        let rewritten = rewrite(body)?;
        let after = crate::profile_scope!(
            "semantic.completion.after",
            super::SemanticCompletion::analyze(&rewritten)
        );
        if !before.same_void_method_outcomes(&after) {
            return Err(SemanticFoldError::CompletionChanged { transform: name });
        }
        Ok(rewritten)
    }
}

struct SemanticNormalization {
    reachability: ReachabilityMode,
}

impl SemanticNormalization {
    fn new(reachability: ReachabilityMode) -> Self {
        Self { reachability }
    }

    fn rewrite(&mut self, body: SemanticNode) -> Result<SemanticNode, SemanticFoldError> {
        crate::profile_scope!(
            "semantic.normalize.fused",
            SemanticFolder::fold_node(self, body)
        )
    }
}

impl SemanticFolder for SemanticNormalization {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        let node = SemanticNormalizer::new(self.reachability).finish_node(node)?;
        if self.reachability.preserves_cfg_topology() {
            return Ok(node);
        }
        let mut composer = TerminalLabelComposer::new(self.reachability);
        let node = composer.finish_node(node)?;
        if composer.changed {
            SemanticNormalizer::new(self.reachability).finish_node(node)
        } else {
            Ok(node)
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ReachabilityMode {
    PreserveCfgTopology,
    PruneUnreachable,
}

impl ReachabilityMode {
    fn preserves_cfg_topology(self) -> bool {
        self == Self::PreserveCfgTopology
    }
}

struct SemanticNormalizer {
    reachability: ReachabilityMode,
}

impl SemanticNormalizer {
    fn new(reachability: ReachabilityMode) -> Self {
        Self { reachability }
    }

    fn branch(
        &self,
        condition: SemanticPredicate,
        then_node: SemanticNode,
        else_node: Option<SemanticNode>,
    ) -> SemanticNode {
        if matches!(self.reachability, ReachabilityMode::PreserveCfgTopology)
            && condition.constant_value().is_some()
        {
            return SemanticNode::If {
                condition: crate::ir::SemanticOperand::new(condition),
                then_node: Box::new(then_node),
                else_node: else_node.map(Box::new),
            };
        }
        SemanticNode::branch(condition, then_node, else_node)
    }
}

impl SemanticFolder for SemanticNormalizer {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        let node = if self.reachability.preserves_cfg_topology() {
            node
        } else {
            NaturalLoopCompletion::normalize(node)?
        };
        let node = LoopBinding::rewrite(node, self.reachability)?;
        let node = AcyclicExitComposer::rewrite(node, self.reachability);
        let node = match node {
            SemanticNode::Sequence(nodes) if self.reachability.preserves_cfg_topology() => {
                SemanticNode::sequence(nodes)
            }
            SemanticNode::Sequence(nodes) => NormalCompletion::sequence(nodes),
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => self.branch(
                condition.into_inner(),
                *then_node,
                else_node.map(|node| *node),
            ),
            node => node,
        };
        Ok(node)
    }
}

#[derive(PartialEq, Eq)]
struct SemanticCfgIdentity {
    blocks: BTreeSet<crate::ir::BlockId>,
    edges: BTreeSet<crate::ir::RegionEdge>,
}

impl SemanticCfgIdentity {
    fn collect(root: &SemanticNode) -> Self {
        let mut identity = Self {
            blocks: BTreeSet::new(),
            edges: BTreeSet::new(),
        };
        identity.visit_node(root);
        identity
    }
}

impl SemanticVisitor for SemanticCfgIdentity {
    fn enter_node(&mut self, node: &SemanticNode) {
        if let SemanticNode::BasicBlock(block) = node {
            self.blocks.insert(block.id);
        }
        if let SemanticNode::Leave(leave) = node {
            self.edges.extend(leave.edge);
        }
    }
}

struct LoopBinding;

impl LoopBinding {
    fn rewrite(
        node: SemanticNode,
        reachability: ReachabilityMode,
    ) -> Result<SemanticNode, SemanticFoldError> {
        let SemanticNode::Label { label, body } = node else {
            return Ok(node);
        };
        let control = match body.as_ref() {
            SemanticNode::Loop { control, .. }
            | SemanticNode::For { control, .. }
            | SemanticNode::ForEach { control, .. } => *control,
            _ => {
                return Ok(SemanticNode::Label { label, body });
            }
        };
        let references = LabelReferences::count(&body, label);
        let mut binding = LoopExitBinding {
            source: label,
            target: control,
            count: 0,
            reachability,
        };
        let body = binding.fold_node(*body)?;
        Ok(if binding.count == references {
            body
        } else {
            SemanticNode::Label {
                label,
                body: Box::new(body),
            }
        })
    }
}

struct LoopExitBinding {
    source: SemanticLabel,
    target: crate::ir::SemanticLoopControl,
    count: usize,
    reachability: ReachabilityMode,
}

impl SemanticFolder for LoopExitBinding {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        Ok(match node {
            SemanticNode::Leave(mut leave) if matches!(leave.kind, SemanticLeaveKind::BreakLabel(label) if label == self.source) =>
            {
                self.count += 1;
                match self.target {
                    crate::ir::SemanticLoopControl::Region(region) => {
                        leave.kind = SemanticLeaveKind::Break;
                        leave.target = region;
                    }
                    crate::ir::SemanticLoopControl::Label(label) => {
                        leave.kind = SemanticLeaveKind::BreakLabel(label);
                    }
                }
                SemanticNode::Leave(leave)
            }
            SemanticNode::Sequence(nodes) => SemanticNode::sequence(nodes),
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => SemanticNormalizer::new(self.reachability).branch(
                condition.into_inner(),
                *then_node,
                else_node.map(|node| *node),
            ),
            node => node,
        })
    }
}

/// Eliminate a single-exit acyclic label by composing its continuation into
/// normally completing paths. Mutually exclusive paths may receive cloned
/// continuations under a strict semantic-node growth budget.
struct AcyclicExitComposer;

impl AcyclicExitComposer {
    const EXPANSION_BUDGET: usize = 256;

    fn rewrite(node: SemanticNode, reachability: ReachabilityMode) -> SemanticNode {
        if reachability.preserves_cfg_topology() {
            return node;
        }
        let SemanticNode::Label { label, body } = node else {
            return node;
        };
        if LabelReferences::count(&body, label) == 0 {
            return *body;
        }
        let original = (*body).clone();
        let Some(composed) = Self::compose(*body, label) else {
            return SemanticNode::Label {
                label,
                body: Box::new(original),
            };
        };
        if LabelReferences::count(&composed, label) != 0 {
            SemanticNode::Label {
                label,
                body: Box::new(original),
            }
        } else {
            composed
        }
    }

    fn compose(root: SemanticNode, label: SemanticLabel) -> Option<SemanticNode> {
        let mut tasks = vec![ExitCompositionTask::Visit {
            node: root,
            continuation: ExitContinuation::Boundary,
            cleanups: Vec::new(),
        }];
        let mut results = Vec::new();
        let mut expansion = 0usize;
        while let Some(task) = tasks.pop() {
            match task {
                ExitCompositionTask::Visit {
                    node,
                    continuation,
                    cleanups,
                } => {
                    if LabelReferences::count(&node, label) == 0 {
                        results.push(if NormalCompletion::can_complete(&node) {
                            SemanticNode::sequence([node, continuation.into_node()])
                        } else {
                            node
                        });
                        continue;
                    }
                    match node {
                        SemanticNode::Leave(leave)
                            if leave.cleanup == cleanups
                                && matches!(leave.kind, SemanticLeaveKind::BreakLabel(target) if target == label) =>
                        {
                            results.push(SemanticNode::Empty);
                        }
                        SemanticNode::Sequence(children) => {
                            tasks.push(ExitCompositionTask::Sequence {
                                children,
                                continuation,
                                cleanups,
                            });
                        }
                        SemanticNode::If {
                            condition,
                            then_node,
                            else_node,
                        } => {
                            let else_node =
                                else_node.map(|node| *node).unwrap_or(SemanticNode::Empty);
                            if NormalCompletion::can_complete(&then_node)
                                && NormalCompletion::can_complete(&else_node)
                            {
                                expansion = expansion
                                    .checked_add(continuation.node_size())
                                    .filter(|size| *size <= Self::EXPANSION_BUDGET)?;
                            }
                            tasks.push(ExitCompositionTask::RebuildIf(condition));
                            tasks.push(ExitCompositionTask::Visit {
                                node: else_node,
                                continuation: continuation.clone(),
                                cleanups: cleanups.clone(),
                            });
                            tasks.push(ExitCompositionTask::Visit {
                                node: *then_node,
                                continuation,
                                cleanups,
                            });
                        }
                        SemanticNode::Synchronized {
                            region,
                            lock,
                            method,
                            body,
                        } if continuation.is_boundary() => {
                            let mut body_cleanups = Vec::with_capacity(cleanups.len() + 1);
                            body_cleanups.push(region);
                            body_cleanups.extend(cleanups);
                            tasks.push(ExitCompositionTask::RebuildSynchronized {
                                region,
                                lock,
                                method,
                            });
                            tasks.push(ExitCompositionTask::Visit {
                                node: *body,
                                continuation: ExitContinuation::Boundary,
                                cleanups: body_cleanups,
                            });
                        }
                        SemanticNode::Try {
                            region,
                            body,
                            mut catches,
                            finally,
                        } if continuation.is_boundary() => {
                            if finally.as_ref().is_some_and(|finally| {
                                LabelReferences::count(&finally.body, label) != 0
                            }) {
                                return None;
                            }
                            let mut body_cleanups = cleanups;
                            if let Some(finally) = &finally {
                                body_cleanups.insert(0, finally.region);
                            }
                            let catch_bodies = catches
                                .iter_mut()
                                .map(|catch| {
                                    std::mem::replace(&mut catch.body, SemanticNode::Empty)
                                })
                                .collect::<Vec<_>>();
                            tasks.push(ExitCompositionTask::RebuildTry {
                                region,
                                catches,
                                finally,
                            });
                            tasks.extend(catch_bodies.into_iter().rev().map(|node| {
                                ExitCompositionTask::Visit {
                                    node,
                                    continuation: ExitContinuation::Boundary,
                                    cleanups: body_cleanups.clone(),
                                }
                            }));
                            tasks.push(ExitCompositionTask::Visit {
                                node: *body,
                                continuation: ExitContinuation::Boundary,
                                cleanups: body_cleanups,
                            });
                        }
                        _ => return None,
                    }
                }
                ExitCompositionTask::Sequence {
                    mut children,
                    continuation,
                    cleanups,
                } => {
                    let Some(node) = children.pop() else {
                        results.push(continuation.into_node());
                        continue;
                    };
                    tasks.push(ExitCompositionTask::ContinueSequence {
                        children,
                        cleanups: cleanups.clone(),
                    });
                    tasks.push(ExitCompositionTask::Visit {
                        node,
                        continuation,
                        cleanups,
                    });
                }
                ExitCompositionTask::ContinueSequence { children, cleanups } => {
                    let continuation = results.pop()?;
                    tasks.push(ExitCompositionTask::Sequence {
                        children,
                        continuation: ExitContinuation::from_node(continuation),
                        cleanups,
                    });
                }
                ExitCompositionTask::RebuildIf(condition) => {
                    let else_node = results.pop()?;
                    let then_node = results.pop()?;
                    results.push(SemanticNode::branch(
                        condition.into_inner(),
                        then_node,
                        Some(else_node),
                    ));
                }
                ExitCompositionTask::RebuildSynchronized {
                    region,
                    lock,
                    method,
                } => {
                    let body = results.pop()?;
                    results.push(SemanticNode::Synchronized {
                        region,
                        lock,
                        method,
                        body: Box::new(body),
                    });
                }
                ExitCompositionTask::RebuildTry {
                    region,
                    mut catches,
                    finally,
                } => {
                    let count = catches.len() + 1;
                    let start = results.len().checked_sub(count)?;
                    let drained = results.drain(start..).collect::<Vec<_>>();
                    let mut children = drained.into_iter();
                    let body = children.next()?;
                    for catch in &mut catches {
                        catch.body = children.next()?;
                    }
                    results.push(SemanticNode::Try {
                        region,
                        body: Box::new(body),
                        catches,
                        finally,
                    });
                }
            }
        }
        (results.len() == 1).then(|| results.pop()).flatten()
    }
}

#[derive(Clone)]
enum ExitContinuation {
    Boundary,
    Code(SemanticNode),
}

impl ExitContinuation {
    fn from_node(node: SemanticNode) -> Self {
        if TerminalLabelComposer::is_empty(&node) {
            Self::Boundary
        } else {
            Self::Code(node)
        }
    }

    fn is_boundary(&self) -> bool {
        matches!(self, Self::Boundary)
    }

    fn into_node(self) -> SemanticNode {
        match self {
            Self::Boundary => SemanticNode::Empty,
            Self::Code(node) => node,
        }
    }

    fn node_size(&self) -> usize {
        match self {
            Self::Boundary => 0,
            Self::Code(node) => SemanticSize::of(node),
        }
    }
}

enum ExitCompositionTask {
    Visit {
        node: SemanticNode,
        continuation: ExitContinuation,
        cleanups: Vec<crate::ir::RegionId>,
    },
    Sequence {
        children: Vec<SemanticNode>,
        continuation: ExitContinuation,
        cleanups: Vec<crate::ir::RegionId>,
    },
    ContinueSequence {
        children: Vec<SemanticNode>,
        cleanups: Vec<crate::ir::RegionId>,
    },
    RebuildIf(crate::ir::SemanticOperand<crate::ir::SemanticPredicate>),
    RebuildSynchronized {
        region: crate::ir::RegionId,
        lock: crate::ir::SemanticOperand<SemanticExpression>,
        method: bool,
    },
    RebuildTry {
        region: crate::ir::RegionId,
        catches: Vec<crate::ir::SemanticCatch>,
        finally: Option<crate::ir::SemanticFinally>,
    },
}

struct SourceSemanticNormalizer;

impl SemanticFolder for SourceSemanticNormalizer {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        let node = match node {
            SemanticNode::BasicBlock(block) if block.statements.is_empty() => SemanticNode::Empty,
            node => node,
        };
        let node = RedundantVacuousPredicate::rewrite(node);
        let node = BranchLinearizer::rewrite(node);
        let node = TryLexicalScope::extend(node);
        SemanticNormalizer::new(ReachabilityMode::PruneUnreachable).finish_node(node)
    }
}

/// Remove a vacuous predicate when source-value recovery has transferred its
/// evaluation into the immediately following condition or value expression.
///
/// The shared instruction identity is important: two bytecode comparisons
/// that happen to look alike must still be emitted twice. We also require the
/// replay to occur before any other effect in the following condition so that
/// deleting the stale evaluation cannot reorder throws or side effects.
struct RedundantVacuousPredicate;

struct OperationRegisterReplacement {
    target: crate::ir::InstructionId,
    result: crate::ir::RegisterArg,
    replaced: bool,
}

impl SemanticExpressionTransform for OperationRegisterReplacement {
    fn transform_operation(&mut self, operation: SemanticOperation) -> SemanticExpression {
        if operation.id == self.target {
            self.replaced = true;
            SemanticExpression::Register(self.result.clone())
        } else {
            SemanticExpression::Operation(Box::new(operation))
        }
    }
}

impl RedundantVacuousPredicate {
    fn rewrite(node: SemanticNode) -> SemanticNode {
        let SemanticNode::Sequence(nodes) = node else {
            return node;
        };
        let mut retained = Vec::with_capacity(nodes.len());
        let mut index = 0;
        while index < nodes.len() {
            let redundant = Self::vacuous_is_pure(&nodes[index])
                || nodes
                    .get(index + 1)
                    .and_then(|following| {
                        Self::vacuous_effectful_test_id(&nodes[index]).map(|test| (following, test))
                    })
                    .is_some_and(|(following, test)| {
                        Self::node_replays_before_effects(following, test)
                    });
            if redundant {
                index += 1;
                continue;
            }
            if let Some(following) = nodes.get(index + 1) {
                if let Some(materialized) = Self::materialize_vacuous(&nodes[index], following) {
                    retained.push(materialized);
                    index += 2;
                    continue;
                }
            }
            retained.push(nodes[index].clone());
            index += 1;
        }
        SemanticNode::sequence(retained)
    }

    fn vacuous_is_pure(node: &SemanticNode) -> bool {
        let SemanticNode::If {
            condition,
            then_node,
            else_node: None,
        } = node
        else {
            return false;
        };
        matches!(then_node.as_ref(), SemanticNode::Empty) && condition.effects().is_pure()
    }

    fn vacuous_effectful_test_id(node: &SemanticNode) -> Option<crate::ir::InstructionId> {
        let SemanticNode::If {
            condition,
            then_node,
            else_node: None,
        } = node
        else {
            return None;
        };
        if !matches!(then_node.as_ref(), SemanticNode::Empty) {
            return None;
        }
        let mut ids = BTreeSet::new();
        Self::collect_effectful_test_ids(condition, &mut ids);
        (ids.len() == 1).then(|| ids.into_iter().next()).flatten()
    }

    fn materialize_vacuous(node: &SemanticNode, following: &SemanticNode) -> Option<SemanticNode> {
        let test_id = Self::vacuous_effectful_test_id(node)?;
        let condition = match node {
            SemanticNode::If {
                condition,
                then_node,
                else_node: None,
            } if matches!(then_node.as_ref(), SemanticNode::Empty) => condition,
            _ => return None,
        };
        let test = Self::find_test_operation(condition, test_id)?;
        let target = Self::direct_replayed_operation(&test, following)?;
        let result = target.result.clone()?;
        if Self::operation_occurrences(following, target.id) == 0 {
            return None;
        }
        let guard = Self::guard_for_test(condition, test_id)?;
        let value = if matches!(guard, SemanticPredicate::True) {
            SemanticExpression::Operation(Box::new(target.clone()))
        } else {
            let fallback = result
                .ty
                .is_known()
                .then(|| LiteralArg::new(0, result.ty.clone()))?;
            SemanticExpression::select(
                guard,
                SemanticExpression::Operation(Box::new(target.clone())),
                SemanticExpression::Literal(fallback),
            )
        };
        let definition = SemanticStatement::definition(target.id, result.clone(), value);
        let SemanticNode::BasicBlock(block) = following.clone() else {
            return None;
        };
        if block.statements.iter().any(|statement| {
            statement
                .instruction_ref()
                .is_some_and(|operation| operation.id == target.id)
        }) {
            return None;
        }
        let mut block = SemanticNode::BasicBlock(block);
        let mut replacement = OperationRegisterReplacement {
            target: target.id,
            result,
            replaced: false,
        };
        SemanticInstructions::transform_node(&mut block, &mut replacement).ok()?;
        replacement.replaced.then(|| {
            let SemanticNode::BasicBlock(mut block) = block else {
                unreachable!("materialized basic block changed shape");
            };
            block.statements.insert(0, definition);
            SemanticNode::BasicBlock(block)
        })
    }

    fn find_test_operation(
        predicate: &SemanticPredicate,
        target: crate::ir::InstructionId,
    ) -> Option<SemanticOperation> {
        match predicate {
            SemanticPredicate::Test(operation) if operation.id == target => Some(operation.clone()),
            SemanticPredicate::Not(inner) => Self::find_test_operation(inner, target),
            SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => terms
                .iter()
                .find_map(|term| Self::find_test_operation(term, target)),
            SemanticPredicate::Test(_) | SemanticPredicate::True | SemanticPredicate::False => None,
        }
    }

    fn direct_replayed_operation(
        test: &SemanticOperation,
        following: &SemanticNode,
    ) -> Option<SemanticOperation> {
        let operands = test.evaluation_operands().ok()?;
        let candidates = operands
            .into_iter()
            .filter_map(|operand| match operand {
                SemanticExpression::Operation(operation)
                    if operation.result.is_some()
                        && operation.id.is_valid()
                        && !operation.effects().without_control().is_pure()
                        && Self::operation_occurrences(following, operation.id) != 0 =>
                {
                    Some(operation.as_ref().clone())
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        (candidates.len() == 1)
            .then(|| candidates.into_iter().next())
            .flatten()
    }

    fn guard_for_test(
        predicate: &SemanticPredicate,
        target: crate::ir::InstructionId,
    ) -> Option<SemanticPredicate> {
        match predicate {
            SemanticPredicate::Test(operation) if operation.id == target => {
                Some(SemanticPredicate::True)
            }
            SemanticPredicate::Not(inner) => Self::guard_for_test(inner, target),
            SemanticPredicate::And(terms) => {
                for (index, term) in terms.iter().enumerate() {
                    let direct = match term {
                        SemanticPredicate::Test(operation) => operation.id == target,
                        SemanticPredicate::Not(inner) => {
                            matches!(inner.as_ref(), SemanticPredicate::Test(operation) if operation.id == target)
                        }
                        _ => false,
                    };
                    if !direct {
                        continue;
                    }
                    if terms[..index]
                        .iter()
                        .any(|prefix| !prefix.effects().is_pure())
                    {
                        return None;
                    }
                    return Some(match &terms[..index] {
                        [] => SemanticPredicate::True,
                        [single] => single.clone(),
                        prefix => SemanticPredicate::And(prefix.to_vec()),
                    });
                }
                None
            }
            SemanticPredicate::Or(_) => None,
            SemanticPredicate::Test(_) | SemanticPredicate::True | SemanticPredicate::False => None,
        }
    }

    fn operation_occurrences(node: &SemanticNode, target: crate::ir::InstructionId) -> usize {
        struct Counter {
            target: crate::ir::InstructionId,
            count: usize,
        }
        impl SemanticVisitor for Counter {
            fn enter_operation(&mut self, operation: &SemanticOperation) {
                if operation.id == self.target {
                    self.count += 1;
                }
            }
        }
        let mut counter = Counter { target, count: 0 };
        counter.visit_node(node);
        counter.count
    }

    fn collect_effectful_test_ids(
        predicate: &SemanticPredicate,
        ids: &mut BTreeSet<crate::ir::InstructionId>,
    ) {
        match predicate {
            SemanticPredicate::Test(operation) => {
                if operation.id.is_valid() && !operation.effects().without_control().is_pure() {
                    ids.insert(operation.id);
                }
            }
            SemanticPredicate::Not(inner) => Self::collect_effectful_test_ids(inner, ids),
            SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                terms
                    .iter()
                    .for_each(|term| Self::collect_effectful_test_ids(term, ids));
            }
            SemanticPredicate::True | SemanticPredicate::False => {}
        }
    }

    fn single_test_id(predicate: &SemanticPredicate) -> Option<crate::ir::InstructionId> {
        let operation = match predicate {
            SemanticPredicate::Test(operation) => operation,
            SemanticPredicate::Not(inner) => return Self::single_test_id(inner),
            SemanticPredicate::True
            | SemanticPredicate::False
            | SemanticPredicate::And(_)
            | SemanticPredicate::Or(_) => return None,
        };
        operation.id.is_valid().then_some(operation.id)
    }

    fn node_replays_before_effects(node: &SemanticNode, target: crate::ir::InstructionId) -> bool {
        match node {
            SemanticNode::If { condition, .. } => {
                Self::predicate_replays_before_effects(condition, target)
            }
            SemanticNode::BasicBlock(block) => {
                for statement in &block.statements {
                    if Self::statement_replays_before_effects(statement, target) {
                        return true;
                    }
                    if !statement.effects().is_pure() {
                        return false;
                    }
                }
                false
            }
            SemanticNode::Leave(leave) => {
                if let Some(condition) = &leave.condition {
                    if Self::predicate_replays_before_effects(condition, target) {
                        return true;
                    }
                    if !condition.effects().is_pure() {
                        return false;
                    }
                }
                leave
                    .value()
                    .is_some_and(|value| Self::expression_replays_before_effects(value, target))
            }
            SemanticNode::Empty
            | SemanticNode::Sequence(_)
            | SemanticNode::Loop { .. }
            | SemanticNode::For { .. }
            | SemanticNode::ForEach { .. }
            | SemanticNode::Switch { .. }
            | SemanticNode::Try { .. }
            | SemanticNode::Synchronized { .. }
            | SemanticNode::Label { .. } => false,
        }
    }

    fn statement_replays_before_effects(
        statement: &crate::ir::SemanticStatement,
        target: crate::ir::InstructionId,
    ) -> bool {
        if let Some(value) = statement.value() {
            return Self::expression_replays_before_effects(value, target);
        }
        let Some(instruction) = statement.instruction_ref() else {
            return false;
        };
        let Ok(operands) = instruction.evaluation_operands() else {
            return false;
        };
        for operand in operands {
            if Self::expression_replays_before_effects(operand, target) {
                return true;
            }
            if !operand.effects().is_pure() {
                return false;
            }
        }
        false
    }

    fn predicate_replays_before_effects(
        predicate: &SemanticPredicate,
        target: crate::ir::InstructionId,
    ) -> bool {
        if Self::single_test_id(predicate) == Some(target) {
            return true;
        }
        match predicate {
            SemanticPredicate::Test(operation) => {
                let Ok(operands) = operation.evaluation_operands() else {
                    return false;
                };
                for operand in operands {
                    if Self::expression_replays_before_effects(operand, target) {
                        return true;
                    }
                    if !operand.effects().is_pure() {
                        return false;
                    }
                }
                false
            }
            SemanticPredicate::Not(inner) => Self::predicate_replays_before_effects(inner, target),
            SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                for term in terms {
                    if Self::predicate_replays_before_effects(term, target) {
                        return true;
                    }
                    if !term.effects().is_pure() {
                        return false;
                    }
                }
                false
            }
            SemanticPredicate::True | SemanticPredicate::False => false,
        }
    }

    fn expression_replays_before_effects(
        expression: &SemanticExpression,
        target: crate::ir::InstructionId,
    ) -> bool {
        match expression {
            SemanticExpression::Register(_) | SemanticExpression::Literal(_) => false,
            SemanticExpression::Select { condition, .. } => {
                Self::predicate_replays_before_effects(condition, target)
            }
            SemanticExpression::Operation(operation) => {
                let Ok(operands) = operation.evaluation_operands() else {
                    return false;
                };
                for operand in operands {
                    if Self::expression_replays_before_effects(operand, target) {
                        return true;
                    }
                    if !operand.effects().is_pure() {
                        return false;
                    }
                }
                false
            }
        }
    }
}

struct BranchLinearizer;

impl BranchLinearizer {
    fn rewrite(node: SemanticNode) -> SemanticNode {
        let SemanticNode::If {
            condition,
            then_node,
            else_node: Some(else_node),
        } = node
        else {
            return node;
        };
        let then_normal = super::SemanticCompletion::analyze(&then_node).can_complete_normally();
        let else_normal = super::SemanticCompletion::analyze(&else_node).can_complete_normally();
        match (then_normal, else_normal) {
            (false, _) => SemanticNode::sequence([
                SemanticNode::If {
                    condition,
                    then_node,
                    else_node: None,
                },
                *else_node,
            ]),
            (true, false) => SemanticNode::sequence([
                SemanticNode::If {
                    condition: crate::ir::SemanticOperand {
                        site: condition.site,
                        value: condition.into_inner().negate(),
                    },
                    then_node: else_node,
                    else_node: None,
                },
                *then_node,
            ]),
            _ => SemanticNode::If {
                condition,
                then_node,
                else_node: Some(else_node),
            },
        }
    }
}

struct TryLexicalScope;

impl TryLexicalScope {
    fn extend(node: SemanticNode) -> SemanticNode {
        let SemanticNode::Sequence(mut nodes) = node else {
            return node;
        };
        let mut index = 0;
        while index + 1 < nodes.len() {
            let can_extend = match &nodes[index] {
                SemanticNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    finally.is_none()
                        && super::SemanticCompletion::analyze(body).can_complete_normally()
                        && catches.iter().all(|catch| {
                            !super::SemanticCompletion::analyze(&catch.body).can_complete_normally()
                        })
                        && !SemanticThrowability::analyze(&nodes[index + 1])
                }
                _ => false,
            };
            if !can_extend {
                index += 1;
                continue;
            }
            let continuation = nodes.remove(index + 1);
            let SemanticNode::Try { body, .. } = &mut nodes[index] else {
                unreachable!("try lexical extension lost its checked node");
            };
            let protected = std::mem::replace(body.as_mut(), SemanticNode::Empty);
            *body = Box::new(SemanticNode::sequence([protected, continuation]));
        }
        SemanticNode::sequence(nodes)
    }
}

#[derive(Default)]
struct SemanticThrowability {
    may_throw: bool,
}

impl SemanticThrowability {
    fn analyze(node: &SemanticNode) -> bool {
        let mut facts = Self::default();
        facts.visit_node(node);
        facts.may_throw
    }
}

impl SemanticVisitor for SemanticThrowability {
    fn enter_node(&mut self, node: &SemanticNode) {
        self.may_throw |= matches!(
            node,
            SemanticNode::Try { .. }
                | SemanticNode::Synchronized { .. }
                | SemanticNode::Leave(crate::ir::SemanticLeave {
                    kind: SemanticLeaveKind::Throw(_),
                    ..
                })
        );
    }

    fn enter_operation(&mut self, operation: &crate::ir::SemanticOperation) {
        self.may_throw |= operation.direct_effects().may_throw();
    }
}

#[derive(Clone, Copy)]
enum TerminalCompletionTarget {
    Method,
    Region(crate::ir::RegionId),
    LoopLabel(SemanticLabel),
    BlockLabel(SemanticLabel),
}

struct NaturalLoopCompletion;

impl NaturalLoopCompletion {
    fn normalize(node: SemanticNode) -> Result<SemanticNode, SemanticFoldError> {
        Ok(match node {
            SemanticNode::Loop {
                control,
                header,
                kind,
                test,
                body,
            } => SemanticNode::Loop {
                control,
                header,
                kind,
                test,
                body: Box::new(Self::rewrite_loop(body, control)?),
            },
            SemanticNode::For {
                control,
                init,
                condition,
                update,
                body,
            } => SemanticNode::For {
                control,
                init,
                condition,
                update,
                body: Box::new(Self::rewrite_loop(body, control)?),
            },
            SemanticNode::ForEach {
                control,
                variable,
                iterable,
                body,
            } => SemanticNode::ForEach {
                control,
                variable,
                iterable,
                body: Box::new(Self::rewrite_loop(body, control)?),
            },
            SemanticNode::Label { label, body } => {
                let body = TerminalCompletionRewrite::rewrite(
                    *body,
                    TerminalCompletionTarget::BlockLabel(label),
                )?;
                if LabelReferences::count(&body, label) == 0 {
                    body
                } else {
                    SemanticNode::Label {
                        label,
                        body: Box::new(body),
                    }
                }
            }
            node => node,
        })
    }

    fn rewrite_loop(
        body: Box<SemanticNode>,
        control: crate::ir::SemanticLoopControl,
    ) -> Result<SemanticNode, SemanticFoldError> {
        match control {
            crate::ir::SemanticLoopControl::Region(region) => {
                TerminalCompletionRewrite::rewrite(*body, TerminalCompletionTarget::Region(region))
            }
            crate::ir::SemanticLoopControl::Label(label) => TerminalCompletionRewrite::rewrite(
                *body,
                TerminalCompletionTarget::LoopLabel(label),
            ),
        }
    }
}

struct TerminalCompletionRewrite;

impl TerminalCompletionRewrite {
    fn rewrite(
        root: SemanticNode,
        target: TerminalCompletionTarget,
    ) -> Result<SemanticNode, SemanticFoldError> {
        let mut tasks = vec![TerminalRewriteTask::Visit {
            node: root,
            switch_exit: None,
        }];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                TerminalRewriteTask::Visit { node, switch_exit } => {
                    Self::schedule(node, target, switch_exit, &mut tasks, &mut results)
                }
                TerminalRewriteTask::Rebuild(frame) => {
                    let count = frame.child_count();
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(SemanticFoldError::MalformedWorkStack)?;
                    let children = results.drain(start..).collect::<Vec<_>>();
                    results.push(frame.rebuild(children)?);
                }
            }
        }
        if results.len() != 1 {
            return Err(SemanticFoldError::MalformedWorkStack);
        }
        results.pop().ok_or(SemanticFoldError::MalformedWorkStack)
    }

    fn schedule(
        node: SemanticNode,
        target: TerminalCompletionTarget,
        switch_exit: Option<crate::ir::RegionId>,
        tasks: &mut Vec<TerminalRewriteTask>,
        results: &mut Vec<SemanticNode>,
    ) {
        match node {
            SemanticNode::Leave(leave) if Self::is_natural_completion(&leave, target) => results
                .push(match switch_exit {
                    Some(region) => Self::switch_break(leave, region),
                    None => SemanticNode::Empty,
                }),
            SemanticNode::Sequence(mut nodes) => {
                let Some(last) = nodes.pop() else {
                    results.push(SemanticNode::Empty);
                    return;
                };
                tasks.push(TerminalRewriteTask::Rebuild(
                    TerminalRewriteFrame::Sequence(nodes),
                ));
                tasks.push(TerminalRewriteTask::Visit {
                    node: last,
                    switch_exit,
                });
            }
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => {
                let has_else = else_node.is_some();
                tasks.push(TerminalRewriteTask::Rebuild(TerminalRewriteFrame::If {
                    condition,
                    has_else,
                }));
                if let Some(else_node) = else_node {
                    tasks.push(TerminalRewriteTask::Visit {
                        node: *else_node,
                        switch_exit,
                    });
                }
                tasks.push(TerminalRewriteTask::Visit {
                    node: *then_node,
                    switch_exit,
                });
            }
            SemanticNode::Switch {
                region,
                selector,
                mut cases,
            } => {
                let bodies = cases
                    .iter_mut()
                    .map(|case| std::mem::replace(&mut case.body, SemanticNode::Empty))
                    .collect::<Vec<_>>();
                tasks.push(TerminalRewriteTask::Rebuild(TerminalRewriteFrame::Switch {
                    region,
                    selector,
                    cases,
                }));
                let case_exit = region.or(switch_exit);
                tasks.extend(
                    bodies
                        .into_iter()
                        .rev()
                        .map(|node| TerminalRewriteTask::Visit {
                            node,
                            switch_exit: case_exit,
                        }),
                );
            }
            SemanticNode::Try {
                region,
                body,
                mut catches,
                finally,
            } => {
                let catch_bodies = catches
                    .iter_mut()
                    .map(|catch| std::mem::replace(&mut catch.body, SemanticNode::Empty))
                    .collect::<Vec<_>>();
                tasks.push(TerminalRewriteTask::Rebuild(TerminalRewriteFrame::Try {
                    region,
                    catches,
                    finally,
                }));
                tasks.extend(
                    catch_bodies
                        .into_iter()
                        .rev()
                        .map(|node| TerminalRewriteTask::Visit { node, switch_exit }),
                );
                tasks.push(TerminalRewriteTask::Visit {
                    node: *body,
                    switch_exit,
                });
            }
            SemanticNode::Synchronized {
                region,
                lock,
                method,
                body,
            } => {
                tasks.push(TerminalRewriteTask::Rebuild(
                    TerminalRewriteFrame::Synchronized {
                        region,
                        lock,
                        method,
                    },
                ));
                tasks.push(TerminalRewriteTask::Visit {
                    node: *body,
                    switch_exit,
                });
            }
            SemanticNode::Label { label, body } => {
                tasks.push(TerminalRewriteTask::Rebuild(TerminalRewriteFrame::Label(
                    label,
                )));
                tasks.push(TerminalRewriteTask::Visit {
                    node: *body,
                    switch_exit,
                });
            }
            node => results.push(node),
        }
    }

    fn is_natural_completion(
        leave: &crate::ir::SemanticLeave,
        target: TerminalCompletionTarget,
    ) -> bool {
        if !leave.cleanup.is_empty() {
            return false;
        }
        match (target, &leave.kind) {
            (TerminalCompletionTarget::Method, SemanticLeaveKind::Return(None)) => true,
            (TerminalCompletionTarget::Region(region), SemanticLeaveKind::Continue) => {
                leave.target == region
            }
            (
                TerminalCompletionTarget::LoopLabel(expected),
                SemanticLeaveKind::ContinueLabel(label),
            ) => *label == expected,
            (
                TerminalCompletionTarget::BlockLabel(expected),
                SemanticLeaveKind::BreakLabel(label),
            ) => *label == expected,
            _ => false,
        }
    }

    fn switch_break(leave: crate::ir::SemanticLeave, region: crate::ir::RegionId) -> SemanticNode {
        SemanticNode::Leave(crate::ir::SemanticLeave {
            site: leave.site,
            condition: leave.condition,
            kind: SemanticLeaveKind::Break,
            edge: None,
            origin: leave.origin,
            source: leave.source,
            destination: region,
            target: region,
            cleanup: Vec::new(),
        })
    }
}

enum TerminalRewriteTask {
    Visit {
        node: SemanticNode,
        switch_exit: Option<crate::ir::RegionId>,
    },
    Rebuild(TerminalRewriteFrame),
}

enum TerminalRewriteFrame {
    Sequence(Vec<SemanticNode>),
    If {
        condition: crate::ir::SemanticOperand<crate::ir::SemanticPredicate>,
        has_else: bool,
    },
    Switch {
        region: Option<crate::ir::RegionId>,
        selector: crate::ir::SemanticOperand<SemanticExpression>,
        cases: Vec<crate::ir::SemanticSwitchCase>,
    },
    Try {
        region: crate::ir::RegionId,
        catches: Vec<crate::ir::SemanticCatch>,
        finally: Option<crate::ir::SemanticFinally>,
    },
    Synchronized {
        region: crate::ir::RegionId,
        lock: crate::ir::SemanticOperand<SemanticExpression>,
        method: bool,
    },
    Label(SemanticLabel),
}

impl TerminalRewriteFrame {
    fn child_count(&self) -> usize {
        match self {
            Self::Sequence(_) | Self::Synchronized { .. } | Self::Label(_) => 1,
            Self::If { has_else, .. } => usize::from(*has_else) + 1,
            Self::Switch { cases, .. } => cases.len(),
            Self::Try { catches, .. } => 1 + catches.len(),
        }
    }

    fn rebuild(self, children: Vec<SemanticNode>) -> Result<SemanticNode, SemanticFoldError> {
        let mut children = children.into_iter();
        Ok(match self {
            Self::Sequence(mut prefix) => {
                prefix.push(Self::child(&mut children)?);
                SemanticNode::sequence(prefix)
            }
            Self::If {
                condition,
                has_else,
            } => {
                let then_node = Self::child(&mut children)?;
                let else_node = has_else.then(|| Self::child(&mut children)).transpose()?;
                SemanticNode::branch(condition.into_inner(), then_node, else_node)
            }
            Self::Switch {
                region,
                selector,
                mut cases,
            } => {
                for case in &mut cases {
                    case.body = Self::child(&mut children)?;
                }
                SemanticNode::Switch {
                    region,
                    selector,
                    cases,
                }
            }
            Self::Try {
                region,
                mut catches,
                finally,
            } => {
                let body = Self::child(&mut children)?;
                for catch in &mut catches {
                    catch.body = Self::child(&mut children)?;
                }
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
                body: Box::new(Self::child(&mut children)?),
            },
            Self::Label(label) => SemanticNode::Label {
                label,
                body: Box::new(Self::child(&mut children)?),
            },
        })
    }

    fn child(
        children: &mut impl Iterator<Item = SemanticNode>,
    ) -> Result<SemanticNode, SemanticFoldError> {
        children.next().ok_or(SemanticFoldError::MalformedWorkStack)
    }
}

struct NormalCompletion;

impl NormalCompletion {
    fn sequence(nodes: Vec<SemanticNode>) -> SemanticNode {
        let mut reachable = true;
        SemanticNode::sequence(nodes.into_iter().take_while(|node| {
            let keep = reachable;
            reachable = reachable && Self::can_complete(node);
            keep
        }))
    }

    fn can_complete(node: &SemanticNode) -> bool {
        super::SemanticCompletion::analyze(node).can_complete_normally()
    }
}

struct TerminalLabelComposer {
    reachability: ReachabilityMode,
    changed: bool,
}

impl TerminalLabelComposer {
    fn new(reachability: ReachabilityMode) -> Self {
        Self {
            reachability,
            changed: false,
        }
    }

    fn compose_sequence(
        &mut self,
        mut nodes: Vec<SemanticNode>,
    ) -> Result<SemanticNode, SemanticFoldError> {
        for index in 0..nodes.len() {
            let node = std::mem::replace(&mut nodes[index], SemanticNode::Empty);
            let (label, mut body) = match node {
                SemanticNode::Label { label, body } => (label, body),
                node => {
                    nodes[index] = node;
                    continue;
                }
            };
            let references = LabelReferences::count(&body, label);
            if references == 0 {
                nodes[index] = *body;
                self.changed = true;
                continue;
            }
            let suffix = SemanticNode::sequence(nodes[index + 1..].iter().cloned());
            if matches!(suffix, SemanticNode::Empty) || NormalCompletion::can_complete(&suffix) {
                nodes[index] = SemanticNode::Label { label, body };
                continue;
            }
            if let Some(exit) = Self::method_exit(&suffix) {
                let mut binding = MethodExitBinding::new(label, exit, self.reachability);
                let composed =
                    binding.fold_node(std::mem::replace(body.as_mut(), SemanticNode::Empty))?;
                nodes[index] = if binding.count == references {
                    composed
                } else {
                    SemanticNode::Label {
                        label,
                        body: Box::new(composed),
                    }
                };
                if binding.count != 0 {
                    self.changed = true;
                    continue;
                }
                let SemanticNode::Label { body: restored, .. } =
                    std::mem::replace(&mut nodes[index], SemanticNode::Empty)
                else {
                    return Err(SemanticFoldError::MalformedWorkStack);
                };
                body = restored;
            }
            let expansion = references.saturating_mul(SemanticSize::of(&suffix).saturating_sub(1));
            if expansion > 1 {
                nodes[index] = SemanticNode::Label { label, body };
                continue;
            }
            let mut substitution = TerminalLabelSubstitution::new(label, &suffix);
            let composed =
                substitution.fold_node(std::mem::replace(body.as_mut(), SemanticNode::Empty))?;
            nodes[index] = if substitution.count == references {
                composed
            } else {
                SemanticNode::Label {
                    label,
                    body: Box::new(composed),
                }
            };
            self.changed |= substitution.count != 0;
        }
        Ok(if self.reachability.preserves_cfg_topology() {
            SemanticNode::sequence(nodes)
        } else {
            NormalCompletion::sequence(nodes)
        })
    }

    fn method_exit(node: &SemanticNode) -> Option<&crate::ir::SemanticLeave> {
        match node {
            SemanticNode::Leave(leave)
                if matches!(
                    leave.kind,
                    SemanticLeaveKind::Return(_) | SemanticLeaveKind::Throw(_)
                ) =>
            {
                Some(leave)
            }
            SemanticNode::Sequence(nodes) => {
                let (last, leading) = nodes.split_last()?;
                leading
                    .iter()
                    .all(Self::is_empty)
                    .then(|| Self::method_exit(last))
                    .flatten()
            }
            _ => None,
        }
    }

    fn is_empty(node: &SemanticNode) -> bool {
        match node {
            SemanticNode::Empty => true,
            SemanticNode::Sequence(nodes) => nodes.iter().all(Self::is_empty),
            SemanticNode::BasicBlock(_)
            | SemanticNode::If { .. }
            | SemanticNode::Loop { .. }
            | SemanticNode::For { .. }
            | SemanticNode::ForEach { .. }
            | SemanticNode::Switch { .. }
            | SemanticNode::Try { .. }
            | SemanticNode::Synchronized { .. }
            | SemanticNode::Label { .. }
            | SemanticNode::Leave(_) => false,
        }
    }
}

impl SemanticFolder for TerminalLabelComposer {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        match node {
            SemanticNode::Sequence(nodes) => self.compose_sequence(nodes),
            node => Ok(node),
        }
    }
}

struct MethodExitBinding {
    label: SemanticLabel,
    kind: SemanticLeaveKind,
    destination: crate::ir::RegionId,
    target: crate::ir::RegionId,
    count: usize,
    reachability: ReachabilityMode,
}

impl MethodExitBinding {
    fn new(
        label: SemanticLabel,
        exit: &crate::ir::SemanticLeave,
        reachability: ReachabilityMode,
    ) -> Self {
        Self {
            label,
            kind: exit.kind.clone(),
            destination: exit.destination,
            target: exit.target,
            count: 0,
            reachability,
        }
    }
}

impl SemanticFolder for MethodExitBinding {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        Ok(match node {
            SemanticNode::Leave(mut leave)
                if leave.destination == self.destination
                    && leave.target == self.target
                    && matches!(leave.kind, SemanticLeaveKind::BreakLabel(label) if label == self.label) =>
            {
                self.count += 1;
                leave.kind = self.kind.clone();
                SemanticNode::Leave(leave)
            }
            SemanticNode::Sequence(nodes) => SemanticNode::sequence(nodes),
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => SemanticNormalizer::new(self.reachability).branch(
                condition.into_inner(),
                *then_node,
                else_node.map(|node| *node),
            ),
            node => node,
        })
    }
}

struct TerminalLabelSubstitution<'a> {
    label: SemanticLabel,
    continuation: &'a SemanticNode,
    count: usize,
}

impl<'a> TerminalLabelSubstitution<'a> {
    fn new(label: SemanticLabel, continuation: &'a SemanticNode) -> Self {
        Self {
            label,
            continuation,
            count: 0,
        }
    }
}

impl SemanticFolder for TerminalLabelSubstitution<'_> {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        let SemanticNode::Leave(leave) = &node else {
            return Ok(node);
        };
        if leave.cleanup.is_empty()
            && matches!(leave.kind, SemanticLeaveKind::BreakLabel(label) if label == self.label)
        {
            self.count += 1;
            return Ok(self.continuation.clone());
        }
        Ok(node)
    }
}

struct LabelReferences {
    label: SemanticLabel,
    count: usize,
}

impl LabelReferences {
    fn count(root: &SemanticNode, label: SemanticLabel) -> usize {
        let mut references = Self { label, count: 0 };
        references.visit_node(root);
        references.count
    }
}

impl SemanticVisitor for LabelReferences {
    fn enter_node(&mut self, node: &SemanticNode) {
        let SemanticNode::Leave(leave) = node else {
            return;
        };
        if matches!(
            leave.kind,
            SemanticLeaveKind::BreakLabel(label) | SemanticLeaveKind::ContinueLabel(label)
                if label == self.label
        ) {
            self.count += 1;
        }
    }
}

#[derive(Default)]
struct SemanticSize {
    nodes: usize,
}

impl SemanticSize {
    fn of(root: &SemanticNode) -> usize {
        let mut size = Self::default();
        size.visit_node(root);
        size.nodes
    }
}

impl SemanticVisitor for SemanticSize {
    fn enter_node(&mut self, _node: &SemanticNode) {
        self.nodes = self.nodes.saturating_add(1);
    }
}

#[cfg(test)]
mod redundant_vacuous_predicate_tests {
    use super::*;
    use crate::ir::{
        ArgType, BlockId, IfOp, InsnNode, InsnType, InstructionId, InvokeType, LiteralArg,
        RegionId, RegisterArg, SemanticBlock, SemanticLeave, SemanticLeaveKind, SemanticOperand,
        SemanticOperation, SemanticStatement,
    };

    fn invoke_predicate(id: usize) -> SemanticPredicate {
        let mut instruction = InsnNode::new(InsnType::Invoke, 0);
        instruction.id = InstructionId::new(id);
        instruction.payload.invoke_type = Some(InvokeType::Static);
        instruction.result = Some(RegisterArg::new_ssa(0, id as u32, ArgType::BOOLEAN));
        SemanticPredicate::Test(SemanticOperation::from_parts(instruction, Vec::new(), None))
    }

    fn pure_predicate(id: usize) -> SemanticPredicate {
        let mut instruction = InsnNode::new(InsnType::If, 2);
        instruction.id = InstructionId::new(id);
        instruction.payload.if_op = Some(IfOp::Eq);
        let left = RegisterArg::new_ssa(0, id as u32, ArgType::INT);
        SemanticPredicate::Test(SemanticOperation::from_parts(
            instruction,
            vec![
                SemanticExpression::Register(left),
                SemanticExpression::Literal(LiteralArg::int(0)),
            ],
            None,
        ))
    }

    fn replaying_predicate(
        id: usize,
        replayed: SemanticPredicate,
        prefix: Option<SemanticExpression>,
    ) -> SemanticPredicate {
        let selected = SemanticExpression::select(
            replayed,
            SemanticExpression::Literal(LiteralArg::int(0)),
            SemanticExpression::Literal(LiteralArg::int(1)),
        );
        let mut operands = Vec::new();
        operands.extend(prefix);
        operands.push(selected);
        operands.push(SemanticExpression::Literal(LiteralArg::int(0)));
        let mut instruction = InsnNode::new(InsnType::If, 0);
        instruction.id = InstructionId::new(id);
        instruction.payload.if_op = Some(IfOp::Eq);
        SemanticPredicate::Test(SemanticOperation::from_parts(instruction, operands, None))
    }

    fn vacuous(condition: SemanticPredicate) -> SemanticNode {
        SemanticNode::If {
            condition: SemanticOperand::new(condition),
            then_node: Box::new(SemanticNode::Empty),
            else_node: None,
        }
    }

    fn replaying_block(id: usize, replayed: SemanticPredicate) -> SemanticNode {
        let value = SemanticExpression::select(
            replayed,
            SemanticExpression::Literal(LiteralArg::int(0)),
            SemanticExpression::Literal(LiteralArg::int(1)),
        );
        SemanticNode::BasicBlock(SemanticBlock {
            id: BlockId::new(id as u32),
            statements: vec![SemanticStatement::definition(
                InstructionId::new(id),
                RegisterArg::new_ssa(1, id as u32, ArgType::INT),
                value,
            )],
        })
    }

    fn invoke_value(id: usize) -> SemanticOperation {
        let mut instruction = InsnNode::new(InsnType::Invoke, 0);
        instruction.id = InstructionId::new(id);
        instruction.payload.invoke_type = Some(InvokeType::Static);
        instruction.result = Some(RegisterArg::new_ssa(0, id as u32, ArgType::INT));
        SemanticOperation::from_parts(instruction, Vec::new(), None)
    }

    fn value_test(id: usize, value: SemanticOperation) -> SemanticPredicate {
        let mut instruction = InsnNode::new(InsnType::If, 2);
        instruction.id = InstructionId::new(id);
        instruction.payload.if_op = Some(IfOp::Le);
        SemanticPredicate::Test(SemanticOperation::from_parts(
            instruction,
            vec![
                SemanticExpression::Operation(Box::new(value)),
                SemanticExpression::Literal(LiteralArg::int(0)),
            ],
            None,
        ))
    }

    fn effectful_following_block(
        id: usize,
        predicate: SemanticPredicate,
        prefix: SemanticOperation,
    ) -> SemanticNode {
        let selected = SemanticExpression::select(
            predicate,
            SemanticExpression::Literal(LiteralArg::int(0)),
            SemanticExpression::Literal(LiteralArg::int(1)),
        );
        let mut instruction = InsnNode::new(InsnType::Invoke, 2);
        instruction.id = InstructionId::new(id);
        instruction.payload.invoke_type = Some(InvokeType::Static);
        instruction.result = Some(RegisterArg::new_ssa(1, id as u32, ArgType::INT));
        let value = SemanticExpression::Operation(Box::new(SemanticOperation::from_parts(
            instruction,
            vec![SemanticExpression::Operation(Box::new(prefix)), selected],
            None,
        )));
        SemanticNode::BasicBlock(SemanticBlock {
            id: BlockId::new(id as u32),
            statements: vec![SemanticStatement::definition(
                InstructionId::new(id),
                RegisterArg::new_ssa(1, id as u32, ArgType::INT),
                value,
            )],
        })
    }

    fn replaying_return(replayed: SemanticPredicate) -> SemanticNode {
        let value = SemanticExpression::select(
            replayed,
            SemanticExpression::Literal(LiteralArg::int(0)),
            SemanticExpression::Literal(LiteralArg::int(1)),
        );
        SemanticNode::Leave(SemanticLeave {
            site: None,
            condition: None,
            kind: SemanticLeaveKind::Return(Some(value)),
            edge: None,
            origin: None,
            source: RegionId::new(0),
            destination: RegionId::new(0),
            target: RegionId::new(0),
            cleanup: Vec::new(),
        })
    }

    #[test]
    fn removes_vacuous_predicate_replayed_by_following_condition() {
        let predicate = invoke_predicate(1);
        let following = vacuous(replaying_predicate(2, predicate.clone(), None));
        let rewritten = RedundantVacuousPredicate::rewrite(SemanticNode::Sequence(vec![
            vacuous(predicate),
            following,
        ]));

        let SemanticNode::If { condition, .. } = rewritten else {
            panic!("expected only the following condition, got {rewritten:?}");
        };
        assert_eq!(
            RedundantVacuousPredicate::single_test_id(&condition),
            Some(InstructionId::new(2))
        );
    }

    #[test]
    fn removes_vacuous_predicate_replayed_by_following_value() {
        let predicate = invoke_predicate(1);
        let rewritten = RedundantVacuousPredicate::rewrite(SemanticNode::Sequence(vec![
            vacuous(predicate.clone()),
            replaying_block(2, predicate),
        ]));

        assert!(
            matches!(rewritten, SemanticNode::BasicBlock(block) if block.statements.len() == 1)
        );
    }

    #[test]
    fn materializes_shared_value_before_an_effectful_following_statement() {
        let target = invoke_value(1);
        let predicate = value_test(2, target.clone());
        let rewritten = RedundantVacuousPredicate::rewrite(SemanticNode::Sequence(vec![
            vacuous(predicate.clone()),
            effectful_following_block(3, predicate, invoke_value(4)),
        ]));

        let SemanticNode::BasicBlock(block) = &rewritten else {
            panic!("expected materialized following block, got {rewritten:?}");
        };
        assert_eq!(block.statements.len(), 2);
        assert!(matches!(
            &block.statements[0].kind,
            crate::ir::SemanticStatementKind::Definition { id, value, .. }
                if *id == target.id
                    && matches!(value, SemanticExpression::Operation(operation) if operation.id == target.id)
        ));
        let remaining = SemanticNode::BasicBlock(SemanticBlock {
            id: block.id,
            statements: vec![block.statements[1].clone()],
        });
        assert_eq!(
            RedundantVacuousPredicate::operation_occurrences(&remaining, target.id),
            0
        );
    }

    #[test]
    fn materializes_shared_value_under_pure_short_circuit_guard() {
        let target = invoke_value(1);
        let predicate =
            SemanticPredicate::And(vec![pure_predicate(2), value_test(3, target.clone())]);
        let rewritten = RedundantVacuousPredicate::rewrite(SemanticNode::Sequence(vec![
            vacuous(predicate.clone()),
            effectful_following_block(4, predicate, invoke_value(5)),
        ]));

        let SemanticNode::BasicBlock(block) = &rewritten else {
            panic!("expected materialized following block, got {rewritten:?}");
        };
        assert!(matches!(
            &block.statements[0].kind,
            crate::ir::SemanticStatementKind::Definition {
                value: SemanticExpression::Select { condition, .. },
                ..
            } if matches!(condition, SemanticPredicate::Test(_))
        ));
    }

    #[test]
    fn removes_vacuous_composite_predicate_when_its_effectful_test_replays() {
        let predicate = invoke_predicate(1);
        let composite = SemanticPredicate::And(vec![pure_predicate(2), predicate.clone()]);
        let rewritten = RedundantVacuousPredicate::rewrite(SemanticNode::Sequence(vec![
            vacuous(composite),
            replaying_block(3, predicate),
        ]));

        assert!(
            matches!(rewritten, SemanticNode::BasicBlock(block) if block.statements.len() == 1)
        );
    }

    #[test]
    fn removes_vacuous_predicate_replayed_in_later_short_circuit_term() {
        let predicate = invoke_predicate(1);
        let composite = SemanticPredicate::Or(vec![pure_predicate(2), predicate.clone()]);
        let rewritten = RedundantVacuousPredicate::rewrite(SemanticNode::Sequence(vec![
            vacuous(composite),
            replaying_block(3, predicate),
        ]));

        assert!(
            matches!(rewritten, SemanticNode::BasicBlock(block) if block.statements.len() == 1)
        );
    }

    #[test]
    fn removes_vacuous_predicate_replayed_by_following_return_value() {
        let predicate = invoke_predicate(1);
        let rewritten = RedundantVacuousPredicate::rewrite(SemanticNode::Sequence(vec![
            vacuous(predicate.clone()),
            replaying_return(predicate),
        ]));

        assert!(matches!(
            rewritten,
            SemanticNode::Leave(SemanticLeave {
                kind: SemanticLeaveKind::Return(Some(_)),
                ..
            })
        ));
    }

    #[test]
    fn keeps_vacuous_predicate_when_effect_precedes_value_replay() {
        let predicate = invoke_predicate(1);
        let mut following = replaying_block(2, predicate.clone());
        let SemanticNode::BasicBlock(block) = &mut following else {
            unreachable!();
        };
        let prefix = match invoke_predicate(3) {
            SemanticPredicate::Test(operation) => SemanticStatement::definition(
                InstructionId::new(3),
                RegisterArg::new_ssa(2, 3, ArgType::BOOLEAN),
                SemanticExpression::Operation(Box::new(operation)),
            ),
            _ => unreachable!(),
        };
        block.statements.insert(0, prefix);
        let rewritten = RedundantVacuousPredicate::rewrite(SemanticNode::Sequence(vec![
            vacuous(predicate),
            following,
        ]));

        assert!(matches!(rewritten, SemanticNode::Sequence(nodes) if nodes.len() == 2));
    }

    #[test]
    fn keeps_vacuous_predicate_without_a_replay() {
        let rewritten = RedundantVacuousPredicate::rewrite(SemanticNode::Sequence(vec![
            vacuous(invoke_predicate(1)),
            vacuous(invoke_predicate(2)),
        ]));

        assert!(matches!(rewritten, SemanticNode::Sequence(nodes) if nodes.len() == 2));
    }

    #[test]
    fn removes_pure_vacuous_predicate_without_replay() {
        let rewritten = RedundantVacuousPredicate::rewrite(SemanticNode::Sequence(vec![vacuous(
            pure_predicate(1),
        )]));

        assert!(matches!(rewritten, SemanticNode::Empty));
    }

    #[test]
    fn keeps_vacuous_predicate_when_an_effect_precedes_the_replay() {
        let predicate = invoke_predicate(1);
        let prefix = SemanticExpression::Operation(Box::new(match invoke_predicate(3) {
            SemanticPredicate::Test(operation) => operation,
            _ => unreachable!(),
        }));
        let following = vacuous(replaying_predicate(2, predicate.clone(), Some(prefix)));
        let rewritten = RedundantVacuousPredicate::rewrite(SemanticNode::Sequence(vec![
            vacuous(predicate),
            following,
        ]));

        assert!(matches!(rewritten, SemanticNode::Sequence(nodes) if nodes.len() == 2));
    }
}
