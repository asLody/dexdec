//! Source-language legalization of non-local lexical exits.
//!
//! Kotlin can name a non-local loop or block exit, but source recovery deliberately
//! avoids labels.  This module derives all exit facts in one lexical walk and then
//! rewrites the method once.  Pending exits are represented by a compact bit set;
//! no enclosing construct rescans an already processed subtree.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    analysis::SourceTypeEnvironment, ArgType, BlockId, IfOp, InsnArg, InsnNode, InstructionId,
    RegionId, RegisterArg, SemanticBlock, SemanticCatch, SemanticExpression, SemanticFinally,
    SemanticFoldError, SemanticLabel, SemanticLabelKind, SemanticLeave, SemanticLeaveKind,
    SemanticLoopControl, SemanticLoopKind, SemanticLoopTest, SemanticNode, SemanticPredicate,
    SemanticStatement, SemanticSwitchCase, SemanticVisitor,
};

use super::SourceVariableError;

pub(super) struct LexicalExitLowering;

impl LexicalExitLowering {
    pub(super) fn apply(
        root: &mut SemanticNode,
        next_variable: u32,
        types: &mut SourceTypeEnvironment,
    ) -> Result<(), SourceVariableError> {
        let identities = MethodIdentities::scan(root)?;
        let selection = ExitFacts::analyze(root).select();
        let mut rewriter = LexicalExitRewriter {
            next_variable,
            next_block: identities.next_block,
            next_instruction: identities.next_instruction,
            types,
        };
        let catalog = rewriter.catalog(selection)?;
        let body = std::mem::replace(root, SemanticNode::Empty);
        *root = rewriter.rewrite(body, &catalog)?;
        Ok(())
    }
}

struct LexicalExitRewriter<'a> {
    next_variable: u32,
    next_block: u32,
    next_instruction: usize,
    types: &'a mut SourceTypeEnvironment,
}

impl LexicalExitRewriter<'_> {
    fn catalog(&mut self, selection: ExitSelection) -> Result<ExitCatalog, SourceVariableError> {
        let mut entries = Vec::with_capacity(selection.targets.len());
        for key in selection.targets {
            entries.push(ExitEntry {
                key,
                target: key.target,
                flag: self.allocate_flag()?,
            });
        }
        Ok(ExitCatalog::new(
            entries,
            selection.owners,
            selection.retained_owners,
        ))
    }

    fn rewrite(
        &mut self,
        root: SemanticNode,
        catalog: &ExitCatalog,
    ) -> Result<SemanticNode, SourceVariableError> {
        let mut scopes = ScopeArena::default();
        let mut owners = OwnerCursor::default();
        let mut tasks = vec![RewriteTask::Visit {
            node: root,
            scope: None,
        }];
        let mut results = Vec::<RewriteResult>::new();
        while let Some(task) = tasks.pop() {
            match task {
                RewriteTask::Visit { node, scope } => match node {
                    SemanticNode::Sequence(nodes) => {
                        tasks.push(RewriteTask::Rebuild(RewriteFrame::Sequence(nodes.len())));
                        tasks.extend(
                            nodes
                                .into_iter()
                                .rev()
                                .map(|node| RewriteTask::Visit { node, scope }),
                        );
                    }
                    SemanticNode::If {
                        condition,
                        then_node,
                        else_node,
                    } => {
                        tasks.push(RewriteTask::Rebuild(RewriteFrame::If {
                            condition,
                            has_else: else_node.is_some(),
                        }));
                        if let Some(else_node) = else_node {
                            tasks.push(RewriteTask::Visit {
                                node: *else_node,
                                scope,
                            });
                        }
                        tasks.push(RewriteTask::Visit {
                            node: *then_node,
                            scope,
                        });
                    }
                    SemanticNode::Loop {
                        control,
                        header,
                        kind,
                        test,
                        body,
                    } => {
                        let control_scope = ControlScope::loop_(control);
                        let owner =
                            owners.claim(ExitOwner::Control(control_scope.identity), catalog)?;
                        let body_scope =
                            scopes.push(scope, BoundScope::control(owner, control_scope));
                        tasks.push(RewriteTask::Rebuild(RewriteFrame::Loop {
                            control,
                            header,
                            kind,
                            condition: test.condition,
                            parent: scope,
                            owner,
                        }));
                        tasks.push(RewriteTask::Visit {
                            node: *body,
                            scope: Some(body_scope),
                        });
                        tasks.push(RewriteTask::Visit {
                            node: *test.setup,
                            scope: Some(body_scope),
                        });
                    }
                    SemanticNode::For {
                        control,
                        init,
                        condition,
                        update,
                        body,
                    } => {
                        let control_scope = ControlScope::loop_(control);
                        let owner =
                            owners.claim(ExitOwner::Control(control_scope.identity), catalog)?;
                        let body_scope =
                            scopes.push(scope, BoundScope::control(owner, control_scope));
                        tasks.push(RewriteTask::Rebuild(RewriteFrame::For {
                            control,
                            init,
                            condition,
                            update,
                            parent: scope,
                            owner,
                        }));
                        tasks.push(RewriteTask::Visit {
                            node: *body,
                            scope: Some(body_scope),
                        });
                    }
                    SemanticNode::ForEach {
                        control,
                        variable,
                        iterable,
                        body,
                    } => {
                        let control_scope = ControlScope::loop_(control);
                        let owner =
                            owners.claim(ExitOwner::Control(control_scope.identity), catalog)?;
                        let body_scope =
                            scopes.push(scope, BoundScope::control(owner, control_scope));
                        tasks.push(RewriteTask::Rebuild(RewriteFrame::ForEach {
                            control,
                            variable,
                            iterable,
                            parent: scope,
                            owner,
                        }));
                        tasks.push(RewriteTask::Visit {
                            node: *body,
                            scope: Some(body_scope),
                        });
                    }
                    SemanticNode::Switch {
                        region,
                        selector,
                        cases,
                    } => {
                        let control_scope = region.map(ControlScope::switch);
                        let owner = control_scope
                            .map(|control| {
                                owners
                                    .claim(ExitOwner::Control(control.identity), catalog)
                                    .map(|owner| (owner, control))
                            })
                            .transpose()?;
                        let case_scope = owner
                            .map(|(owner, control)| {
                                scopes.push(scope, BoundScope::control(owner, control))
                            })
                            .or(scope);
                        let metadata = cases
                            .iter()
                            .map(|case| (case.values.clone(), case.is_default))
                            .collect::<Vec<_>>();
                        tasks.push(RewriteTask::Rebuild(RewriteFrame::Switch {
                            region,
                            selector,
                            metadata,
                            parent: scope,
                            owner: owner.map(|(owner, _)| owner),
                        }));
                        tasks.extend(cases.into_iter().rev().map(|case| RewriteTask::Visit {
                            node: case.body,
                            scope: case_scope,
                        }));
                    }
                    SemanticNode::Try {
                        region,
                        body,
                        catches,
                        finally,
                    } => {
                        let catch_metadata = catches
                            .iter()
                            .map(|catch| {
                                (
                                    catch.region,
                                    catch.exception_types.clone(),
                                    catch.exception_value.clone(),
                                )
                            })
                            .collect::<Vec<_>>();
                        let finally_region = finally.as_ref().map(|finally| finally.region);
                        tasks.push(RewriteTask::Rebuild(RewriteFrame::Try {
                            region,
                            catch_metadata,
                            finally_region,
                        }));
                        if let Some(finally) = finally {
                            tasks.push(RewriteTask::Visit {
                                node: *finally.body,
                                scope,
                            });
                        }
                        tasks.extend(catches.into_iter().rev().map(|catch| RewriteTask::Visit {
                            node: catch.body,
                            scope,
                        }));
                        tasks.push(RewriteTask::Visit { node: *body, scope });
                    }
                    SemanticNode::Synchronized {
                        region,
                        lock,
                        method,
                        body,
                    } => {
                        tasks.push(RewriteTask::Rebuild(RewriteFrame::Synchronized {
                            region,
                            lock,
                            method,
                        }));
                        tasks.push(RewriteTask::Visit { node: *body, scope });
                    }
                    SemanticNode::Label { label, body } => {
                        let owner = owners.claim(ExitOwner::Block(label), catalog)?;
                        let body_scope = scopes.push(scope, BoundScope::block(owner, label));
                        tasks.push(RewriteTask::Rebuild(RewriteFrame::Label { label, owner }));
                        tasks.push(RewriteTask::Visit {
                            node: *body,
                            scope: Some(body_scope),
                        });
                    }
                    SemanticNode::Leave(leave) => {
                        results.push(self.rewrite_leave(leave, scope, &scopes, catalog)?);
                    }
                    node => results.push(RewriteResult::plain(node, catalog.len())),
                },
                RewriteTask::Rebuild(frame) => {
                    let count = frame.child_count();
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(SemanticFoldError::MalformedWorkStack)?;
                    let children = results.drain(start..).collect::<Vec<_>>();
                    results.push(frame.rebuild(self, children, &scopes, catalog)?);
                }
            }
        }
        if results.len() != 1 {
            return Err(SemanticFoldError::MalformedWorkStack.into());
        }
        if owners.next != catalog.owners.len() {
            return Err(SemanticFoldError::MalformedWorkStack.into());
        }
        results
            .pop()
            .map(|result| result.node)
            .ok_or_else(|| SemanticFoldError::MalformedWorkStack.into())
    }

    fn rewrite_leave(
        &mut self,
        mut leave: SemanticLeave,
        scope: Option<ScopeId>,
        scopes: &ScopeArena,
        catalog: &ExitCatalog,
    ) -> Result<RewriteResult, SourceVariableError> {
        let Some(key) = scopes.resolve(scope, &leave) else {
            return Ok(RewriteResult::plain(
                SemanticNode::Leave(leave),
                catalog.len(),
            ));
        };
        let Some(id) = catalog.id(key) else {
            return Ok(RewriteResult::plain(
                SemanticNode::Leave(leave),
                catalog.len(),
            ));
        };

        if let ExitTarget::Control { identity, transfer } = key.target {
            if scopes
                .nearest(scope, transfer)
                .is_some_and(|control| control.owner == key.owner)
            {
                self.retarget(&mut leave, identity, transfer);
                return Ok(RewriteResult::plain(
                    SemanticNode::Leave(leave),
                    catalog.len(),
                ));
            }
        }

        let assignment = self.assignment(&catalog.entry(id).flag, true)?;
        let blocking_control = match key.target {
            ExitTarget::Block(_) => scopes.nearest_before(scope, key.owner, ControlTransfer::Break),
            ExitTarget::Control { .. } => scopes.nearest(scope, ControlTransfer::Break),
        };
        let node = match blocking_control {
            Some(control) => {
                self.retarget(&mut leave, control.control.identity, ControlTransfer::Break);
                SemanticNode::sequence([assignment, SemanticNode::Leave(leave)])
            }
            None => assignment,
        };
        let mut pending = ExitSet::empty(catalog.len());
        pending.insert(id);
        Ok(RewriteResult { node, pending })
    }

    fn close_control(
        &mut self,
        node: SemanticNode,
        pending: &mut ExitSet,
        parent: Option<ScopeId>,
        scopes: &ScopeArena,
        catalog: &ExitCatalog,
    ) -> Result<SemanticNode, SourceVariableError> {
        let mut continuation = Vec::new();
        for id in pending.indices() {
            let entry = catalog.entry(id);
            let transfer = match entry.target {
                ExitTarget::Control { transfer, .. } => match scopes.nearest(parent, transfer) {
                    Some(control) if control.owner == entry.key.owner => {
                        pending.remove(id);
                        Some((control, transfer))
                    }
                    _ => scopes
                        .nearest(parent, ControlTransfer::Break)
                        .map(|control| (control, ControlTransfer::Break)),
                },
                ExitTarget::Block(_) => scopes
                    .nearest_before(parent, entry.key.owner, ControlTransfer::Break)
                    .map(|control| (control, ControlTransfer::Break)),
            };
            if let Some((control, transfer)) = transfer {
                let leave = SemanticNode::Leave(self.local_transfer(control.control, transfer));
                continuation.push(self.flag_guard(&entry.flag, true, leave)?);
            }
        }
        Ok(SemanticNode::sequence(
            std::iter::once(node).chain(continuation),
        ))
    }

    fn initialize_owner(
        &mut self,
        owner: OwnerId,
        node: SemanticNode,
        catalog: &ExitCatalog,
        lifetime: ExitLifetime,
    ) -> Result<SemanticNode, SourceVariableError> {
        let Some(entries) = catalog.owner_entries.get(&owner) else {
            return Ok(node);
        };
        let mut sequence = Vec::with_capacity(entries.len() + 1);
        for id in entries
            .iter()
            .filter(|id| catalog.entry(**id).target.lifetime() == lifetime)
        {
            sequence.push(self.assignment(&catalog.entry(*id).flag, false)?);
        }
        if sequence.is_empty() {
            return Ok(node);
        }
        sequence.push(node);
        Ok(SemanticNode::sequence(sequence))
    }

    fn guard_block_continuation(
        &mut self,
        pending: &ExitSet,
        node: SemanticNode,
        catalog: &ExitCatalog,
    ) -> Result<SemanticNode, SourceVariableError> {
        let mut terms = Vec::new();
        for id in pending.indices() {
            let entry = catalog.entry(id);
            if matches!(entry.target, ExitTarget::Block(_)) {
                terms.push(self.flag_predicate(&entry.flag, false)?);
            }
        }
        let predicate = match terms.len() {
            0 => return Ok(node),
            1 => terms.pop().ok_or(SemanticFoldError::MalformedWorkStack)?,
            _ => SemanticPredicate::And(terms),
        };
        Ok(SemanticNode::guard(predicate, node))
    }

    fn retarget(
        &self,
        leave: &mut SemanticLeave,
        identity: ControlIdentity,
        transfer: ControlTransfer,
    ) {
        leave.target = identity.region();
        leave.kind = match (identity, transfer) {
            (ControlIdentity::Region(_), ControlTransfer::Break) => SemanticLeaveKind::Break,
            (ControlIdentity::Region(_), ControlTransfer::Continue) => SemanticLeaveKind::Continue,
            (ControlIdentity::Label(label), ControlTransfer::Break) => {
                SemanticLeaveKind::BreakLabel(label)
            }
            (ControlIdentity::Label(label), ControlTransfer::Continue) => {
                SemanticLeaveKind::ContinueLabel(label)
            }
        };
    }

    fn local_transfer(&self, control: ControlScope, transfer: ControlTransfer) -> SemanticLeave {
        let region = control.identity.region();
        let kind = match (control.identity, transfer) {
            (ControlIdentity::Region(_), ControlTransfer::Break) => SemanticLeaveKind::Break,
            (ControlIdentity::Region(_), ControlTransfer::Continue) => SemanticLeaveKind::Continue,
            (ControlIdentity::Label(label), ControlTransfer::Break) => {
                SemanticLeaveKind::BreakLabel(label)
            }
            (ControlIdentity::Label(label), ControlTransfer::Continue) => {
                SemanticLeaveKind::ContinueLabel(label)
            }
        };
        SemanticLeave {
            site: None,
            condition: None,
            kind,
            edge: None,
            origin: None,
            source: region,
            destination: region,
            target: region,
            cleanup: Vec::new(),
        }
    }

    fn allocate_flag(&mut self) -> Result<RegisterArg, SourceVariableError> {
        let variable = self.next_variable;
        self.next_variable = self
            .next_variable
            .checked_add(1)
            .ok_or(SourceVariableError::SyntheticIdentityExhausted)?;
        self.types.bind_variable(variable, ArgType::BOOLEAN)?;
        let mut register = RegisterArg::new(variable, ArgType::BOOLEAN);
        register.code_var = Some(variable);
        Ok(register)
    }

    fn assignment(
        &mut self,
        flag: &RegisterArg,
        value: bool,
    ) -> Result<SemanticNode, SourceVariableError> {
        let mut instruction = InsnNode::mov(
            flag.clone(),
            InsnArg::lit(i64::from(value), ArgType::BOOLEAN),
        );
        instruction.id = self.allocate_instruction()?;
        Ok(SemanticNode::BasicBlock(SemanticBlock {
            id: self.allocate_block()?,
            statements: vec![SemanticStatement::instruction(instruction)?],
        }))
    }

    fn flag_guard(
        &mut self,
        flag: &RegisterArg,
        expected: bool,
        body: SemanticNode,
    ) -> Result<SemanticNode, SourceVariableError> {
        Ok(SemanticNode::guard(
            self.flag_predicate(flag, expected)?,
            body,
        ))
    }

    fn flag_predicate(
        &mut self,
        flag: &RegisterArg,
        expected: bool,
    ) -> Result<SemanticPredicate, SourceVariableError> {
        let mut test = InsnNode::if_cmp(
            if expected { IfOp::Ne } else { IfOp::Eq },
            InsnArg::Reg(flag.clone()),
            InsnArg::lit(0, ArgType::BOOLEAN),
            0,
        );
        test.id = self.allocate_instruction()?;
        Ok(SemanticPredicate::Test(
            crate::ir::SemanticOperation::from_instruction(test)?,
        ))
    }

    fn allocate_block(&mut self) -> Result<BlockId, SourceVariableError> {
        let id = self.next_block;
        self.next_block = self
            .next_block
            .checked_add(1)
            .ok_or(SourceVariableError::SyntheticIdentityExhausted)?;
        Ok(BlockId::new(id))
    }

    fn allocate_instruction(&mut self) -> Result<InstructionId, SourceVariableError> {
        let id = self.next_instruction;
        self.next_instruction = self
            .next_instruction
            .checked_add(1)
            .ok_or(SourceVariableError::SyntheticIdentityExhausted)?;
        Ok(InstructionId::new(id))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum ControlTransfer {
    Break,
    Continue,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum ControlIdentity {
    Region(RegionId),
    Label(SemanticLabel),
}

impl ControlIdentity {
    fn of_loop(control: SemanticLoopControl) -> Self {
        match control {
            SemanticLoopControl::Region(region) => Self::Region(region),
            SemanticLoopControl::Label(label) => Self::Label(label),
        }
    }

    fn region(self) -> RegionId {
        match self {
            Self::Region(region) => region,
            Self::Label(label) => label.region,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum ExitTarget {
    Control {
        identity: ControlIdentity,
        transfer: ControlTransfer,
    },
    Block(SemanticLabel),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExitLifetime {
    Activation,
    Iteration,
}

impl ExitTarget {
    fn of_leave(leave: &SemanticLeave) -> Option<Self> {
        match &leave.kind {
            SemanticLeaveKind::Break => Some(Self::Control {
                identity: ControlIdentity::Region(leave.target),
                transfer: ControlTransfer::Break,
            }),
            SemanticLeaveKind::Continue => Some(Self::Control {
                identity: ControlIdentity::Region(leave.target),
                transfer: ControlTransfer::Continue,
            }),
            SemanticLeaveKind::BreakLabel(label) => match label.kind {
                SemanticLabelKind::Loop => Some(Self::Control {
                    identity: ControlIdentity::Label(*label),
                    transfer: ControlTransfer::Break,
                }),
                SemanticLabelKind::Block => Some(Self::Block(*label)),
            },
            SemanticLeaveKind::ContinueLabel(label) if label.kind == SemanticLabelKind::Loop => {
                Some(Self::Control {
                    identity: ControlIdentity::Label(*label),
                    transfer: ControlTransfer::Continue,
                })
            }
            SemanticLeaveKind::ContinueLabel(_)
            | SemanticLeaveKind::FallThrough(_)
            | SemanticLeaveKind::Jump(_)
            | SemanticLeaveKind::Return(_)
            | SemanticLeaveKind::Throw(_) => None,
        }
    }

    fn owner(self) -> ExitOwner {
        match self {
            Self::Control { identity, .. } => ExitOwner::Control(identity),
            Self::Block(label) => ExitOwner::Block(label),
        }
    }

    fn lifetime(self) -> ExitLifetime {
        match self {
            Self::Control {
                transfer: ControlTransfer::Continue,
                ..
            } => ExitLifetime::Iteration,
            Self::Control {
                transfer: ControlTransfer::Break,
                ..
            }
            | Self::Block(_) => ExitLifetime::Activation,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum ExitOwner {
    Control(ControlIdentity),
    Block(SemanticLabel),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ControlScope {
    identity: ControlIdentity,
    accepts_continue: bool,
}

impl ControlScope {
    fn loop_(control: SemanticLoopControl) -> Self {
        Self {
            identity: ControlIdentity::of_loop(control),
            accepts_continue: true,
        }
    }

    fn switch(region: RegionId) -> Self {
        Self {
            identity: ControlIdentity::Region(region),
            accepts_continue: false,
        }
    }

    fn accepts(self, transfer: ControlTransfer) -> bool {
        transfer == ControlTransfer::Break || self.accepts_continue
    }
}

#[derive(Default)]
struct ExitFacts {
    targets: BTreeMap<ExitKey, TargetFact>,
    owners: Vec<ExitOwner>,
    active: Vec<BoundScope>,
}

impl ExitFacts {
    fn analyze(root: &SemanticNode) -> Self {
        let mut facts = Self::default();
        facts.visit_node(root);
        facts
    }

    fn select(self) -> ExitSelection {
        let Self {
            targets,
            owners,
            active: _,
        } = self;
        let retained_owners = targets
            .iter()
            .filter_map(|(key, fact)| match key.target {
                ExitTarget::Block(_) if fact.references != 0 => Some(key.owner),
                _ => None,
            })
            .collect();
        let targets = targets
            .into_iter()
            .filter_map(|(key, fact)| {
                let selected = match key.target {
                    ExitTarget::Control { .. } => fact.non_local != 0 && fact.cleanup_safe,
                    ExitTarget::Block(_) => fact.references != 0,
                };
                selected.then_some(key)
            })
            .collect();
        ExitSelection {
            targets,
            owners,
            retained_owners,
        }
    }

    fn nearest(&self, transfer: ControlTransfer) -> Option<BoundControl> {
        self.active
            .iter()
            .rev()
            .filter_map(BoundScope::as_control)
            .find(|scope| scope.control.accepts(transfer))
    }

    fn bind(&mut self, kind: ScopeKind) {
        let owner = self.owners.len();
        self.owners.push(kind.owner());
        self.active.push(BoundScope { owner, kind });
    }

    fn resolve(&self, leave: &SemanticLeave) -> Option<ExitKey> {
        let target = ExitTarget::of_leave(leave)?;
        let owner = target.owner();
        self.active
            .iter()
            .rev()
            .find(|scope| scope.kind.owner() == owner)
            .map(|scope| ExitKey {
                owner: scope.owner,
                target,
            })
    }

    fn record_leave(&mut self, leave: &SemanticLeave) {
        let Some(key) = self.resolve(leave) else {
            return;
        };
        let non_local = match key.target {
            ExitTarget::Control { transfer, .. } => {
                self.nearest(transfer).map(|scope| scope.owner) != Some(key.owner)
            }
            ExitTarget::Block(_) => false,
        };
        let fact = self.targets.entry(key).or_default();
        fact.references += 1;
        if non_local {
            fact.non_local += 1;
            fact.cleanup_safe &= leave.cleanup.is_empty();
        }
    }

    fn scope(node: &SemanticNode) -> Option<ScopeKind> {
        match node {
            SemanticNode::Loop { control, .. }
            | SemanticNode::For { control, .. }
            | SemanticNode::ForEach { control, .. } => {
                Some(ScopeKind::Control(ControlScope::loop_(*control)))
            }
            SemanticNode::Switch {
                region: Some(region),
                ..
            } => Some(ScopeKind::Control(ControlScope::switch(*region))),
            SemanticNode::Label { label, .. } => Some(ScopeKind::Block(*label)),
            _ => None,
        }
    }
}

impl SemanticVisitor for ExitFacts {
    fn enter_node(&mut self, node: &SemanticNode) {
        if let SemanticNode::Leave(leave) = node {
            self.record_leave(leave);
        }
        if let Some(scope) = Self::scope(node) {
            self.bind(scope);
        }
    }

    fn exit_node(&mut self, node: &SemanticNode) {
        let Some(scope) = Self::scope(node) else {
            return;
        };
        debug_assert_eq!(self.active.pop().map(|bound| bound.kind), Some(scope));
    }
}

struct TargetFact {
    references: usize,
    non_local: usize,
    cleanup_safe: bool,
}

impl Default for TargetFact {
    fn default() -> Self {
        Self {
            references: 0,
            non_local: 0,
            cleanup_safe: true,
        }
    }
}

struct ExitSelection {
    targets: Vec<ExitKey>,
    owners: Vec<ExitOwner>,
    retained_owners: BTreeSet<OwnerId>,
}

struct ExitEntry {
    key: ExitKey,
    target: ExitTarget,
    flag: RegisterArg,
}

struct ExitCatalog {
    entries: Vec<ExitEntry>,
    ids: BTreeMap<ExitKey, usize>,
    owners: Vec<ExitOwner>,
    owner_entries: BTreeMap<OwnerId, Vec<usize>>,
    retained_owners: BTreeSet<OwnerId>,
}

impl ExitCatalog {
    fn new(
        entries: Vec<ExitEntry>,
        owners: Vec<ExitOwner>,
        retained_owners: BTreeSet<OwnerId>,
    ) -> Self {
        let mut ids = BTreeMap::new();
        let mut owner_entries = BTreeMap::<OwnerId, Vec<usize>>::new();
        for (id, entry) in entries.iter().enumerate() {
            ids.insert(entry.key, id);
            owner_entries.entry(entry.key.owner).or_default().push(id);
        }
        Self {
            entries,
            ids,
            owners,
            owner_entries,
            retained_owners,
        }
    }

    fn len(&self) -> usize {
        self.entries.len()
    }

    fn id(&self, key: ExitKey) -> Option<usize> {
        self.ids.get(&key).copied()
    }

    fn entry(&self, id: usize) -> &ExitEntry {
        &self.entries[id]
    }
}

type ScopeId = usize;
type OwnerId = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ExitKey {
    owner: OwnerId,
    target: ExitTarget,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScopeKind {
    Control(ControlScope),
    Block(SemanticLabel),
}

impl ScopeKind {
    fn owner(self) -> ExitOwner {
        match self {
            Self::Control(control) => ExitOwner::Control(control.identity),
            Self::Block(label) => ExitOwner::Block(label),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BoundScope {
    owner: OwnerId,
    kind: ScopeKind,
}

impl BoundScope {
    fn control(owner: OwnerId, control: ControlScope) -> Self {
        Self {
            owner,
            kind: ScopeKind::Control(control),
        }
    }

    fn block(owner: OwnerId, label: SemanticLabel) -> Self {
        Self {
            owner,
            kind: ScopeKind::Block(label),
        }
    }

    fn as_control(&self) -> Option<BoundControl> {
        match self.kind {
            ScopeKind::Control(control) => Some(BoundControl {
                owner: self.owner,
                control,
            }),
            ScopeKind::Block(_) => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BoundControl {
    owner: OwnerId,
    control: ControlScope,
}

#[derive(Default)]
struct ScopeArena {
    scopes: Vec<ScopeLink>,
}

impl ScopeArena {
    fn push(&mut self, parent: Option<ScopeId>, binding: BoundScope) -> ScopeId {
        let id = self.scopes.len();
        self.scopes.push(ScopeLink { parent, binding });
        id
    }

    fn nearest(
        &self,
        mut scope: Option<ScopeId>,
        transfer: ControlTransfer,
    ) -> Option<BoundControl> {
        while let Some(id) = scope {
            let link = self.scopes.get(id)?;
            if let Some(control) = link.binding.as_control() {
                if control.control.accepts(transfer) {
                    return Some(control);
                }
            }
            scope = link.parent;
        }
        None
    }

    fn nearest_before(
        &self,
        mut scope: Option<ScopeId>,
        owner: OwnerId,
        transfer: ControlTransfer,
    ) -> Option<BoundControl> {
        while let Some(id) = scope {
            let link = self.scopes.get(id)?;
            if link.binding.owner == owner {
                return None;
            }
            if let Some(control) = link.binding.as_control() {
                if control.control.accepts(transfer) {
                    return Some(control);
                }
            }
            scope = link.parent;
        }
        None
    }

    fn resolve(&self, mut scope: Option<ScopeId>, leave: &SemanticLeave) -> Option<ExitKey> {
        let target = ExitTarget::of_leave(leave)?;
        let owner = target.owner();
        while let Some(id) = scope {
            let link = self.scopes.get(id)?;
            if link.binding.kind.owner() == owner {
                return Some(ExitKey {
                    owner: link.binding.owner,
                    target,
                });
            }
            scope = link.parent;
        }
        None
    }
}

struct ScopeLink {
    parent: Option<ScopeId>,
    binding: BoundScope,
}

#[derive(Default)]
struct OwnerCursor {
    next: OwnerId,
}

impl OwnerCursor {
    fn claim(
        &mut self,
        expected: ExitOwner,
        catalog: &ExitCatalog,
    ) -> Result<OwnerId, SourceVariableError> {
        if catalog.owners.get(self.next).copied() != Some(expected) {
            return Err(SemanticFoldError::MalformedWorkStack.into());
        }
        let owner = self.next;
        self.next += 1;
        Ok(owner)
    }
}

struct ExitSet {
    words: Vec<u64>,
}

impl ExitSet {
    fn empty(len: usize) -> Self {
        Self {
            words: vec![0; len.div_ceil(u64::BITS as usize)],
        }
    }

    fn insert(&mut self, id: usize) {
        self.words[id / u64::BITS as usize] |= 1 << (id % u64::BITS as usize);
    }

    fn remove(&mut self, id: usize) {
        self.words[id / u64::BITS as usize] &= !(1 << (id % u64::BITS as usize));
    }

    fn union_with(&mut self, other: &Self) {
        debug_assert_eq!(self.words.len(), other.words.len());
        for (left, right) in self.words.iter_mut().zip(&other.words) {
            *left |= *right;
        }
    }

    fn indices(&self) -> Vec<usize> {
        let mut indices = Vec::new();
        for (word_index, word) in self.words.iter().copied().enumerate() {
            let mut remaining = word;
            while remaining != 0 {
                let bit = remaining.trailing_zeros() as usize;
                indices.push(word_index * u64::BITS as usize + bit);
                remaining &= remaining - 1;
            }
        }
        indices
    }
}

struct RewriteResult {
    node: SemanticNode,
    pending: ExitSet,
}

impl RewriteResult {
    fn plain(node: SemanticNode, exits: usize) -> Self {
        Self {
            node,
            pending: ExitSet::empty(exits),
        }
    }
}

enum RewriteTask {
    Visit {
        node: SemanticNode,
        scope: Option<ScopeId>,
    },
    Rebuild(RewriteFrame),
}

enum RewriteFrame {
    Sequence(usize),
    If {
        condition: crate::ir::SemanticOperand<SemanticPredicate>,
        has_else: bool,
    },
    Loop {
        control: SemanticLoopControl,
        header: Option<BlockId>,
        kind: SemanticLoopKind,
        condition: crate::ir::SemanticOperand<SemanticPredicate>,
        parent: Option<ScopeId>,
        owner: OwnerId,
    },
    For {
        control: SemanticLoopControl,
        init: SemanticStatement,
        condition: crate::ir::SemanticOperand<SemanticPredicate>,
        update: SemanticStatement,
        parent: Option<ScopeId>,
        owner: OwnerId,
    },
    ForEach {
        control: SemanticLoopControl,
        variable: RegisterArg,
        iterable: crate::ir::SemanticOperand<SemanticExpression>,
        parent: Option<ScopeId>,
        owner: OwnerId,
    },
    Switch {
        region: Option<RegionId>,
        selector: crate::ir::SemanticOperand<SemanticExpression>,
        metadata: Vec<(Vec<i32>, bool)>,
        parent: Option<ScopeId>,
        owner: Option<OwnerId>,
    },
    Try {
        region: RegionId,
        catch_metadata: Vec<(RegionId, Vec<ArgType>, Option<RegisterArg>)>,
        finally_region: Option<RegionId>,
    },
    Synchronized {
        region: RegionId,
        lock: crate::ir::SemanticOperand<SemanticExpression>,
        method: bool,
    },
    Label {
        label: SemanticLabel,
        owner: OwnerId,
    },
}

impl RewriteFrame {
    fn child_count(&self) -> usize {
        match self {
            Self::Sequence(count) => *count,
            Self::If { has_else, .. } => 1 + usize::from(*has_else),
            Self::Loop { .. } => 2,
            Self::For { .. }
            | Self::ForEach { .. }
            | Self::Synchronized { .. }
            | Self::Label { .. } => 1,
            Self::Switch { metadata, .. } => metadata.len(),
            Self::Try {
                catch_metadata,
                finally_region,
                ..
            } => 1 + catch_metadata.len() + usize::from(finally_region.is_some()),
        }
    }

    fn rebuild(
        self,
        rewriter: &mut LexicalExitRewriter<'_>,
        children: Vec<RewriteResult>,
        scopes: &ScopeArena,
        catalog: &ExitCatalog,
    ) -> Result<RewriteResult, SourceVariableError> {
        match self {
            Self::Sequence(_) => {
                let mut pending = ExitSet::empty(catalog.len());
                let mut nodes = Vec::with_capacity(children.len());
                for child in children {
                    let node = rewriter.guard_block_continuation(&pending, child.node, catalog)?;
                    pending.union_with(&child.pending);
                    nodes.push(node);
                }
                Ok(RewriteResult {
                    node: SemanticNode::sequence(nodes),
                    pending,
                })
            }
            Self::If {
                condition,
                has_else,
            } => {
                let mut children = children.into_iter();
                let when_true = Self::child(&mut children)?;
                let when_false = has_else.then(|| Self::child(&mut children)).transpose()?;
                if children.next().is_some() {
                    return Err(SemanticFoldError::MalformedWorkStack.into());
                }
                let mut pending = when_true.pending;
                if let Some(when_false) = &when_false {
                    pending.union_with(&when_false.pending);
                }
                Ok(RewriteResult {
                    node: SemanticNode::branch(
                        condition.into_inner(),
                        when_true.node,
                        when_false.map(|branch| branch.node),
                    ),
                    pending,
                })
            }
            Self::Loop {
                control,
                header,
                kind,
                condition,
                parent,
                owner,
            } => {
                let mut children = children.into_iter();
                let setup = Self::child(&mut children)?;
                let body = Self::child(&mut children)?;
                if children.next().is_some() {
                    return Err(SemanticFoldError::MalformedWorkStack.into());
                }
                let mut pending = setup.pending;
                pending.union_with(&body.pending);
                let body = rewriter.initialize_owner(
                    owner,
                    body.node,
                    catalog,
                    ExitLifetime::Iteration,
                )?;
                let node = SemanticNode::Loop {
                    control,
                    header,
                    kind,
                    test: SemanticLoopTest {
                        setup: Box::new(setup.node),
                        condition,
                    },
                    body: Box::new(body),
                };
                let node = rewriter.close_control(node, &mut pending, parent, scopes, catalog)?;
                let node =
                    rewriter.initialize_owner(owner, node, catalog, ExitLifetime::Activation)?;
                Ok(RewriteResult { node, pending })
            }
            Self::For {
                control,
                init,
                condition,
                update,
                parent,
                owner,
            } => {
                let body = Self::only_child(children)?;
                let mut pending = body.pending;
                let body = rewriter.initialize_owner(
                    owner,
                    body.node,
                    catalog,
                    ExitLifetime::Iteration,
                )?;
                let node = SemanticNode::For {
                    control,
                    init,
                    condition,
                    update,
                    body: Box::new(body),
                };
                let node = rewriter.close_control(node, &mut pending, parent, scopes, catalog)?;
                let node =
                    rewriter.initialize_owner(owner, node, catalog, ExitLifetime::Activation)?;
                Ok(RewriteResult { node, pending })
            }
            Self::ForEach {
                control,
                variable,
                iterable,
                parent,
                owner,
            } => {
                let body = Self::only_child(children)?;
                let mut pending = body.pending;
                let body = rewriter.initialize_owner(
                    owner,
                    body.node,
                    catalog,
                    ExitLifetime::Iteration,
                )?;
                let node = SemanticNode::ForEach {
                    control,
                    variable,
                    iterable,
                    body: Box::new(body),
                };
                let node = rewriter.close_control(node, &mut pending, parent, scopes, catalog)?;
                let node =
                    rewriter.initialize_owner(owner, node, catalog, ExitLifetime::Activation)?;
                Ok(RewriteResult { node, pending })
            }
            Self::Switch {
                region,
                selector,
                metadata,
                parent,
                owner,
            } => {
                if children.len() != metadata.len() {
                    return Err(SemanticFoldError::MalformedWorkStack.into());
                }
                let mut pending = ExitSet::empty(catalog.len());
                let cases = metadata
                    .into_iter()
                    .zip(children)
                    .map(|((values, is_default), child)| {
                        pending.union_with(&child.pending);
                        SemanticSwitchCase {
                            values,
                            is_default,
                            body: child.node,
                        }
                    })
                    .collect();
                let mut node = SemanticNode::Switch {
                    region,
                    selector,
                    cases,
                };
                if let Some(owner) = owner {
                    node = rewriter.close_control(node, &mut pending, parent, scopes, catalog)?;
                    node = rewriter.initialize_owner(
                        owner,
                        node,
                        catalog,
                        ExitLifetime::Activation,
                    )?;
                }
                Ok(RewriteResult { node, pending })
            }
            Self::Try {
                region,
                catch_metadata,
                finally_region,
            } => {
                let mut children = children.into_iter();
                let body = Self::child(&mut children)?;
                let mut pending = body.pending;
                let mut catches = Vec::with_capacity(catch_metadata.len());
                for (region, exception_types, exception_value) in catch_metadata {
                    let child = Self::child(&mut children)?;
                    pending.union_with(&child.pending);
                    catches.push(SemanticCatch {
                        region,
                        exception_types,
                        exception_value,
                        body: child.node,
                    });
                }
                let finally = match finally_region {
                    Some(region) => {
                        let child = Self::child(&mut children)?;
                        pending.union_with(&child.pending);
                        Some(SemanticFinally {
                            region,
                            body: Box::new(child.node),
                        })
                    }
                    None => None,
                };
                if children.next().is_some() {
                    return Err(SemanticFoldError::MalformedWorkStack.into());
                }
                Ok(RewriteResult {
                    node: SemanticNode::Try {
                        region,
                        body: Box::new(body.node),
                        catches,
                        finally,
                    },
                    pending,
                })
            }
            Self::Synchronized {
                region,
                lock,
                method,
            } => {
                let body = Self::only_child(children)?;
                Ok(RewriteResult {
                    node: SemanticNode::Synchronized {
                        region,
                        lock,
                        method,
                        body: Box::new(body.node),
                    },
                    pending: body.pending,
                })
            }
            Self::Label { label, owner } => {
                let mut body = Self::only_child(children)?;
                let key = ExitKey {
                    owner,
                    target: ExitTarget::Block(label),
                };
                let node = match catalog.id(key) {
                    Some(id) => {
                        body.pending.remove(id);
                        rewriter.initialize_owner(
                            owner,
                            body.node,
                            catalog,
                            ExitLifetime::Activation,
                        )?
                    }
                    None if catalog.retained_owners.contains(&owner) => SemanticNode::Label {
                        label,
                        body: Box::new(body.node),
                    },
                    None => body.node,
                };
                Ok(RewriteResult {
                    node,
                    pending: body.pending,
                })
            }
        }
    }

    fn child(
        children: &mut impl Iterator<Item = RewriteResult>,
    ) -> Result<RewriteResult, SourceVariableError> {
        children
            .next()
            .ok_or_else(|| SemanticFoldError::MalformedWorkStack.into())
    }

    fn only_child(mut children: Vec<RewriteResult>) -> Result<RewriteResult, SourceVariableError> {
        if children.len() != 1 {
            return Err(SemanticFoldError::MalformedWorkStack.into());
        }
        children
            .pop()
            .ok_or_else(|| SemanticFoldError::MalformedWorkStack.into())
    }
}

struct MethodIdentities {
    next_block: u32,
    next_instruction: usize,
}

impl MethodIdentities {
    fn scan(root: &SemanticNode) -> Result<Self, SourceVariableError> {
        let mut scan = IdentityScan::default();
        scan.visit_node(root);
        Ok(Self {
            next_block: scan.max_block.map_or(Ok(0), |id| {
                id.checked_add(1)
                    .ok_or(SourceVariableError::SyntheticIdentityExhausted)
            })?,
            next_instruction: scan.max_instruction.map_or(Ok(0), |id| {
                id.checked_add(1)
                    .ok_or(SourceVariableError::SyntheticIdentityExhausted)
            })?,
        })
    }
}

#[derive(Default)]
struct IdentityScan {
    max_block: Option<u32>,
    max_instruction: Option<usize>,
}

impl SemanticVisitor for IdentityScan {
    fn enter_node(&mut self, node: &SemanticNode) {
        let block = match node {
            SemanticNode::BasicBlock(block) => Some(block.id.raw()),
            SemanticNode::Label { label, .. } => Some(label.block.raw()),
            SemanticNode::Loop { header, .. } => header.map(BlockId::raw),
            _ => None,
        };
        if let Some(block) = block {
            self.max_block = Some(self.max_block.map_or(block, |current| current.max(block)));
        }
    }

    fn enter_operation(&mut self, instruction: &crate::ir::SemanticOperation) {
        if instruction.id.is_valid() {
            let id = instruction.id.raw();
            self.max_instruction = Some(self.max_instruction.map_or(id, |current| current.max(id)));
        }
    }
}
