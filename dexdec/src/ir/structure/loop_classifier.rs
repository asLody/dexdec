//! Loop classification over structured region semantics.

use std::collections::BTreeSet;

use crate::ir::{
    BlockId, RegionId, SemanticExpressionFacts, SemanticFoldError, SemanticFolder, SemanticLabel,
    SemanticLeaveKind, SemanticLoopControl, SemanticLoopKind, SemanticLoopTest, SemanticNode,
    SemanticPredicate, SemanticVisitor,
};

pub(crate) struct LoopClassifier {
    region: RegionId,
    header: crate::ir::BlockId,
    control: SemanticLoopControl,
    follow: Option<crate::ir::BlockId>,
    preserved_blocks: BTreeSet<BlockId>,
}

impl LoopClassifier {
    pub(crate) fn new(region: RegionId, header: crate::ir::BlockId) -> Self {
        Self {
            region,
            header,
            control: SemanticLoopControl::Region(region),
            follow: None,
            preserved_blocks: BTreeSet::new(),
        }
    }

    pub(super) fn for_label(label: SemanticLabel, follow: Option<crate::ir::BlockId>) -> Self {
        Self {
            region: label.region,
            header: label.block,
            control: SemanticLoopControl::Label(label),
            follow,
            preserved_blocks: BTreeSet::new(),
        }
    }

    pub(super) fn preserve_blocks(mut self, blocks: BTreeSet<BlockId>) -> Self {
        self.preserved_blocks = blocks;
        self
    }

    pub(crate) fn classify(&self, body: SemanticNode) -> Result<SemanticNode, SemanticFoldError> {
        let identities = BlockIdentity::collect(&body, &self.preserved_blocks);
        let body = LoopBody::from_node(body);
        let loop_label = match self.control {
            SemanticLoopControl::Region(_) => None,
            SemanticLoopControl::Label(label) => Some(label),
        };
        let classification = LoopAnalysis::new(
            self.region,
            self.header,
            loop_label,
            self.follow,
            &self.preserved_blocks,
            &body,
        )
        .classify()?;
        let result = classification.into_loop(self.control, self.header, body);
        if identities != BlockIdentity::collect(&result, &self.preserved_blocks) {
            return Err(SemanticFoldError::BlockIdentityChanged {
                transform: "loop-classification",
            });
        }
        Ok(result)
    }
}

struct LoopAnalysis<'a> {
    region: RegionId,
    header: crate::ir::BlockId,
    loop_label: Option<SemanticLabel>,
    follow: Option<crate::ir::BlockId>,
    preserved_blocks: &'a BTreeSet<BlockId>,
    body: &'a LoopBody,
}

impl<'a> LoopAnalysis<'a> {
    fn new(
        region: RegionId,
        header: crate::ir::BlockId,
        loop_label: Option<SemanticLabel>,
        follow: Option<crate::ir::BlockId>,
        preserved_blocks: &'a BTreeSet<BlockId>,
        body: &'a LoopBody,
    ) -> Self {
        Self {
            region,
            header,
            loop_label,
            follow,
            preserved_blocks,
            body,
        }
    }

    fn classify(&self) -> Result<LoopClassification, SemanticFoldError> {
        if let Some(classification) = self.pre_tested()? {
            return Ok(classification);
        }
        if let Some(classification) = self.post_tested()? {
            return Ok(classification);
        }
        Ok(LoopClassification::Endless)
    }

    fn pre_tested(&self) -> Result<Option<LoopClassification>, SemanticFoldError> {
        let Some((exit_index, setup)) = self.body.entry_test(self.header) else {
            return Ok(None);
        };
        let entry = if let Some(entry) = LoopEntry::analyze(
            &self.body.nodes[exit_index],
            self.region,
            self.loop_label,
            self.follow,
            self.preserved_blocks,
        ) {
            Some((entry, exit_index + 1))
        } else if let Some(entry) = LoopEntry::analyze_decision(
            &self.body.nodes[exit_index],
            self.region,
            self.loop_label,
            self.follow,
            self.preserved_blocks,
        )? {
            Some((entry, exit_index + 1))
        } else {
            self.guarded_entry(exit_index)
        };
        let Some((entry, tail_start)) = entry else {
            return Ok(None);
        };
        let condition = entry.condition;
        let after = entry.after;
        let close_normal_to_after = entry.close_normal_to_after;
        let exit_label = entry
            .edge_block
            .map(|block| SemanticLabel::block(self.region, block));
        let mut body = entry.body;
        body.extend_from_slice(&self.body.nodes[tail_start..]);
        LoopBody::trim_discardable(&mut body, self.preserved_blocks);
        body = LoopGuard::unwrap_equivalent(body, &condition)?;
        if after.is_some() {
            let completion = crate::ir::semantic::SemanticCompletion::analyze(
                &SemanticNode::sequence(body.iter().cloned()),
            );
            let conflicting_break = completion.has_break_to_region(self.region)
                || self
                    .loop_label
                    .is_some_and(|label| completion.has_break_to_label(label));
            if conflicting_break && exit_label.is_none() {
                return Ok(None);
            }
        }
        if close_normal_to_after {
            body.push(LoopExit::local_break(self.region));
        }
        LoopExit::strip_terminal(
            &mut body,
            self.region,
            ExitDirection::Continue,
            self.preserved_blocks,
        );
        if let Some(label) = self.loop_label {
            LoopExit::strip_continue_label(&mut body, label, self.preserved_blocks);
        }
        let mut test = SemanticLoopTest::new(setup, condition);
        LoopContinuationDecision::refine(
            &mut test,
            &mut body,
            self.region,
            self.loop_label,
            self.preserved_blocks,
        )?;
        if let Some(label) = exit_label {
            body = LocalBreakRetargeting::new(self.region, self.loop_label, label).apply(body)?;
        }
        Ok(Some(LoopClassification::PreTested {
            test,
            body,
            after,
            exit_label,
        }))
    }

    fn guarded_entry(&self, entry_index: usize) -> Option<(LoopEntry, usize)> {
        let mut tail = self
            .body
            .nodes
            .iter()
            .enumerate()
            .skip(entry_index + 1)
            .filter(|(_, node)| !LoopBody::is_empty(node));
        let (exit_index, exit) = tail.next()?;
        tail.next().is_none().then_some(())?;
        if self.body.nodes[entry_index + 1..exit_index]
            .iter()
            .any(|node| BlockIdentity::contains(node, self.preserved_blocks))
        {
            return None;
        }
        let entry = LoopEntry::analyze_guarded(
            &self.body.nodes[entry_index],
            exit,
            self.region,
            self.loop_label,
            self.follow,
            self.preserved_blocks,
        )?;
        Some((entry, exit_index + 1))
    }

    fn post_tested(&self) -> Result<Option<LoopClassification>, SemanticFoldError> {
        let meaningful = self.body.meaningful_indices();
        let Some((&last, prefix)) = meaningful.split_last() else {
            return Ok(None);
        };
        if let Some(preserved) =
            BlockIdentity::extract_empty(&self.body.nodes[last], self.preserved_blocks)
        {
            if let Some(flow) =
                DecisionFlow::analyze(&self.body.nodes[last], self.region, self.loop_label)
            {
                if let Some(condition) = flow.binary_loop_condition()? {
                    let mut body = self.body.nodes.clone();
                    body.remove(last);
                    body.extend(preserved);
                    LoopBody::trim_discardable(&mut body, self.preserved_blocks);
                    return Ok(Some(LoopClassification::PostTested {
                        test: SemanticLoopTest::pure(condition),
                        body,
                    }));
                }
            }
        }
        let Some(&previous) = prefix.last() else {
            return Ok(None);
        };
        let exits = ExitPair::analyze(
            self.region,
            previous,
            &self.body.nodes[previous],
            last,
            &self.body.nodes[last],
            self.preserved_blocks,
        )?;
        let Some(exits) = exits else {
            return Ok(None);
        };
        let mut body = self.body.nodes.clone();
        for index in exits.removed_indices() {
            body.remove(index);
        }
        LoopBody::trim_discardable(&mut body, self.preserved_blocks);
        Ok(Some(LoopClassification::PostTested {
            test: SemanticLoopTest::pure(exits.continue_condition),
            body,
        }))
    }
}

struct LoopEntry {
    condition: SemanticPredicate,
    body: Vec<SemanticNode>,
    /// Non-local exit leave re-emitted after the pre-tested loop (e.g. continue
    /// to an enclosing loop). Local `break` becomes natural while-exit.
    after: Option<SemanticNode>,
    edge_block: Option<crate::ir::BlockId>,
    /// In a guarded entry (`if (test) body; exit`), normal completion of
    /// `body` reaches the trailing exit rather than the loop latch.
    close_normal_to_after: bool,
}

impl LoopEntry {
    fn analyze(
        node: &SemanticNode,
        region: RegionId,
        loop_label: Option<SemanticLabel>,
        follow: Option<crate::ir::BlockId>,
        preserved_blocks: &BTreeSet<BlockId>,
    ) -> Option<Self> {
        let SemanticNode::If {
            condition,
            then_node,
            else_node,
        } = node
        else {
            return None;
        };
        if let Some(exit) =
            LoopExit::pretest_exit(then_node, region, loop_label, follow, preserved_blocks)
        {
            return Some(Self {
                condition: condition.value.clone().negate(),
                body: else_node.as_deref().map(Self::nodes).unwrap_or_default(),
                after: exit.after,
                edge_block: exit.edge_block,
                close_normal_to_after: false,
            });
        }
        let else_node = else_node.as_deref()?;
        LoopExit::pretest_exit(else_node, region, loop_label, follow, preserved_blocks).map(
            |exit| Self {
                condition: condition.value.clone(),
                body: Self::nodes(then_node),
                after: exit.after,
                edge_block: exit.edge_block,
                close_normal_to_after: false,
            },
        )
    }

    fn analyze_guarded(
        node: &SemanticNode,
        exit: &SemanticNode,
        region: RegionId,
        loop_label: Option<SemanticLabel>,
        follow: Option<crate::ir::BlockId>,
        preserved_blocks: &BTreeSet<BlockId>,
    ) -> Option<Self> {
        let exit = LoopExit::pretest_exit(exit, region, loop_label, follow, preserved_blocks)?;
        let SemanticNode::If {
            condition,
            then_node,
            else_node,
        } = node
        else {
            return None;
        };
        let then_completion = crate::ir::semantic::SemanticCompletion::analyze(then_node);
        let else_is_empty = else_node.as_deref().is_none_or(LoopBody::is_empty);
        let then_continues = then_completion.has_continue_to_region(region)
            || loop_label.is_some_and(|label| then_completion.has_continue_to_label(label));
        if else_is_empty && then_continues {
            return Some(Self {
                condition: condition.value.clone(),
                body: Self::nodes(then_node),
                after: exit.after,
                edge_block: exit.edge_block,
                close_normal_to_after: then_completion.can_complete_normally(),
            });
        }
        let else_node = else_node.as_deref()?;
        let else_completion = crate::ir::semantic::SemanticCompletion::analyze(else_node);
        let else_continues = else_completion.has_continue_to_region(region)
            || loop_label.is_some_and(|label| else_completion.has_continue_to_label(label));
        if LoopBody::is_empty(then_node) && else_continues {
            return Some(Self {
                condition: condition.value.clone().negate(),
                body: Self::nodes(else_node),
                after: exit.after,
                edge_block: exit.edge_block,
                close_normal_to_after: else_completion.can_complete_normally(),
            });
        }
        None
    }

    fn analyze_decision(
        node: &SemanticNode,
        region: RegionId,
        loop_label: Option<SemanticLabel>,
        follow: Option<crate::ir::BlockId>,
        preserved_blocks: &BTreeSet<BlockId>,
    ) -> Result<Option<Self>, SemanticFoldError> {
        let Some(flow) = EntryDecisionFlow::analyze(node) else {
            return Ok(None);
        };
        let Some((condition, exit_node)) = flow.binary_exit_condition()? else {
            return Ok(None);
        };
        let Some(exit) =
            LoopExit::pretest_exit(&exit_node, region, loop_label, follow, preserved_blocks)
        else {
            return Ok(None);
        };
        let Some(body) = BlockIdentity::extract_empty(node, preserved_blocks) else {
            return Ok(None);
        };
        Ok(Some(Self {
            condition,
            body,
            after: exit.after,
            edge_block: exit.edge_block,
            close_normal_to_after: false,
        }))
    }

    fn nodes(node: &SemanticNode) -> Vec<SemanticNode> {
        match node {
            SemanticNode::Sequence(nodes) => nodes.clone(),
            SemanticNode::Empty => Vec::new(),
            node => vec![node.clone()],
        }
    }
}

struct EntryDecisionExit {
    condition: SemanticPredicate,
    node: SemanticNode,
}

struct EntryDecisionFlow {
    normal: SemanticPredicate,
    normal_identity: Vec<SemanticNode>,
    exit: Option<EntryDecisionExit>,
}

impl EntryDecisionFlow {
    fn analyze(node: &SemanticNode) -> Option<Self> {
        match node {
            SemanticNode::Empty => Some(Self::normal(Vec::new())),
            SemanticNode::BasicBlock(block) if block.statements.is_empty() => {
                Some(Self::normal(vec![node.clone()]))
            }
            SemanticNode::Leave(leave) if leave.condition.is_none() => Some(Self {
                normal: SemanticPredicate::False,
                normal_identity: Vec::new(),
                exit: Some(EntryDecisionExit {
                    condition: SemanticPredicate::True,
                    node: node.clone(),
                }),
            }),
            SemanticNode::Sequence(nodes) => {
                let mut flow = Self::normal(Vec::new());
                for node in nodes {
                    flow = flow.sequence(Self::analyze(node)?)?;
                }
                Some(flow)
            }
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => {
                let when_true = Self::analyze(then_node)?;
                let when_false = match else_node {
                    Some(node) => Self::analyze(node)?,
                    None => Self::normal(Vec::new()),
                };
                Self::branch(condition.value.clone(), when_true, when_false)
            }
            SemanticNode::BasicBlock(_)
            | SemanticNode::Leave(_)
            | SemanticNode::Loop { .. }
            | SemanticNode::For { .. }
            | SemanticNode::ForEach { .. }
            | SemanticNode::Switch { .. }
            | SemanticNode::Try { .. }
            | SemanticNode::Synchronized { .. }
            | SemanticNode::Label { .. } => None,
        }
    }

    fn normal(identity: Vec<SemanticNode>) -> Self {
        Self {
            normal: SemanticPredicate::True,
            normal_identity: identity,
            exit: None,
        }
    }

    fn sequence(mut self, mut next: Self) -> Option<Self> {
        if self.exit.is_some() && next.exit.is_some() {
            return None;
        }
        if let Some(exit) = &mut next.exit {
            exit.condition = PredicateAlgebra::and(self.normal.clone(), exit.condition.clone());
            if !self.normal_identity.is_empty() {
                exit.node = SemanticNode::sequence(
                    self.normal_identity
                        .iter()
                        .cloned()
                        .chain(std::iter::once(exit.node.clone())),
                );
            }
        }
        self.normal = PredicateAlgebra::and(self.normal, next.normal);
        self.normal_identity.extend(next.normal_identity);
        if self.exit.is_none() {
            self.exit = next.exit;
        }
        Some(self)
    }

    fn branch(
        condition: SemanticPredicate,
        mut when_true: Self,
        mut when_false: Self,
    ) -> Option<Self> {
        if when_true.exit.is_some() && when_false.exit.is_some() {
            return None;
        }
        let inverse = condition.clone().negate();
        if let Some(exit) = &mut when_true.exit {
            exit.condition = PredicateAlgebra::and(condition.clone(), exit.condition.clone());
        }
        if let Some(exit) = &mut when_false.exit {
            exit.condition = PredicateAlgebra::and(inverse.clone(), exit.condition.clone());
        }
        Some(Self {
            normal: PredicateAlgebra::or(
                PredicateAlgebra::and(condition, when_true.normal),
                PredicateAlgebra::and(inverse, when_false.normal),
            ),
            normal_identity: Vec::new(),
            exit: when_true.exit.or(when_false.exit),
        })
    }

    fn binary_exit_condition(
        self,
    ) -> Result<Option<(SemanticPredicate, SemanticNode)>, SemanticFoldError> {
        let Some(exit) = self.exit else {
            return Ok(None);
        };
        if PredicateProof::equivalent(&self.normal, &SemanticPredicate::False)?
            || PredicateProof::equivalent(&exit.condition, &SemanticPredicate::False)?
            || !PredicateProof::equivalent(&exit.condition, &self.normal.clone().negate())?
        {
            return Ok(None);
        }
        Ok(Some((self.normal, exit.node)))
    }
}

enum LoopClassification {
    PreTested {
        test: SemanticLoopTest,
        body: Vec<SemanticNode>,
        after: Option<SemanticNode>,
        exit_label: Option<SemanticLabel>,
    },
    PostTested {
        test: SemanticLoopTest,
        body: Vec<SemanticNode>,
    },
    Endless,
}

impl LoopClassification {
    fn into_loop(
        self,
        control: SemanticLoopControl,
        header: crate::ir::BlockId,
        original: LoopBody,
    ) -> SemanticNode {
        let (kind, test, body, after, exit_label) = match self {
            Self::PreTested {
                test,
                body,
                after,
                exit_label,
            } => (SemanticLoopKind::PreTested, test, body, after, exit_label),
            Self::PostTested { test, body } => {
                (SemanticLoopKind::PostTested, test, body, None, None)
            }
            Self::Endless => (
                SemanticLoopKind::Endless,
                SemanticLoopTest::pure(SemanticPredicate::True),
                original.nodes,
                None,
                None,
            ),
        };
        let loop_node = SemanticNode::Loop {
            control,
            header: Some(header),
            kind,
            test,
            body: Box::new(SemanticNode::sequence(body)),
        };
        let body = match after {
            Some(after) => SemanticNode::sequence([loop_node, after]),
            None => loop_node,
        };
        match exit_label {
            Some(label) => SemanticNode::Label {
                label,
                body: Box::new(body),
            },
            None => body,
        }
    }
}

struct LoopBody {
    nodes: Vec<SemanticNode>,
}

impl LoopBody {
    fn from_node(body: SemanticNode) -> Self {
        let nodes = match body {
            SemanticNode::Sequence(nodes) => nodes,
            SemanticNode::Empty => Vec::new(),
            node => vec![node],
        };
        Self { nodes }
    }

    fn entry_test(&self, header: crate::ir::BlockId) -> Option<(usize, SemanticNode)> {
        let mut setup = Vec::new();
        let mut seen_header = false;
        for (index, node) in self.nodes.iter().enumerate() {
            if matches!(
                node,
                SemanticNode::BasicBlock(block) if !seen_header && block.id == header
            ) {
                seen_header = true;
                setup.push(node.clone());
                continue;
            }
            if Self::is_empty(node) {
                setup.push(node.clone());
                continue;
            }
            match node {
                SemanticNode::BasicBlock(_) if seen_header => setup.push(node.clone()),
                SemanticNode::If { .. } if setup.is_empty() || seen_header => {
                    return Some((index, SemanticNode::sequence(setup)));
                }
                _ => return None,
            }
        }
        None
    }

    fn meaningful_indices(&self) -> Vec<usize> {
        self.nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| !Self::is_empty(node))
            .map(|(index, _)| index)
            .collect()
    }

    fn trim_discardable(nodes: &mut Vec<SemanticNode>, preserved: &BTreeSet<BlockId>) {
        while nodes
            .first()
            .is_some_and(|node| Self::is_empty(node) && !BlockIdentity::contains(node, preserved))
        {
            nodes.remove(0);
        }
        while nodes
            .last()
            .is_some_and(|node| Self::is_empty(node) && !BlockIdentity::contains(node, preserved))
        {
            nodes.pop();
        }
    }

    fn is_empty(node: &SemanticNode) -> bool {
        match node {
            SemanticNode::Empty => true,
            SemanticNode::BasicBlock(block) => block.statements.is_empty(),
            SemanticNode::Sequence(nodes) => nodes.iter().all(Self::is_empty),
            _ => false,
        }
    }
}

struct BlockIdentity<'a> {
    required: &'a BTreeSet<BlockId>,
    found: BTreeSet<BlockId>,
}

impl BlockIdentity<'_> {
    fn collect(root: &SemanticNode, required: &BTreeSet<BlockId>) -> BTreeSet<BlockId> {
        let mut collector = BlockIdentity {
            required,
            found: BTreeSet::new(),
        };
        collector.visit_node(root);
        collector.found
    }

    fn contains(root: &SemanticNode, required: &BTreeSet<BlockId>) -> bool {
        !Self::collect(root, required).is_empty()
    }

    fn extract_empty(
        root: &SemanticNode,
        required: &BTreeSet<BlockId>,
    ) -> Option<Vec<SemanticNode>> {
        let mut pending = vec![root];
        let mut blocks = Vec::new();
        let mut found = BTreeSet::new();
        while let Some(node) = pending.pop() {
            match node {
                SemanticNode::BasicBlock(block) if required.contains(&block.id) => {
                    if !block.statements.is_empty() {
                        return None;
                    }
                    if found.insert(block.id) {
                        blocks.push(SemanticNode::BasicBlock(block.clone()));
                    }
                }
                SemanticNode::Sequence(nodes) => pending.extend(nodes.iter().rev()),
                SemanticNode::If {
                    then_node,
                    else_node,
                    ..
                } => {
                    if let Some(else_node) = else_node {
                        pending.push(else_node);
                    }
                    pending.push(then_node);
                }
                SemanticNode::Leave(leave) => {
                    for block in Self::leave_blocks(leave, required) {
                        if found.insert(block) {
                            blocks.push(SemanticNode::BasicBlock(crate::ir::SemanticBlock {
                                id: block,
                                statements: Vec::new(),
                            }));
                        }
                    }
                }
                SemanticNode::Empty
                | SemanticNode::BasicBlock(_)
                | SemanticNode::Loop { .. }
                | SemanticNode::For { .. }
                | SemanticNode::ForEach { .. }
                | SemanticNode::Switch { .. }
                | SemanticNode::Try { .. }
                | SemanticNode::Synchronized { .. }
                | SemanticNode::Label { .. } => {}
            }
        }
        Some(blocks)
    }

    fn leave_blocks(
        leave: &crate::ir::SemanticLeave,
        required: &BTreeSet<BlockId>,
    ) -> BTreeSet<BlockId> {
        leave
            .edge
            .into_iter()
            .flat_map(|edge| [edge.source, edge.target])
            .chain(leave.origin)
            .filter(|block| required.contains(block))
            .collect()
    }
}

impl SemanticVisitor for BlockIdentity<'_> {
    fn enter_node(&mut self, node: &SemanticNode) {
        match node {
            SemanticNode::BasicBlock(block) if self.required.contains(&block.id) => {
                self.found.insert(block.id);
            }
            SemanticNode::Leave(leave) => {
                self.found.extend(Self::leave_blocks(leave, self.required));
            }
            _ => {}
        }
    }
}

struct LoopGuard;

impl LoopGuard {
    fn unwrap_equivalent(
        nodes: Vec<SemanticNode>,
        condition: &SemanticPredicate,
    ) -> Result<Vec<SemanticNode>, SemanticFoldError> {
        let mut meaningful = nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| !LoopBody::is_empty(node));
        let Some((
            guard_index,
            SemanticNode::If {
                condition: guard,
                then_node,
                else_node: None,
            },
        )) = meaningful.next()
        else {
            return Ok(nodes);
        };
        if meaningful.next().is_some() || !PredicateProof::equivalent(guard, condition)? {
            return Ok(nodes);
        }
        let replacement = match then_node.as_ref() {
            SemanticNode::Sequence(children) => children.clone(),
            SemanticNode::Empty => Vec::new(),
            node => vec![node.clone()],
        };
        let mut result = nodes;
        result.splice(guard_index..=guard_index, replacement);
        Ok(result)
    }
}

struct LoopExit;

struct PretestExit {
    after: Option<SemanticNode>,
    edge_block: Option<crate::ir::BlockId>,
}

impl LoopExit {
    fn local_break(region: RegionId) -> SemanticNode {
        SemanticNode::Leave(crate::ir::SemanticLeave {
            site: None,
            condition: None,
            kind: SemanticLeaveKind::Break,
            edge: None,
            origin: None,
            source: region,
            destination: region,
            target: region,
            cleanup: Vec::new(),
        })
    }

    fn guarded(
        node: &SemanticNode,
        region: RegionId,
        direction: ExitDirection,
    ) -> Option<&SemanticPredicate> {
        let SemanticNode::If {
            condition,
            then_node,
            else_node: None,
        } = node
        else {
            return None;
        };
        Self::is_single(then_node, region, direction).then_some(condition)
    }

    fn is_single(node: &SemanticNode, region: RegionId, direction: ExitDirection) -> bool {
        match node {
            SemanticNode::Leave(leave) => {
                leave.target == region
                    && leave.cleanup.is_empty()
                    && matches!(
                        (&leave.kind, direction),
                        (&SemanticLeaveKind::Break, ExitDirection::Break)
                            | (&SemanticLeaveKind::Continue, ExitDirection::Continue)
                    )
            }
            SemanticNode::Sequence(nodes) => {
                let mut meaningful = nodes.iter().filter(|node| !LoopBody::is_empty(node));
                meaningful
                    .next()
                    .is_some_and(|node| Self::is_single(node, region, direction))
                    && meaningful.next().is_none()
            }
            _ => false,
        }
    }

    /// Entry exit for a pre-tested loop. A local break or the unique SCC follow
    /// becomes the natural while-exit; every other completion is re-emitted
    /// after the loop so its destination remains explicit.
    fn pretest_exit(
        node: &SemanticNode,
        region: RegionId,
        loop_label: Option<SemanticLabel>,
        follow: Option<crate::ir::BlockId>,
        preserved_blocks: &BTreeSet<BlockId>,
    ) -> Option<PretestExit> {
        let Some(leave) = Self::single_leave(node) else {
            return crate::ir::semantic::SemanticCompletion::analyze(node)
                .exits_loop(region, loop_label)
                .then(|| PretestExit {
                    after: Some(node.clone()),
                    edge_block: None,
                });
        };
        let edge = Self::edge_identity(node, preserved_blocks);
        let edge_block = Self::first_block(&edge);
        let natural = || PretestExit {
            after: edge_block.map(|_| edge.clone()),
            edge_block,
        };
        match &leave.kind {
            SemanticLeaveKind::Break if leave.target == region && leave.cleanup.is_empty() => {
                Some(natural())
            }
            SemanticLeaveKind::BreakLabel(label)
                if loop_label.is_some_and(|loop_label| *label == loop_label)
                    && leave.cleanup.is_empty() =>
            {
                Some(natural())
            }
            SemanticLeaveKind::FallThrough(target) | SemanticLeaveKind::Jump(target)
                if follow.is_some_and(|follow| *target == follow) && leave.cleanup.is_empty() =>
            {
                Some(natural())
            }
            SemanticLeaveKind::Continue | SemanticLeaveKind::Break if leave.target != region => {
                Some(PretestExit {
                    after: Some(node.clone()),
                    edge_block: None,
                })
            }
            SemanticLeaveKind::ContinueLabel(label)
                if loop_label.is_some_and(|loop_label| *label == loop_label) =>
            {
                None
            }
            SemanticLeaveKind::BreakLabel(_) | SemanticLeaveKind::ContinueLabel(_) => {
                Some(PretestExit {
                    after: Some(node.clone()),
                    edge_block: None,
                })
            }
            SemanticLeaveKind::FallThrough(_)
            | SemanticLeaveKind::Jump(_)
            | SemanticLeaveKind::Return(_)
            | SemanticLeaveKind::Throw(_) => Some(PretestExit {
                after: Some(node.clone()),
                edge_block: None,
            }),
            _ => None,
        }
    }

    fn edge_identity(node: &SemanticNode, preserved_blocks: &BTreeSet<BlockId>) -> SemanticNode {
        match node {
            SemanticNode::BasicBlock(block) if block.statements.is_empty() => node.clone(),
            SemanticNode::Sequence(nodes) => SemanticNode::sequence(
                nodes
                    .iter()
                    .map(|node| Self::edge_identity(node, preserved_blocks)),
            ),
            SemanticNode::Leave(leave) => SemanticNode::sequence(
                BlockIdentity::leave_blocks(leave, preserved_blocks)
                    .into_iter()
                    .map(|block| {
                        SemanticNode::BasicBlock(crate::ir::SemanticBlock {
                            id: block,
                            statements: Vec::new(),
                        })
                    }),
            ),
            SemanticNode::Empty
            | SemanticNode::BasicBlock(_)
            | SemanticNode::If { .. }
            | SemanticNode::Loop { .. }
            | SemanticNode::For { .. }
            | SemanticNode::ForEach { .. }
            | SemanticNode::Label { .. }
            | SemanticNode::Switch { .. }
            | SemanticNode::Try { .. }
            | SemanticNode::Synchronized { .. } => SemanticNode::Empty,
        }
    }

    fn retain_edge_identity(
        nodes: &mut Vec<SemanticNode>,
        index: usize,
        preserved_blocks: &BTreeSet<BlockId>,
    ) {
        let identity = Self::edge_identity(&nodes[index], preserved_blocks);
        if BlockIdentity::contains(&identity, preserved_blocks) {
            nodes[index] = identity;
        } else {
            nodes.remove(index);
        }
    }

    fn strip_terminal(
        nodes: &mut Vec<SemanticNode>,
        region: RegionId,
        direction: ExitDirection,
        preserved_blocks: &BTreeSet<BlockId>,
    ) {
        if let Some(index) = nodes.iter().rposition(|node| !LoopBody::is_empty(node)) {
            if Self::is_single(&nodes[index], region, direction) {
                Self::retain_edge_identity(nodes, index, preserved_blocks);
            }
        }
    }

    fn first_block(node: &SemanticNode) -> Option<crate::ir::BlockId> {
        match node {
            SemanticNode::BasicBlock(block) => Some(block.id),
            SemanticNode::Sequence(nodes) => nodes.iter().find_map(Self::first_block),
            _ => None,
        }
    }

    fn single_leave(node: &SemanticNode) -> Option<&crate::ir::SemanticLeave> {
        match node {
            SemanticNode::Leave(leave) => Some(leave),
            SemanticNode::Sequence(nodes) => {
                let mut meaningful = nodes.iter().filter(|node| !LoopBody::is_empty(node));
                let leave = meaningful.next().and_then(Self::single_leave)?;
                meaningful.next().is_none().then_some(leave)
            }
            _ => None,
        }
    }

    fn strip_continue_label(
        nodes: &mut Vec<SemanticNode>,
        label: SemanticLabel,
        preserved_blocks: &BTreeSet<BlockId>,
    ) {
        let is_continue = |node: &SemanticNode| match node {
            SemanticNode::Leave(leave) => {
                matches!(&leave.kind, SemanticLeaveKind::ContinueLabel(l) if *l == label)
                    && leave.cleanup.is_empty()
            }
            SemanticNode::Sequence(items) => {
                let mut meaningful = items.iter().filter(|node| !LoopBody::is_empty(node));
                meaningful
                    .next()
                    .is_some_and(|node| {
                        matches!(
                            node,
                            SemanticNode::Leave(leave)
                                if matches!(&leave.kind, SemanticLeaveKind::ContinueLabel(l) if *l == label)
                                    && leave.cleanup.is_empty()
                        )
                    })
                    && meaningful.next().is_none()
            }
            _ => false,
        };
        if let Some(index) = nodes.iter().rposition(|node| !LoopBody::is_empty(node)) {
            if is_continue(&nodes[index]) {
                Self::retain_edge_identity(nodes, index, preserved_blocks);
            }
        }
    }
}

struct LocalBreakRetargeting {
    region: RegionId,
    loop_label: Option<SemanticLabel>,
    exit_label: SemanticLabel,
}

impl LocalBreakRetargeting {
    fn new(region: RegionId, loop_label: Option<SemanticLabel>, exit_label: SemanticLabel) -> Self {
        Self {
            region,
            loop_label,
            exit_label,
        }
    }

    fn apply(self, body: Vec<SemanticNode>) -> Result<Vec<SemanticNode>, SemanticFoldError> {
        let mut retargeting = self;
        let body = retargeting.fold_node(SemanticNode::sequence(body))?;
        Ok(match body {
            SemanticNode::Sequence(nodes) => nodes,
            SemanticNode::Empty => Vec::new(),
            node => vec![node],
        })
    }
}

impl SemanticFolder for LocalBreakRetargeting {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        Ok(match node {
            SemanticNode::Leave(mut leave)
                if leave.cleanup.is_empty()
                    && (matches!(&leave.kind, SemanticLeaveKind::Break)
                        && leave.target == self.region
                        || matches!(
                            &leave.kind,
                            SemanticLeaveKind::BreakLabel(label)
                                if self.loop_label == Some(*label)
                        )) =>
            {
                leave.kind = SemanticLeaveKind::BreakLabel(self.exit_label);
                SemanticNode::Leave(leave)
            }
            SemanticNode::Sequence(nodes) => SemanticNode::sequence(nodes),
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => SemanticNode::branch(
                condition.into_inner(),
                *then_node,
                else_node.map(|node| *node),
            ),
            node => node,
        })
    }
}

struct ExitPair {
    break_index: usize,
    continue_index: usize,
    continue_condition: SemanticPredicate,
}

impl ExitPair {
    fn analyze(
        region: RegionId,
        first_index: usize,
        first: &SemanticNode,
        second_index: usize,
        second: &SemanticNode,
        preserved_blocks: &BTreeSet<BlockId>,
    ) -> Result<Option<Self>, SemanticFoldError> {
        if BlockIdentity::contains(first, preserved_blocks)
            || BlockIdentity::contains(second, preserved_blocks)
        {
            return Ok(None);
        }
        let direct = (
            LoopExit::guarded(first, region, ExitDirection::Break),
            LoopExit::guarded(second, region, ExitDirection::Continue),
        );
        let reversed = (
            LoopExit::guarded(first, region, ExitDirection::Continue),
            LoopExit::guarded(second, region, ExitDirection::Break),
        );
        let (break_index, break_condition, continue_index, continue_condition) = match direct {
            (Some(break_condition), Some(continue_condition)) => (
                first_index,
                break_condition,
                second_index,
                continue_condition,
            ),
            _ => match reversed {
                (Some(continue_condition), Some(break_condition)) => (
                    second_index,
                    break_condition,
                    first_index,
                    continue_condition,
                ),
                _ => return Ok(None),
            },
        };
        let complement = continue_condition.clone().negate();
        if !PredicateProof::equivalent(break_condition, &complement)? {
            return Ok(None);
        }
        Ok(Some(Self {
            break_index,
            continue_index,
            continue_condition: continue_condition.clone(),
        }))
    }

    fn removed_indices(&self) -> [usize; 2] {
        let mut indices = [self.break_index, self.continue_index];
        indices.sort_unstable_by(|left, right| right.cmp(left));
        indices
    }
}

struct PredicateProof;

impl PredicateProof {
    fn equivalent(
        left: &SemanticPredicate,
        right: &SemanticPredicate,
    ) -> Result<bool, SemanticFoldError> {
        match left.domain()?.equivalent(&right.domain()?) {
            Ok(equivalent) => Ok(equivalent),
            Err(error) if error.is_resource_limit() => Ok(false),
            Err(error) => Err(error.into()),
        }
    }
}

/// Derives the predicate under which a pre-tested loop body reaches its local
/// continuation. A body containing only complementary local continue/break
/// outcomes is another part of the loop test, not an executable loop body.
struct LoopContinuationDecision;

impl LoopContinuationDecision {
    fn refine(
        test: &mut SemanticLoopTest,
        body: &mut Vec<SemanticNode>,
        region: RegionId,
        loop_label: Option<SemanticLabel>,
        preserved_blocks: &BTreeSet<BlockId>,
    ) -> Result<(), SemanticFoldError> {
        let setup_len = MovableDecisionSetup::length(body, &test.condition);
        let decision = SemanticNode::sequence(body[setup_len..].iter().cloned());
        if BlockIdentity::contains(&decision, preserved_blocks) {
            return Ok(());
        }
        let Some(flow) = DecisionFlow::analyze(&decision, region, loop_label) else {
            return Ok(());
        };
        let Some(continue_path) = flow.binary_loop_condition()? else {
            return Ok(());
        };

        let decision_setup = SemanticNode::sequence(body.drain(..setup_len));
        let setup = std::mem::replace(&mut *test.setup, SemanticNode::Empty);
        test.setup = Box::new(SemanticNode::sequence([setup, decision_setup]));
        test.condition.value = PredicateAlgebra::and(
            std::mem::replace(&mut test.condition.value, SemanticPredicate::True),
            continue_path,
        );
        body.clear();
        Ok(())
    }
}

/// Straight-line definitions that can become part of loop-test evaluation
/// without changing effects or overwriting an entry-test operand.
struct MovableDecisionSetup;

impl MovableDecisionSetup {
    fn length(nodes: &[SemanticNode], condition: &SemanticPredicate) -> usize {
        let condition_facts = SemanticExpressionFacts::of_predicate(condition);
        let condition_ssa = condition_facts
            .used_ssa_variables()
            .collect::<BTreeSet<_>>();
        let condition_variables = condition_facts.used_variables().collect::<BTreeSet<_>>();
        nodes
            .iter()
            .take_while(|node| {
                if LoopBody::is_empty(node) {
                    return true;
                }
                let SemanticNode::BasicBlock(block) = node else {
                    return false;
                };
                if block.statements.iter().any(|statement| {
                    statement
                        .instruction_ref()
                        .is_none_or(|instruction| !instruction.effects().is_pure())
                }) {
                    return false;
                }
                let facts = SemanticExpressionFacts::of_node(node);
                facts
                    .defined_ssa_variables()
                    .all(|variable| !condition_ssa.contains(&variable))
                    && facts
                        .defined_variables()
                        .all(|variable| !condition_variables.contains(&variable))
            })
            .count()
    }
}

/// Boolean completion domains for a side-effect-free structured decision.
struct DecisionFlow {
    normal: SemanticPredicate,
    continue_path: SemanticPredicate,
    break_path: SemanticPredicate,
}

impl DecisionFlow {
    fn analyze(
        node: &SemanticNode,
        region: RegionId,
        loop_label: Option<SemanticLabel>,
    ) -> Option<Self> {
        match node {
            SemanticNode::Empty => Some(Self::normal()),
            SemanticNode::BasicBlock(block) if block.statements.is_empty() => Some(Self::normal()),
            SemanticNode::Sequence(nodes) => {
                let mut flow = Self::normal();
                for node in nodes {
                    flow = flow.sequence(Self::analyze(node, region, loop_label)?);
                }
                Some(flow)
            }
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => {
                let when_true = Self::analyze(then_node, region, loop_label)?;
                let when_false = match else_node {
                    Some(node) => Self::analyze(node, region, loop_label)?,
                    None => Self::normal(),
                };
                Some(Self::alternatives(
                    condition.value.clone(),
                    when_true,
                    when_false,
                ))
            }
            SemanticNode::Leave(leave) if leave.cleanup.is_empty() => match &leave.kind {
                SemanticLeaveKind::Continue if leave.target == region => Some(Self::continuing()),
                SemanticLeaveKind::Break if leave.target == region => Some(Self::breaking()),
                SemanticLeaveKind::ContinueLabel(label)
                    if loop_label.is_some_and(|expected| *label == expected) =>
                {
                    Some(Self::continuing())
                }
                SemanticLeaveKind::BreakLabel(label)
                    if loop_label.is_some_and(|expected| *label == expected) =>
                {
                    Some(Self::breaking())
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn binary_loop_condition(&self) -> Result<Option<SemanticPredicate>, SemanticFoldError> {
        if !PredicateProof::equivalent(&self.normal, &SemanticPredicate::False)?
            || PredicateProof::equivalent(&self.continue_path, &SemanticPredicate::False)?
            || PredicateProof::equivalent(&self.break_path, &SemanticPredicate::False)?
            || !PredicateProof::equivalent(&self.break_path, &self.continue_path.clone().negate())?
        {
            return Ok(None);
        }
        Ok(Some(self.continue_path.clone()))
    }

    fn normal() -> Self {
        Self {
            normal: SemanticPredicate::True,
            continue_path: SemanticPredicate::False,
            break_path: SemanticPredicate::False,
        }
    }

    fn continuing() -> Self {
        Self {
            normal: SemanticPredicate::False,
            continue_path: SemanticPredicate::True,
            break_path: SemanticPredicate::False,
        }
    }

    fn breaking() -> Self {
        Self {
            normal: SemanticPredicate::False,
            continue_path: SemanticPredicate::False,
            break_path: SemanticPredicate::True,
        }
    }

    fn sequence(self, next: Self) -> Self {
        let reaches_next = self.normal.clone();
        Self {
            normal: PredicateAlgebra::and(reaches_next.clone(), next.normal),
            continue_path: PredicateAlgebra::or(
                self.continue_path,
                PredicateAlgebra::and(reaches_next.clone(), next.continue_path),
            ),
            break_path: PredicateAlgebra::or(
                self.break_path,
                PredicateAlgebra::and(reaches_next, next.break_path),
            ),
        }
    }

    fn alternatives(condition: SemanticPredicate, when_true: Self, when_false: Self) -> Self {
        let inverse = condition.clone().negate();
        Self {
            normal: PredicateAlgebra::or(
                PredicateAlgebra::and(condition.clone(), when_true.normal),
                PredicateAlgebra::and(inverse.clone(), when_false.normal),
            ),
            continue_path: PredicateAlgebra::or(
                PredicateAlgebra::and(condition.clone(), when_true.continue_path),
                PredicateAlgebra::and(inverse.clone(), when_false.continue_path),
            ),
            break_path: PredicateAlgebra::or(
                PredicateAlgebra::and(condition, when_true.break_path),
                PredicateAlgebra::and(inverse, when_false.break_path),
            ),
        }
    }
}

struct PredicateAlgebra;

impl PredicateAlgebra {
    fn and(left: SemanticPredicate, right: SemanticPredicate) -> SemanticPredicate {
        if let Some(reduced) = Self::absorb_conjunction(&left, &right) {
            return reduced;
        }
        if let Some(reduced) = Self::absorb_conjunction(&right, &left) {
            return reduced;
        }
        match (left, right) {
            (SemanticPredicate::False, _) | (_, SemanticPredicate::False) => {
                SemanticPredicate::False
            }
            (SemanticPredicate::True, right) => right,
            (left, SemanticPredicate::True) => left,
            (SemanticPredicate::And(mut left), SemanticPredicate::And(right)) => {
                left.extend(right);
                SemanticPredicate::And(left)
            }
            (SemanticPredicate::And(mut terms), right) => {
                terms.push(right);
                SemanticPredicate::And(terms)
            }
            (left, SemanticPredicate::And(mut terms)) => {
                terms.insert(0, left);
                SemanticPredicate::And(terms)
            }
            (left, right) => SemanticPredicate::And(vec![left, right]),
        }
    }

    fn or(left: SemanticPredicate, right: SemanticPredicate) -> SemanticPredicate {
        if let Some(reduced) = Self::absorb_disjunction(&left, &right) {
            return reduced;
        }
        if let Some(reduced) = Self::absorb_disjunction(&right, &left) {
            return reduced;
        }
        match (left, right) {
            (SemanticPredicate::True, _) | (_, SemanticPredicate::True) => SemanticPredicate::True,
            (SemanticPredicate::False, right) => right,
            (left, SemanticPredicate::False) => left,
            (SemanticPredicate::Or(mut left), SemanticPredicate::Or(right)) => {
                left.extend(right);
                SemanticPredicate::Or(left)
            }
            (SemanticPredicate::Or(mut terms), right) => {
                terms.push(right);
                SemanticPredicate::Or(terms)
            }
            (left, SemanticPredicate::Or(mut terms)) => {
                terms.insert(0, left);
                SemanticPredicate::Or(terms)
            }
            (left, right) => SemanticPredicate::Or(vec![left, right]),
        }
    }

    /// `A || (!A && B) == A || B`, preserving the single evaluation of `A`
    /// represented by its semantic instruction identity.
    fn absorb_disjunction(
        term: &SemanticPredicate,
        conjunction: &SemanticPredicate,
    ) -> Option<SemanticPredicate> {
        let SemanticPredicate::And(terms) = conjunction else {
            return None;
        };
        let complement = terms
            .iter()
            .position(|candidate| Self::complements(term, candidate))?;
        let mut remainder = terms.clone();
        remainder.remove(complement);
        Some(Self::or(
            term.clone(),
            remainder
                .into_iter()
                .fold(SemanticPredicate::True, Self::and),
        ))
    }

    /// `A && (!A || B) == A && B`, the dual short-circuit absorption law.
    fn absorb_conjunction(
        term: &SemanticPredicate,
        disjunction: &SemanticPredicate,
    ) -> Option<SemanticPredicate> {
        let SemanticPredicate::Or(terms) = disjunction else {
            return None;
        };
        let complement = terms
            .iter()
            .position(|candidate| Self::complements(term, candidate))?;
        let mut remainder = terms.clone();
        remainder.remove(complement);
        Some(Self::and(
            term.clone(),
            remainder
                .into_iter()
                .fold(SemanticPredicate::False, Self::or),
        ))
    }

    fn complements(left: &SemanticPredicate, right: &SemanticPredicate) -> bool {
        match (left, right) {
            (SemanticPredicate::Not(inner), right) | (right, SemanticPredicate::Not(inner)) => {
                Self::same(inner, right)
            }
            _ => false,
        }
    }

    fn same(left: &SemanticPredicate, right: &SemanticPredicate) -> bool {
        match (left, right) {
            (SemanticPredicate::True, SemanticPredicate::True)
            | (SemanticPredicate::False, SemanticPredicate::False) => true,
            (SemanticPredicate::Test(left), SemanticPredicate::Test(right)) => left.id == right.id,
            (SemanticPredicate::Not(left), SemanticPredicate::Not(right)) => {
                Self::same(left, right)
            }
            (SemanticPredicate::And(left), SemanticPredicate::And(right))
            | (SemanticPredicate::Or(left), SemanticPredicate::Or(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .zip(right)
                        .all(|(left, right)| Self::same(left, right))
            }
            _ => false,
        }
    }
}

#[derive(Clone, Copy)]
enum ExitDirection {
    Break,
    Continue,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leave(region: RegionId, kind: SemanticLeaveKind) -> SemanticNode {
        SemanticNode::Leave(crate::ir::SemanticLeave {
            site: None,
            condition: None,
            kind,
            edge: None,
            origin: None,
            source: region,
            destination: region,
            target: region,
            cleanup: Vec::new(),
        })
    }

    #[test]
    fn unique_scc_follow_becomes_natural_loop_exit() {
        let region = RegionId::new(0);
        let header = crate::ir::BlockId::new(1);
        let follow = crate::ir::BlockId::new(9);
        let label = SemanticLabel::loop_(region, header);
        let condition = SemanticPredicate::Test(
            crate::ir::SemanticOperation::from_instruction(crate::ir::InsnNode::new(
                crate::ir::InsnType::If,
                0,
            ))
            .expect("semantic predicate"),
        );
        let body = SemanticNode::sequence([
            SemanticNode::BasicBlock(crate::ir::SemanticBlock {
                id: header,
                statements: Vec::new(),
            }),
            SemanticNode::branch(
                condition,
                SemanticNode::Empty,
                Some(leave(region, SemanticLeaveKind::Jump(follow))),
            ),
            leave(region, SemanticLeaveKind::ContinueLabel(label)),
        ]);

        let classified = LoopClassifier::for_label(label, Some(follow))
            .classify(body)
            .expect("loop classification");

        assert!(matches!(
            classified,
            SemanticNode::Loop {
                control: SemanticLoopControl::Label(control),
                kind: SemanticLoopKind::PreTested,
                ..
            } if control == label
        ));
    }

    #[test]
    fn current_loop_continue_is_not_externalized_as_entry_exit() {
        let region = RegionId::new(0);
        let header = crate::ir::BlockId::new(1);
        let label = SemanticLabel::loop_(region, header);
        let body = SemanticNode::sequence([
            SemanticNode::BasicBlock(crate::ir::SemanticBlock {
                id: header,
                statements: Vec::new(),
            }),
            SemanticNode::branch(
                SemanticPredicate::True,
                leave(region, SemanticLeaveKind::ContinueLabel(label)),
                None,
            ),
        ]);

        let classified = LoopClassifier::for_label(label, None)
            .classify(body)
            .expect("loop classification");

        assert!(matches!(
            classified,
            SemanticNode::Loop {
                control: SemanticLoopControl::Label(control),
                kind: SemanticLoopKind::Endless,
                ..
            } if control == label
        ));
    }

    #[test]
    fn post_test_accepts_one_complete_binary_decision() {
        let region = RegionId::new(0);
        let header = crate::ir::BlockId::new(1);
        let mut body_block = crate::ir::SemanticBlock {
            id: header,
            statements: Vec::new(),
        };
        body_block.statements.push(
            crate::ir::SemanticStatement::instruction(crate::ir::InsnNode::nop())
                .expect("semantic statement"),
        );
        let test = SemanticPredicate::Test(
            crate::ir::SemanticOperation::from_instruction(crate::ir::InsnNode::new(
                crate::ir::InsnType::If,
                0,
            ))
            .expect("semantic predicate"),
        );
        let body = LoopBody::from_node(SemanticNode::sequence([
            SemanticNode::BasicBlock(body_block),
            SemanticNode::branch(
                test,
                leave(region, SemanticLeaveKind::Continue),
                Some(leave(region, SemanticLeaveKind::Break)),
            ),
        ]));
        let preserved = BTreeSet::new();
        let analysis = LoopAnalysis::new(region, header, None, None, &preserved, &body);

        assert!(matches!(
            analysis.post_tested().expect("post-test analysis"),
            Some(LoopClassification::PostTested { .. })
        ));
    }
}
