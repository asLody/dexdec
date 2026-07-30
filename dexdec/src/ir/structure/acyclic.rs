//! Pattern-independent construction of acyclic semantic regions.
//!
//! The query stage computes exact reaching conditions and clusters nodes by
//! Boolean implication plus graph reachability. The construction stage is a
//! separate, mechanical translation from the resulting fact tree to semantic IR.

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::ir::analysis::{
    DominanceError, DominatorTree, ReachingConditionError, ReachingConditions,
};
use crate::ir::bdd::Bdd;
use crate::ir::semantic::{SemanticCompletion, SemanticFactory};
use crate::ir::{
    BlockId, BoolExpr, BoolVariable, InsnType, SemanticBuildError, SemanticNode, SemanticPredicate,
    CFG,
};

pub(super) enum AcyclicStructure {
    Structured(SemanticNode),
    RequiresGraphReduction(AcyclicReductionReason),
}

#[derive(Debug)]
pub(super) enum AcyclicReductionReason {
    ReachingConditions(ReachingConditionError),
    ConditionExpression,
}

pub(super) struct AcyclicStructurer<'a, 'semantic, 'seeded> {
    cfg: &'a CFG,
    semantic: &'semantic SemanticFactory<'semantic>,
    seeded: &'seeded mut BTreeMap<BlockId, SemanticNode>,
    predicates: Option<&'a BTreeMap<BlockId, SemanticPredicate>>,
}

impl<'a, 'semantic, 'seeded> AcyclicStructurer<'a, 'semantic, 'seeded> {
    pub(super) fn new(
        cfg: &'a CFG,
        semantic: &'semantic SemanticFactory<'semantic>,
        seeded: &'seeded mut BTreeMap<BlockId, SemanticNode>,
    ) -> Self {
        Self {
            cfg,
            semantic,
            seeded,
            predicates: None,
        }
    }

    pub(super) fn predicates(
        mut self,
        predicates: &'a BTreeMap<BlockId, SemanticPredicate>,
    ) -> Self {
        self.predicates = Some(predicates);
        self
    }

    pub(super) fn structure(&mut self) -> Result<AcyclicStructure, AcyclicStructureError> {
        let facts = match ReachingConditions::analyze(self.cfg) {
            Ok(facts) => facts,
            Err(error) if error.requires_graph_reduction() => {
                return Ok(AcyclicStructure::RequiresGraphReduction(
                    AcyclicReductionReason::ReachingConditions(error),
                ));
            }
            Err(error) => return Err(error.into()),
        };
        let closed = self
            .cfg
            .graph_node_ids()
            .into_iter()
            .filter(|block| self.cfg.normal_successors(*block).next().is_none())
            .filter(|block| self.is_closed_block(*block))
            .collect();
        let structure = match AcyclicStructureAnalysis::new(self.cfg, &facts, closed).analyze() {
            Ok(structure) => structure,
            Err(AcyclicStructureError::ReachingCondition(error))
                if error.requires_graph_reduction() =>
            {
                return Ok(AcyclicStructure::RequiresGraphReduction(
                    AcyclicReductionReason::ReachingConditions(error),
                ));
            }
            Err(error) => return Err(error),
        };
        let Some(structure) = structure else {
            return Ok(AcyclicStructure::RequiresGraphReduction(
                AcyclicReductionReason::ConditionExpression,
            ));
        };
        Ok(AcyclicStructure::Structured(
            AcyclicStructureLowering::new(self.semantic, &mut *self.seeded, self.predicates)
                .lower(structure)?,
        ))
    }

    fn is_closed_block(&self, block: BlockId) -> bool {
        if let Some(node) = self.seeded.get(&block) {
            return !SemanticCompletion::analyze(node).can_complete_normally();
        }
        self.cfg
            .block(block)
            .and_then(|body| body.terminator())
            .is_some_and(|terminator| {
                matches!(terminator.insn_type, InsnType::Return | InsnType::Throw)
            })
    }
}

struct AcyclicStructureAnalysis<'a> {
    cfg: &'a CFG,
    facts: &'a ReachingConditions,
    closed: BTreeSet<BlockId>,
    expression_budget: Cell<usize>,
}

impl<'a> AcyclicStructureAnalysis<'a> {
    fn new(cfg: &'a CFG, facts: &'a ReachingConditions, closed: BTreeSet<BlockId>) -> Self {
        let expression_budget = facts.order().len().saturating_mul(64).clamp(256, 32_768);
        Self {
            cfg,
            facts,
            closed,
            expression_budget: Cell::new(expression_budget),
        }
    }

    fn analyze(&self) -> Result<Option<AcyclicStructureFact>, AcyclicStructureError> {
        let nodes = self.cfg.graph_node_ids();
        let predecessors = self.cfg.normal_predecessor_snapshot();
        let dominators = DominatorTree::compute_with_predecessors(
            self.cfg,
            self.cfg.entry,
            nodes,
            &predecessors,
        )?;
        let mut subtrees = BTreeMap::<BlockId, StructureItem>::new();
        for block in dominators.postorder() {
            let assumption = ConditionDomain {
                domain: self
                    .facts
                    .condition(block)
                    .ok_or(AcyclicStructureError::MissingCondition(block))?
                    .domain(),
            };
            let mut children = dominators
                .children(block)
                .map(|child| {
                    subtrees
                        .remove(&child)
                        .ok_or(AcyclicStructureError::MissingDominatorSubtree(child))
                })
                .collect::<Result<Vec<_>, _>>()?;
            children.sort_by_key(|child| child.lexical_rank);
            let descendants = if children.is_empty() {
                AcyclicStructureFact::Empty
            } else {
                let Some(structure) = self.refine(children, assumption.clone())? else {
                    return Ok(None);
                };
                structure
            };
            let block_structure = self.block_structure(block)?;
            let mut blocks = BTreeSet::from([block]);
            blocks.extend(Self::fact_blocks(&descendants));
            subtrees.insert(
                block,
                StructureItem {
                    condition: assumption,
                    blocks,
                    lexical_rank: self
                        .facts
                        .rank(block)
                        .ok_or(AcyclicStructureError::MissingRank(block))?,
                    structure: AcyclicStructureFact::sequence(vec![block_structure, descendants]),
                },
            );
        }
        let root = subtrees.remove(&self.cfg.entry).ok_or(
            AcyclicStructureError::MissingDominatorSubtree(self.cfg.entry),
        )?;
        if !subtrees.is_empty() {
            return Err(AcyclicStructureError::MalformedDominatorTree);
        }
        Ok(Some(root.structure))
    }

    fn refine(
        &self,
        items: Vec<StructureItem>,
        assumption: ConditionDomain,
    ) -> Result<Option<AcyclicStructureFact>, AcyclicStructureError> {
        let mut tasks = vec![RefineTask::Refine { items, assumption }];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                RefineTask::Refine { items, assumption } => {
                    let Some(mut cluster) = self.cluster(&items, &assumption)? else {
                        let Some(structure) = self.finish(items, &assumption)? else {
                            return Ok(None);
                        };
                        results.push(structure);
                        continue;
                    };
                    let condition = cluster.condition;
                    let condition_domain = self.facts.compile(&condition)?;
                    let negated_domain = self.facts.not(condition_domain)?;
                    let true_assumption = ConditionDomain {
                        domain: self.facts.and(assumption.domain, condition_domain)?,
                    };
                    let false_assumption = ConditionDomain {
                        domain: self.facts.and(assumption.domain, negated_domain)?,
                    };
                    for item in &mut cluster.when_true {
                        item.condition.domain = self
                            .facts
                            .and(item.condition.domain, true_assumption.domain)?;
                    }
                    for item in &mut cluster.when_false {
                        item.condition.domain = self
                            .facts
                            .and(item.condition.domain, false_assumption.domain)?;
                    }
                    tasks.push(RefineTask::Resume {
                        remaining: cluster.remaining,
                        insertion: cluster.insertion,
                        assumption: assumption.clone(),
                        condition,
                        blocks: cluster.blocks,
                        lexical_rank: cluster.lexical_rank,
                        has_false_branch: !cluster.when_false.is_empty(),
                    });
                    tasks.push(RefineTask::Refine {
                        items: cluster.when_false,
                        assumption: false_assumption,
                    });
                    tasks.push(RefineTask::Refine {
                        items: cluster.when_true,
                        assumption: true_assumption,
                    });
                }
                RefineTask::Resume {
                    mut remaining,
                    insertion,
                    assumption,
                    condition,
                    blocks,
                    lexical_rank,
                    has_false_branch,
                } => {
                    let when_false = results
                        .pop()
                        .ok_or(AcyclicStructureError::MalformedWorkStack)?;
                    let when_true = results
                        .pop()
                        .ok_or(AcyclicStructureError::MalformedWorkStack)?;
                    let branch = AcyclicStructureFact::If {
                        condition,
                        when_true: Box::new(when_true),
                        when_false: has_false_branch.then(|| Box::new(when_false)),
                    };
                    remaining.insert(
                        insertion,
                        StructureItem {
                            condition: assumption.clone(),
                            blocks,
                            lexical_rank,
                            structure: branch,
                        },
                    );
                    tasks.push(RefineTask::Refine {
                        items: remaining,
                        assumption,
                    });
                }
            }
        }
        if results.len() != 1 {
            return Err(AcyclicStructureError::MalformedWorkStack);
        }
        results
            .pop()
            .map(Some)
            .ok_or(AcyclicStructureError::MalformedWorkStack)
    }

    fn block_structure(
        &self,
        block: BlockId,
    ) -> Result<AcyclicStructureFact, AcyclicStructureError> {
        let body = self
            .cfg
            .block(block)
            .ok_or(AcyclicStructureError::MissingBlock(block))?;
        let prefix_only = body.terminator().is_some_and(|terminator| {
            matches!(terminator.insn_type, InsnType::If | InsnType::Switch)
        });
        Ok(AcyclicStructureFact::Block { block, prefix_only })
    }

    fn fact_blocks(structure: &AcyclicStructureFact) -> BTreeSet<BlockId> {
        let mut blocks = BTreeSet::new();
        let mut pending = vec![structure];
        while let Some(structure) = pending.pop() {
            match structure {
                AcyclicStructureFact::Block { block, .. } => {
                    blocks.insert(*block);
                }
                AcyclicStructureFact::Sequence(children) => pending.extend(children),
                AcyclicStructureFact::Guard { body, .. } => pending.push(body),
                AcyclicStructureFact::If {
                    when_true,
                    when_false,
                    ..
                } => {
                    pending.push(when_true);
                    pending.extend(when_false.iter().map(|node| node.as_ref()));
                }
                AcyclicStructureFact::Empty => {}
            }
        }
        blocks
    }

    fn cluster(
        &self,
        items: &[StructureItem],
        assumption: &ConditionDomain,
    ) -> Result<Option<ConditionCluster>, AcyclicStructureError> {
        for condition in self.facts.branch_variables().iter().copied() {
            let owner = self
                .facts
                .condition(condition)
                .ok_or(AcyclicStructureError::MissingCondition(condition))?;
            if !self.facts.implies(assumption.domain, owner.domain())? {
                continue;
            }
            let domain = self.facts.compile(&BoolExpr::block(condition))?;
            let negated = self.facts.not(domain)?;
            if self.facts.implies(assumption.domain, domain)?
                || self.facts.implies(assumption.domain, negated)?
            {
                continue;
            }
            let classes = items
                .iter()
                .map(|item| self.classify(item, domain, negated))
                .collect::<Result<Vec<_>, _>>()?;
            let clustered = classes
                .iter()
                .filter(|class| !matches!(class, BranchClass::Remaining))
                .count();
            if clustered < 2 {
                continue;
            }
            if let Some(cluster) = self.partition(
                BoolExpr::block(condition),
                self.facts
                    .rank(condition)
                    .ok_or(AcyclicStructureError::MissingRank(condition))?,
                items,
                &classes,
            )? {
                return Ok(Some(cluster));
            }
        }
        for (index, candidate) in items.iter().enumerate() {
            if items[..index]
                .iter()
                .any(|previous| previous.condition.domain == candidate.condition.domain)
            {
                continue;
            }
            let domain = candidate.condition.domain;
            let negated = self.facts.not(domain)?;
            if self.facts.implies(assumption.domain, domain)?
                || self.facts.implies(assumption.domain, negated)?
            {
                continue;
            }
            let classes = items
                .iter()
                .map(|item| self.classify(item, domain, negated))
                .collect::<Result<Vec<_>, _>>()?;
            if !classes
                .iter()
                .any(|class| matches!(class, BranchClass::True))
                || !classes
                    .iter()
                    .any(|class| matches!(class, BranchClass::False))
            {
                continue;
            }
            let remaining = self.expression_budget.get();
            let relative = self.facts.constrain(domain, assumption.domain)?;
            let Some((condition, nodes)) = self.facts.expression(relative, remaining)? else {
                continue;
            };
            if let Some(cluster) =
                self.partition(condition, candidate.lexical_rank, items, &classes)?
            {
                self.expression_budget.set(remaining.saturating_sub(nodes));
                return Ok(Some(cluster));
            }
        }
        Ok(None)
    }

    fn classify(
        &self,
        item: &StructureItem,
        condition: Bdd,
        negated: Bdd,
    ) -> Result<BranchClass, AcyclicStructureError> {
        if self.facts.implies(item.condition.domain, condition)? {
            Ok(BranchClass::True)
        } else if self.facts.implies(item.condition.domain, negated)? {
            Ok(BranchClass::False)
        } else {
            Ok(BranchClass::Remaining)
        }
    }

    fn partition(
        &self,
        condition: BoolExpr,
        condition_rank: usize,
        items: &[StructureItem],
        classes: &[BranchClass],
    ) -> Result<Option<ConditionCluster>, AcyclicStructureError> {
        let mut when_true = Vec::new();
        let mut when_false = Vec::new();
        let mut remaining = Vec::new();
        let mut blocks = BTreeSet::new();
        let mut lexical_rank = condition_rank;
        for (item, class) in items.iter().cloned().zip(classes.iter().copied()) {
            match class {
                BranchClass::True => {
                    blocks.extend(item.blocks.iter().copied());
                    lexical_rank = lexical_rank.min(item.lexical_rank);
                    when_true.push(item);
                }
                BranchClass::False => {
                    blocks.extend(item.blocks.iter().copied());
                    lexical_rank = lexical_rank.min(item.lexical_rank);
                    when_false.push(item);
                }
                BranchClass::Remaining => remaining.push(item),
            }
        }
        if self
            .facts
            .any_reaches(&Self::blocks(&when_true), &Self::blocks(&when_false))
            || self
                .facts
                .any_reaches(&Self::blocks(&when_false), &Self::blocks(&when_true))
        {
            return Ok(None);
        }
        let mut lower = 0usize;
        let mut upper = remaining.len();
        for (index, item) in remaining.iter().enumerate() {
            if self.facts.any_reaches(&item.blocks, &blocks) {
                lower = lower.max(index + 1);
            }
            if self.facts.any_reaches(&blocks, &item.blocks) {
                upper = upper.min(index);
            }
        }
        if lower > upper {
            return Ok(None);
        }
        let desired = remaining
            .iter()
            .take_while(|item| item.lexical_rank < lexical_rank)
            .count();
        let insertion = desired.clamp(lower, upper);
        Ok(Some(ConditionCluster {
            condition,
            when_true,
            when_false,
            remaining,
            insertion,
            blocks,
            lexical_rank,
        }))
    }

    fn blocks(items: &[StructureItem]) -> BTreeSet<BlockId> {
        items
            .iter()
            .flat_map(|item| item.blocks.iter().copied())
            .collect()
    }

    fn finish(
        &self,
        items: Vec<StructureItem>,
        assumption: &ConditionDomain,
    ) -> Result<Option<AcyclicStructureFact>, AcyclicStructureError> {
        let mut structures = Vec::with_capacity(items.len());
        let mut active = assumption.domain;
        for item in items {
            let structure = if self.facts.implies(active, item.condition.domain)? {
                item.structure
            } else {
                let remaining = self.expression_budget.get();
                let relative = self.facts.constrain(item.condition.domain, active)?;
                let Some((condition, nodes)) = self.facts.expression(relative, remaining)? else {
                    return Ok(None);
                };
                self.expression_budget.set(remaining.saturating_sub(nodes));
                AcyclicStructureFact::Guard {
                    condition,
                    body: Box::new(item.structure),
                }
            };
            let terminal = item.blocks.iter().copied().try_fold(
                self.facts.not(self.facts.truth())?,
                |domain, block| -> Result<Bdd, AcyclicStructureError> {
                    if !self.closed.contains(&block) {
                        return Ok(domain);
                    }
                    let reached = self
                        .facts
                        .condition(block)
                        .ok_or(AcyclicStructureError::MissingCondition(block))?
                        .domain();
                    Ok(self.facts.or(domain, reached)?)
                },
            )?;
            active = self.facts.and(active, self.facts.not(terminal)?)?;
            structures.push(structure);
        }
        Ok(Some(AcyclicStructureFact::sequence(structures)))
    }
}

#[derive(Clone)]
struct ConditionDomain {
    domain: Bdd,
}

#[derive(Clone)]
struct StructureItem {
    condition: ConditionDomain,
    blocks: BTreeSet<BlockId>,
    lexical_rank: usize,
    structure: AcyclicStructureFact,
}

struct ConditionCluster {
    condition: BoolExpr,
    when_true: Vec<StructureItem>,
    when_false: Vec<StructureItem>,
    remaining: Vec<StructureItem>,
    insertion: usize,
    blocks: BTreeSet<BlockId>,
    lexical_rank: usize,
}

#[derive(Clone, Copy)]
enum BranchClass {
    True,
    False,
    Remaining,
}

#[derive(Debug, Clone)]
enum AcyclicStructureFact {
    Empty,
    Block {
        block: BlockId,
        prefix_only: bool,
    },
    Sequence(Vec<AcyclicStructureFact>),
    Guard {
        condition: BoolExpr,
        body: Box<AcyclicStructureFact>,
    },
    If {
        condition: BoolExpr,
        when_true: Box<AcyclicStructureFact>,
        when_false: Option<Box<AcyclicStructureFact>>,
    },
}

impl AcyclicStructureFact {
    fn sequence(structures: Vec<Self>) -> Self {
        let mut flattened = Vec::new();
        for structure in structures {
            match structure {
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
}

enum RefineTask {
    Refine {
        items: Vec<StructureItem>,
        assumption: ConditionDomain,
    },
    Resume {
        remaining: Vec<StructureItem>,
        insertion: usize,
        assumption: ConditionDomain,
        condition: BoolExpr,
        blocks: BTreeSet<BlockId>,
        lexical_rank: usize,
        has_false_branch: bool,
    },
}

struct AcyclicStructureLowering<'a, 'semantic> {
    semantic: &'semantic SemanticFactory<'semantic>,
    seeded: &'a mut BTreeMap<BlockId, SemanticNode>,
    predicates: Option<&'a BTreeMap<BlockId, SemanticPredicate>>,
}

impl<'a, 'semantic> AcyclicStructureLowering<'a, 'semantic> {
    fn new(
        semantic: &'semantic SemanticFactory<'semantic>,
        seeded: &'a mut BTreeMap<BlockId, SemanticNode>,
        predicates: Option<&'a BTreeMap<BlockId, SemanticPredicate>>,
    ) -> Self {
        Self {
            semantic,
            seeded,
            predicates,
        }
    }

    fn lower(
        &mut self,
        structure: AcyclicStructureFact,
    ) -> Result<SemanticNode, AcyclicStructureError> {
        let mut tasks = vec![LowerTask::Visit(structure)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                LowerTask::Visit(AcyclicStructureFact::Empty) => results.push(SemanticNode::Empty),
                LowerTask::Visit(AcyclicStructureFact::Block { block, prefix_only }) => {
                    results.push(match self.seeded.remove(&block) {
                        Some(node) => node,
                        None => self.semantic.block(block, prefix_only)?,
                    });
                }
                LowerTask::Visit(AcyclicStructureFact::Sequence(structures)) => {
                    tasks.push(LowerTask::Sequence(structures.len()));
                    tasks.extend(structures.into_iter().rev().map(LowerTask::Visit));
                }
                LowerTask::Visit(AcyclicStructureFact::Guard { condition, body }) => {
                    tasks.push(LowerTask::Guard(condition));
                    tasks.push(LowerTask::Visit(*body));
                }
                LowerTask::Visit(AcyclicStructureFact::If {
                    condition,
                    when_true,
                    when_false,
                }) => {
                    tasks.push(LowerTask::If {
                        condition,
                        has_false_branch: when_false.is_some(),
                    });
                    if let Some(when_false) = when_false {
                        tasks.push(LowerTask::Visit(*when_false));
                    }
                    tasks.push(LowerTask::Visit(*when_true));
                }
                LowerTask::Sequence(count) => {
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(AcyclicStructureError::MalformedWorkStack)?;
                    let children = results.drain(start..).collect::<Vec<_>>();
                    results.push(SemanticNode::sequence(children));
                }
                LowerTask::Guard(condition) => {
                    let body = results
                        .pop()
                        .ok_or(AcyclicStructureError::MalformedWorkStack)?;
                    results.push(SemanticNode::branch(self.predicate(condition)?, body, None));
                }
                LowerTask::If {
                    condition,
                    has_false_branch,
                } => {
                    let when_false = if has_false_branch {
                        Some(
                            results
                                .pop()
                                .ok_or(AcyclicStructureError::MalformedWorkStack)?,
                        )
                    } else {
                        None
                    };
                    let when_true = results
                        .pop()
                        .ok_or(AcyclicStructureError::MalformedWorkStack)?;
                    results.push(SemanticNode::branch(
                        self.predicate(condition)?,
                        when_true,
                        when_false,
                    ));
                }
            }
        }
        if results.len() != 1 {
            return Err(AcyclicStructureError::MalformedWorkStack);
        }
        results
            .pop()
            .ok_or(AcyclicStructureError::MalformedWorkStack)
    }

    fn predicate(&self, condition: BoolExpr) -> Result<SemanticPredicate, SemanticBuildError> {
        let Some(predicates) = self.predicates else {
            return self.semantic.predicate(condition);
        };
        MappedPredicate::new(predicates).lower(condition)
    }
}

struct MappedPredicate<'a> {
    predicates: &'a BTreeMap<BlockId, SemanticPredicate>,
}

impl<'a> MappedPredicate<'a> {
    fn new(predicates: &'a BTreeMap<BlockId, SemanticPredicate>) -> Self {
        Self { predicates }
    }

    fn lower(&self, condition: BoolExpr) -> Result<SemanticPredicate, SemanticBuildError> {
        let mut pending = vec![PredicateTask::Visit(condition)];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                PredicateTask::Visit(condition) => match condition {
                    BoolExpr::True => results.push(SemanticPredicate::True),
                    BoolExpr::False => results.push(SemanticPredicate::False),
                    BoolExpr::Symbol(BoolVariable::Block(block)) => {
                        results.push(
                            self.predicates
                                .get(&block)
                                .cloned()
                                .ok_or(SemanticBuildError::MissingCondition(block))?,
                        );
                    }
                    BoolExpr::Symbol(variable) => {
                        return Err(SemanticBuildError::InvalidVariable(variable));
                    }
                    BoolExpr::Not(inner) => {
                        pending.push(PredicateTask::Not);
                        pending.push(PredicateTask::Visit(*inner));
                    }
                    BoolExpr::And(terms) => {
                        let count = terms.len();
                        pending.push(PredicateTask::Junction {
                            count,
                            conjunction: true,
                        });
                        pending.extend(terms.into_iter().rev().map(PredicateTask::Visit));
                    }
                    BoolExpr::Or(terms) => {
                        let count = terms.len();
                        pending.push(PredicateTask::Junction {
                            count,
                            conjunction: false,
                        });
                        pending.extend(terms.into_iter().rev().map(PredicateTask::Visit));
                    }
                },
                PredicateTask::Not => {
                    let inner = results
                        .pop()
                        .ok_or(SemanticBuildError::MalformedPredicate)?;
                    results.push(inner.negate());
                }
                PredicateTask::Junction { count, conjunction } => {
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(SemanticBuildError::MalformedPredicate)?;
                    let terms = results.drain(start..).collect();
                    results.push(if conjunction {
                        SemanticPredicate::And(terms)
                    } else {
                        SemanticPredicate::Or(terms)
                    });
                }
            }
        }
        if results.len() != 1 {
            return Err(SemanticBuildError::MalformedPredicate);
        }
        results.pop().ok_or(SemanticBuildError::MalformedPredicate)
    }
}

enum PredicateTask {
    Visit(BoolExpr),
    Not,
    Junction { count: usize, conjunction: bool },
}

enum LowerTask {
    Visit(AcyclicStructureFact),
    Sequence(usize),
    Guard(BoolExpr),
    If {
        condition: BoolExpr,
        has_false_branch: bool,
    },
}

#[derive(Debug)]
pub enum AcyclicStructureError {
    MissingBlock(BlockId),
    MissingCondition(BlockId),
    MissingRank(BlockId),
    MissingDominatorSubtree(BlockId),
    MalformedDominatorTree,
    MalformedWorkStack,
    Dominance(DominanceError),
    ReachingCondition(ReachingConditionError),
    Semantic(SemanticBuildError),
}

impl fmt::Display for AcyclicStructureError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingBlock(block) => write!(formatter, "missing acyclic block {block}"),
            Self::MissingCondition(block) => {
                write!(formatter, "block {block} has no reaching condition")
            }
            Self::MissingRank(block) => write!(formatter, "block {block} has no lexical rank"),
            Self::MissingDominatorSubtree(block) => {
                write!(formatter, "dominator subtree for block {block} is missing")
            }
            Self::MalformedDominatorTree => formatter.write_str("malformed dominator tree"),
            Self::MalformedWorkStack => {
                formatter.write_str("malformed acyclic structuring work stack")
            }
            Self::Dominance(source) => write!(formatter, "dominance analysis failed: {source}"),
            Self::ReachingCondition(source) => {
                write!(formatter, "reaching-condition analysis failed: {source}")
            }
            Self::Semantic(source) => write!(formatter, "semantic construction failed: {source}"),
        }
    }
}

impl std::error::Error for AcyclicStructureError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Dominance(source) => Some(source),
            Self::ReachingCondition(source) => Some(source),
            Self::Semantic(source) => Some(source),
            _ => None,
        }
    }
}

impl From<DominanceError> for AcyclicStructureError {
    fn from(source: DominanceError) -> Self {
        Self::Dominance(source)
    }
}

impl From<ReachingConditionError> for AcyclicStructureError {
    fn from(source: ReachingConditionError) -> Self {
        Self::ReachingCondition(source)
    }
}

impl From<SemanticBuildError> for AcyclicStructureError {
    fn from(source: SemanticBuildError) -> Self {
        Self::Semantic(source)
    }
}
