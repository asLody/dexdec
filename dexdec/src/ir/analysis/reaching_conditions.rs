//! Symbolic reachability facts for acyclic ordinary-control-flow graphs.
//!
//! Every block is associated with the exact Boolean condition under which it
//! is reached from the graph entry. ROBDD variables follow topological
//! evaluation order and provide canonical equivalence and implication.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::ir::bdd::{Bdd, BddContext, BddError};
use crate::ir::{BlockId, BoolExpr, BoolVariable, EdgeKind, InsnType, CFG};

#[derive(Debug, Clone)]
pub struct ReachingCondition {
    domain: Bdd,
}

impl ReachingCondition {
    pub fn domain(&self) -> Bdd {
        self.domain
    }
}

pub struct ReachingConditions {
    order: Vec<BlockId>,
    ranks: BTreeMap<BlockId, usize>,
    conditions: BTreeMap<BlockId, ReachingCondition>,
    reachability: ReachabilityMatrix,
    branch_variables: Vec<BlockId>,
    boolean_domain: BddContext,
}

impl ReachingConditions {
    pub fn analyze(cfg: &CFG) -> Result<Self, ReachingConditionError> {
        let nodes = cfg.graph_node_ids().into_iter().collect::<BTreeSet<_>>();
        Self::analyze_slice(cfg, cfg.entry, &nodes)
    }

    /// Compute exact reaching conditions for an induced acyclic CFG slice.
    ///
    /// Keeping the Boolean domain local is important for gated SSA: a Phi
    /// selection depends on the branch frontier that feeds its join, not on
    /// every predicate in the containing method.
    pub fn analyze_slice(
        cfg: &CFG,
        entry: BlockId,
        nodes: &BTreeSet<BlockId>,
    ) -> Result<Self, ReachingConditionError> {
        if !nodes.contains(&entry) {
            return Err(ReachingConditionError::MissingEntry(entry));
        }
        let (order, incoming) = AcyclicTopology::new(cfg, entry, nodes)?.sort()?;
        let branch_variables = order
            .iter()
            .copied()
            .filter(|block| {
                cfg.block(*block).is_some_and(|body| {
                    body.terminator()
                        .is_some_and(|terminator| terminator.insn_type == InsnType::If)
                })
            })
            .collect::<Vec<_>>();
        let variables = branch_variables
            .iter()
            .copied()
            .map(BoolVariable::Block)
            .collect::<Vec<_>>();
        let boolean_domain = BddContext::ordered(variables);
        let mut conditions = BTreeMap::<BlockId, ReachingCondition>::new();
        for block in &order {
            let domain = if *block == entry {
                boolean_domain.truth()
            } else {
                let terms = incoming
                    .get(block)
                    .into_iter()
                    .flatten()
                    .map(|(source, edge)| {
                        let predecessor = conditions.get(source).ok_or(
                            ReachingConditionError::MissingPredecessorCondition {
                                block: *block,
                                predecessor: *source,
                            },
                        )?;
                        let edge = boolean_domain.compile(
                            &EdgePredicate::new(cfg, *source, *block, *edge)?.expression(),
                        )?;
                        Ok(boolean_domain.and(predecessor.domain, edge)?)
                    })
                    .collect::<Result<Vec<_>, ReachingConditionError>>()?;
                terms
                    .into_iter()
                    .try_fold(boolean_domain.falsity(), |left, right| {
                        boolean_domain.or(left, right)
                    })?
            };
            if domain.is_false() {
                return Err(ReachingConditionError::UnreachableBlock(*block));
            }
            conditions.insert(*block, ReachingCondition { domain });
        }
        let reachability = ReachabilityMatrix::analyze(cfg, &nodes, &order)?;
        let ranks = order
            .iter()
            .copied()
            .enumerate()
            .map(|(rank, block)| (block, rank))
            .collect();
        Ok(Self {
            order,
            ranks,
            conditions,
            reachability,
            branch_variables,
            boolean_domain,
        })
    }

    pub fn edge_condition(
        &self,
        cfg: &CFG,
        source: BlockId,
        target: BlockId,
        edge: EdgeKind,
    ) -> Result<Bdd, ReachingConditionError> {
        self.compile(&EdgePredicate::new(cfg, source, target, edge)?.expression())
    }

    pub fn order(&self) -> &[BlockId] {
        &self.order
    }

    pub fn rank(&self, block: BlockId) -> Option<usize> {
        self.ranks.get(&block).copied()
    }

    pub fn condition(&self, block: BlockId) -> Option<&ReachingCondition> {
        self.conditions.get(&block)
    }

    pub fn branch_variables(&self) -> &[BlockId] {
        &self.branch_variables
    }

    pub fn truth(&self) -> Bdd {
        self.boolean_domain.truth()
    }

    pub fn compile(&self, expression: &BoolExpr) -> Result<Bdd, ReachingConditionError> {
        Ok(self.boolean_domain.compile(expression)?)
    }

    pub fn expression(
        &self,
        domain: Bdd,
        node_limit: usize,
    ) -> Result<Option<(BoolExpr, usize)>, ReachingConditionError> {
        Ok(self.boolean_domain.expression(domain, node_limit)?)
    }

    pub fn and(&self, left: Bdd, right: Bdd) -> Result<Bdd, ReachingConditionError> {
        Ok(self.boolean_domain.and(left, right)?)
    }

    pub fn or(&self, left: Bdd, right: Bdd) -> Result<Bdd, ReachingConditionError> {
        Ok(self.boolean_domain.or(left, right)?)
    }

    pub fn not(&self, value: Bdd) -> Result<Bdd, ReachingConditionError> {
        Ok(self.boolean_domain.not(value)?)
    }

    pub fn constrain(&self, value: Bdd, care: Bdd) -> Result<Bdd, ReachingConditionError> {
        Ok(self.boolean_domain.constrain(value, care)?)
    }

    pub fn implies(&self, premise: Bdd, consequence: Bdd) -> Result<bool, ReachingConditionError> {
        Ok(self.boolean_domain.implies_bdd(premise, consequence)?)
    }

    pub fn reaches(&self, source: BlockId, target: BlockId) -> bool {
        self.reachability.reaches(source, target)
    }

    pub fn any_reaches(&self, sources: &BTreeSet<BlockId>, targets: &BTreeSet<BlockId>) -> bool {
        sources.iter().copied().any(|source| {
            targets
                .iter()
                .copied()
                .any(|target| self.reaches(source, target))
        })
    }
}

struct AcyclicTopology {
    entry: BlockId,
    nodes: BTreeSet<BlockId>,
    indegree: BTreeMap<BlockId, usize>,
    incoming: BTreeMap<BlockId, Vec<(BlockId, EdgeKind)>>,
    successors: BTreeMap<BlockId, Vec<BlockId>>,
}

impl AcyclicTopology {
    fn new(
        cfg: &CFG,
        entry: BlockId,
        nodes: &BTreeSet<BlockId>,
    ) -> Result<Self, ReachingConditionError> {
        let mut indegree = nodes
            .iter()
            .copied()
            .map(|block| (block, 0usize))
            .collect::<BTreeMap<_, _>>();
        let mut incoming = nodes
            .iter()
            .copied()
            .map(|block| (block, Vec::new()))
            .collect::<BTreeMap<_, _>>();
        let mut successors = incoming
            .keys()
            .copied()
            .map(|block| (block, Vec::new()))
            .collect::<BTreeMap<_, _>>();
        for source in nodes {
            for &(target, edge) in cfg.successors_with_kind(*source) {
                if edge == EdgeKind::Exception || !nodes.contains(&target) {
                    continue;
                }
                *indegree
                    .get_mut(&target)
                    .ok_or(ReachingConditionError::MissingBlock(target))? += 1;
                incoming
                    .get_mut(&target)
                    .ok_or(ReachingConditionError::MissingBlock(target))?
                    .push((*source, edge));
                successors
                    .get_mut(source)
                    .ok_or(ReachingConditionError::MissingBlock(*source))?
                    .push(target);
            }
        }
        for edges in incoming.values_mut() {
            edges.sort();
        }
        for edges in successors.values_mut() {
            edges.sort();
        }
        Ok(Self {
            entry,
            nodes: nodes.clone(),
            indegree,
            incoming,
            successors,
        })
    }

    fn sort(
        mut self,
    ) -> Result<(Vec<BlockId>, BTreeMap<BlockId, Vec<(BlockId, EdgeKind)>>), ReachingConditionError>
    {
        let mut ready = self
            .indegree
            .iter()
            .filter_map(|(block, degree)| (*degree == 0).then_some(*block))
            .collect::<BTreeSet<_>>();
        if ready != BTreeSet::from([self.entry]) {
            return Err(ReachingConditionError::MultipleEntries {
                expected: self.entry,
                actual: ready.first().copied(),
            });
        }
        let mut order = Vec::with_capacity(self.nodes.len());
        while let Some(block) = ready.pop_first() {
            order.push(block);
            for target in self.successors.get(&block).into_iter().flatten() {
                let degree = self
                    .indegree
                    .get_mut(target)
                    .ok_or(ReachingConditionError::MissingBlock(*target))?;
                *degree = degree
                    .checked_sub(1)
                    .ok_or(ReachingConditionError::MalformedTopology(*target))?;
                if *degree == 0 {
                    ready.insert(*target);
                }
            }
        }
        if order.len() != self.nodes.len() {
            return Err(ReachingConditionError::CyclicGraph);
        }
        if order.first().copied() != Some(self.entry) {
            return Err(ReachingConditionError::MultipleEntries {
                expected: self.entry,
                actual: order.first().copied(),
            });
        }
        Ok((order, self.incoming))
    }
}

struct ReachabilityMatrix {
    indices: BTreeMap<BlockId, usize>,
    rows: Vec<Vec<u64>>,
}

impl ReachabilityMatrix {
    const BYTE_LIMIT: usize = 8 * 1024 * 1024;

    fn analyze(
        cfg: &CFG,
        nodes: &BTreeSet<BlockId>,
        order: &[BlockId],
    ) -> Result<Self, ReachingConditionError> {
        let indices = order
            .iter()
            .copied()
            .enumerate()
            .map(|(index, block)| (block, index))
            .collect::<BTreeMap<_, _>>();
        let words = (order.len() + u64::BITS as usize - 1) / u64::BITS as usize;
        let bytes = order
            .len()
            .checked_mul(words)
            .and_then(|cells| cells.checked_mul(std::mem::size_of::<u64>()))
            .ok_or(ReachingConditionError::ResourceLimit {
                resource: ReachingResource::Reachability,
                limit: Self::BYTE_LIMIT,
            })?;
        if bytes > Self::BYTE_LIMIT {
            return Err(ReachingConditionError::ResourceLimit {
                resource: ReachingResource::Reachability,
                limit: Self::BYTE_LIMIT,
            });
        }
        let mut rows = vec![vec![0u64; words]; order.len()];
        for source in order.iter().rev().copied() {
            let Some(source_index) = indices.get(&source).copied() else {
                continue;
            };
            let mut row = vec![0u64; words];
            for target in cfg
                .normal_successors(source)
                .filter(|target| nodes.contains(target))
            {
                let Some(target_index) = indices.get(&target).copied() else {
                    continue;
                };
                row[target_index / u64::BITS as usize] |=
                    1u64 << (target_index % u64::BITS as usize);
                for (word, descendants) in row.iter_mut().zip(&rows[target_index]) {
                    *word |= descendants;
                }
            }
            rows[source_index] = row;
        }
        Ok(Self { indices, rows })
    }

    fn reaches(&self, source: BlockId, target: BlockId) -> bool {
        let (Some(source), Some(target)) = (
            self.indices.get(&source).copied(),
            self.indices.get(&target).copied(),
        ) else {
            return false;
        };
        self.rows
            .get(source)
            .and_then(|row| row.get(target / u64::BITS as usize))
            .is_some_and(|word| word & (1u64 << (target % u64::BITS as usize)) != 0)
    }
}

struct EdgePredicate {
    expression: BoolExpr,
}

impl EdgePredicate {
    fn new(
        cfg: &CFG,
        source: BlockId,
        target: BlockId,
        edge: EdgeKind,
    ) -> Result<Self, ReachingConditionError> {
        let block = cfg
            .block(source)
            .ok_or(ReachingConditionError::MissingBlock(source))?;
        let terminator = block.terminator().map(|instruction| instruction.insn_type);
        let expression = match (terminator, edge) {
            (Some(InsnType::If), EdgeKind::True) => BoolExpr::block(source),
            (Some(InsnType::If), EdgeKind::False) => BoolExpr::not(BoolExpr::block(source)),
            (Some(InsnType::If), _) => {
                return Err(ReachingConditionError::MalformedBranchEdge {
                    source,
                    target,
                    edge,
                });
            }
            (Some(InsnType::Switch), _) => {
                return Err(ReachingConditionError::UnownedSwitch(source));
            }
            (_, EdgeKind::Normal) => BoolExpr::True,
            (_, _) => {
                return Err(ReachingConditionError::UnexpectedEdge {
                    source,
                    target,
                    edge,
                });
            }
        };
        Ok(Self { expression })
    }

    fn expression(self) -> BoolExpr {
        self.expression
    }
}

#[derive(Debug)]
pub enum ReachingConditionError {
    MissingEntry(BlockId),
    MissingBlock(BlockId),
    MissingPredecessorCondition {
        block: BlockId,
        predecessor: BlockId,
    },
    MultipleEntries {
        expected: BlockId,
        actual: Option<BlockId>,
    },
    MalformedTopology(BlockId),
    CyclicGraph,
    UnreachableBlock(BlockId),
    MalformedBranchEdge {
        source: BlockId,
        target: BlockId,
        edge: EdgeKind,
    },
    UnexpectedEdge {
        source: BlockId,
        target: BlockId,
        edge: EdgeKind,
    },
    UnownedSwitch(BlockId),
    ResourceLimit {
        resource: ReachingResource,
        limit: usize,
    },
    Bdd(BddError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReachingResource {
    Reachability,
}

impl fmt::Display for ReachingConditionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingEntry(block) => write!(formatter, "graph entry {block} is missing"),
            Self::MissingBlock(block) => write!(formatter, "graph block {block} is missing"),
            Self::MissingPredecessorCondition { block, predecessor } => write!(
                formatter,
                "predecessor {predecessor} of {block} has no reaching condition"
            ),
            Self::MultipleEntries { expected, actual } => write!(
                formatter,
                "acyclic graph starts at {actual:?}, expected unique entry {expected}"
            ),
            Self::MalformedTopology(block) => {
                write!(
                    formatter,
                    "acyclic graph has malformed indegree for {block}"
                )
            }
            Self::CyclicGraph => formatter.write_str("reaching-condition graph is cyclic"),
            Self::UnreachableBlock(block) => {
                write!(
                    formatter,
                    "block {block} has an unsatisfiable reaching condition"
                )
            }
            Self::MalformedBranchEdge {
                source,
                target,
                edge,
            } => write!(
                formatter,
                "conditional edge {source} -> {target} has kind {edge:?}"
            ),
            Self::UnexpectedEdge {
                source,
                target,
                edge,
            } => write!(
                formatter,
                "ordinary edge {source} -> {target} has unexpected kind {edge:?}"
            ),
            Self::UnownedSwitch(block) => write!(
                formatter,
                "switch block {block} reached the Boolean region structurer"
            ),
            Self::ResourceLimit { resource, limit } => {
                write!(formatter, "{resource:?} resource limit {limit} exceeded")
            }
            Self::Bdd(source) => write!(formatter, "Boolean decision diagram failed: {source}"),
        }
    }
}

impl std::error::Error for ReachingConditionError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Bdd(source) => Some(source),
            _ => None,
        }
    }
}

impl ReachingConditionError {
    pub fn requires_graph_reduction(&self) -> bool {
        matches!(self, Self::UnownedSwitch(_))
            || matches!(self, Self::ResourceLimit { .. })
            || matches!(self, Self::Bdd(source) if source.is_resource_limit())
    }
}

impl From<BddError> for ReachingConditionError {
    fn from(source: BddError) -> Self {
        Self::Bdd(source)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Block, InsnNode};

    #[test]
    fn slice_uses_its_own_entry_condition() {
        let mut cfg = CFG::new("slice");
        for id in 0..=4 {
            cfg.add_block(Block::new(BlockId::new(id)));
        }
        cfg.block_mut(BlockId::new(1))
            .expect("branch block")
            .insns
            .push(InsnNode::new(InsnType::If, 0));
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(1), BlockId::new(2), EdgeKind::True);
        cfg.add_edge(BlockId::new(1), BlockId::new(3), EdgeKind::False);
        cfg.add_edge(BlockId::new(2), BlockId::new(4), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(3), BlockId::new(4), EdgeKind::Normal);

        let nodes = [1, 2, 3, 4]
            .into_iter()
            .map(BlockId::new)
            .collect::<BTreeSet<_>>();
        let facts =
            ReachingConditions::analyze_slice(&cfg, BlockId::new(1), &nodes).expect("local slice");

        assert!(facts
            .condition(BlockId::new(1))
            .expect("entry condition")
            .domain()
            .is_true());
        assert!(facts
            .condition(BlockId::new(4))
            .expect("join condition")
            .domain()
            .is_true());
    }
}
