use std::collections::BTreeSet;
use std::fmt;

use crate::ir::{
    BlockId, BoolExpr, BoolVariable, InsnNode, InsnType, RegionGraph, SemanticBlock,
    SemanticExpression, SemanticFoldError, SemanticLeave, SemanticLeaveKind, SemanticNode,
    SemanticOperation, SemanticPredicate, SemanticStatement, SemanticStatementKind,
    StatementOrigin, CFG,
};

#[derive(Debug)]
pub enum SemanticBuildError {
    MissingBlock(BlockId),
    MissingCondition(BlockId),
    InvalidVariable(BoolVariable),
    MalformedPredicate,
    MalformedExpression,
    Region(crate::ir::RegionInvariantError),
}

impl fmt::Display for SemanticBuildError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingBlock(block) => write!(formatter, "missing semantic block {block}"),
            Self::MissingCondition(block) => {
                write!(formatter, "predicate block {block} has no condition")
            }
            Self::InvalidVariable(variable) => {
                write!(formatter, "invalid CFG predicate variable {variable:?}")
            }
            Self::MalformedPredicate => write!(formatter, "malformed predicate expression"),
            Self::MalformedExpression => write!(formatter, "malformed semantic expression"),
            Self::Region(source) => write!(formatter, "region semantics failed: {source}"),
        }
    }
}

impl std::error::Error for SemanticBuildError {}

impl From<SemanticFoldError> for SemanticBuildError {
    fn from(_: SemanticFoldError) -> Self {
        Self::MalformedExpression
    }
}

impl From<crate::ir::RegionInvariantError> for SemanticBuildError {
    fn from(source: crate::ir::RegionInvariantError) -> Self {
        Self::Region(source)
    }
}

/// Constructs fully-owned semantic nodes from CFG blocks and region facts.
///
/// This is the only component allowed to translate low-level block contents
/// and reaching-condition symbols into semantic IR.
pub(crate) struct SemanticFactory<'a> {
    cfg: &'a CFG,
    regions: &'a RegionGraph,
    region: crate::ir::RegionId,
}

impl<'a> SemanticFactory<'a> {
    pub(crate) fn new(cfg: &'a CFG, regions: &'a RegionGraph, region: crate::ir::RegionId) -> Self {
        Self {
            cfg,
            regions,
            region,
        }
    }

    pub(crate) fn is_switch_region(&self, region: crate::ir::RegionId) -> bool {
        self.regions
            .tree()
            .region(region)
            .is_some_and(|region| matches!(&region.kind, crate::ir::RegionKind::Switch(_)))
    }

    pub(crate) fn phi_copy_blocks(&self) -> BTreeSet<BlockId> {
        self.cfg
            .blocks
            .values()
            .flat_map(|block| &block.insns)
            .filter(|instruction| instruction.insn_type == InsnType::Phi)
            .flat_map(|instruction| {
                instruction
                    .payload
                    .phi_edges
                    .iter()
                    .map(|(predecessor, _)| *predecessor)
            })
            .collect()
    }

    pub(crate) fn branch(
        &self,
        condition: BoolExpr,
        then_node: SemanticNode,
        else_node: Option<SemanticNode>,
    ) -> Result<SemanticNode, SemanticBuildError> {
        Ok(SemanticNode::branch(
            self.predicate(condition)?,
            then_node,
            else_node,
        ))
    }

    pub(crate) fn block(
        &self,
        block_id: BlockId,
        prefix_only: bool,
    ) -> Result<SemanticNode, SemanticBuildError> {
        let block = self
            .cfg
            .block(block_id)
            .ok_or(SemanticBuildError::MissingBlock(block_id))?;
        let limit = if prefix_only {
            block
                .insns
                .iter()
                .position(|insn| insn.insn_type.is_branch() || insn.insn_type.is_terminal())
                .unwrap_or(block.insns.len())
        } else {
            block.insns.len()
        };

        let mut statements = Vec::new();
        for insn in &block.insns[..limit] {
            let origin = insn.id.is_valid().then_some(StatementOrigin {
                block: block_id,
                instruction: insn.id,
            });
            if !Self::is_statement(insn)
                || origin
                    .as_ref()
                    .map(|origin| self.regions.is_elided_in(self.cfg, self.region, origin))
                    .transpose()?
                    .unwrap_or(false)
            {
                continue;
            }
            let mut instruction = insn.clone();
            let kind = match (
                instruction.insn_type,
                instruction.payload.bool_expr.take(),
                instruction.args.as_slice(),
                instruction.result.as_ref(),
            ) {
                (InsnType::Ternary, Some(condition), [when_true, when_false], Some(result)) => {
                    SemanticStatementKind::Definition {
                        id: instruction.id,
                        result: result.clone(),
                        value: SemanticExpression::select(
                            self.predicate(condition)?,
                            SemanticExpression::from_argument(when_true.clone())?,
                            SemanticExpression::from_argument(when_false.clone())?,
                        ),
                    }
                }
                (_, condition, _, _) => {
                    instruction.payload.bool_expr = condition;
                    SemanticStatementKind::Instruction(SemanticOperation::from_instruction(
                        instruction,
                    )?)
                }
            };
            statements.push(SemanticStatement {
                site: None,
                origin,
                kind,
            });
        }
        let mut nodes = vec![SemanticNode::BasicBlock(SemanticBlock {
            id: block_id,
            statements,
        })];

        nodes.extend(self.terminal_leaves_from(block_id)?);

        Ok(SemanticNode::sequence(nodes))
    }

    fn terminal_leaves_from(
        &self,
        block: BlockId,
    ) -> Result<Vec<SemanticNode>, SemanticBuildError> {
        let implicit_cleanup_completion = self
            .regions
            .is_enclosed_implicit_cleanup_completion(self.region, block)?;
        self.regions
            .leaves()
            .iter()
            .filter(move |resolved| {
                resolved.leave.source_block == Some(block)
                    && resolved.leave.edge.is_none()
                    && !(implicit_cleanup_completion
                        && matches!(resolved.leave.exit, crate::ir::RegionExit::Throw(_)))
            })
            .map(|resolved| self.leave(resolved))
            .collect()
    }

    pub(crate) fn leave(
        &self,
        resolved: &crate::ir::ResolvedRegionExit,
    ) -> Result<SemanticNode, SemanticBuildError> {
        Ok(SemanticNode::Leave(SemanticLeave {
            site: None,
            condition: None,
            kind: match &resolved.leave.exit {
                crate::ir::RegionExit::FallThrough(target) => {
                    SemanticLeaveKind::FallThrough(*target)
                }
                crate::ir::RegionExit::Return(value) => SemanticLeaveKind::Return(
                    value
                        .clone()
                        .map(SemanticExpression::from_argument)
                        .transpose()?,
                ),
                crate::ir::RegionExit::Throw(value) => {
                    SemanticLeaveKind::Throw(SemanticExpression::from_argument(value.clone())?)
                }
                crate::ir::RegionExit::Break => SemanticLeaveKind::Break,
                crate::ir::RegionExit::Continue => SemanticLeaveKind::Continue,
            },
            edge: resolved.leave.edge,
            origin: resolved.leave.source_block,
            source: resolved.leave.source,
            destination: resolved.leave.target,
            target: resolved
                .leave
                .control_target
                .unwrap_or(resolved.leave.target),
            cleanup: resolved.cleanup_regions.clone(),
        }))
    }

    pub(crate) fn predicate(
        &self,
        condition: BoolExpr,
    ) -> Result<SemanticPredicate, SemanticBuildError> {
        let mut pending = vec![PredicateTask::Visit(condition)];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                PredicateTask::Visit(condition) => match condition {
                    BoolExpr::True => results.push(SemanticPredicate::True),
                    BoolExpr::False => results.push(SemanticPredicate::False),
                    BoolExpr::Symbol(BoolVariable::Block(block)) => {
                        results.push(SemanticPredicate::Test(self.condition_test(block)?))
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
                    results.push(SemanticPredicate::Not(Box::new(inner)));
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

    fn condition_test(&self, block: BlockId) -> Result<SemanticOperation, SemanticBuildError> {
        let body = self
            .cfg
            .block(block)
            .ok_or(SemanticBuildError::MissingBlock(block))?;
        let instruction = body
            .insns
            .iter()
            .rev()
            .find(|insn| insn.insn_type == InsnType::If)
            .cloned()
            .ok_or(SemanticBuildError::MissingCondition(block))?;
        Ok(SemanticOperation::from_instruction(instruction)?)
    }

    fn is_statement(insn: &InsnNode) -> bool {
        !matches!(
            insn.insn_type,
            InsnType::Nop
                | InsnType::Phi
                | InsnType::If
                | InsnType::Goto
                | InsnType::Switch
                | InsnType::Return
                | InsnType::Throw
        )
    }
}

enum PredicateTask {
    Visit(BoolExpr),
    Not,
    Junction { count: usize, conjunction: bool },
}
