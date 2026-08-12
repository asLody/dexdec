//! Sparse reaching-definition facts over occurrence-sensitive Semantic IR.
//!
//! Candidate selection is derived exclusively from the semantic control graph.
//! Effect-aware movement and source rewriting remain planner responsibilities.

use std::collections::BTreeMap;
use std::sync::Arc;

use super::{DefinitionFact, UseFact, UseSite, ValueFlowGraph, ValueIdentity};
use crate::analysis::value_recovery::ValueRecoveryError;
use crate::ir::analysis::{
    SemanticFlowPoint, SemanticReachability, SemanticReachingValues, SemanticValueDefinition,
    SsaVar,
};

pub(super) struct SemanticReachingAnalysis<'a> {
    graph: &'a ValueFlowGraph<'a>,
    model: ReachingModel,
}

enum ReachingModel {
    Ssa(Arc<SemanticReachability>),
    Source {
        values: BTreeMap<SsaVar, usize>,
        facts: SemanticReachingValues,
    },
    Incomplete,
}

impl<'a> SemanticReachingAnalysis<'a> {
    pub(super) fn new(
        graph: &'a ValueFlowGraph<'a>,
        reachability: Option<Arc<SemanticReachability>>,
    ) -> Self {
        let Some(flow) = graph.semantic_flow().filter(|flow| flow.is_complete()) else {
            return Self {
                graph,
                model: ReachingModel::Incomplete,
            };
        };
        if graph.identity() == ValueIdentity::Ssa {
            return Self {
                graph,
                model: ReachingModel::Ssa(
                    reachability.unwrap_or_else(|| Arc::new(flow.reachability())),
                ),
            };
        }

        let values = graph
            .definitions
            .keys()
            .copied()
            .enumerate()
            .map(|(value, key)| (key, value))
            .collect::<BTreeMap<_, _>>();
        let definitions = graph
            .definitions
            .iter()
            .flat_map(|(key, definitions)| {
                let value = values[key];
                definitions
                    .iter()
                    .enumerate()
                    .filter_map(move |(ordinal, definition)| {
                        definition.site.map(|site| {
                            SemanticValueDefinition::new(
                                SemanticFlowPoint::after(site),
                                value,
                                ordinal,
                            )
                        })
                    })
            })
            .collect::<Vec<_>>();
        let targets = graph.movement_points();
        Self {
            graph,
            model: ReachingModel::Source {
                facts: flow.reaching_values(&definitions, values.len(), &targets),
                values,
            },
        }
    }

    fn value(&self, key: SsaVar) -> Result<usize, ValueRecoveryError> {
        match &self.model {
            ReachingModel::Source { values, .. } => values
                .get(&key)
                .copied()
                .ok_or(ValueRecoveryError::MissingSemanticSite),
            ReachingModel::Ssa(_) | ReachingModel::Incomplete => {
                Err(ValueRecoveryError::MissingSemanticSite)
            }
        }
    }

    fn facts(&self) -> Result<&SemanticReachingValues, ValueRecoveryError> {
        match &self.model {
            ReachingModel::Source { facts, .. } => Ok(facts),
            ReachingModel::Ssa(_) | ReachingModel::Incomplete => {
                Err(ValueRecoveryError::IncompleteSemanticFlow)
            }
        }
    }

    fn has_complete_definitions(&self, key: SsaVar) -> bool {
        self.graph.definitions.get(&key).is_some_and(|definitions| {
            definitions
                .iter()
                .all(|definition| definition.site.is_some())
        })
    }

    pub(super) fn candidates(
        &self,
        key: SsaVar,
        point: SemanticFlowPoint,
    ) -> Result<Vec<usize>, ValueRecoveryError> {
        if !self.has_complete_definitions(key) {
            return Err(ValueRecoveryError::MissingDefinitionSite(key));
        }
        match &self.model {
            ReachingModel::Ssa(reachability) => {
                let definitions = &self.graph.definitions[&key];
                Ok(definitions
                    .iter()
                    .enumerate()
                    .filter_map(|(ordinal, definition)| {
                        definition
                            .site
                            .map(SemanticFlowPoint::after)
                            .filter(|definition| reachability.reaches(*definition, point))
                            .map(|_| ordinal)
                    })
                    .collect())
            }
            ReachingModel::Source { .. } => {
                let value = self.value(key)?;
                let candidates = self.facts()?.at(value, point);
                candidates.ok_or(ValueRecoveryError::MissingReachingFact { value: key, point })
            }
            ReachingModel::Incomplete => Err(ValueRecoveryError::IncompleteSemanticFlow),
        }
    }

    pub(super) fn unchanged(
        &self,
        key: SsaVar,
        source: SemanticFlowPoint,
        target: SemanticFlowPoint,
    ) -> bool {
        if !self.graph.definitions.contains_key(&key) {
            return true;
        }
        if !self.has_complete_definitions(key) {
            return false;
        }
        match &self.model {
            ReachingModel::Ssa(_) => true,
            ReachingModel::Source { .. } => self
                .value(key)
                .ok()
                .and_then(|value| self.facts().ok().map(|facts| (value, facts)))
                .and_then(|(value, facts)| facts.unchanged(value, source, target))
                .unwrap_or(false),
            ReachingModel::Incomplete => false,
        }
    }

    pub(super) fn supports(&self, source: SemanticFlowPoint, target: SemanticFlowPoint) -> bool {
        source != target && !matches!(&self.model, ReachingModel::Incomplete)
    }
}

pub(super) struct ReachingDefinitionFacts {
    pub(super) uses: Vec<ReachingUse>,
    /// Number of uses for which each definition remains a feasible reaching
    /// value, including uses whose path relation cannot select one definition.
    pub(super) candidate_uses: Vec<usize>,
}

pub(super) struct ReachingUse {
    pub(super) candidates: Vec<usize>,
    pub(super) selected: Option<usize>,
    pub(super) control: bool,
}

pub(super) struct ReachingDefinitions<'a, 'graph> {
    graph: &'graph ValueFlowGraph<'graph>,
    analysis: &'a SemanticReachingAnalysis<'graph>,
}

impl<'a, 'graph> ReachingDefinitions<'a, 'graph> {
    pub(super) fn new(
        graph: &'graph ValueFlowGraph<'graph>,
        analysis: &'a SemanticReachingAnalysis<'graph>,
    ) -> Self {
        Self { graph, analysis }
    }

    pub(super) fn analyze(
        &self,
        definitions: &[DefinitionFact],
        uses: &[UseFact],
    ) -> Result<ReachingDefinitionFacts, ValueRecoveryError> {
        let key = definitions
            .first()
            .map(|definition| definition.key)
            .ok_or(ValueRecoveryError::MissingSemanticSite)?;
        let mut candidate_uses = vec![0usize; definitions.len()];
        let mut relations = Vec::with_capacity(uses.len());

        for usage in uses {
            let Some(point) = usage.point else {
                return Err(ValueRecoveryError::MissingUsePoint(key));
            };
            let indices = self.analysis.candidates(key, point)?;
            let control = matches!(
                usage.site,
                Some(
                    UseSite::Predicate(_) | UseSite::SelectedPredicate(_, _) | UseSite::Argument(_)
                )
            );
            let mut candidates = Vec::new();
            for index in indices {
                // A definition in a repetitive scope can reach the use from an
                // earlier iteration. Its execution domain describes one
                // iteration only, so comparing it directly with the use domain
                // can incorrectly make the two look disjoint.
                if definitions[index].repetitive
                    || !self
                        .graph
                        .logic
                        .disjoint(usage.domain, definitions[index].domain)?
                {
                    candidates.push(index);
                }
            }
            for &index in &candidates {
                candidate_uses[index] += 1;
            }

            let selected = if control {
                let mut unique = Vec::new();
                for &index in &candidates {
                    if self
                        .graph
                        .logic
                        .implies(usage.domain, definitions[index].domain)?
                        && self.excludes_other_definitions(
                            index,
                            &candidates,
                            usage,
                            definitions,
                        )?
                    {
                        unique.push(index);
                    }
                }
                unique
                    .into_iter()
                    .max_by_key(|index| definitions[*index].event)
            } else {
                match candidates.as_slice() {
                    [index] => Some(*index),
                    _ => None,
                }
            };

            relations.push(ReachingUse {
                candidates,
                selected,
                control,
            });
        }

        Ok(ReachingDefinitionFacts {
            uses: relations,
            candidate_uses,
        })
    }

    fn excludes_other_definitions(
        &self,
        selected: usize,
        reaching: &[usize],
        usage: &UseFact,
        definitions: &[DefinitionFact],
    ) -> Result<bool, ValueRecoveryError> {
        for &candidate in reaching {
            if candidate != selected
                && (definitions[candidate].repetitive
                    || !self
                        .graph
                        .logic
                        .disjoint(usage.domain, definitions[candidate].domain)?)
            {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{
        ArgType, BlockId, InsnArg, InsnNode, InsnType, InstructionId, LiteralArg, RegionId,
        RegisterArg, SemanticBlock, SemanticExpression, SemanticLeave, SemanticLeaveKind,
        SemanticLoopControl, SemanticNode, SemanticOperand, SemanticPredicate,
        SemanticSiteNumbering, SemanticStatement,
    };
    use std::collections::BTreeSet;

    fn predicate(id: usize) -> SemanticPredicate {
        let mut instruction = InsnNode::new(InsnType::If, 0);
        instruction.id = InstructionId::new(id);
        SemanticPredicate::Test(
            crate::ir::SemanticOperation::from_instruction(instruction).unwrap(),
        )
    }

    fn value_predicate(id: usize, register: u32, variable: u32) -> SemanticPredicate {
        let mut instruction = InsnNode::new(InsnType::If, 0);
        instruction.id = InstructionId::new(id);
        SemanticPredicate::Test(crate::ir::SemanticOperation::from_parts(
            instruction,
            vec![SemanticExpression::Register(local(register, variable))],
            None,
        ))
    }

    fn local(register: u32, variable: u32) -> RegisterArg {
        let mut result = RegisterArg::new(register, ArgType::INT);
        result.code_var = Some(variable);
        result
    }

    fn move_statement(
        register: u32,
        variable: u32,
        value: i64,
        edge_copy: bool,
    ) -> SemanticStatement {
        let mut instruction = InsnNode::mov(
            local(register, variable),
            InsnArg::Lit(LiteralArg::new(value, ArgType::INT)),
        );
        instruction.payload.edge_copy = edge_copy;
        SemanticStatement::instruction(instruction).unwrap()
    }

    fn nop_statement() -> SemanticStatement {
        SemanticStatement::instruction(InsnNode::new(InsnType::Nop, 0)).unwrap()
    }

    #[test]
    fn repetitive_definition_reaches_a_disjoint_loop_exit_domain() {
        let region = RegionId::new(1);
        let variable = 2;
        let mut root = SemanticNode::sequence([
            SemanticNode::BasicBlock(SemanticBlock {
                id: BlockId::new(0),
                statements: vec![move_statement(0, variable, 0, true)],
            }),
            SemanticNode::For {
                control: SemanticLoopControl::Region(region),
                init: nop_statement(),
                condition: SemanticOperand::new(predicate(1)),
                update: nop_statement(),
                body: Box::new(SemanticNode::guard(
                    predicate(2),
                    SemanticNode::BasicBlock(SemanticBlock {
                        id: BlockId::new(1),
                        statements: vec![move_statement(0, variable, 7, true)],
                    }),
                )),
            },
            SemanticNode::guard(
                value_predicate(3, 0, variable),
                SemanticNode::Leave(SemanticLeave {
                    site: None,
                    condition: None,
                    kind: SemanticLeaveKind::Return(None),
                    edge: None,
                    origin: None,
                    source: region,
                    destination: region,
                    target: region,
                    cleanup: Vec::new(),
                }),
            ),
        ]);
        SemanticSiteNumbering::assign(&mut root).unwrap();
        let graph = ValueFlowGraph::build_source(&root, &BTreeSet::new()).unwrap();
        let key = SsaVar::new(variable, 0);
        let definitions = &graph.definitions[&key];
        let uses = &graph.uses[&key];
        let analysis = SemanticReachingAnalysis::new(&graph, None);

        let facts = ReachingDefinitions::new(&graph, &analysis)
            .analyze(definitions, uses)
            .unwrap();
        let repetitive = definitions
            .iter()
            .position(|definition| definition.repetitive)
            .expect("loop definition");

        assert_eq!(uses.len(), 1);
        assert!(facts.uses[0].control);
        assert!(facts.uses[0].candidates.contains(&repetitive));
        assert_eq!(facts.uses[0].selected, None);
        assert_eq!(facts.candidate_uses[repetitive], 1);
    }
}
