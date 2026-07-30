use std::collections::{BTreeMap, BTreeSet};

use crate::{
    ir::{
        analysis::{VariableEdgeKind, VariableSemanticGraph},
        ArgType, InsnType,
    },
    platform_symbols::{PlatformConstant, PlatformSymbolSet},
};

pub(crate) struct RelationalNameInference {
    names: BTreeMap<u32, String>,
}

impl RelationalNameInference {
    pub(crate) fn analyze(graph: &VariableSemanticGraph) -> Self {
        let names = graph
            .variables()
            .filter(|variable| variable.ty() == &ArgType::BOOLEAN)
            .filter_map(|variable| {
                let names = graph
                    .edges_for(variable.identity())
                    .filter(|edge| matches!(edge.kind(), VariableEdgeKind::Definition))
                    .filter_map(|edge| edge.operation().and_then(|id| graph.operation(id)))
                    .filter_map(Self::operation_name)
                    .collect::<BTreeSet<_>>();
                let mut names = names.into_iter();
                let name = names.next()?;
                names
                    .next()
                    .is_none()
                    .then_some((variable.identity(), name))
            })
            .collect();
        Self { names }
    }

    pub(crate) fn name(&self, variable: u32) -> Option<&str> {
        self.names.get(&variable).map(String::as_str)
    }

    fn operation_name(operation: &crate::ir::analysis::OperationNode) -> Option<String> {
        let crate::ir::MemberReference::Method(method) = operation.reference()? else {
            return None;
        };
        if operation.kind() != InsnType::Invoke
            || method.name != "equals"
            || method.descriptor.return_type != ArgType::BOOLEAN
        {
            return None;
        }
        let concepts = operation
            .operands()
            .iter()
            .filter_map(|operand| Self::concept(operand.reference()?))
            .collect::<BTreeSet<_>>();
        let mut concepts = concepts.into_iter();
        let concept = concepts.next()?;
        if concepts.next().is_some() {
            return None;
        }
        Some(format!("same{}", Self::upper_camel(&concept)))
    }

    fn concept(reference: &crate::ir::MemberReference) -> Option<String> {
        let name = match reference {
            crate::ir::MemberReference::Method(method) => method.name.as_str(),
            crate::ir::MemberReference::Field(field) => field.name.as_str(),
        };
        if name.starts_with('<')
            || name.contains('$')
            || name
                .chars()
                .filter(|character| character.is_alphanumeric())
                .count()
                < 3
        {
            return None;
        }
        let concept = name.strip_prefix("get").filter(|suffix| {
            suffix
                .chars()
                .next()
                .is_some_and(|character| character.is_ascii_uppercase())
        });
        Some(concept.unwrap_or(name).to_owned())
    }

    fn upper_camel(value: &str) -> String {
        let mut characters = value.chars();
        let Some(first) = characters.next() else {
            return String::new();
        };
        first.to_uppercase().chain(characters).collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ConstantCandidate {
    owner: String,
    field: String,
    family: String,
}

#[derive(Debug, Clone)]
struct ConstantObservation {
    variable: u32,
    candidates: Vec<ConstantCandidate>,
}

/// Resolves literal-backed names by treating a method's constant families as
/// latent domains. Unique observations establish the domain; ambiguous values
/// can then select the candidate consistent with the rest of the method.
pub(crate) struct TypedConstantNameInference {
    names: BTreeMap<u32, String>,
}

impl TypedConstantNameInference {
    pub(crate) fn analyze(graph: &VariableSemanticGraph, symbols: &PlatformSymbolSet) -> Self {
        let observations = graph
            .variables()
            .filter(|variable| variable.ty() == &ArgType::BOOLEAN)
            .flat_map(|variable| {
                graph
                    .edges_for(variable.identity())
                    .filter(|edge| matches!(edge.kind(), VariableEdgeKind::Definition))
                    .filter_map(|edge| edge.operation().and_then(|id| graph.operation(id)))
                    .filter(|operation| operation.kind() == InsnType::Invoke)
                    .filter_map(move |operation| {
                        let candidates = Self::operation_candidates(operation, symbols);
                        (!candidates.is_empty()).then_some(ConstantObservation {
                            variable: variable.identity(),
                            candidates,
                        })
                    })
            })
            .collect::<Vec<_>>();
        let family_scores = Self::family_scores(&observations);
        let mut names = BTreeMap::<u32, BTreeSet<String>>::new();
        for observation in observations {
            let Some(candidate) = Self::select(&observation.candidates, &family_scores) else {
                continue;
            };
            names
                .entry(observation.variable)
                .or_default()
                .insert(candidate.field.clone());
        }
        Self {
            names: names
                .into_iter()
                .filter_map(|(variable, names)| {
                    let mut names = names.into_iter();
                    let name = names.next()?;
                    names.next().is_none().then_some((variable, name))
                })
                .collect(),
        }
    }

    pub(crate) fn name(&self, variable: u32) -> Option<&str> {
        self.names.get(&variable).map(String::as_str)
    }

    fn operation_candidates(
        operation: &crate::ir::analysis::OperationNode,
        symbols: &PlatformSymbolSet,
    ) -> Vec<ConstantCandidate> {
        let values = operation
            .operands()
            .iter()
            .filter_map(|operand| operand.literal())
            .filter(|value| *value != 0)
            .collect::<BTreeSet<_>>();
        let owners = operation
            .operands()
            .iter()
            .filter_map(|operand| operand.ty()?.as_object())
            .map(ToOwned::to_owned)
            .collect::<BTreeSet<_>>();
        owners
            .into_iter()
            .filter_map(|owner| {
                let descriptor = ArgType::object(&owner).to_descriptor();
                symbols.class(&descriptor).map(|class| (owner, class))
            })
            .flat_map(|(owner, class)| {
                class
                    .fields
                    .iter()
                    .filter(|field| {
                        field.constant.as_ref().is_some_and(|constant| {
                            matches!(constant, PlatformConstant::Integer(value) if values.contains(value))
                        })
                    })
                    .map(move |field| ConstantCandidate {
                        owner: owner.clone(),
                        family: Self::family(&field.name),
                        field: field.name.clone(),
                    })
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    fn family(field: &str) -> String {
        let mut words = field.split('_').filter(|word| !word.is_empty());
        let first = words.next().unwrap_or(field);
        match words.next() {
            Some(second) => format!("{first}_{second}"),
            None => first.to_owned(),
        }
    }

    fn family_scores(observations: &[ConstantObservation]) -> BTreeMap<(String, String), u16> {
        let mut scores = BTreeMap::<(String, String), u16>::new();
        for observation in observations {
            let unique_bonus = if observation.candidates.len() == 1 {
                8
            } else {
                0
            };
            for candidate in &observation.candidates {
                let score = scores
                    .entry((candidate.owner.clone(), candidate.family.clone()))
                    .or_default();
                *score = score.saturating_add(1 + unique_bonus);
            }
        }
        scores
    }

    fn select<'a>(
        candidates: &'a [ConstantCandidate],
        scores: &BTreeMap<(String, String), u16>,
    ) -> Option<&'a ConstantCandidate> {
        let mut ranked = candidates
            .iter()
            .map(|candidate| {
                let score = scores
                    .get(&(candidate.owner.clone(), candidate.family.clone()))
                    .copied()
                    .unwrap_or_default();
                (candidate, score)
            })
            .collect::<Vec<_>>();
        ranked.sort_by(|left, right| right.1.cmp(&left.1).then_with(|| left.0.cmp(right.0)));
        let (winner, score) = ranked.first().copied()?;
        let tied = ranked.get(1).is_some_and(|candidate| candidate.1 == score);
        (!tied).then_some(winner)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn candidate(field: &str) -> ConstantCandidate {
        ConstantCandidate {
            owner: "android/content/Intent".to_owned(),
            field: field.to_owned(),
            family: TypedConstantNameInference::family(field),
        }
    }

    #[test]
    fn cooccurring_constants_disambiguate_a_latent_domain() {
        let activity = candidate("FLAG_ACTIVITY_CLEAR_TOP");
        let ambiguous = vec![
            candidate("FLAG_ACTIVITY_NEW_TASK"),
            candidate("FLAG_RECEIVER_FOREGROUND"),
        ];
        let observations = vec![
            ConstantObservation {
                variable: 1,
                candidates: vec![activity],
            },
            ConstantObservation {
                variable: 2,
                candidates: ambiguous.clone(),
            },
        ];
        let scores = TypedConstantNameInference::family_scores(&observations);

        assert_eq!(
            TypedConstantNameInference::select(&ambiguous, &scores)
                .map(|value| value.field.as_str()),
            Some("FLAG_ACTIVITY_NEW_TASK")
        );
    }

    #[test]
    fn unresolved_domain_ties_are_not_guessed() {
        let ambiguous = vec![
            candidate("FLAG_ACTIVITY_NEW_TASK"),
            candidate("FLAG_RECEIVER_FOREGROUND"),
        ];
        let observations = vec![ConstantObservation {
            variable: 1,
            candidates: ambiguous.clone(),
        }];
        let scores = TypedConstantNameInference::family_scores(&observations);

        assert!(TypedConstantNameInference::select(&ambiguous, &scores).is_none());
    }
}
