use std::collections::{BTreeMap, BTreeSet};

use crate::analysis::jadx_local_names;
use crate::ir::{
    analysis::{
        StructuralVariableRoleAnalysis, VariableNode, VariableRole, VariableRoleAnalysis,
        VariableRoleScores, VariableSemanticGraph,
    },
    ArgType, InsnType, MemberReference, PrimitiveType, SemanticNode,
};
use crate::language::kotlin::{KotlinIdentifier, KotlinPrimitiveType, KotlinType};

use super::type_names::KotlinTypeNameResolver;

#[derive(Debug, Clone, PartialEq, Eq)]
struct NameCandidate {
    name: KotlinIdentifier,
    score: u16,
}

trait IdentifierMorphology {
    fn lower_camel(&self, name: &KotlinIdentifier) -> KotlinIdentifier;
    fn plural(&self, name: &KotlinIdentifier) -> KotlinIdentifier;
}

#[derive(Debug, Clone, Copy, Default)]
struct KotlinIdentifierMorphology;

impl IdentifierMorphology for KotlinIdentifierMorphology {
    fn lower_camel(&self, name: &KotlinIdentifier) -> KotlinIdentifier {
        let source = name.as_str();
        let words = source
            .split('_')
            .filter(|word| !word.is_empty())
            .collect::<Vec<_>>();
        if words.len() > 1 {
            let mut result = words[0].to_ascii_lowercase();
            for word in &words[1..] {
                let lowered = word.to_ascii_lowercase();
                let mut characters = lowered.chars();
                if let Some(first) = characters.next() {
                    result.extend(first.to_uppercase());
                    result.extend(characters);
                }
            }
            return KotlinIdentifier::from_hint(&result);
        }
        if source
            .chars()
            .filter(|character| character.is_alphabetic())
            .all(|character| character.is_uppercase())
        {
            return KotlinIdentifier::from_hint(&source.to_lowercase());
        }
        let mut characters = source.chars();
        let Some(first) = characters.next() else {
            return name.clone();
        };
        let mut lowered = first.to_lowercase().collect::<String>();
        lowered.extend(characters);
        KotlinIdentifier::from_hint(&lowered)
    }

    fn plural(&self, name: &KotlinIdentifier) -> KotlinIdentifier {
        let source = name.as_str();
        let plural = if source.ends_with('y')
            && source
                .chars()
                .rev()
                .nth(1)
                .is_some_and(|character| !"aeiou".contains(character))
        {
            format!("{}ies", &source[..source.len() - 1])
        } else if source.ends_with('s')
            || source.ends_with('x')
            || source.ends_with('z')
            || source.ends_with("ch")
            || source.ends_with("sh")
        {
            format!("{source}es")
        } else {
            format!("{source}s")
        };
        KotlinIdentifier::from_hint(&plural)
    }
}

trait MethodResultSemantics {
    fn candidate(&self, name: &str) -> Option<NameCandidate>;
}

#[derive(Debug, Clone, Copy, Default)]
struct KotlinMethodResultSemantics {
    morphology: KotlinIdentifierMorphology,
}

impl MethodResultSemantics for KotlinMethodResultSemantics {
    fn candidate(&self, name: &str) -> Option<NameCandidate> {
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
        let identifier = KotlinIdentifier::from_hint(name);
        if let Some(name) = jadx_local_names::invoke_local_name(name) {
            return Some(NameCandidate {
                name: KotlinIdentifier::from_hint(&name),
                score: 85,
            });
        }
        Some(NameCandidate {
            name: self.morphology.lower_camel(&identifier),
            score: 55,
        })
    }
}

trait VariableNameModel {
    fn candidates(
        &self,
        variable: &VariableNode,
        graph: &VariableSemanticGraph,
        roles: &VariableRoleScores,
    ) -> Vec<NameCandidate>;
}

struct StructuralNameModel<'a> {
    types: &'a KotlinTypeNameResolver,
    morphology: KotlinIdentifierMorphology,
    methods: KotlinMethodResultSemantics,
    constants: Option<crate::analysis::TypedConstantNameInference>,
    relations: Option<crate::analysis::RelationalNameInference>,
}

impl<'a> StructuralNameModel<'a> {
    fn new(types: &'a KotlinTypeNameResolver) -> Self {
        Self {
            types,
            morphology: KotlinIdentifierMorphology,
            methods: KotlinMethodResultSemantics::default(),
            constants: None,
            relations: None,
        }
    }

    fn for_graph(types: &'a KotlinTypeNameResolver, graph: &VariableSemanticGraph) -> Self {
        let mut model = Self::new(types);
        model.constants = crate::platform_symbols::default_platform_symbols()
            .ok()
            .map(|symbols| crate::analysis::TypedConstantNameInference::analyze(graph, &symbols));
        model.relations = Some(crate::analysis::RelationalNameInference::analyze(graph));
        model
    }

    fn role_name(role: VariableRole) -> &'static str {
        match role {
            VariableRole::Exception => "exception",
            VariableRole::Element => "element",
            VariableRole::Index => "index",
            VariableRole::Limit => "limit",
            VariableRole::Size => "size",
            VariableRole::Counter => "count",
            VariableRole::Remaining => "remaining",
            VariableRole::Step => "step",
            VariableRole::Value => "value",
            VariableRole::Accumulator => "total",
            VariableRole::Condition => "condition",
            VariableRole::Result => "result",
            VariableRole::Lock => "lock",
            VariableRole::Selector => "selector",
            VariableRole::Iterator => "iterator",
        }
    }

    fn type_name(&self, ty: &ArgType) -> Option<KotlinIdentifier> {
        let resolved = self.types.resolve_type(ty).ok()?;
        self.java_type_name(&resolved)
    }

    fn java_type_name(&self, ty: &KotlinType) -> Option<KotlinIdentifier> {
        Some(KotlinIdentifier::from_hint(&kotlin_jadx_type_name(ty)?))
    }

    fn lower_camel(name: &KotlinIdentifier) -> KotlinIdentifier {
        let source = name.as_str();
        if source
            .chars()
            .filter(|character| character.is_alphabetic())
            .all(|character| character.is_uppercase())
        {
            return KotlinIdentifier::from_hint(&source.to_lowercase());
        }
        let mut characters = source.chars();
        let Some(first) = characters.next() else {
            return name.clone();
        };
        let mut lowered = first.to_lowercase().collect::<String>();
        lowered.extend(characters);
        KotlinIdentifier::from_hint(&lowered)
    }

    fn field_candidates(
        &self,
        variable: &VariableNode,
        graph: &VariableSemanticGraph,
    ) -> Vec<NameCandidate> {
        graph
            .edges_for(variable.identity())
            .filter_map(|edge| {
                let score = match edge.kind() {
                    crate::ir::analysis::VariableEdgeKind::Definition => 110,
                    crate::ir::analysis::VariableEdgeKind::FieldValue => 85,
                    _ => return None,
                };
                let operation = edge.operation().and_then(|id| graph.operation(id))?;
                if !matches!(
                    (edge.kind(), operation.kind()),
                    (
                        crate::ir::analysis::VariableEdgeKind::Definition,
                        InsnType::Iget | InsnType::Sget
                    ) | (
                        crate::ir::analysis::VariableEdgeKind::FieldValue,
                        InsnType::Iput | InsnType::Sput
                    )
                ) {
                    return None;
                }
                let MemberReference::Field(field) = operation.reference()? else {
                    return None;
                };
                Some(NameCandidate {
                    name: self
                        .morphology
                        .lower_camel(&KotlinIdentifier::from_hint(&field.name)),
                    score,
                })
            })
            .collect()
    }

    fn loop_value_candidates(
        &self,
        variable: &VariableNode,
        graph: &VariableSemanticGraph,
    ) -> Vec<NameCandidate> {
        graph
            .edges_for(variable.identity())
            .filter_map(|edge| {
                if !matches!(
                    edge.kind(),
                    crate::ir::analysis::VariableEdgeKind::LoopValue
                ) {
                    return None;
                }
                let operation = edge.operation().and_then(|id| graph.operation(id))?;
                if operation.kind() != InsnType::Invoke {
                    return None;
                }
                let MemberReference::Method(method) = operation.reference()? else {
                    return None;
                };
                (!method.name.starts_with('<')).then(|| NameCandidate {
                    name: self
                        .morphology
                        .lower_camel(&KotlinIdentifier::from_hint(&method.name)),
                    score: 90,
                })
            })
            .collect()
    }

    fn method_result_candidates(
        &self,
        variable: &VariableNode,
        graph: &VariableSemanticGraph,
    ) -> Vec<NameCandidate> {
        graph
            .edges_for(variable.identity())
            .filter_map(|edge| {
                if !matches!(
                    edge.kind(),
                    crate::ir::analysis::VariableEdgeKind::Definition
                ) {
                    return None;
                }
                let operation = edge.operation().and_then(|id| graph.operation(id))?;
                if operation.kind() != InsnType::Invoke {
                    return None;
                }
                let MemberReference::Method(method) = operation.reference()? else {
                    return None;
                };
                self.methods.candidate(&method.name)
            })
            .collect()
    }

    fn constant_candidates(
        &self,
        variable: &VariableNode,
        _graph: &VariableSemanticGraph,
    ) -> Vec<NameCandidate> {
        self.constants
            .as_ref()
            .and_then(|constants| constants.name(variable.identity()))
            .map(|field| field.strip_prefix("FLAG_").unwrap_or(field))
            .map(|semantic| NameCandidate {
                name: self
                    .morphology
                    .lower_camel(&KotlinIdentifier::from_hint(semantic)),
                score: 125,
            })
            .into_iter()
            .collect()
    }

    fn relation_candidates(&self, variable: &VariableNode) -> Vec<NameCandidate> {
        self.relations
            .as_ref()
            .and_then(|relations| relations.name(variable.identity()))
            .map(|name| NameCandidate {
                name: KotlinIdentifier::from_hint(name),
                score: 115,
            })
            .into_iter()
            .collect()
    }

    fn merge(candidates: impl IntoIterator<Item = NameCandidate>) -> Vec<NameCandidate> {
        let mut scores = BTreeMap::<KotlinIdentifier, u16>::new();
        for candidate in candidates {
            scores
                .entry(candidate.name)
                .and_modify(|score| *score = (*score).max(candidate.score))
                .or_insert(candidate.score);
        }
        let mut candidates = scores
            .into_iter()
            .map(|(name, score)| NameCandidate { name, score })
            .collect::<Vec<_>>();
        candidates.sort_by(|left, right| {
            right
                .score
                .cmp(&left.score)
                .then_with(|| left.name.cmp(&right.name))
        });
        candidates
    }
}

impl VariableNameModel for StructuralNameModel<'_> {
    fn candidates(
        &self,
        variable: &VariableNode,
        graph: &VariableSemanticGraph,
        roles: &VariableRoleScores,
    ) -> Vec<NameCandidate> {
        let role_candidates = roles
            .roles(variable.identity())
            .map(|(role, score)| NameCandidate {
                name: KotlinIdentifier::from_hint(Self::role_name(role)),
                score,
            });
        let element_score = roles.score(variable.identity(), VariableRole::Element);
        let typed_role_candidate = (element_score != 0)
            .then(|| {
                self.type_name(variable.ty()).map(|name| NameCandidate {
                    name,
                    score: element_score.saturating_add(25),
                })
            })
            .flatten();
        let field_candidates = self.field_candidates(variable, graph);
        let loop_value_candidates = self.loop_value_candidates(variable, graph);
        let method_result_candidates = self.method_result_candidates(variable, graph);
        let constant_candidates = self.constant_candidates(variable, graph);
        let relation_candidates = self.relation_candidates(variable);
        let type_candidate = self
            .type_name(variable.ty())
            .map(|name| NameCandidate { name, score: 40 });
        Self::merge(
            role_candidates
                .chain(typed_role_candidate)
                .chain(field_candidates)
                .chain(loop_value_candidates)
                .chain(method_result_candidates)
                .chain(constant_candidates)
                .chain(relation_candidates)
                .chain(type_candidate),
        )
    }
}

pub(super) struct ParameterNameRecovery<'a> {
    model: StructuralNameModel<'a>,
}

impl<'a> ParameterNameRecovery<'a> {
    pub(super) fn new(types: &'a KotlinTypeNameResolver) -> Self {
        Self {
            model: StructuralNameModel::new(types),
        }
    }

    pub(super) fn candidate(&self, ty: &ArgType) -> Option<KotlinIdentifier> {
        self.model.type_name(ty)
    }
}

trait VariableNameSolver {
    fn solve(
        &self,
        graph: &VariableSemanticGraph,
        roles: &VariableRoleScores,
        reserved: &[KotlinIdentifier],
        excluded: &BTreeSet<u32>,
    ) -> BTreeMap<u32, KotlinIdentifier>;
}

struct ConstrainedNameSolver<Model> {
    model: Model,
    minimum_score: u16,
    conflict_penalty: u16,
}

impl<Model> ConstrainedNameSolver<Model> {
    fn new(model: Model, minimum_score: u16) -> Self {
        Self {
            model,
            minimum_score,
            conflict_penalty: 20,
        }
    }
}

impl<Model: VariableNameModel> VariableNameSolver for ConstrainedNameSolver<Model> {
    fn solve(
        &self,
        graph: &VariableSemanticGraph,
        roles: &VariableRoleScores,
        reserved: &[KotlinIdentifier],
        excluded: &BTreeSet<u32>,
    ) -> BTreeMap<u32, KotlinIdentifier> {
        let mut proposals = graph
            .variables()
            .filter(|variable| {
                variable.is_source_binding() && !excluded.contains(&variable.identity())
            })
            .filter_map(|variable| {
                let candidates = self.model.candidates(variable, graph, roles);
                let score = candidates.first()?.score;
                (score >= self.minimum_score).then_some((variable.identity(), score, candidates))
            })
            .collect::<Vec<_>>();
        proposals.sort_by(|left, right| right.1.cmp(&left.1).then_with(|| left.0.cmp(&right.0)));

        let mut used = BTreeSet::new();
        for name in reserved {
            used.insert(name.clone());
        }

        let mut solution = BTreeMap::new();
        for (variable, _, candidates) in proposals {
            let selected = candidates
                .iter()
                .filter(|candidate| candidate.score >= self.minimum_score)
                .map(|candidate| {
                    let conflicts = used.contains(&candidate.name);
                    let utility = candidate
                        .score
                        .saturating_sub(u16::from(conflicts) * self.conflict_penalty);
                    (candidate, utility, conflicts)
                })
                .max_by(|left, right| {
                    left.1
                        .cmp(&right.1)
                        .then_with(|| right.0.name.cmp(&left.0.name))
                })
                .map(|(candidate, _, conflicts)| {
                    if conflicts {
                        return Self::claim_variant(&candidate.name, &mut used);
                    }
                    used.insert(candidate.name.clone());
                    candidate.name.clone()
                })
                .unwrap_or_else(|| Self::claim_variant(&candidates[0].name, &mut used));
            solution.insert(variable, selected);
        }
        solution
    }
}

impl<Model> ConstrainedNameSolver<Model> {
    fn claim_variant(
        preferred: &KotlinIdentifier,
        used: &mut BTreeSet<KotlinIdentifier>,
    ) -> KotlinIdentifier {
        for suffix in 2u32.. {
            let candidate = KotlinIdentifier::from_hint(&format!("{}{suffix}", preferred.as_str()));
            if used.insert(candidate.clone()) {
                return candidate;
            }
        }
        unreachable!()
    }
}

pub(super) struct SemanticNameRecovery<'a> {
    types: &'a KotlinTypeNameResolver,
}

impl<'a> SemanticNameRecovery<'a> {
    pub(super) fn new(types: &'a KotlinTypeNameResolver) -> Self {
        Self { types }
    }

    pub(super) fn recover(
        &self,
        root: &SemanticNode,
        source_types: &crate::ir::analysis::SourceTypeEnvironment,
        parameter_names: &[KotlinIdentifier],
        parameter_variables: &[Option<u32>],
        this_variable: Option<u32>,
    ) -> BTreeMap<u32, KotlinIdentifier> {
        let graph = VariableSemanticGraph::analyze(root, source_types);
        let roles = StructuralVariableRoleAnalysis.analyze(&graph);
        let intrinsic_names = jadx_local_names::intrinsic_local_names(root);
        let excluded = parameter_variables
            .iter()
            .copied()
            .flatten()
            .chain(this_variable)
            .chain(intrinsic_names.keys().copied())
            .collect::<BTreeSet<_>>();
        let model = StructuralNameModel::for_graph(self.types, &graph);
        let mut names =
            ConstrainedNameSolver::new(StructuralNameModel::for_graph(self.types, &graph), 35)
                .solve(&graph, &roles, parameter_names, &excluded);
        for (identity, name) in intrinsic_names {
            names
                .entry(identity)
                .or_insert_with(|| KotlinIdentifier::from_hint(&name));
        }
        fill_remaining_source_names(
            &graph,
            &roles,
            &model,
            parameter_names,
            &excluded,
            &mut names,
        );
        names
    }
}

fn kotlin_jadx_type_name(ty: &KotlinType) -> Option<String> {
    match ty {
        KotlinType::Primitive(primitive) => {
            jadx_local_names::primitive_local_name(kotlin_primitive(*primitive)).map(str::to_string)
        }
        KotlinType::Class(class) => Some(jadx_local_names::class_local_name_from_segments(
            class.segments.iter().map(|segment| segment.name.as_str()),
        )),
        KotlinType::Variable(name) => Some(jadx_local_names::class_local_name(name.as_str())),
        KotlinType::Array(element) => Some(jadx_local_names::array_local_name(
            &kotlin_jadx_type_name(element.as_type())?,
        )),
    }
}

fn kotlin_primitive(primitive: KotlinPrimitiveType) -> PrimitiveType {
    match primitive {
        KotlinPrimitiveType::Void => PrimitiveType::Void,
        KotlinPrimitiveType::Boolean => PrimitiveType::Boolean,
        KotlinPrimitiveType::Byte => PrimitiveType::Byte,
        KotlinPrimitiveType::Short => PrimitiveType::Short,
        KotlinPrimitiveType::Char => PrimitiveType::Char,
        KotlinPrimitiveType::Int => PrimitiveType::Int,
        KotlinPrimitiveType::Long => PrimitiveType::Long,
        KotlinPrimitiveType::Float => PrimitiveType::Float,
        KotlinPrimitiveType::Double => PrimitiveType::Double,
    }
}

fn fill_remaining_source_names(
    graph: &VariableSemanticGraph,
    roles: &VariableRoleScores,
    model: &StructuralNameModel<'_>,
    reserved: &[KotlinIdentifier],
    excluded: &BTreeSet<u32>,
    names: &mut BTreeMap<u32, KotlinIdentifier>,
) {
    let mut used = names.values().cloned().collect::<BTreeSet<_>>();
    for name in reserved {
        used.insert(name.clone());
    }
    for variable in graph.variables() {
        if !variable.is_source_binding() || excluded.contains(&variable.identity()) {
            continue;
        }
        if names.contains_key(&variable.identity()) {
            continue;
        }
        let preferred = model
            .type_name(variable.ty())
            .or_else(|| {
                roles
                    .roles(variable.identity())
                    .max_by_key(|(_, score)| *score)
                    .filter(|(_, score)| *score > 0)
                    .map(|(role, _)| {
                        KotlinIdentifier::from_hint(StructuralNameModel::role_name(role))
                    })
            })
            .unwrap_or_else(|| KotlinIdentifier::from_hint("value"));
        let name = if used.insert(preferred.clone()) {
            preferred
        } else {
            ConstrainedNameSolver::<StructuralNameModel>::claim_variant(&preferred, &mut used)
        };
        names.insert(variable.identity(), name);
    }
}
