use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use crate::ir::analysis::SsaVar;
use crate::ir::generic_types::{
    ClassTypeSignature, GenericFieldContract, GenericMethodContract, JvmTypeSignature,
    TypeArgument, TypeParameter,
};
use crate::ir::{
    ArgType, FieldReference, InsnType, MemberReference, MethodReference, PrimitiveType,
    RegisterArg, SemanticExpression, SemanticLeaveKind, SemanticNode, SemanticOperation,
    SemanticStatement, SemanticStatementKind, SemanticVisitor,
};

use super::{
    KotlinClassType, KotlinIdentifier, KotlinPrimitiveType, KotlinType, KotlinTypeArgument,
};

pub(super) fn invocation_expression_signature<'a>(
    operation: &SemanticOperation,
    contract: &'a GenericMethodContract,
) -> Cow<'a, JvmTypeSignature> {
    if operation.insn_type == InsnType::Constructor {
        if let Some(allocation) = operation.allocation_type() {
            let contract_owner = contract.owner.erased_name();
            if allocation.as_object() != Some(contract_owner.as_str()) {
                if let Some(signature) = JvmTypeSignature::from_erased(allocation) {
                    return Cow::Owned(signature);
                }
            }
        }
        Cow::Owned(JvmTypeSignature::ClassType(contract.owner.clone()))
    } else {
        Cow::Borrowed(&contract.signature.return_type)
    }
}

fn owner_type_parameter_name(argument: &TypeArgument) -> Option<&str> {
    match argument {
        TypeArgument::Exact(JvmTypeSignature::TypeVariable(name)) => Some(name),
        TypeArgument::Unbounded
        | TypeArgument::Extends(_)
        | TypeArgument::Super(_)
        | TypeArgument::Exact(_) => None,
    }
}

pub(crate) trait GenericTypeProjection: std::fmt::Debug + Send + Sync {
    fn specialize_subtype(
        &self,
        subtype: &ArgType,
        expected_supertype: &KotlinType,
    ) -> Option<KotlinType>;

    fn infer_subtype(
        &self,
        subtype: &ArgType,
        expected_supertype: &KotlinType,
    ) -> Option<KotlinType> {
        self.specialize_subtype(subtype, expected_supertype)
    }

    fn project_supertype(
        &self,
        subtype: &KotlinType,
        expected_supertype: &ArgType,
    ) -> Option<KotlinType>;

    fn is_subtype(&self, _subtype: &ArgType, _supertype: &ArgType) -> bool {
        false
    }

    fn uses_mapped_collection_size(&self, _owner: &ArgType) -> bool {
        false
    }

    fn least_common_supertype(&self, _left: &ArgType, _right: &ArgType) -> Option<ArgType> {
        None
    }

    fn is_cast_convertible(&self, _source: &ArgType, _target: &ArgType) -> bool {
        true
    }

    fn resolve_type(&self, _ty: &ArgType) -> Option<KotlinType> {
        None
    }

    fn erasure_of(&self, _ty: &KotlinType) -> Option<ArgType> {
        None
    }

    fn declared_type_parameters(&self, _ty: &ArgType) -> Option<Vec<TypeParameter>> {
        None
    }
}

#[derive(Debug, Clone, Default)]
struct KotlinTypeErasureIndex {
    classes: HashMap<u64, Vec<(Vec<KotlinIdentifier>, ArgType)>>,
    primitives: HashMap<KotlinPrimitiveType, ArgType>,
}

impl KotlinTypeErasureIndex {
    fn from_source_types(source_types: &BTreeMap<ArgType, KotlinType>) -> Self {
        let mut index = Self::default();
        for (erased, source) in source_types {
            match source {
                KotlinType::Class(class) => {
                    let entries = index
                        .classes
                        .entry(Self::class_fingerprint(class))
                        .or_default();
                    if !entries
                        .iter()
                        .any(|(name, _)| Self::class_name_matches(class, name))
                    {
                        entries.push((
                            class
                                .segments
                                .iter()
                                .map(|segment| segment.name.clone())
                                .collect(),
                            erased.clone(),
                        ));
                    }
                }
                KotlinType::Primitive(primitive) => {
                    index
                        .primitives
                        .entry(*primitive)
                        .or_insert_with(|| erased.clone());
                }
                KotlinType::Variable(_) | KotlinType::Array(_) => {}
            }
        }
        index
    }

    fn erasure_of(
        &self,
        ty: &KotlinType,
        variable_erasures: &BTreeMap<KotlinIdentifier, ArgType>,
    ) -> Option<ArgType> {
        match ty {
            KotlinType::Array(element) => {
                Some(ArgType::array(self.erasure_of(element, variable_erasures)?))
            }
            KotlinType::Variable(variable) => variable_erasures
                .get(variable)
                .cloned()
                .or_else(|| Some(ArgType::object("java/lang/Object"))),
            KotlinType::Class(class) => self.erasure_of_class(class),
            KotlinType::Primitive(primitive) => self.primitives.get(primitive).cloned(),
        }
    }

    fn erasure_of_class(&self, class: &KotlinClassType) -> Option<ArgType> {
        self.classes
            .get(&Self::class_fingerprint(class))?
            .iter()
            .find_map(|(name, erased)| {
                Self::class_name_matches(class, name).then(|| erased.clone())
            })
    }

    fn class_fingerprint(class: &KotlinClassType) -> u64 {
        const OFFSET: u64 = 0xcbf29ce484222325;
        const PRIME: u64 = 0x100000001b3;

        let mut fingerprint = OFFSET;
        for segment in &class.segments {
            for byte in segment.name.as_str().bytes() {
                fingerprint ^= u64::from(byte);
                fingerprint = fingerprint.wrapping_mul(PRIME);
            }
            fingerprint ^= 0xff;
            fingerprint = fingerprint.wrapping_mul(PRIME);
        }
        fingerprint
    }

    fn class_name_matches(class: &KotlinClassType, name: &[KotlinIdentifier]) -> bool {
        class.segments.len() == name.len()
            && class
                .segments
                .iter()
                .zip(name)
                .all(|(segment, name)| &segment.name == name)
    }
}

pub(super) struct KotlinTypeRelations<'a> {
    source_types: &'a BTreeMap<ArgType, KotlinType>,
    source_erasures: Option<&'a KotlinTypeErasureIndex>,
    variable_erasures: &'a BTreeMap<KotlinIdentifier, ArgType>,
    variable_bounds: Option<&'a BTreeMap<KotlinIdentifier, KotlinType>>,
    hierarchy: Option<&'a dyn GenericTypeProjection>,
}

#[cfg_attr(feature = "profiling", hotpath::measure_all)]
impl<'a> KotlinTypeRelations<'a> {
    pub(super) fn new(
        source_types: &'a BTreeMap<ArgType, KotlinType>,
        variable_erasures: &'a BTreeMap<KotlinIdentifier, ArgType>,
        hierarchy: Option<&'a dyn GenericTypeProjection>,
    ) -> Self {
        Self {
            source_types,
            source_erasures: None,
            variable_erasures,
            variable_bounds: None,
            hierarchy,
        }
    }

    fn with_erasure_index(mut self, index: Option<&'a KotlinTypeErasureIndex>) -> Self {
        self.source_erasures = index;
        self
    }

    pub(super) fn with_variable_bounds(
        mut self,
        bounds: Option<&'a BTreeMap<KotlinIdentifier, KotlinType>>,
    ) -> Self {
        self.variable_bounds = bounds;
        self
    }

    pub(super) fn erasure_of(&self, ty: &KotlinType) -> Option<ArgType> {
        if let Some(erased) = self
            .source_erasures
            .and_then(|index| index.erasure_of(ty, self.variable_erasures))
        {
            return Some(erased);
        }
        match ty {
            KotlinType::Array(element) => Some(ArgType::array(self.erasure_of(element)?)),
            KotlinType::Class(class) => self
                .source_types
                .iter()
                .find_map(|(erased, source)| {
                    matches!(source, KotlinType::Class(source) if Self::same_class_name(source, class))
                        .then(|| erased.clone())
                })
                .or_else(|| {
                    self.hierarchy
                        .and_then(|hierarchy| hierarchy.erasure_of(ty))
                }),
            KotlinType::Variable(variable) => self
                .variable_erasures
                .get(variable)
                .cloned()
                .or_else(|| Some(ArgType::object("java/lang/Object"))),
            KotlinType::Primitive(_) => self
                .source_types
                .iter()
                .find_map(|(erased, source)| (source == ty).then(|| erased.clone())),
        }
    }

    fn erasure_of_class(&self, class: &KotlinClassType) -> Option<ArgType> {
        if let Some(erased) = self
            .source_erasures
            .and_then(|index| index.erasure_of_class(class))
        {
            return Some(erased);
        }
        self.source_types
            .iter()
            .find_map(|(erased, source)| {
                matches!(source, KotlinType::Class(source) if Self::same_class_name(source, class))
                    .then(|| erased.clone())
            })
            .or_else(|| {
                self.hierarchy
                    .and_then(|hierarchy| hierarchy.erasure_of(&KotlinType::Class(class.clone())))
            })
    }

    pub(super) fn is_assignable(&self, source: &KotlinType, target: &KotlinType) -> bool {
        if source == target {
            return true;
        }
        match (source, target) {
            (KotlinType::Array(source), KotlinType::Array(target)) => {
                !matches!(source.as_type(), KotlinType::Primitive(_))
                    && !matches!(target.as_type(), KotlinType::Primitive(_))
                    && self.is_assignable(source, target)
            }
            (KotlinType::Array(_), KotlinType::Class(_)) => self
                .erasure_of(target)
                .is_some_and(|target| Self::is_array_supertype(&target)),
            (KotlinType::Class(source), KotlinType::Class(target)) => {
                self.class_is_assignable(source, target)
            }
            (KotlinType::Variable(variable), _) => self.variable_is_assignable(variable, target),
            _ => false,
        }
    }

    pub(super) fn least_upper_bound(
        &self,
        left: &KotlinType,
        right: &KotlinType,
    ) -> Option<KotlinType> {
        GenericRequirementLattice::new(self.source_types, self.variable_erasures, self.hierarchy)
            .join(left, right)
    }

    fn variable_is_assignable(&self, variable: &KotlinIdentifier, target: &KotlinType) -> bool {
        let Some(bound) = self.variable_erasures.get(variable) else {
            return false;
        };
        if self.erasure_of(target).as_ref() == Some(bound) && Self::is_raw(target) {
            return true;
        }
        if self
            .variable_bounds
            .and_then(|bounds| bounds.get(variable))
            .is_some_and(|bound| self.is_assignable(bound, target))
        {
            return true;
        }
        self.source_types
            .get(bound)
            .is_some_and(|source| self.is_assignable(source, target))
    }

    fn class_is_assignable(
        &self,
        source: &super::KotlinClassType,
        target: &super::KotlinClassType,
    ) -> bool {
        let (source_erasure, target_erasure) =
            crate::profile_scope!("type_relations.class.erasures", {
                (self.erasure_of_class(source), self.erasure_of_class(target))
            });
        let erased_subtype = crate::profile_scope!("type_relations.class.subtype", {
            source_erasure
                .as_ref()
                .zip(target_erasure.as_ref())
                .is_some_and(|(source, target)| {
                    self.hierarchy
                        .is_some_and(|hierarchy| hierarchy.is_subtype(source, target))
                })
        });
        if erased_subtype && Self::class_is_raw(target) {
            return true;
        }
        let projected;
        let source = if Self::same_class_name(source, target) {
            source
        } else {
            let Some(target_erasure) = target_erasure.as_ref() else {
                return false;
            };
            let Some(value) = crate::profile_scope!("type_relations.class.project", {
                self.hierarchy.and_then(|hierarchy| {
                    hierarchy.project_supertype(&KotlinType::Class(source.clone()), target_erasure)
                })
            }) else {
                return false;
            };
            projected = value;
            let KotlinType::Class(projected) = &projected else {
                return false;
            };
            projected
        };
        source.segments.len() == target.segments.len()
            && source
                .segments
                .iter()
                .zip(&target.segments)
                .all(|(source, target)| {
                    source.name == target.name
                        && self.arguments_are_assignable(&source.arguments, &target.arguments)
                })
    }

    fn arguments_are_assignable(
        &self,
        source: &[KotlinTypeArgument],
        target: &[KotlinTypeArgument],
    ) -> bool {
        if target.is_empty() {
            return true;
        }
        source.len() == target.len()
            && source
                .iter()
                .zip(target)
                .all(|(source, target)| self.argument_is_contained_by(source, target))
    }

    fn argument_is_contained_by(
        &self,
        source: &KotlinTypeArgument,
        target: &KotlinTypeArgument,
    ) -> bool {
        use KotlinTypeArgument::{Any, Exact, Extends, Super};

        match (source, target) {
            (_, Any) => true,
            (Exact(source), Exact(target)) => source == target,
            (Exact(source) | Extends(source), Extends(target)) => {
                self.is_assignable(source, target)
            }
            (Any, Extends(target)) => {
                self.source_types.get(&ArgType::object("java/lang/Object")) == Some(target)
            }
            (Exact(source) | Super(source), Super(target)) => self.is_assignable(target, source),
            _ => false,
        }
    }

    fn same_erasure(left: &KotlinType, right: &KotlinType) -> bool {
        match (left, right) {
            (KotlinType::Class(left), KotlinType::Class(right)) => {
                Self::same_class_name(left, right)
            }
            (KotlinType::Array(left), KotlinType::Array(right)) => Self::same_erasure(left, right),
            (KotlinType::Primitive(left), KotlinType::Primitive(right)) => left == right,
            _ => left == right,
        }
    }

    fn same_class_name(left: &KotlinClassType, right: &KotlinClassType) -> bool {
        left.segments.len() == right.segments.len()
            && left
                .segments
                .iter()
                .zip(&right.segments)
                .all(|(left, right)| left.name == right.name)
    }

    fn class_is_raw(class: &KotlinClassType) -> bool {
        class
            .segments
            .iter()
            .all(|segment| segment.arguments.is_empty())
    }

    fn is_raw(ty: &KotlinType) -> bool {
        matches!(ty, KotlinType::Class(class) if Self::class_is_raw(class))
    }

    fn is_array_supertype(ty: &ArgType) -> bool {
        [
            "java/lang/Object",
            "java/lang/Cloneable",
            "java/io/Serializable",
        ]
        .into_iter()
        .any(|name| ty == &ArgType::object(name))
    }
}

#[derive(Clone)]
pub(super) struct GenericTypeSolver<'a> {
    source_types: &'a BTreeMap<ArgType, KotlinType>,
    source_erasures: Option<Arc<KotlinTypeErasureIndex>>,
    generic_projection: Option<&'a dyn GenericTypeProjection>,
    visible_variables: Option<&'a BTreeMap<KotlinIdentifier, ArgType>>,
    visible_bounds: Option<&'a BTreeMap<KotlinIdentifier, KotlinType>>,
    inference_variables: BTreeSet<String>,
    values: BTreeMap<String, GenericTypeBinding>,
    raw_owner: BTreeSet<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum GenericTypeBinding {
    Bound {
        value: GenericTypeValue,
        origin: GenericConstraintOrigin,
    },
    Conflict {
        origin: GenericConstraintOrigin,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct GenericTypeValue {
    argument: KotlinTypeArgument,
    captured: bool,
}

impl GenericTypeValue {
    fn declared(argument: KotlinTypeArgument) -> Self {
        Self {
            captured: !matches!(&argument, KotlinTypeArgument::Exact(_)),
            argument,
        }
    }

    fn inferred(argument: KotlinTypeArgument, captured: bool) -> Self {
        Self { argument, captured }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum GenericConstraintOrigin {
    Bound,
    Context,
    Argument,
    Owner,
}

#[cfg_attr(feature = "profiling", hotpath::measure_all)]
impl<'a> GenericTypeSolver<'a> {
    pub(super) fn new(source_types: &'a BTreeMap<ArgType, KotlinType>) -> Self {
        Self {
            source_types,
            source_erasures: None,
            generic_projection: None,
            visible_variables: None,
            visible_bounds: None,
            inference_variables: BTreeSet::new(),
            values: BTreeMap::new(),
            raw_owner: BTreeSet::new(),
        }
    }

    fn with_erasure_index(mut self, index: Option<Arc<KotlinTypeErasureIndex>>) -> Self {
        self.source_erasures = index;
        self
    }

    pub(super) fn with_projection(
        mut self,
        projection: Option<&'a dyn GenericTypeProjection>,
    ) -> Self {
        self.generic_projection = projection;
        self
    }

    pub(super) fn with_visible_variables(
        mut self,
        variables: &'a BTreeMap<KotlinIdentifier, ArgType>,
    ) -> Self {
        self.visible_variables = Some(variables);
        self
    }

    pub(super) fn with_visible_bounds(
        mut self,
        bounds: &'a BTreeMap<KotlinIdentifier, KotlinType>,
    ) -> Self {
        self.visible_bounds = Some(bounds);
        self
    }

    pub(super) fn with_inference_variables(mut self, parameters: &[TypeParameter]) -> Self {
        self.inference_variables
            .extend(parameters.iter().map(|parameter| parameter.name.clone()));
        self
    }

    pub(super) fn with_local_owner_variables(mut self, owner: &ClassTypeSignature) -> Self {
        self.inference_variables
            .extend(Self::local_owner_parameters(owner).map(ToOwned::to_owned));
        self
    }

    pub(super) fn with_lexical_scope(
        mut self,
        current: Option<&ArgType>,
        owner: &ClassTypeSignature,
        variables: &'a BTreeMap<KotlinIdentifier, ArgType>,
        bounds: &'a BTreeMap<KotlinIdentifier, KotlinType>,
    ) -> Self {
        self.visible_bounds = Some(bounds);
        let Some(ArgType::Object(current)) = current else {
            return self;
        };
        if current.split('$').next() == owner.raw_name.split('$').next() {
            self.visible_variables = Some(variables);
        }
        self
    }

    pub(super) fn get(&self, name: &str) -> Option<KotlinType> {
        match self.value(name) {
            Some(KotlinTypeArgument::Exact(value) | KotlinTypeArgument::Extends(value)) => {
                Some(value.clone())
            }
            Some(KotlinTypeArgument::Super(_) | KotlinTypeArgument::Any) => self
                .source_types
                .get(&ArgType::object("java/lang/Object"))
                .cloned(),
            None => self.visible_variable(name),
        }
    }

    pub(super) fn evidenced_type_argument(&self, name: &str) -> Option<KotlinType> {
        let value = match self.values.get(name) {
            Some(GenericTypeBinding::Bound {
                origin:
                    GenericConstraintOrigin::Context
                    | GenericConstraintOrigin::Argument
                    | GenericConstraintOrigin::Owner,
                ..
            }) => self.get(name),
            Some(GenericTypeBinding::Bound {
                origin: GenericConstraintOrigin::Bound,
                ..
            })
            | Some(GenericTypeBinding::Conflict { .. })
            | None => None,
        }?;
        (!self.is_default_reference_type(&value)).then_some(value)
    }

    pub(super) fn bounded_type_argument(&self, parameter: &TypeParameter) -> Option<KotlinType> {
        let value = self.evidenced_type_argument(&parameter.name)?;
        self.satisfies_parameter_bounds(parameter, &value)
            .then_some(value)
    }

    pub(super) fn type_argument_is_captured(&self, parameter: &TypeParameter) -> bool {
        matches!(
            self.values.get(&parameter.name),
            Some(GenericTypeBinding::Bound { value, .. }) if value.captured
        )
    }

    pub(super) fn specialize_explicit_arguments(
        &self,
        parameters: &[TypeParameter],
    ) -> Option<(Self, Vec<KotlinType>)> {
        let mut specialized = self.clone();
        let mut arguments = Vec::with_capacity(parameters.len());
        for parameter in parameters {
            let argument = self.bounded_type_argument(parameter)?;
            let origin = match self.values.get(&parameter.name)? {
                GenericTypeBinding::Bound { origin, .. } => *origin,
                GenericTypeBinding::Conflict { .. } => return None,
            };
            specialized.values.insert(
                parameter.name.clone(),
                GenericTypeBinding::Bound {
                    value: GenericTypeValue::inferred(
                        KotlinTypeArgument::Exact(argument.clone()),
                        false,
                    ),
                    origin,
                },
            );
            arguments.push(argument);
        }
        Some((specialized, arguments))
    }

    pub(super) fn satisfies_declared_bounds(&self, parameters: &[TypeParameter]) -> bool {
        parameters.iter().all(|parameter| {
            self.get(&parameter.name)
                .is_none_or(|value| self.satisfies_parameter_bounds(parameter, &value))
        })
    }

    fn satisfies_parameter_bounds(&self, parameter: &TypeParameter, value: &KotlinType) -> bool {
        let empty_variables = BTreeMap::new();
        let relations = KotlinTypeRelations::new(
            self.source_types,
            self.visible_variables.unwrap_or(&empty_variables),
            self.generic_projection,
        )
        .with_erasure_index(self.source_erasures.as_deref())
        .with_variable_bounds(self.visible_bounds);
        parameter
            .class_bound
            .iter()
            .chain(&parameter.interface_bounds)
            .all(|bound| {
                self.instantiate(bound).is_some_and(|bound| {
                    self.value_satisfies_bound(value, &bound, &relations, &mut BTreeSet::new())
                })
            })
    }

    fn value_satisfies_bound(
        &self,
        value: &KotlinType,
        bound: &KotlinType,
        relations: &KotlinTypeRelations<'_>,
        visiting: &mut BTreeSet<KotlinIdentifier>,
    ) -> bool {
        let KotlinType::Variable(variable) = value else {
            return relations.is_assignable(value, bound);
        };
        if !visiting.insert(variable.clone()) {
            return false;
        }
        let result = self
            .visible_bounds
            .and_then(|bounds| bounds.get(variable))
            .is_some_and(|visible| {
                visible == bound || self.value_satisfies_bound(visible, bound, relations, visiting)
            });
        visiting.remove(variable);
        result
    }

    pub(super) fn valid_source_type(&self, ty: &KotlinType) -> bool {
        match ty {
            KotlinType::Primitive(_) | KotlinType::Variable(_) => true,
            KotlinType::Array(element) => self.valid_source_type(element),
            KotlinType::Class(class) => {
                if !class.segments.iter().all(|segment| {
                    segment.arguments.iter().all(|argument| match argument {
                        KotlinTypeArgument::Any => true,
                        KotlinTypeArgument::Exact(value)
                        | KotlinTypeArgument::Extends(value)
                        | KotlinTypeArgument::Super(value) => self.valid_source_type(value),
                    })
                }) {
                    return false;
                }
                let Some(erased) = self.source_erasure(ty) else {
                    return true;
                };
                let Some(parameters) = self
                    .generic_projection
                    .and_then(|projection| projection.declared_type_parameters(&erased))
                else {
                    return true;
                };
                if parameters.is_empty() {
                    return true;
                }
                let Some(arguments) = class.segments.last().map(|segment| &segment.arguments)
                else {
                    return false;
                };
                if arguments.is_empty() {
                    return true;
                }
                if arguments.len() != parameters.len() {
                    return false;
                }
                let Some(raw_name) = erased.as_object() else {
                    return false;
                };
                let owner = ClassTypeSignature {
                    raw_name: raw_name.to_string(),
                    type_arguments: parameters
                        .iter()
                        .map(|parameter| {
                            TypeArgument::Exact(JvmTypeSignature::TypeVariable(
                                parameter.name.clone(),
                            ))
                        })
                        .collect(),
                    inner_segments: Vec::new(),
                };
                let mut checker = GenericTypeSolver::new(self.source_types)
                    .with_erasure_index(self.source_erasures.clone())
                    .with_projection(self.generic_projection)
                    .with_inference_variables(&parameters);
                checker.visible_variables = self.visible_variables;
                checker.visible_bounds = self.visible_bounds;
                checker.constrain_owner(&owner, ty);
                checker.satisfies_declared_bounds(&parameters)
            }
        }
    }

    fn source_erasure(&self, ty: &KotlinType) -> Option<ArgType> {
        if let Some(index) = self.source_erasures.as_deref() {
            let empty = BTreeMap::new();
            if let Some(erased) = index.erasure_of(ty, self.visible_variables.unwrap_or(&empty)) {
                return Some(erased);
            }
        }
        match ty {
            KotlinType::Array(element) => Some(ArgType::array(self.source_erasure(element)?)),
            KotlinType::Class(class) => self.source_types.iter().find_map(|(erased, source)| {
                matches!(source, KotlinType::Class(source) if source.name() == class.name())
                    .then(|| erased.clone())
            }),
            KotlinType::Variable(variable) => self
                .visible_variables
                .and_then(|variables| variables.get(variable))
                .cloned()
                .or_else(|| Some(ArgType::object("java/lang/Object"))),
            KotlinType::Primitive(_) => self
                .source_types
                .iter()
                .find_map(|(erased, source)| (source == ty).then(|| erased.clone())),
        }
    }

    fn is_default_reference_type(&self, value: &KotlinType) -> bool {
        let Some(KotlinType::Class(object)) =
            self.source_types.get(&ArgType::object("java/lang/Object"))
        else {
            return false;
        };
        let KotlinType::Class(value) = value else {
            return false;
        };
        value.name() == object.name()
            || (value.segments.len() == 1
                && value.segments[0].arguments.is_empty()
                && value.segments[0].name
                    == object.segments.last().expect("Object type segment").name)
    }

    fn visible_variable(&self, name: &str) -> Option<KotlinType> {
        if self.inference_variables.contains(name) {
            return None;
        }
        let name = KotlinIdentifier::from_dex(name);
        self.visible_variables?
            .contains_key(&name)
            .then_some(KotlinType::Variable(name))
    }

    fn input_variable(&self, name: &str) -> Option<KotlinTypeArgument> {
        match self.values.get(name) {
            Some(GenericTypeBinding::Bound {
                value,
                origin:
                    GenericConstraintOrigin::Context
                    | GenericConstraintOrigin::Argument
                    | GenericConstraintOrigin::Owner,
            }) => Some(value.argument.clone()),
            Some(GenericTypeBinding::Bound {
                origin: GenericConstraintOrigin::Bound,
                ..
            })
            | Some(GenericTypeBinding::Conflict { .. })
            | None => self.visible_variable(name).map(KotlinTypeArgument::Exact),
        }
    }

    pub(super) fn constrain_owner(&mut self, owner: &ClassTypeSignature, actual: &KotlinType) {
        let actual = match actual {
            KotlinType::Class(actual) => KotlinType::Class(actual.clone()),
            KotlinType::Variable(variable) => {
                let Some(bound @ KotlinType::Class(_)) = self
                    .visible_bounds
                    .and_then(|bounds| bounds.get(variable))
                    .filter(|bound| *bound != actual)
                else {
                    return;
                };
                bound.clone()
            }
            KotlinType::Array(_) | KotlinType::Primitive(_) => return,
        };
        let owner_erasure = JvmTypeSignature::ClassType(owner.clone()).erased();
        let actual = if self.source_erasure(&actual).as_ref() == Some(&owner_erasure) {
            actual
        } else {
            let Some(projected) = self
                .generic_projection
                .and_then(|projection| projection.project_supertype(&actual, &owner_erasure))
            else {
                return;
            };
            projected
        };
        let KotlinType::Class(actual) = actual else {
            return;
        };
        let formal_groups = std::iter::once(owner.type_arguments.as_slice())
            .chain(
                owner
                    .inner_segments
                    .iter()
                    .map(|segment| segment.type_arguments.as_slice()),
            )
            .collect::<Vec<_>>();
        let formal_offset = formal_groups.len().saturating_sub(actual.segments.len());
        let actual_offset = actual.segments.len().saturating_sub(formal_groups.len());
        for (formal, actual) in formal_groups
            .iter()
            .skip(formal_offset)
            .zip(actual.segments.iter().skip(actual_offset))
        {
            if !formal.is_empty() && actual.arguments.is_empty() {
                self.raw_owner.extend(
                    formal
                        .iter()
                        .filter_map(|argument| owner_type_parameter_name(argument))
                        .map(ToOwned::to_owned),
                );
            }
        }
        self.constrain_with_origin(
            &JvmTypeSignature::ClassType(owner.clone()),
            &KotlinType::Class(actual),
            GenericConstraintOrigin::Owner,
        );
    }

    pub(super) fn constrain_current_owner(&mut self, owner: &ClassTypeSignature) {
        for parameter in Self::owner_parameters(owner) {
            self.bind(
                parameter,
                GenericTypeValue::inferred(
                    KotlinTypeArgument::Exact(KotlinType::Variable(KotlinIdentifier::from_dex(
                        parameter,
                    ))),
                    false,
                ),
                GenericConstraintOrigin::Owner,
            );
        }
    }

    pub(super) fn constrain(&mut self, formal: &JvmTypeSignature, actual: &KotlinType) {
        self.constrain_with_origin(formal, actual, GenericConstraintOrigin::Argument);
    }

    pub(super) fn constrain_context(&mut self, formal: &JvmTypeSignature, actual: &KotlinType) {
        self.constrain_with_origin(formal, actual, GenericConstraintOrigin::Context);
    }

    pub(super) fn complete_with_bounds(&mut self, parameters: &[TypeParameter]) {
        loop {
            let before = self.values.clone();
            for parameter in parameters {
                let Some((value, origin)) = self.bound_value(&parameter.name) else {
                    continue;
                };
                for bound in parameter
                    .class_bound
                    .iter()
                    .chain(&parameter.interface_bounds)
                {
                    self.constrain_with_origin(bound, &value, origin);
                }
            }
            if self.values == before {
                break;
            }
        }
        for parameter in parameters {
            let captured_origin = match self.values.get(&parameter.name) {
                None => None,
                Some(GenericTypeBinding::Bound {
                    value:
                        GenericTypeValue {
                            argument: KotlinTypeArgument::Any,
                            ..
                        },
                    origin,
                }) => Some(*origin),
                Some(GenericTypeBinding::Bound { .. } | GenericTypeBinding::Conflict { .. }) => {
                    continue;
                }
            };
            let value = self
                .parameter_completion_type(parameter)
                .or_else(|| self.resolve_source_type(&ArgType::object("java/lang/Object")));
            if let Some(value) = value {
                let value = GenericTypeValue::inferred(KotlinTypeArgument::Exact(value), false);
                if let Some(origin) = captured_origin {
                    self.values.insert(
                        parameter.name.clone(),
                        GenericTypeBinding::Bound { value, origin },
                    );
                } else {
                    self.bind(&parameter.name, value, GenericConstraintOrigin::Bound);
                }
            }
        }
    }

    fn bound_value(&self, name: &str) -> Option<(KotlinType, GenericConstraintOrigin)> {
        let GenericTypeBinding::Bound { value, origin } = self.values.get(name)? else {
            return None;
        };
        let value = match &value.argument {
            KotlinTypeArgument::Exact(value) | KotlinTypeArgument::Extends(value) => value.clone(),
            KotlinTypeArgument::Super(_) | KotlinTypeArgument::Any => return None,
        };
        Some((value, *origin))
    }

    fn parameter_completion_type(&self, parameter: &TypeParameter) -> Option<KotlinType> {
        parameter
            .class_bound
            .iter()
            .chain(&parameter.interface_bounds)
            .find_map(|bound| {
                (!Self::references_type_variable(bound, &parameter.name))
                    .then(|| self.instantiate(bound))
                    .flatten()
                    .or_else(|| {
                        self.resolve_source_type(&bound.erased())
                            .map(KotlinType::into_raw)
                    })
            })
    }

    fn constrain_with_origin(
        &mut self,
        formal: &JvmTypeSignature,
        actual: &KotlinType,
        origin: GenericConstraintOrigin,
    ) {
        match (formal, actual) {
            (JvmTypeSignature::TypeVariable(name), actual) => {
                self.bind(
                    name,
                    GenericTypeValue::inferred(KotlinTypeArgument::Exact(actual.clone()), false),
                    origin,
                );
            }
            (JvmTypeSignature::Array(formal), KotlinType::Array(actual)) => {
                self.constrain_with_origin(formal, actual, origin);
            }
            (JvmTypeSignature::ClassType(formal), KotlinType::Variable(actual)) => {
                let Some(bound) = self
                    .visible_bounds
                    .and_then(|bounds| bounds.get(actual))
                    .filter(|bound| *bound != &KotlinType::Variable(actual.clone()))
                    .cloned()
                else {
                    return;
                };
                self.constrain_with_origin(
                    &JvmTypeSignature::ClassType(formal.clone()),
                    &bound,
                    origin,
                );
            }
            (JvmTypeSignature::ClassType(formal), KotlinType::Class(actual)) => {
                let formal_type = JvmTypeSignature::ClassType(formal.clone());
                let formal_erasure = formal_type.erased();
                let Some(KotlinType::Class(expected)) = self.resolve_source_type(&formal_erasure)
                else {
                    return;
                };
                if expected.name() != actual.name() {
                    let Some(projected) = self.generic_projection.and_then(|projection| {
                        projection
                            .project_supertype(&KotlinType::Class(actual.clone()), &formal_erasure)
                    }) else {
                        return;
                    };
                    self.constrain_with_origin(&formal_type, &projected, origin);
                    return;
                }
                let formal_arguments = std::iter::once(formal.type_arguments.as_slice())
                    .chain(
                        formal
                            .inner_segments
                            .iter()
                            .map(|segment| segment.type_arguments.as_slice()),
                    )
                    .collect::<Vec<_>>();
                let formal_offset = formal_arguments.len().saturating_sub(actual.segments.len());
                let actual_offset = actual.segments.len().saturating_sub(formal_arguments.len());
                for (formal_segment, actual_segment) in formal_arguments
                    .into_iter()
                    .skip(formal_offset)
                    .zip(actual.segments.iter().skip(actual_offset))
                {
                    for (formal, actual) in formal_segment.iter().zip(&actual_segment.arguments) {
                        self.constrain_argument(formal, actual, origin);
                    }
                }
            }
            _ => {}
        }
    }

    pub(super) fn instantiate(&self, signature: &JvmTypeSignature) -> Option<KotlinType> {
        self.instantiate_value(signature).map(|value| value.ty)
    }

    pub(super) fn invocation_input_type(&self, signature: &JvmTypeSignature) -> Option<KotlinType> {
        match signature {
            JvmTypeSignature::TypeVariable(name) => match self.input_variable(name).as_ref() {
                Some(KotlinTypeArgument::Exact(value) | KotlinTypeArgument::Super(value)) => {
                    Some(value.clone())
                }
                Some(KotlinTypeArgument::Extends(_) | KotlinTypeArgument::Any) => None,
                None => self.visible_variable(name),
            },
            JvmTypeSignature::Array(element) => {
                self.invocation_input_type(element).map(KotlinType::array)
            }
            JvmTypeSignature::ClassType(class) => self.instantiate_input_class(class),
            JvmTypeSignature::BaseType(_) => self.instantiate(signature),
        }
    }

    fn instantiate_input_class(&self, signature: &ClassTypeSignature) -> Option<KotlinType> {
        let KotlinType::Class(mut resolved) =
            self.resolve_source_type(&JvmTypeSignature::ClassType(signature.clone()).erased())?
        else {
            return None;
        };
        let argument_groups = std::iter::once(signature.type_arguments.as_slice())
            .chain(
                signature
                    .inner_segments
                    .iter()
                    .map(|segment| segment.type_arguments.as_slice()),
            )
            .collect::<Vec<_>>();
        let argument_offset = argument_groups
            .len()
            .saturating_sub(resolved.segments.len());
        let segment_offset = resolved
            .segments
            .len()
            .saturating_sub(argument_groups.len());
        for (segment, arguments) in resolved
            .segments
            .iter_mut()
            .skip(segment_offset)
            .zip(argument_groups.into_iter().skip(argument_offset))
        {
            segment.arguments = arguments
                .iter()
                .map(|argument| self.instantiate_input_argument(argument))
                .collect::<Option<Vec<_>>>()?;
        }
        Some(KotlinType::Class(resolved))
    }

    fn instantiate_input_argument(&self, argument: &TypeArgument) -> Option<KotlinTypeArgument> {
        let projected = match argument {
            TypeArgument::Extends(JvmTypeSignature::TypeVariable(name)) => {
                Self::compose_input_variance(&self.input_variable(name)?, GenericVariance::Extends)
            }
            TypeArgument::Super(JvmTypeSignature::TypeVariable(name)) => {
                Self::compose_input_variance(&self.input_variable(name)?, GenericVariance::Super)
            }
            argument => self.instantiate_argument(argument)?.argument,
        };
        Some(projected)
    }

    fn compose_input_variance(
        argument: &KotlinTypeArgument,
        variance: GenericVariance,
    ) -> KotlinTypeArgument {
        let value = match argument {
            KotlinTypeArgument::Any => return KotlinTypeArgument::Any,
            KotlinTypeArgument::Exact(value)
            | KotlinTypeArgument::Extends(value)
            | KotlinTypeArgument::Super(value) => value.clone(),
        };
        match variance {
            GenericVariance::Extends => KotlinTypeArgument::Extends(value),
            GenericVariance::Super => KotlinTypeArgument::Super(value),
        }
    }

    fn instantiate_value(&self, signature: &JvmTypeSignature) -> Option<InstantiatedType> {
        match signature {
            JvmTypeSignature::TypeVariable(name) => {
                let ty = self.get(name)?;
                Some(InstantiatedType {
                    ty,
                    captured: self.binding(name).is_some_and(|binding| binding.captured),
                })
            }
            JvmTypeSignature::Array(element) => {
                let element = self.instantiate_value(element)?;
                Some(InstantiatedType {
                    ty: KotlinType::array(element.ty),
                    captured: element.captured,
                })
            }
            JvmTypeSignature::BaseType(_) => Some(InstantiatedType {
                ty: self.resolve_source_type(&signature.erased())?,
                captured: false,
            }),
            JvmTypeSignature::ClassType(class) => {
                let KotlinType::Class(mut resolved) =
                    self.resolve_source_type(&signature.erased())?
                else {
                    return None;
                };
                let argument_groups = std::iter::once(class.type_arguments.as_slice())
                    .chain(
                        class
                            .inner_segments
                            .iter()
                            .map(|segment| segment.type_arguments.as_slice()),
                    )
                    .collect::<Vec<_>>();
                let argument_offset = argument_groups
                    .len()
                    .saturating_sub(resolved.segments.len());
                let segment_offset = resolved
                    .segments
                    .len()
                    .saturating_sub(argument_groups.len());
                let mut captured = false;
                for (segment, arguments) in resolved
                    .segments
                    .iter_mut()
                    .skip(segment_offset)
                    .zip(argument_groups.into_iter().skip(argument_offset))
                {
                    let instantiated = arguments
                        .iter()
                        .map(|argument| self.instantiate_argument(argument))
                        .collect::<Option<Vec<_>>>()?;
                    captured |= instantiated.iter().any(|argument| argument.captured);
                    segment.arguments = instantiated
                        .into_iter()
                        .map(|argument| argument.argument)
                        .collect();
                }
                Some(InstantiatedType {
                    ty: KotlinType::Class(resolved),
                    captured,
                })
            }
        }
    }

    pub(super) fn owner_type(&self, owner: &ClassTypeSignature) -> Option<KotlinType> {
        if Self::owner_parameters(owner).next().is_none() {
            return None;
        }
        if Self::owner_parameters(owner).any(|parameter| self.raw_owner.contains(parameter)) {
            return self
                .resolve_source_type(&JvmTypeSignature::ClassType(owner.clone()).erased())
                .map(KotlinType::into_raw);
        }
        self.instantiate(&JvmTypeSignature::ClassType(owner.clone()))
            .filter(|ty| self.valid_source_type(ty))
    }

    pub(super) fn evidenced_owner_type(&self, owner: &ClassTypeSignature) -> Option<KotlinType> {
        Self::owner_parameters(owner)
            .any(|parameter| self.evidenced_type_argument(parameter).is_some())
            .then(|| self.owner_type(owner))
            .flatten()
    }

    pub(super) fn argument_inferred_owner_type(
        &self,
        owner: &ClassTypeSignature,
    ) -> Option<KotlinType> {
        Self::owner_parameters(owner)
            .any(|parameter| {
                matches!(
                    self.values.get(parameter),
                    Some(GenericTypeBinding::Bound {
                        origin: GenericConstraintOrigin::Argument,
                        ..
                    })
                )
            })
            .then(|| self.owner_type(owner))
            .flatten()
    }

    fn resolve_source_type(&self, erased: &ArgType) -> Option<KotlinType> {
        self.source_types.get(erased).cloned().or_else(|| {
            self.generic_projection
                .and_then(|projection| projection.resolve_type(erased))
        })
    }

    pub(super) fn owner_is_raw(&self, owner: &ClassTypeSignature) -> bool {
        Self::owner_parameters(owner).any(|parameter| self.raw_owner.contains(parameter))
    }

    pub(super) fn assume_raw_owner_if_unbound(&mut self, owner: &ClassTypeSignature) {
        // Lexically inherited parameters belong to an enclosing declaration,
        // not to the receiver whose rawness is being decided here.
        for parameter in Self::local_owner_parameters(owner) {
            if !self.values.contains_key(parameter) {
                self.raw_owner.insert(parameter.to_string());
            }
        }
    }

    fn owner_parameters(owner: &ClassTypeSignature) -> impl Iterator<Item = &str> + '_ {
        owner
            .type_arguments
            .iter()
            .chain(
                owner
                    .inner_segments
                    .iter()
                    .flat_map(|segment| &segment.type_arguments),
            )
            .filter_map(owner_type_parameter_name)
    }

    fn local_owner_parameters(owner: &ClassTypeSignature) -> impl Iterator<Item = &str> + '_ {
        owner
            .inner_segments
            .last()
            .map(|segment| segment.type_arguments.as_slice())
            .unwrap_or(&owner.type_arguments)
            .iter()
            .filter_map(owner_type_parameter_name)
    }

    pub(super) fn owner_requires_capture_conversion(
        &self,
        owner: &ClassTypeSignature,
        method_parameters: &[JvmTypeSignature],
    ) -> bool {
        Self::owner_parameters(owner).any(|parameter| {
            self.binding(parameter).is_some_and(|binding| {
                binding.captured
                    && !matches!(binding.argument, KotlinTypeArgument::Super(_))
                    && method_parameters
                        .iter()
                        .any(|ty| Self::capture_requires_conversion(ty, parameter))
            })
        })
    }

    fn capture_requires_conversion(ty: &JvmTypeSignature, name: &str) -> bool {
        match ty {
            JvmTypeSignature::TypeVariable(variable) => variable == name,
            JvmTypeSignature::Array(element) => Self::references_type_variable(element, name),
            JvmTypeSignature::ClassType(class) => class
                .type_arguments
                .iter()
                .chain(
                    class
                        .inner_segments
                        .iter()
                        .flat_map(|segment| &segment.type_arguments),
                )
                .any(|argument| match argument {
                    TypeArgument::Unbounded | TypeArgument::Super(_) => false,
                    TypeArgument::Exact(ty) | TypeArgument::Extends(ty) => {
                        Self::references_type_variable(ty, name)
                    }
                }),
            JvmTypeSignature::BaseType(_) => false,
        }
    }

    fn references_type_variable(ty: &JvmTypeSignature, name: &str) -> bool {
        match ty {
            JvmTypeSignature::TypeVariable(variable) => variable == name,
            JvmTypeSignature::Array(element) => Self::references_type_variable(element, name),
            JvmTypeSignature::ClassType(class) => class
                .type_arguments
                .iter()
                .chain(
                    class
                        .inner_segments
                        .iter()
                        .flat_map(|segment| &segment.type_arguments),
                )
                .any(|argument| match argument {
                    TypeArgument::Unbounded => false,
                    TypeArgument::Exact(ty)
                    | TypeArgument::Extends(ty)
                    | TypeArgument::Super(ty) => Self::references_type_variable(ty, name),
                }),
            JvmTypeSignature::BaseType(_) => false,
        }
    }

    fn value(&self, name: &str) -> Option<&KotlinTypeArgument> {
        Some(&self.binding(name)?.argument)
    }

    fn binding(&self, name: &str) -> Option<&GenericTypeValue> {
        match self.values.get(name)? {
            GenericTypeBinding::Bound { value, .. } => Some(value),
            GenericTypeBinding::Conflict { .. } => None,
        }
    }

    fn substitution(&self, name: &str) -> Option<GenericTypeValue> {
        self.binding(name).cloned().or_else(|| {
            self.visible_variable(name).map(|variable| {
                GenericTypeValue::inferred(KotlinTypeArgument::Exact(variable), false)
            })
        })
    }

    fn bind(&mut self, name: &str, value: GenericTypeValue, origin: GenericConstraintOrigin) {
        if self.visible_variable(name).is_some() {
            return;
        }
        if !Self::is_identity(name, &value.argument)
            && self.occurs(name, &value.argument, &mut BTreeSet::new())
        {
            self.conflict(name, origin);
            return;
        }
        if self.raw_owner.contains(name) && origin != GenericConstraintOrigin::Owner {
            return;
        }
        // Class type arguments belong to the receiver's instantiated type. They
        // are not inference variables of the invoked method, so argument and
        // target-context constraints must not refine a captured receiver such
        // as `Stream<?>` into `Stream<? extends E>`.
        if matches!(
            self.values.get(name),
            Some(GenericTypeBinding::Bound {
                origin: GenericConstraintOrigin::Owner,
                ..
            })
        ) && origin != GenericConstraintOrigin::Owner
        {
            return;
        }
        if matches!(
            self.values.get(name),
            Some(GenericTypeBinding::Bound {
                value: GenericTypeValue {
                    argument: KotlinTypeArgument::Any,
                    captured: true,
                },
                origin: GenericConstraintOrigin::Argument,
            })
        ) && origin == GenericConstraintOrigin::Context
        {
            return;
        }
        let next = match self.values.get(name) {
            None => GenericTypeBinding::Bound { value, origin },
            Some(GenericTypeBinding::Bound {
                value: current,
                origin: current_origin,
            }) => {
                if origin < *current_origin {
                    return;
                } else if origin > *current_origin {
                    GenericTypeBinding::Bound { value, origin }
                } else {
                    match GenericTypeEvidence::reconcile(
                        &current.argument,
                        &value.argument,
                        self.source_types.get(&ArgType::object("java/lang/Object")),
                    ) {
                        Some(argument) => {
                            let captured = if matches!(&argument, KotlinTypeArgument::Any) {
                                current.captured || value.captured
                            } else {
                                current.captured && value.captured
                            };
                            GenericTypeBinding::Bound {
                                value: GenericTypeValue::inferred(argument, captured),
                                origin,
                            }
                        }
                        None => GenericTypeBinding::Conflict { origin },
                    }
                }
            }
            Some(GenericTypeBinding::Conflict {
                origin: conflict_origin,
            }) if origin > *conflict_origin => GenericTypeBinding::Bound { value, origin },
            Some(GenericTypeBinding::Conflict { .. }) => return,
        };
        self.values.insert(name.to_string(), next);
    }

    fn is_identity(name: &str, argument: &KotlinTypeArgument) -> bool {
        matches!(
            argument,
            KotlinTypeArgument::Exact(KotlinType::Variable(variable))
                if variable == &KotlinIdentifier::from_dex(name)
        )
    }

    fn occurs(
        &self,
        name: &str,
        argument: &KotlinTypeArgument,
        visiting: &mut BTreeSet<String>,
    ) -> bool {
        match argument {
            KotlinTypeArgument::Any => false,
            KotlinTypeArgument::Exact(ty)
            | KotlinTypeArgument::Extends(ty)
            | KotlinTypeArgument::Super(ty) => self.occurs_in(name, ty, visiting),
        }
    }

    fn occurs_in(&self, name: &str, ty: &KotlinType, visiting: &mut BTreeSet<String>) -> bool {
        match ty {
            KotlinType::Primitive(_) => false,
            KotlinType::Array(element) => self.occurs_in(name, element, visiting),
            KotlinType::Class(class) => class.segments.iter().any(|segment| {
                segment
                    .arguments
                    .iter()
                    .any(|argument| self.occurs(name, argument, visiting))
            }),
            KotlinType::Variable(variable) => {
                let Some(candidate) = self
                    .inference_variables
                    .iter()
                    .find(|candidate| KotlinIdentifier::from_dex(candidate) == *variable)
                else {
                    return false;
                };
                if candidate == name {
                    return true;
                }
                if !visiting.insert(candidate.clone()) {
                    return false;
                }
                let occurs = self
                    .binding(candidate)
                    .is_some_and(|binding| self.occurs(name, &binding.argument, visiting));
                visiting.remove(candidate);
                occurs
            }
        }
    }

    fn conflict(&mut self, name: &str, origin: GenericConstraintOrigin) {
        let replace = match self.values.get(name) {
            None => true,
            Some(GenericTypeBinding::Bound {
                origin: current, ..
            })
            | Some(GenericTypeBinding::Conflict { origin: current }) => origin >= *current,
        };
        if replace {
            self.values
                .insert(name.to_string(), GenericTypeBinding::Conflict { origin });
        }
    }

    fn constrain_argument(
        &mut self,
        formal: &TypeArgument,
        actual: &KotlinTypeArgument,
        origin: GenericConstraintOrigin,
    ) {
        let (formal, actual, binding) = match (formal, actual) {
            (TypeArgument::Unbounded, _) => return,
            (
                TypeArgument::Exact(JvmTypeSignature::TypeVariable(name)),
                KotlinTypeArgument::Any,
            ) => {
                self.bind(
                    name,
                    GenericTypeValue::declared(KotlinTypeArgument::Any),
                    origin,
                );
                return;
            }
            (_, KotlinTypeArgument::Any) => return,
            (TypeArgument::Exact(formal), actual) => {
                let actual_type = match actual {
                    KotlinTypeArgument::Exact(ty)
                    | KotlinTypeArgument::Extends(ty)
                    | KotlinTypeArgument::Super(ty) => ty,
                    KotlinTypeArgument::Any => unreachable!(),
                };
                (
                    formal,
                    actual_type,
                    GenericTypeValue::declared(actual.clone()),
                )
            }
            (TypeArgument::Extends(formal), KotlinTypeArgument::Exact(actual)) => (
                formal,
                actual,
                GenericTypeValue::inferred(KotlinTypeArgument::Exact(actual.clone()), false),
            ),
            (TypeArgument::Super(formal), KotlinTypeArgument::Exact(actual)) => (
                formal,
                actual,
                GenericTypeValue::inferred(KotlinTypeArgument::Exact(actual.clone()), false),
            ),
            (TypeArgument::Extends(formal), KotlinTypeArgument::Extends(actual)) => (
                formal,
                actual,
                GenericTypeValue::inferred(KotlinTypeArgument::Exact(actual.clone()), false),
            ),
            (TypeArgument::Super(formal), KotlinTypeArgument::Super(actual)) => (
                formal,
                actual,
                GenericTypeValue::inferred(KotlinTypeArgument::Exact(actual.clone()), false),
            ),
            (TypeArgument::Extends(_) | TypeArgument::Super(_), _) => return,
        };
        if let JvmTypeSignature::TypeVariable(name) = formal {
            self.bind(name, binding, origin);
            return;
        }
        self.constrain_with_origin(formal, actual, origin);
    }

    fn instantiate_argument(&self, argument: &TypeArgument) -> Option<InstantiatedArgument> {
        Some(match argument {
            TypeArgument::Unbounded => InstantiatedArgument {
                argument: KotlinTypeArgument::Any,
                captured: false,
            },
            TypeArgument::Exact(JvmTypeSignature::TypeVariable(name)) => {
                let value = self.substitution(name)?;
                InstantiatedArgument {
                    argument: DenotableTypeProjection::argument(value.argument, value.captured),
                    captured: value.captured,
                }
            }
            TypeArgument::Exact(ty) => {
                let value = self.instantiate_value(ty)?;
                InstantiatedArgument {
                    argument: DenotableTypeProjection::argument(
                        KotlinTypeArgument::Exact(value.ty),
                        value.captured,
                    ),
                    captured: value.captured,
                }
            }
            TypeArgument::Extends(JvmTypeSignature::TypeVariable(name)) => {
                let value = self.substitution(name)?;
                InstantiatedArgument {
                    argument: Self::compose_variance(&value.argument, GenericVariance::Extends),
                    captured: value.captured,
                }
            }
            TypeArgument::Extends(ty) => {
                let value = self.instantiate_value(ty)?;
                InstantiatedArgument {
                    argument: KotlinTypeArgument::Extends(value.ty),
                    captured: value.captured,
                }
            }
            TypeArgument::Super(JvmTypeSignature::TypeVariable(name)) => {
                let value = self.substitution(name)?;
                InstantiatedArgument {
                    argument: Self::compose_variance(&value.argument, GenericVariance::Super),
                    captured: value.captured,
                }
            }
            TypeArgument::Super(ty) => {
                let value = self.instantiate_value(ty)?;
                InstantiatedArgument {
                    argument: KotlinTypeArgument::Super(value.ty),
                    captured: value.captured,
                }
            }
        })
    }

    fn compose_variance(
        argument: &KotlinTypeArgument,
        variance: GenericVariance,
    ) -> KotlinTypeArgument {
        match (variance, argument) {
            (_, KotlinTypeArgument::Any)
            | (GenericVariance::Extends, KotlinTypeArgument::Super(_))
            | (GenericVariance::Super, KotlinTypeArgument::Extends(_)) => KotlinTypeArgument::Any,
            (GenericVariance::Extends, KotlinTypeArgument::Exact(value))
            | (GenericVariance::Extends, KotlinTypeArgument::Extends(value)) => {
                KotlinTypeArgument::Extends(value.clone())
            }
            (GenericVariance::Super, KotlinTypeArgument::Exact(value))
            | (GenericVariance::Super, KotlinTypeArgument::Super(value)) => {
                KotlinTypeArgument::Super(value.clone())
            }
        }
    }
}

struct DenotableTypeProjection;

#[cfg_attr(feature = "profiling", hotpath::measure_all)]
impl DenotableTypeProjection {
    fn argument(argument: KotlinTypeArgument, captured: bool) -> KotlinTypeArgument {
        match argument {
            KotlinTypeArgument::Exact(ty) if captured => KotlinTypeArgument::Extends(ty),
            argument => argument,
        }
    }
}

struct InstantiatedType {
    ty: KotlinType,
    captured: bool,
}

struct InstantiatedArgument {
    argument: KotlinTypeArgument,
    captured: bool,
}

#[derive(Clone, Copy)]
enum GenericVariance {
    Extends,
    Super,
}

pub(super) struct GenericTypeEvidence;

#[cfg_attr(feature = "profiling", hotpath::measure_all)]
impl GenericTypeEvidence {
    fn reconcile(
        left: &KotlinTypeArgument,
        right: &KotlinTypeArgument,
        object: Option<&KotlinType>,
    ) -> Option<KotlinTypeArgument> {
        if left == right {
            return Some(left.clone());
        }
        match (Self::value(left), Self::value(right)) {
            (None, None) => Some(KotlinTypeArgument::Any),
            (Some(value), None) | (None, Some(value)) => {
                Some(KotlinTypeArgument::Exact(value.clone()))
            }
            (Some(left), Some(right)) => Some(KotlinTypeArgument::Exact(Self::reconcile_type(
                left, right, object,
            )?)),
        }
    }

    fn value(argument: &KotlinTypeArgument) -> Option<&KotlinType> {
        match argument {
            KotlinTypeArgument::Any => None,
            KotlinTypeArgument::Exact(value)
            | KotlinTypeArgument::Extends(value)
            | KotlinTypeArgument::Super(value) => Some(value),
        }
    }

    fn join(
        left: &KotlinTypeArgument,
        right: &KotlinTypeArgument,
        object: Option<&KotlinType>,
    ) -> Option<KotlinTypeArgument> {
        use KotlinTypeArgument::{Any, Exact, Extends, Super};

        match (left, right) {
            (Any, _) | (_, Any) => Some(Any),
            (Exact(left), Exact(right)) => Some(Exact(Self::join_type(left, right, object)?)),
            (Extends(left), Extends(right)) => Some(Extends(Self::join_type(left, right, object)?)),
            (Super(left), Super(right)) => Some(Super(Self::join_type(left, right, object)?)),
            (Exact(left), Extends(right)) | (Extends(right), Exact(left)) => {
                Some(Extends(Self::join_type(left, right, object)?))
            }
            (Exact(left), Super(right)) | (Super(right), Exact(left)) => {
                Some(Super(Self::join_type(left, right, object)?))
            }
            (Extends(_), Super(_)) | (Super(_), Extends(_)) => Some(Any),
        }
    }

    fn join_type(
        left: &KotlinType,
        right: &KotlinType,
        object: Option<&KotlinType>,
    ) -> Option<KotlinType> {
        match (left, right) {
            (left, right) if left == right => Some(left.clone()),
            (left, right) if object == Some(left) && !matches!(right, KotlinType::Primitive(_)) => {
                Some(right.clone())
            }
            (left, right) if object == Some(right) && !matches!(left, KotlinType::Primitive(_)) => {
                Some(left.clone())
            }
            (KotlinType::Variable(_), _) => Some(left.clone()),
            (_, KotlinType::Variable(_)) => Some(right.clone()),
            (KotlinType::Array(left), KotlinType::Array(right)) => {
                Some(KotlinType::array(Self::join_type(left, right, object)?))
            }
            (KotlinType::Class(left), KotlinType::Class(right)) if left.name() == right.name() => {
                let mut merged = left.clone();
                for (segment, right) in merged.segments.iter_mut().zip(&right.segments) {
                    segment.arguments =
                        match (segment.arguments.is_empty(), right.arguments.is_empty()) {
                            (true, false) => right.arguments.clone(),
                            (false, true) | (true, true) => segment.arguments.clone(),
                            (false, false) if segment.arguments.len() == right.arguments.len() => {
                                segment
                                    .arguments
                                    .iter()
                                    .zip(&right.arguments)
                                    .map(|(left, right)| Self::join(left, right, object))
                                    .collect::<Option<Vec<_>>>()?
                            }
                            (false, false) => return None,
                        };
                }
                Some(KotlinType::Class(merged))
            }
            (KotlinType::Primitive(left), KotlinType::Primitive(right)) if left == right => {
                Some(KotlinType::Primitive(*left))
            }
            _ => None,
        }
    }

    pub(super) fn reconcile_type(
        left: &KotlinType,
        right: &KotlinType,
        object: Option<&KotlinType>,
    ) -> Option<KotlinType> {
        match (left, right) {
            (left, right) if left == right => Some(left.clone()),
            (left, right) if object == Some(left) && !matches!(right, KotlinType::Primitive(_)) => {
                Some(right.clone())
            }
            (left, right) if object == Some(right) && !matches!(left, KotlinType::Primitive(_)) => {
                Some(left.clone())
            }
            (KotlinType::Variable(_), _) => Some(left.clone()),
            (_, KotlinType::Variable(_)) => Some(right.clone()),
            (KotlinType::Array(left), KotlinType::Array(right)) => Some(KotlinType::array(
                Self::reconcile_type(left, right, object)?,
            )),
            (KotlinType::Class(left), KotlinType::Class(right)) if left.name() == right.name() => {
                let mut merged = left.clone();
                for (segment, right) in merged.segments.iter_mut().zip(&right.segments) {
                    segment.arguments =
                        match (segment.arguments.is_empty(), right.arguments.is_empty()) {
                            (true, false) => right.arguments.clone(),
                            (false, true) | (true, true) => segment.arguments.clone(),
                            (false, false) if segment.arguments.len() == right.arguments.len() => {
                                segment
                                    .arguments
                                    .iter()
                                    .zip(&right.arguments)
                                    .map(|(left, right)| Self::reconcile(left, right, object))
                                    .collect::<Option<Vec<_>>>()?
                            }
                            (false, false) => return None,
                        };
                }
                Some(KotlinType::Class(merged))
            }
            (KotlinType::Primitive(left), KotlinType::Primitive(right)) if left == right => {
                Some(KotlinType::Primitive(*left))
            }
            _ => None,
        }
    }
}

struct GenericRequirementLattice<'a> {
    source_types: &'a BTreeMap<ArgType, KotlinType>,
    variable_erasures: &'a BTreeMap<KotlinIdentifier, ArgType>,
    projection: Option<&'a dyn GenericTypeProjection>,
}

#[cfg_attr(feature = "profiling", hotpath::measure_all)]
impl<'a> GenericRequirementLattice<'a> {
    fn new(
        source_types: &'a BTreeMap<ArgType, KotlinType>,
        variable_erasures: &'a BTreeMap<KotlinIdentifier, ArgType>,
        projection: Option<&'a dyn GenericTypeProjection>,
    ) -> Self {
        Self {
            source_types,
            variable_erasures,
            projection,
        }
    }

    fn join(&self, left: &KotlinType, right: &KotlinType) -> Option<KotlinType> {
        if left == right {
            return Some(left.clone());
        }
        match (left, right) {
            (KotlinType::Array(left), KotlinType::Array(right)) => {
                return self.join(left, right).map(KotlinType::array);
            }
            (KotlinType::Class(left), KotlinType::Class(right)) if left.name() == right.name() => {
                let mut joined = left.clone();
                for (segment, right) in joined.segments.iter_mut().zip(&right.segments) {
                    segment.arguments =
                        match (segment.arguments.is_empty(), right.arguments.is_empty()) {
                            (true, false) => right.arguments.clone(),
                            (false, true) | (true, true) => segment.arguments.clone(),
                            (false, false) if segment.arguments.len() == right.arguments.len() => {
                                segment
                                    .arguments
                                    .iter()
                                    .zip(&right.arguments)
                                    .map(|(left, right)| self.join_argument(left, right))
                                    .collect::<Option<Vec<_>>>()?
                            }
                            (false, false) => return None,
                        };
                }
                return Some(KotlinType::Class(joined));
            }
            (KotlinType::Primitive(left), KotlinType::Primitive(right)) if left == right => {
                return Some(KotlinType::Primitive(*left));
            }
            _ => {}
        }
        let left = SourceTypeFlow::erased_type(self.source_types, self.variable_erasures, left)?;
        let right = SourceTypeFlow::erased_type(self.source_types, self.variable_erasures, right)?;
        let common = if left == right {
            left
        } else {
            let projection = self.projection?;
            if projection.is_subtype(&left, &right) {
                right
            } else if projection.is_subtype(&right, &left) {
                left
            } else {
                projection.least_common_supertype(&left, &right)?
            }
        };
        self.source_types.get(&common).cloned().or_else(|| {
            self.projection
                .and_then(|projection| projection.resolve_type(&common))
        })
    }

    fn join_argument(
        &self,
        left: &KotlinTypeArgument,
        right: &KotlinTypeArgument,
    ) -> Option<KotlinTypeArgument> {
        use KotlinTypeArgument::{Any, Exact, Extends, Super};

        match (left, right) {
            (left, right) if left == right => Some(left.clone()),
            (Any, _) | (_, Any) => Some(Any),
            (Exact(left), Exact(right)) => Some(Exact(self.join(left, right)?)),
            (Extends(left), Extends(right)) => Some(Extends(self.join(left, right)?)),
            (Super(left), Super(right)) => Some(Super(self.join(left, right)?)),
            (Exact(left), Extends(right)) | (Extends(right), Exact(left)) => {
                Some(Extends(self.join(left, right)?))
            }
            (Exact(left), Super(right)) | (Super(right), Exact(left)) => {
                Some(Super(self.join(left, right)?))
            }
            (Extends(_), Super(_)) | (Super(_), Extends(_)) => Some(Any),
        }
    }
}

pub(super) struct GenericInvocationCompatibility;

#[cfg_attr(feature = "profiling", hotpath::measure_all)]
impl GenericInvocationCompatibility {
    pub(super) fn requires_unchecked_conversion(
        formal: &JvmTypeSignature,
        actual: &KotlinType,
        contract: &GenericMethodContract,
        source_types: &BTreeMap<ArgType, KotlinType>,
    ) -> bool {
        let KotlinType::Class(actual) = actual else {
            return false;
        };
        if actual
            .segments
            .iter()
            .any(|segment| !segment.arguments.is_empty())
        {
            return false;
        }
        let candidates = match formal {
            JvmTypeSignature::TypeVariable(name) => contract
                .signature
                .type_parameters
                .iter()
                .find(|parameter| &parameter.name == name)
                .into_iter()
                .flat_map(|parameter| {
                    parameter
                        .class_bound
                        .iter()
                        .chain(&parameter.interface_bounds)
                })
                .collect::<Vec<_>>(),
            formal => vec![formal],
        };
        candidates.into_iter().any(|candidate| {
            Self::is_parameterized(candidate)
                && source_types
                    .get(&candidate.erased())
                    .is_some_and(|erased| matches!(erased, KotlinType::Class(erased) if erased.name() == actual.name()))
        })
    }

    fn is_parameterized(ty: &JvmTypeSignature) -> bool {
        match ty {
            JvmTypeSignature::ClassType(class) => {
                !class.type_arguments.is_empty()
                    || class
                        .inner_segments
                        .iter()
                        .any(|segment| !segment.type_arguments.is_empty())
            }
            JvmTypeSignature::Array(element) => Self::is_parameterized(element),
            JvmTypeSignature::TypeVariable(_) | JvmTypeSignature::BaseType(_) => false,
        }
    }

    fn has_type_variable(ty: &JvmTypeSignature) -> bool {
        match ty {
            JvmTypeSignature::TypeVariable(_) => true,
            JvmTypeSignature::Array(element) => Self::has_type_variable(element),
            JvmTypeSignature::ClassType(class) => class
                .type_arguments
                .iter()
                .chain(
                    class
                        .inner_segments
                        .iter()
                        .flat_map(|segment| &segment.type_arguments),
                )
                .any(|argument| match argument {
                    TypeArgument::Unbounded => false,
                    TypeArgument::Exact(ty)
                    | TypeArgument::Extends(ty)
                    | TypeArgument::Super(ty) => Self::has_type_variable(ty),
                }),
            JvmTypeSignature::BaseType(_) => false,
        }
    }

    pub(super) fn has_concrete_type_argument(ty: &JvmTypeSignature) -> bool {
        match ty {
            JvmTypeSignature::ClassType(class) => class
                .type_arguments
                .iter()
                .chain(
                    class
                        .inner_segments
                        .iter()
                        .flat_map(|segment| &segment.type_arguments),
                )
                .any(|argument| match argument {
                    TypeArgument::Unbounded => false,
                    TypeArgument::Exact(ty)
                    | TypeArgument::Extends(ty)
                    | TypeArgument::Super(ty) => Self::is_concrete_type(ty),
                }),
            JvmTypeSignature::Array(element) => Self::has_concrete_type_argument(element),
            JvmTypeSignature::TypeVariable(_) | JvmTypeSignature::BaseType(_) => false,
        }
    }

    fn is_concrete_type(ty: &JvmTypeSignature) -> bool {
        match ty {
            JvmTypeSignature::ClassType(class) => class
                .type_arguments
                .iter()
                .chain(
                    class
                        .inner_segments
                        .iter()
                        .flat_map(|segment| &segment.type_arguments),
                )
                .all(|argument| match argument {
                    TypeArgument::Unbounded => true,
                    TypeArgument::Exact(ty)
                    | TypeArgument::Extends(ty)
                    | TypeArgument::Super(ty) => Self::is_concrete_type(ty),
                }),
            JvmTypeSignature::BaseType(_) => true,
            JvmTypeSignature::Array(element) => Self::is_concrete_type(element),
            JvmTypeSignature::TypeVariable(_) => false,
        }
    }
}

pub(super) struct GenericTypeRelation;

#[cfg_attr(feature = "profiling", hotpath::measure_all)]
impl GenericTypeRelation {
    pub(super) fn converge(
        left: &mut GenericTypeSolver<'_>,
        left_signature: &JvmTypeSignature,
        right: &mut GenericTypeSolver<'_>,
        right_signature: &JvmTypeSignature,
    ) {
        loop {
            let left_before = left.values.clone();
            let right_before = right.values.clone();
            Self::relate(left, left_signature, right, right_signature);
            if left.values == left_before && right.values == right_before {
                break;
            }
        }
    }

    fn relate(
        left: &mut GenericTypeSolver<'_>,
        left_signature: &JvmTypeSignature,
        right: &mut GenericTypeSolver<'_>,
        right_signature: &JvmTypeSignature,
    ) {
        if let Some(value) = left
            .invocation_input_type(left_signature)
            .or_else(|| left.instantiate(left_signature))
        {
            right.constrain_context(right_signature, &value);
        }
        if let Some(value) = right
            .invocation_input_type(right_signature)
            .or_else(|| right.instantiate(right_signature))
        {
            left.constrain(left_signature, &value);
        }
        match (left_signature, right_signature) {
            (JvmTypeSignature::Array(left_element), JvmTypeSignature::Array(right_element)) => {
                Self::relate(left, left_element, right, right_element)
            }
            (JvmTypeSignature::ClassType(left_class), JvmTypeSignature::ClassType(right_class))
                if left_class.erased_name() == right_class.erased_name() =>
            {
                let left_arguments = left_class.type_arguments.iter().chain(
                    left_class
                        .inner_segments
                        .iter()
                        .flat_map(|segment| &segment.type_arguments),
                );
                let right_arguments = right_class.type_arguments.iter().chain(
                    right_class
                        .inner_segments
                        .iter()
                        .flat_map(|segment| &segment.type_arguments),
                );
                for (left_argument, right_argument) in left_arguments.zip(right_arguments) {
                    if let (Some(left_argument), Some(right_argument)) = (
                        Self::argument_signature(left_argument),
                        Self::argument_signature(right_argument),
                    ) {
                        Self::relate(left, left_argument, right, right_argument);
                    }
                }
            }
            _ => {}
        }
    }

    fn argument_signature(argument: &TypeArgument) -> Option<&JvmTypeSignature> {
        match argument {
            TypeArgument::Exact(signature)
            | TypeArgument::Extends(signature)
            | TypeArgument::Super(signature) => Some(signature),
            TypeArgument::Unbounded => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TypeState {
    Exact(KotlinType),
    Conflict,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeConstraintKind {
    Definition,
    Context,
    Receiver,
    Declaration,
}

#[derive(Debug, Clone)]
struct TypeEquation {
    result: RegisterArg,
    value: SemanticExpression,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum SourceTypeFact {
    Variable(u32),
    Value(SsaVar),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TypeEquationCandidate {
    ty: KotlinType,
    is_join: bool,
}

#[derive(Default)]
struct TypeEquationGraph {
    dependents: BTreeMap<SourceTypeFact, BTreeSet<usize>>,
    invocation_dependents: BTreeMap<SourceTypeFact, BTreeSet<usize>>,
    outputs: BTreeMap<SourceTypeFact, Vec<usize>>,
    equation_outputs: Vec<Vec<SourceTypeFact>>,
    candidates: Vec<Option<TypeEquationCandidate>>,
    dirty: BTreeSet<usize>,
    dirty_invocations: BTreeSet<usize>,
}

#[cfg_attr(feature = "profiling", hotpath::measure_all)]
impl TypeEquationGraph {
    fn rebuild(&mut self, equations: &[TypeEquation], invocations: &[Arc<SemanticOperation>]) {
        self.dependents.clear();
        self.invocation_dependents.clear();
        self.outputs.clear();
        self.equation_outputs.clear();
        self.candidates.clear();
        self.dirty.clear();
        self.dirty_invocations.clear();

        for (index, equation) in equations.iter().enumerate() {
            let outputs = Self::register_facts(&equation.result);
            for output in &outputs {
                self.outputs.entry(*output).or_default().push(index);
            }
            for dependency in Self::expression_facts(&equation.value) {
                self.dependents.entry(dependency).or_default().insert(index);
            }
            self.equation_outputs.push(outputs);
            self.candidates.push(None);
            self.dirty.insert(index);
        }
        for (index, invocation) in invocations.iter().enumerate() {
            for dependency in Self::operation_facts(invocation.as_ref()) {
                self.invocation_dependents
                    .entry(dependency)
                    .or_default()
                    .insert(index);
            }
            self.dirty_invocations.insert(index);
        }
    }

    fn register_facts(register: &RegisterArg) -> Vec<SourceTypeFact> {
        let mut facts = Vec::with_capacity(2);
        if let Some(value) = SsaVar::from_reg(register) {
            facts.push(SourceTypeFact::Value(value));
        }
        if let Some(variable) = register.code_var {
            facts.push(SourceTypeFact::Variable(variable));
        }
        facts
    }

    fn expression_facts(expression: &SemanticExpression) -> BTreeSet<SourceTypeFact> {
        let mut facts = BTreeSet::new();
        let mut pending = vec![expression];
        while let Some(expression) = pending.pop() {
            match expression {
                SemanticExpression::Register(register) => {
                    facts.extend(Self::register_facts(register));
                }
                SemanticExpression::Operation(operation) => {
                    if let Some(result) = &operation.result {
                        // Poly expressions consume their target constraint as
                        // an input to generic invocation type inference.
                        facts.extend(Self::register_facts(result));
                    }
                    pending.extend(operation.operands());
                }
                SemanticExpression::Select {
                    when_true,
                    when_false,
                    ..
                } => {
                    pending.push(when_true);
                    pending.push(when_false);
                }
                SemanticExpression::Literal(_) => {}
            }
        }
        facts
    }

    fn operation_facts(operation: &SemanticOperation) -> BTreeSet<SourceTypeFact> {
        let mut facts = BTreeSet::new();
        if let Some(result) = &operation.result {
            facts.extend(Self::register_facts(result));
        }
        for operand in operation.operands() {
            facts.extend(Self::expression_facts(operand));
        }
        facts
    }

    fn mark_changed(&mut self, fact: SourceTypeFact) {
        if let Some(dependents) = self.dependents.get(&fact) {
            self.dirty.extend(dependents);
        }
        if let Some(dependents) = self.invocation_dependents.get(&fact) {
            self.dirty_invocations.extend(dependents);
        }
    }

    fn take_dirty(&mut self) -> BTreeSet<usize> {
        std::mem::take(&mut self.dirty)
    }

    fn take_dirty_invocations(&mut self) -> BTreeSet<usize> {
        std::mem::take(&mut self.dirty_invocations)
    }

    fn update_candidate(&mut self, index: usize, candidate: Option<TypeEquationCandidate>) -> bool {
        if self.candidates.get(index) == Some(&candidate) {
            return false;
        }
        self.candidates[index] = candidate;
        true
    }

    fn outputs_for_equation(&self, index: usize) -> &[SourceTypeFact] {
        self.equation_outputs
            .get(index)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    fn equations_for_output(&self, output: SourceTypeFact) -> &[usize] {
        self.outputs
            .get(&output)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }
}

#[derive(Debug, Clone)]
struct ElementEquation {
    variable: RegisterArg,
    iterable: SemanticExpression,
}

pub(super) struct SourceTypeFacts {
    object_types: Vec<(String, String)>,
    definition_variables: BTreeMap<u32, KotlinType>,
    definition_values: BTreeMap<SsaVar, KotlinType>,
    variables: BTreeMap<u32, KotlinType>,
    values: BTreeMap<SsaVar, KotlinType>,
    requirements: BTreeMap<u32, KotlinType>,
    value_requirements: BTreeMap<SsaVar, KotlinType>,
    equations: Vec<crate::ir::SourceTypeEquationDiagnostic>,
    requirement_candidates: BTreeMap<u32, BTreeSet<String>>,
    invocations: Vec<crate::ir::InvocationTypeDiagnostic>,
}

impl SourceTypeFacts {
    pub(super) fn into_parts(
        self,
    ) -> (
        BTreeMap<u32, KotlinType>,
        BTreeMap<SsaVar, KotlinType>,
        BTreeMap<u32, KotlinType>,
        BTreeMap<SsaVar, KotlinType>,
        BTreeMap<u32, KotlinType>,
        BTreeMap<SsaVar, KotlinType>,
    ) {
        (
            self.definition_variables,
            self.definition_values,
            self.variables,
            self.values,
            self.requirements,
            self.value_requirements,
        )
    }

    pub(super) fn diagnostics(&self) -> crate::ir::SourceTypeDiagnostics {
        crate::ir::SourceTypeDiagnostics {
            object_types: self.object_types.clone(),
            definition_variables: self
                .definition_variables
                .iter()
                .map(|(variable, ty)| (*variable, ty.to_string()))
                .collect(),
            definition_values: self
                .definition_values
                .iter()
                .map(|(value, ty)| (value.reg_num, value.version, ty.to_string()))
                .collect(),
            variables: self
                .variables
                .iter()
                .map(|(variable, ty)| (*variable, ty.to_string()))
                .collect(),
            values: self
                .values
                .iter()
                .map(|(value, ty)| (value.reg_num, value.version, ty.to_string()))
                .collect(),
            requirements: self
                .requirements
                .iter()
                .map(|(variable, ty)| (*variable, ty.to_string()))
                .collect(),
            value_requirements: self
                .value_requirements
                .iter()
                .map(|(value, ty)| (value.reg_num, value.version, ty.to_string()))
                .collect(),
            equations: self.equations.clone(),
            requirement_candidates: self
                .requirement_candidates
                .iter()
                .map(|(variable, candidates)| (*variable, candidates.iter().cloned().collect()))
                .collect(),
            invocations: self.invocations.clone(),
        }
    }
}

/// Recovers source-level local types that survive DEX erasure through values
/// whose declarations still carry a generic signature.
pub(super) struct SourceTypeFlow<'a> {
    fields: &'a BTreeMap<FieldReference, KotlinType>,
    generic_fields: &'a BTreeMap<FieldReference, GenericFieldContract>,
    object_types: &'a BTreeMap<ArgType, KotlinType>,
    generic_methods: &'a BTreeMap<MethodReference, GenericMethodContract>,
    generic_projection: Option<&'a dyn GenericTypeProjection>,
    source_types: &'a BTreeMap<ArgType, KotlinType>,
    source_erasures: Arc<KotlinTypeErasureIndex>,
    type_variable_erasures: &'a BTreeMap<KotlinIdentifier, ArgType>,
    type_variable_bounds: &'a BTreeMap<KotlinIdentifier, KotlinType>,
    return_type: Option<&'a KotlinType>,
    current_type: Option<&'a ArgType>,
    source_current_type: Option<&'a KotlinType>,
    this_variable: Option<u32>,
    abi_fixed: BTreeSet<u32>,
    fixed: BTreeSet<u32>,
    fixed_values: BTreeSet<SsaVar>,
    states: BTreeMap<u32, TypeState>,
    definition_states: BTreeMap<u32, TypeState>,
    requirements: BTreeMap<u32, TypeState>,
    value_requirements: BTreeMap<SsaVar, TypeState>,
    receiver_requirements: BTreeMap<u32, TypeState>,
    receiver_value_requirements: BTreeMap<SsaVar, TypeState>,
    requirement_candidates: BTreeMap<u32, BTreeSet<String>>,
    value_states: BTreeMap<SsaVar, TypeState>,
    value_definition_states: BTreeMap<SsaVar, TypeState>,
    value_erased_types: BTreeMap<SsaVar, ArgType>,
    contextual_variables: BTreeSet<u32>,
    contextual_values: BTreeSet<SsaVar>,
    erased_boundary_variables: BTreeSet<u32>,
    declaration_variables: BTreeSet<u32>,
    declaration_values: BTreeSet<SsaVar>,
    join_variables: BTreeSet<u32>,
    equations: Vec<TypeEquation>,
    equation_graph: TypeEquationGraph,
    elements: Vec<ElementEquation>,
    invocations: Vec<Arc<SemanticOperation>>,
    predicate_tests: Vec<SemanticOperation>,
    runtime_type_tests: Vec<SemanticOperation>,
    source_type_validity: RefCell<HashMap<KotlinType, bool>>,
    collect_diagnostics: bool,
}

#[cfg_attr(feature = "profiling", hotpath::measure_all)]
impl<'a> SourceTypeFlow<'a> {
    pub(super) fn solve(
        root: &crate::ir::SemanticNode,
        fields: &'a BTreeMap<FieldReference, KotlinType>,
        generic_fields: &'a BTreeMap<FieldReference, GenericFieldContract>,
        object_types: &'a BTreeMap<ArgType, KotlinType>,
        generic_methods: &'a BTreeMap<MethodReference, GenericMethodContract>,
        generic_projection: Option<&'a dyn GenericTypeProjection>,
        source_types: &'a BTreeMap<ArgType, KotlinType>,
        type_variable_erasures: &'a BTreeMap<KotlinIdentifier, ArgType>,
        type_variable_bounds: &'a BTreeMap<KotlinIdentifier, KotlinType>,
        return_type: Option<&'a KotlinType>,
        current_type: Option<&'a ArgType>,
        source_current_type: Option<&'a KotlinType>,
        this_variable: Option<u32>,
        seeds: &BTreeMap<u32, KotlinType>,
        collect_diagnostics: bool,
    ) -> SourceTypeFacts {
        let mut flow = Self {
            fields,
            generic_fields,
            object_types,
            generic_methods,
            generic_projection,
            source_types,
            source_erasures: Arc::new(KotlinTypeErasureIndex::from_source_types(source_types)),
            type_variable_erasures,
            type_variable_bounds,
            return_type,
            current_type,
            source_current_type,
            this_variable,
            abi_fixed: seeds.keys().copied().collect(),
            fixed: seeds.keys().copied().collect(),
            fixed_values: BTreeSet::new(),
            states: seeds
                .iter()
                .map(|(variable, ty)| (*variable, TypeState::Exact(ty.clone())))
                .collect(),
            definition_states: BTreeMap::new(),
            requirements: BTreeMap::new(),
            value_requirements: BTreeMap::new(),
            receiver_requirements: BTreeMap::new(),
            receiver_value_requirements: BTreeMap::new(),
            requirement_candidates: BTreeMap::new(),
            value_states: BTreeMap::new(),
            value_definition_states: BTreeMap::new(),
            value_erased_types: BTreeMap::new(),
            contextual_variables: BTreeSet::new(),
            contextual_values: BTreeSet::new(),
            erased_boundary_variables: BTreeSet::new(),
            declaration_variables: BTreeSet::new(),
            declaration_values: BTreeSet::new(),
            join_variables: BTreeSet::new(),
            equations: Vec::new(),
            equation_graph: TypeEquationGraph::default(),
            elements: Vec::new(),
            invocations: Vec::new(),
            predicate_tests: Vec::new(),
            runtime_type_tests: Vec::new(),
            source_type_validity: RefCell::new(HashMap::new()),
            collect_diagnostics,
        };
        if let (Some(variable), Some(ty)) = (this_variable, source_current_type) {
            flow.abi_fixed.insert(variable);
            flow.fixed.insert(variable);
            flow.states.insert(variable, TypeState::Exact(ty.clone()));
        }
        flow.visit_node(root);
        flow.constrain_boolean_predicates();
        flow.equation_graph
            .rebuild(&flow.equations, &flow.invocations);
        flow.converge();
        let invocations = collect_diagnostics
            .then(|| flow.invocation_diagnostics())
            .unwrap_or_default();
        let object_types = if collect_diagnostics {
            flow.object_types
                .iter()
                .map(|(implementation, source)| (implementation.to_string(), source.to_string()))
                .collect()
        } else {
            Vec::new()
        };
        let definition_variables =
            Self::retained_states(flow.definition_states.clone(), &flow.contextual_variables);
        let definition_values = Self::retained_states(
            flow.value_definition_states.clone(),
            &flow.contextual_values,
        );
        let requirements = Self::preferred_requirement_states(
            flow.source_types,
            flow.type_variable_erasures,
            flow.generic_projection,
            flow.requirements,
            flow.receiver_requirements,
        );
        let value_requirements = Self::preferred_requirement_states(
            flow.source_types,
            flow.type_variable_erasures,
            flow.generic_projection,
            flow.value_requirements,
            flow.receiver_value_requirements,
        );
        let equations = if collect_diagnostics {
            flow.equations
                .iter()
                .filter_map(|equation| {
                    Some(crate::ir::SourceTypeEquationDiagnostic {
                        variable: equation.result.code_var?,
                        register: equation.result.reg_num,
                        version: equation.result.ssa_version,
                        erased_type: equation.result.ty.to_string(),
                        edge_copy: equation
                            .value
                            .as_operation()
                            .is_some_and(|operation| operation.payload.edge_copy),
                    })
                })
                .collect()
        } else {
            Vec::new()
        };
        SourceTypeFacts {
            object_types,
            definition_variables,
            definition_values,
            variables: Self::retained_states(flow.states, &flow.contextual_variables),
            values: Self::retained_states(flow.value_states, &flow.contextual_values),
            requirements: requirements
                .into_iter()
                .filter_map(|(variable, state)| match state {
                    TypeState::Exact(ty) => Some((variable, ty)),
                    TypeState::Conflict => None,
                })
                .collect(),
            value_requirements: value_requirements
                .into_iter()
                .filter_map(|(value, state)| match state {
                    TypeState::Exact(ty) => Some((value, ty)),
                    TypeState::Conflict => None,
                })
                .collect(),
            equations,
            requirement_candidates: collect_diagnostics
                .then_some(flow.requirement_candidates)
                .unwrap_or_default(),
            invocations,
        }
    }

    fn invocation_diagnostics(&self) -> Vec<crate::ir::InvocationTypeDiagnostic> {
        self.invocations
            .iter()
            .filter_map(|operation| {
                let MemberReference::Method(method) = operation.payload.reference.as_ref()? else {
                    return None;
                };
                let Some((mut solver, _, contract)) = self.invocation_solver(operation) else {
                    return Some(crate::ir::InvocationTypeDiagnostic {
                        reference: method.to_string(),
                        resolved: false,
                        inputs: Vec::new(),
                        output: None,
                        owner_parameters: Vec::new(),
                        owner_bounds_satisfied: None,
                    });
                };
                let inputs = contract
                    .signature
                    .parameter_types
                    .iter()
                    .map(|formal| {
                        solver
                            .invocation_input_type(formal)
                            .map(|ty| ty.to_string())
                    })
                    .collect();
                let owner_parameters = contract
                    .owner_parameters
                    .iter()
                    .map(|parameter| parameter.name.clone())
                    .collect();
                let owner_bounds_satisfied =
                    Some(solver.satisfies_declared_bounds(&contract.owner_parameters));
                solver.complete_with_bounds(&contract.signature.type_parameters);
                let output = solver
                    .instantiate(invocation_expression_signature(operation, contract).as_ref())
                    .map(|ty| ty.to_string());
                Some(crate::ir::InvocationTypeDiagnostic {
                    reference: method.to_string(),
                    resolved: true,
                    inputs,
                    output,
                    owner_parameters,
                    owner_bounds_satisfied,
                })
            })
            .collect()
    }

    fn retained_states<K: Ord>(
        states: BTreeMap<K, TypeState>,
        contextual: &BTreeSet<K>,
    ) -> BTreeMap<K, KotlinType> {
        states
            .into_iter()
            .filter_map(|(identity, state)| match state {
                TypeState::Exact(ty)
                    if !matches!(ty, KotlinType::Primitive(_))
                        || contextual.contains(&identity) =>
                {
                    Some((identity, ty))
                }
                TypeState::Exact(_) => None,
                TypeState::Conflict => None,
            })
            .collect()
    }

    fn preferred_requirement_states<K: Ord>(
        source_types: &BTreeMap<ArgType, KotlinType>,
        type_variable_erasures: &BTreeMap<KotlinIdentifier, ArgType>,
        generic_projection: Option<&dyn GenericTypeProjection>,
        mut primary: BTreeMap<K, TypeState>,
        fallback: BTreeMap<K, TypeState>,
    ) -> BTreeMap<K, TypeState> {
        for (identity, state) in fallback {
            match state {
                TypeState::Exact(ty) => {
                    Self::merge_requirement(
                        source_types,
                        type_variable_erasures,
                        generic_projection,
                        &mut primary,
                        identity,
                        ty,
                    );
                }
                TypeState::Conflict => {
                    primary.entry(identity).or_insert(TypeState::Conflict);
                }
            }
        }
        primary
    }

    fn has_source_specific_type(ty: &KotlinType) -> bool {
        match ty {
            KotlinType::Variable(_) => true,
            KotlinType::Array(element) => Self::has_source_specific_type(element),
            KotlinType::Class(class) => class
                .segments
                .iter()
                .any(|segment| !segment.arguments.is_empty()),
            KotlinType::Primitive(_) => false,
        }
    }

    fn source_type_is_well_formed(&self, ty: &KotlinType) -> bool {
        if let Some(valid) = self.source_type_validity.borrow().get(ty).copied() {
            return valid;
        }
        let valid = Self::type_is_well_formed(ty, self.type_variable_erasures)
            && GenericTypeSolver::new(self.source_types)
                .with_erasure_index(Some(Arc::clone(&self.source_erasures)))
                .with_visible_variables(self.type_variable_erasures)
                .with_visible_bounds(self.type_variable_bounds)
                .with_projection(self.generic_projection)
                .valid_source_type(ty);
        self.source_type_validity
            .borrow_mut()
            .insert(ty.clone(), valid);
        valid
    }

    fn type_is_well_formed(
        ty: &KotlinType,
        type_variable_erasures: &BTreeMap<KotlinIdentifier, ArgType>,
    ) -> bool {
        match ty {
            KotlinType::Variable(variable) => type_variable_erasures.contains_key(variable),
            KotlinType::Array(element) => {
                Self::type_is_well_formed(element, type_variable_erasures)
            }
            KotlinType::Class(class) => class.segments.iter().all(|segment| {
                segment.arguments.iter().all(|argument| match argument {
                    KotlinTypeArgument::Any => true,
                    KotlinTypeArgument::Exact(ty)
                    | KotlinTypeArgument::Extends(ty)
                    | KotlinTypeArgument::Super(ty) => {
                        Self::type_is_well_formed(ty, type_variable_erasures)
                    }
                })
            }),
            KotlinType::Primitive(_) => true,
        }
    }

    fn converge(&mut self) {
        self.converge_definition_facts();
        self.value_definition_states = self.value_states.clone();
        self.definition_states = self.states.clone();
        self.constrain_runtime_type_tests();

        loop {
            self.converge_facts();
            let replacements = self.apply_requirements();
            let value_replacements = self.apply_value_requirements();
            if replacements.is_empty() && value_replacements.is_empty() {
                break;
            }
            self.fixed.extend(replacements);
            self.fixed_values.extend(value_replacements);
        }
    }

    fn converge_definition_facts(&mut self) {
        self.converge_equations();
    }

    fn apply_value_requirements(&mut self) -> Vec<SsaVar> {
        let replacements = self
            .value_requirements
            .keys()
            .chain(self.receiver_value_requirements.keys())
            .copied()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .filter_map(|value| {
                let requirement = self.required_value_type(value)?;
                (self.value_states.get(&value) != Some(&TypeState::Exact(requirement.clone())))
                    .then_some((value, requirement))
            })
            .collect::<Vec<_>>();
        for (value, requirement) in &replacements {
            self.value_states
                .insert(*value, TypeState::Exact(requirement.clone()));
            self.equation_graph
                .mark_changed(SourceTypeFact::Value(*value));
        }
        replacements.into_iter().map(|(value, _)| value).collect()
    }

    fn required_value_type(&self, value: SsaVar) -> Option<KotlinType> {
        let TypeState::Exact(requirement) = self
            .value_requirements
            .get(&value)
            .or_else(|| self.receiver_value_requirements.get(&value))?
        else {
            return None;
        };
        let relations = KotlinTypeRelations::new(
            self.source_types,
            self.type_variable_erasures,
            self.generic_projection,
        )
        .with_erasure_index(Some(self.source_erasures.as_ref()));
        if self.declaration_values.contains(&value)
            && self.value_definition_fits(value, requirement, &relations)
        {
            return (self.value_states.get(&value) != Some(&TypeState::Exact(requirement.clone())))
                .then_some(requirement.clone());
        }
        if let Some(TypeState::Exact(principal)) = self.value_definition_states.get(&value) {
            let principal = principal.clone();
            if let Some(specialized) =
                self.specialize_value_principal_type(value, &principal, requirement, &relations)
            {
                return (self.value_states.get(&value)
                    != Some(&TypeState::Exact(specialized.clone())))
                .then_some(specialized);
            }
            let proper_subtype = relations.is_assignable(&principal, requirement)
                && !relations.is_assignable(requirement, &principal);
            if (proper_subtype
                || self.source_erasure_is_strict_subtype(&principal, requirement)
                || self.value_erasure_is_strict_subtype(value, requirement))
                && self.value_definition_fits(value, &principal, &relations)
            {
                return (self.value_states.get(&value)
                    != Some(&TypeState::Exact(principal.clone())))
                .then_some(principal);
            }
        }
        if self
            .value_states
            .get(&value)
            .is_some_and(|state| match state {
                TypeState::Exact(current) => {
                    relations.is_assignable(current, requirement)
                        && !relations.is_assignable(requirement, current)
                        && self.value_definition_fits(value, current, &relations)
                }
                TypeState::Conflict => false,
            })
        {
            return None;
        }
        if !self.value_definition_fits(value, requirement, &relations) {
            return None;
        }
        match self.value_states.get(&value) {
            Some(TypeState::Exact(current))
                if relations.is_assignable(current, requirement)
                    && (!Self::has_source_specific_type(requirement)
                        || Self::has_source_specific_type(current)) =>
            {
                None
            }
            Some(TypeState::Exact(_) | TypeState::Conflict) | None => Some(requirement.clone()),
        }
    }

    fn value_definition_fits(
        &self,
        value: SsaVar,
        requirement: &KotlinType,
        relations: &KotlinTypeRelations<'_>,
    ) -> bool {
        let Some(equation) = self.equations_for_fact(SourceTypeFact::Value(value)).next() else {
            return false;
        };
        self.expression_fits(&equation.value, requirement, relations)
            || self.expression_accepts_target(&equation.value, requirement)
            || self.erased_reference_result_fits(equation, requirement)
    }

    fn converge_facts(&mut self) {
        loop {
            let mut changed = self.converge_equations();
            for index in 0..self.elements.len() {
                let equation = self.elements[index].clone();
                if let Some(element) = self.iterable_element_type(&equation.iterable) {
                    changed |= self.constrain_register(&equation.variable, element);
                }
                let element = self
                    .register_type(&equation.variable)
                    .cloned()
                    .or_else(|| self.resolved_type(&equation.variable.ty));
                if let Some(expected) = element
                    .and_then(|element| self.iterable_context_type(&equation.iterable, element))
                {
                    changed |= self.constrain_expression_context(&equation.iterable, expected);
                }
            }
            for index in self.equation_graph.take_dirty_invocations() {
                let invocation = Arc::clone(&self.invocations[index]);
                changed |= self.constrain_invocation(invocation.as_ref());
            }
            if !changed {
                break;
            }
        }
    }

    fn converge_equations(&mut self) -> bool {
        let mut any_changed = false;
        loop {
            let dirty = self.equation_graph.take_dirty();
            if dirty.is_empty() {
                break;
            }
            let mut affected_outputs = BTreeSet::new();
            for index in dirty {
                let equation = &self.equations[index];
                let candidate = self
                    .expression_type_for_result(&equation.value, &equation.result.ty)
                    .filter(|ty| self.source_type_is_well_formed(ty))
                    .map(|ty| TypeEquationCandidate {
                        ty,
                        is_join: matches!(equation.value, SemanticExpression::Select { .. }),
                    });
                if self.equation_graph.update_candidate(index, candidate) {
                    affected_outputs.extend(
                        self.equation_graph
                            .outputs_for_equation(index)
                            .iter()
                            .copied(),
                    );
                }
            }
            for output in affected_outputs {
                if self.fact_is_fixed(output) {
                    continue;
                }
                let Some(next) = self.equation_output_state(output) else {
                    continue;
                };
                let next = match next {
                    TypeState::Exact(incoming) => Self::join_type_state(
                        self.source_types,
                        self.type_variable_erasures,
                        self.generic_projection,
                        self.fact_state(output),
                        incoming,
                    ),
                    TypeState::Conflict => TypeState::Conflict,
                };
                if self.fact_state(output) == Some(&next) {
                    continue;
                }
                self.set_fact_state(output, next);
                self.equation_graph.mark_changed(output);
                any_changed = true;
            }
        }
        any_changed
    }

    fn equation_output_state(&self, output: SourceTypeFact) -> Option<TypeState> {
        let mut state = None;
        for &index in self.equation_graph.equations_for_output(output) {
            let Some(candidate) = self.equation_graph.candidates[index].as_ref() else {
                continue;
            };
            if let SourceTypeFact::Variable(variable) = output {
                if self.join_variables.contains(&variable) && !candidate.is_join {
                    continue;
                }
            }
            state = Some(Self::join_type_state(
                self.source_types,
                self.type_variable_erasures,
                self.generic_projection,
                state.as_ref(),
                candidate.ty.clone(),
            ));
        }
        state
    }

    fn fact_is_fixed(&self, fact: SourceTypeFact) -> bool {
        match fact {
            SourceTypeFact::Variable(variable) => self.fixed.contains(&variable),
            SourceTypeFact::Value(value) => self.fixed_values.contains(&value),
        }
    }

    fn fact_state(&self, fact: SourceTypeFact) -> Option<&TypeState> {
        match fact {
            SourceTypeFact::Variable(variable) => self.states.get(&variable),
            SourceTypeFact::Value(value) => self.value_states.get(&value),
        }
    }

    fn equations_for_fact(&self, fact: SourceTypeFact) -> impl Iterator<Item = &TypeEquation> {
        self.equation_graph
            .equations_for_output(fact)
            .iter()
            .map(|&index| &self.equations[index])
    }

    fn set_fact_state(&mut self, fact: SourceTypeFact, state: TypeState) {
        match fact {
            SourceTypeFact::Variable(variable) => {
                self.states.insert(variable, state);
            }
            SourceTypeFact::Value(value) => {
                self.value_states.insert(value, state);
            }
        }
    }

    fn apply_requirements(&mut self) -> Vec<u32> {
        let replacements = self
            .requirements
            .keys()
            .chain(self.receiver_requirements.keys())
            .copied()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .filter_map(|variable| {
                let requirement = self.required_type(variable)?;
                (self.states.get(&variable) != Some(&TypeState::Exact(requirement.clone())))
                    .then_some((variable, requirement))
            })
            .collect::<Vec<_>>();
        for (variable, requirement) in &replacements {
            self.states
                .insert(*variable, TypeState::Exact(requirement.clone()));
            self.equation_graph
                .mark_changed(SourceTypeFact::Variable(*variable));
        }
        replacements
            .into_iter()
            .map(|(variable, _)| variable)
            .collect()
    }

    fn required_type(&self, variable: u32) -> Option<KotlinType> {
        let TypeState::Exact(requirement) = self
            .requirements
            .get(&variable)
            .or_else(|| self.receiver_requirements.get(&variable))?
        else {
            return None;
        };
        if self.abi_fixed.contains(&variable) {
            return None;
        }
        let relations = KotlinTypeRelations::new(
            self.source_types,
            self.type_variable_erasures,
            self.generic_projection,
        )
        .with_erasure_index(Some(self.source_erasures.as_ref()));
        if self.declaration_variables.contains(&variable)
            && self.definitions_fit(variable, requirement, &relations)
        {
            return (self.states.get(&variable) != Some(&TypeState::Exact(requirement.clone())))
                .then_some(requirement.clone());
        }
        if let Some(principal) = self.value_principal_type(variable) {
            if let Some(specialized) =
                self.specialize_principal_type(variable, &principal, requirement, &relations)
            {
                return (self.states.get(&variable)
                    != Some(&TypeState::Exact(specialized.clone())))
                .then_some(specialized);
            }
            let definition_is_stricter = self
                .definition_states
                .get(&variable)
                .and_then(|state| match state {
                    TypeState::Exact(ty) => Some(ty),
                    TypeState::Conflict => None,
                })
                .is_some_and(|definition| {
                    relations.is_assignable(definition, &principal)
                        && !relations.is_assignable(&principal, definition)
                });
            if !definition_is_stricter
                && relations.is_assignable(&principal, requirement)
                && self.definitions_fit(variable, &principal, &relations)
            {
                return (self.states.get(&variable) != Some(&TypeState::Exact(principal.clone())))
                    .then_some(principal);
            }
        }
        if self.erased_boundary_variables.contains(&variable)
            && Self::has_source_specific_type(requirement)
            && self.states.get(&variable).is_some_and(|state| match state {
                TypeState::Exact(current) => {
                    !self.has_generic_argument_evidence(current)
                        && self.indexed_erased_type(current)
                            == self.indexed_erased_type(requirement)
                }
                TypeState::Conflict => false,
            })
        {
            return None;
        }
        if let Some(TypeState::Exact(principal)) = self.definition_states.get(&variable) {
            let principal = principal.clone();
            if let Some(specialized) =
                self.specialize_principal_type(variable, &principal, requirement, &relations)
            {
                return (self.states.get(&variable)
                    != Some(&TypeState::Exact(specialized.clone())))
                .then_some(specialized);
            }
            let proper_subtype = relations.is_assignable(&principal, requirement)
                && !relations.is_assignable(requirement, &principal);
            if (proper_subtype || self.source_erasure_is_strict_subtype(&principal, requirement))
                && self.definitions_fit(variable, &principal, &relations)
            {
                return (self.states.get(&variable) != Some(&TypeState::Exact(principal.clone())))
                    .then_some(principal);
            }
            if self.variable_erasures_are_strict_subtypes(variable, requirement)
                && self.definitions_fit(variable, requirement, &relations)
            {
                return (self.states.get(&variable)
                    != Some(&TypeState::Exact(requirement.clone())))
                .then_some(requirement.clone());
            }
        }
        if self.definitions_preserve_runtime_type(variable, requirement) {
            return (self.states.get(&variable) != Some(&TypeState::Exact(requirement.clone())))
                .then_some(requirement.clone());
        }
        if self.states.get(&variable).is_some_and(|state| match state {
            TypeState::Exact(current) => {
                relations.is_assignable(current, requirement)
                    && !relations.is_assignable(requirement, current)
                    && self.definitions_fit(variable, current, &relations)
            }
            TypeState::Conflict => false,
        }) {
            return None;
        }
        if !self.definitions_fit(variable, requirement, &relations) {
            return None;
        }
        match self.states.get(&variable) {
            Some(TypeState::Exact(current))
                if relations.is_assignable(current, requirement)
                    && (!Self::has_source_specific_type(requirement)
                        || Self::has_source_specific_type(current))
                    && self.definitions_fit(variable, current, &relations) =>
            {
                None
            }
            Some(TypeState::Exact(_) | TypeState::Conflict) | None => Some(requirement.clone()),
        }
    }

    fn value_principal_type(&self, variable: u32) -> Option<KotlinType> {
        let mut principals = self
            .equations_for_fact(SourceTypeFact::Variable(variable))
            .filter_map(|equation| {
                SsaVar::from_reg(&equation.result)
                    .and_then(|value| self.value_definition_states.get(&value))
                    .and_then(|state| match state {
                        TypeState::Exact(ty) => Some(ty.clone()),
                        TypeState::Conflict => None,
                    })
            });
        let principal = principals.next()?;
        principals.try_fold(principal, |principal, incoming| {
            Self::least_common_source_type(
                self.source_types,
                self.type_variable_erasures,
                self.generic_projection,
                &principal,
                &incoming,
            )
        })
    }

    fn least_common_source_type(
        source_types: &BTreeMap<ArgType, KotlinType>,
        type_variable_erasures: &BTreeMap<KotlinIdentifier, ArgType>,
        generic_projection: Option<&dyn GenericTypeProjection>,
        left: &KotlinType,
        right: &KotlinType,
    ) -> Option<KotlinType> {
        GenericRequirementLattice::new(source_types, type_variable_erasures, generic_projection)
            .join(left, right)
            .or_else(|| {
                let left = Self::erased_type(source_types, type_variable_erasures, left)?;
                let right = Self::erased_type(source_types, type_variable_erasures, right)?;
                if !left.is_reference() || !right.is_reference() {
                    return None;
                }
                source_types
                    .get(&ArgType::object("java/lang/Object"))
                    .cloned()
                    .or_else(|| {
                        generic_projection.and_then(|projection| {
                            projection.resolve_type(&ArgType::object("java/lang/Object"))
                        })
                    })
            })
    }

    fn specialize_principal_type(
        &self,
        variable: u32,
        principal: &KotlinType,
        requirement: &KotlinType,
        relations: &KotlinTypeRelations<'_>,
    ) -> Option<KotlinType> {
        let specialized = self.specialized_principal_type(principal, requirement, relations)?;
        self.definitions_fit(variable, &specialized, relations)
            .then_some(specialized)
    }

    fn specialize_value_principal_type(
        &self,
        value: SsaVar,
        principal: &KotlinType,
        requirement: &KotlinType,
        relations: &KotlinTypeRelations<'_>,
    ) -> Option<KotlinType> {
        let specialized = self.specialized_principal_type(principal, requirement, relations)?;
        self.value_definition_fits(value, &specialized, relations)
            .then_some(specialized)
    }

    fn specialized_principal_type(
        &self,
        principal: &KotlinType,
        requirement: &KotlinType,
        relations: &KotlinTypeRelations<'_>,
    ) -> Option<KotlinType> {
        if Self::has_source_specific_type(principal) || !Self::has_source_specific_type(requirement)
        {
            return None;
        }
        let principal_erasure = self.indexed_erased_type(principal)?;
        let requirement_erasure = self.indexed_erased_type(requirement);
        let specialized = if requirement_erasure.as_ref() == Some(&principal_erasure) {
            requirement.clone()
        } else {
            self.generic_projection.and_then(|projection| {
                projection
                    .specialize_subtype(&principal_erasure, requirement)
                    .or_else(|| projection.infer_subtype(&principal_erasure, requirement))
            })?
        };
        (self.indexed_erased_type(&specialized) == Some(principal_erasure)
            && self.source_type_is_well_formed(&specialized)
            && relations.is_assignable(&specialized, requirement))
        .then_some(specialized)
    }

    fn definitions_preserve_runtime_type(&self, variable: u32, target: &KotlinType) -> bool {
        let mut definitions = self
            .equations_for_fact(SourceTypeFact::Variable(variable))
            .peekable();
        definitions.peek().is_some()
            && definitions.all(|equation| {
                self.erased_conversion_preserves_runtime_type(&equation.value, target)
            })
    }

    fn definitions_fit(
        &self,
        variable: u32,
        requirement: &KotlinType,
        relations: &KotlinTypeRelations<'_>,
    ) -> bool {
        if self.verifier_join_fits(variable, requirement) {
            return true;
        }
        let needs_target_evidence = Self::has_source_specific_type(requirement)
            && self.states.get(&variable).is_some_and(|state| match state {
                TypeState::Exact(current) => {
                    Self::has_source_specific_type(current)
                        && !relations.is_assignable(current, requirement)
                }
                TypeState::Conflict => false,
            });
        let mut definitions = self
            .equations_for_fact(SourceTypeFact::Variable(variable))
            .peekable();
        if definitions.peek().is_none() {
            return false;
        }
        let mut target_evidence = false;
        let fits = definitions.all(|equation| {
            let accepts_target = self.expression_accepts_target(&equation.value, requirement);
            target_evidence |= accepts_target;
            self.expression_fits(&equation.value, requirement, relations)
                || accepts_target
                || self.erased_reference_result_fits(equation, requirement)
        });
        fits && (!needs_target_evidence || target_evidence)
    }

    fn verifier_join_fits(&self, variable: u32, requirement: &KotlinType) -> bool {
        if Self::has_source_specific_type(requirement) {
            return false;
        }
        let Some(target) = self
            .indexed_erased_type(requirement)
            .filter(ArgType::is_reference)
        else {
            return false;
        };
        let definitions = self
            .equations_for_fact(SourceTypeFact::Variable(variable))
            .collect::<Vec<_>>();
        let exact_join = definitions
            .iter()
            .any(|equation| equation.result.ty == target);
        let edge_join = target.as_object().is_some()
            && definitions.iter().any(|equation| {
                equation
                    .value
                    .as_operation()
                    .is_some_and(|operation| operation.payload.edge_copy)
            });
        let constrained_join = target.as_object().is_some()
            && definitions.len() > 1
            && definitions.iter().all(|equation| {
                SsaVar::from_reg(&equation.result).is_some_and(|value| {
                    self.value_requirements
                        .get(&value)
                        .or_else(|| self.receiver_value_requirements.get(&value))
                        .is_some_and(|state| match state {
                            TypeState::Exact(ty) => {
                                self.indexed_erased_type(ty) == Some(target.clone())
                            }
                            TypeState::Conflict => false,
                        })
                })
            });
        (exact_join
            && definitions
                .iter()
                .all(|equation| self.expression_is_reference(&equation.value)))
            || constrained_join
            || (edge_join
                && definitions
                    .iter()
                    .all(|equation| self.expression_fits_object_join(&equation.value, &target)))
    }

    fn expression_fits_object_join(
        &self,
        expression: &SemanticExpression,
        target: &ArgType,
    ) -> bool {
        if Self::constant(expression) == Some(0) {
            return true;
        }
        match expression {
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                self.expression_fits_object_join(when_true, target)
                    && self.expression_fits_object_join(when_false, target)
            }
            SemanticExpression::Operation(operation) if operation.insn_type == InsnType::Move => {
                operation
                    .operands()
                    .first()
                    .is_some_and(|operand| self.expression_fits_object_join(operand, target))
            }
            expression => self
                .expression_type(expression)
                .and_then(|ty| self.indexed_erased_type(&ty))
                .is_some_and(|source| match source {
                    ArgType::Object(_) => {
                        source == *target
                            || self
                                .generic_projection
                                .is_some_and(|projection| projection.is_subtype(&source, target))
                    }
                    ArgType::Array(_) => matches!(
                        target.as_object(),
                        Some("java/lang/Object" | "java/lang/Cloneable" | "java/io/Serializable")
                    ),
                    ArgType::Primitive(_) | ArgType::Unknown(_) => false,
                }),
        }
    }

    fn value_erasure_is_strict_subtype(&self, value: SsaVar, target: &KotlinType) -> bool {
        let Some(equation) = self.equations_for_fact(SourceTypeFact::Value(value)).next() else {
            return false;
        };
        self.erasure_is_strict_subtype(&equation.result.ty, target)
    }

    fn variable_erasures_are_strict_subtypes(&self, variable: u32, target: &KotlinType) -> bool {
        let mut definitions = self
            .equations_for_fact(SourceTypeFact::Variable(variable))
            .peekable();
        definitions.peek().is_some()
            && definitions
                .all(|equation| self.erasure_is_strict_subtype(&equation.result.ty, target))
    }

    fn erasure_is_strict_subtype(&self, source: &ArgType, target: &KotlinType) -> bool {
        let Some(target) = self.indexed_erased_type(target) else {
            return false;
        };
        source != &target
            && self
                .generic_projection
                .is_some_and(|projection| projection.is_subtype(source, &target))
    }

    fn source_erasure_is_strict_subtype(&self, source: &KotlinType, target: &KotlinType) -> bool {
        let Some(source) = self.indexed_erased_type(source) else {
            return false;
        };
        self.erasure_is_strict_subtype(&source, target)
    }

    fn expression_accepts_target(
        &self,
        expression: &SemanticExpression,
        target: &KotlinType,
    ) -> bool {
        if self.erased_conversion_preserves_runtime_type(expression, target) {
            let source = self.expression_type(expression);
            let source_has_generic_evidence =
                source.as_ref().is_some_and(Self::has_source_specific_type);
            let source_is_assignable = source.as_ref().is_some_and(|source| {
                KotlinTypeRelations::new(
                    self.source_types,
                    self.type_variable_erasures,
                    self.generic_projection,
                )
                .with_erasure_index(Some(self.source_erasures.as_ref()))
                .is_assignable(source, target)
            });
            if !source_has_generic_evidence || source_is_assignable {
                return true;
            }
        }
        match expression {
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                self.expression_accepts_target(when_true, target)
                    && self.expression_accepts_target(when_false, target)
            }
            SemanticExpression::Operation(operation)
                if matches!(operation.insn_type, InsnType::Move | InsnType::CheckCast) =>
            {
                operation
                    .operands()
                    .first()
                    .is_some_and(|operand| self.expression_accepts_target(operand, target))
            }
            SemanticExpression::Operation(operation)
                if operation.insn_type == InsnType::Constructor =>
            {
                let Some(owner) =
                    operation
                        .payload
                        .reference
                        .as_ref()
                        .and_then(|reference| match reference {
                            MemberReference::Method(method) => Some(&method.owner),
                            MemberReference::Field(_) => None,
                        })
                else {
                    return false;
                };
                let target_erasure = self.indexed_erased_type(target);
                self.source_type_is_well_formed(target)
                    && (target_erasure.as_ref() == Some(owner)
                        || self.generic_projection.is_some_and(|projection| {
                            projection.specialize_subtype(owner, target).is_some()
                        }))
            }
            SemanticExpression::Operation(operation)
                if matches!(
                    operation.insn_type,
                    InsnType::NewArray | InsnType::FilledNewArray
                ) =>
            {
                self.array_allocation_accepts_target(operation, target)
            }
            SemanticExpression::Operation(operation) if operation.insn_type == InsnType::Invoke => {
                let Some((mut solver, arguments, contract)) = self.invocation_solver(operation)
                else {
                    return false;
                };
                let result = invocation_expression_signature(operation, contract);
                let return_depends_on_type_variables =
                    GenericInvocationCompatibility::has_type_variable(result.as_ref());
                let raw_owner_affects_return =
                    solver.owner_is_raw(&contract.owner) && return_depends_on_type_variables;
                let unchecked_input_affects_return = return_depends_on_type_variables
                    && contract
                        .signature
                        .parameter_types
                        .iter()
                        .zip(arguments)
                        .any(|(formal, actual)| {
                            self.expression_type(actual).is_some_and(|actual| {
                                GenericInvocationCompatibility::requires_unchecked_conversion(
                                    formal,
                                    &actual,
                                    contract,
                                    self.source_types,
                                )
                            })
                        });
                if raw_owner_affects_return || unchecked_input_affects_return {
                    return false;
                }
                solver.constrain_context(&contract.signature.return_type, target);
                let Some(output) = solver.instantiate(result.as_ref()) else {
                    return false;
                };
                KotlinTypeRelations::new(
                    self.source_types,
                    self.type_variable_erasures,
                    self.generic_projection,
                )
                .with_erasure_index(Some(self.source_erasures.as_ref()))
                .is_assignable(&output, target)
            }
            SemanticExpression::Register(_)
            | SemanticExpression::Literal(_)
            | SemanticExpression::Operation(_) => false,
        }
    }

    fn erased_reference_result_fits(
        &self,
        equation: &TypeEquation,
        requirement: &KotlinType,
    ) -> bool {
        let definition_has_generic_evidence = SsaVar::from_reg(&equation.result)
            .and_then(|value| self.value_definition_states.get(&value))
            .or_else(|| {
                equation
                    .result
                    .code_var
                    .and_then(|variable| self.definition_states.get(&variable))
            })
            .is_some_and(|state| match state {
                TypeState::Exact(ty) => Self::has_source_specific_type(ty),
                TypeState::Conflict => false,
            });
        if definition_has_generic_evidence {
            return false;
        }
        let Some(required_erasure) = self.indexed_erased_type(requirement) else {
            return false;
        };
        let exact_erasure = equation.result.ty == required_erasure;
        (!Self::has_source_specific_type(requirement) || exact_erasure)
            && exact_erasure
            && required_erasure.is_reference()
            && self.expression_is_reference(&equation.value)
    }

    fn expression_is_reference(&self, expression: &SemanticExpression) -> bool {
        if Self::constant(expression) == Some(0) {
            return true;
        }
        match expression {
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                self.expression_is_reference(when_true) && self.expression_is_reference(when_false)
            }
            expression if Self::is_null(expression) => true,
            SemanticExpression::Register(register) => Self::is_reference_domain(&register.ty),
            SemanticExpression::Operation(operation) if operation.insn_type == InsnType::Move => {
                operation
                    .operands()
                    .first()
                    .is_some_and(|operand| self.expression_is_reference(operand))
            }
            SemanticExpression::Operation(operation) => operation
                .result
                .as_ref()
                .is_some_and(|result| Self::is_reference_domain(&result.ty)),
            SemanticExpression::Literal(_) => false,
        }
    }

    fn is_reference_domain(ty: &ArgType) -> bool {
        ty.is_reference()
            || matches!(
                ty,
                ArgType::Unknown(types)
                    if types
                        .iter()
                        .all(|ty| matches!(ty, PrimitiveType::Object | PrimitiveType::Array))
            )
    }

    fn array_allocation_accepts_target(
        &self,
        operation: &SemanticOperation,
        target: &KotlinType,
    ) -> bool {
        let KotlinType::Array(_) = target else {
            return false;
        };
        let Some(target) = self.indexed_erased_type(target) else {
            return false;
        };
        operation.payload.class_type.as_ref() == Some(&target)
            || operation
                .result
                .as_ref()
                .is_some_and(|result| result.ty == target)
    }

    fn erased_conversion_preserves_runtime_type(
        &self,
        expression: &SemanticExpression,
        target: &KotlinType,
    ) -> bool {
        if !Self::has_source_specific_type(target) {
            return false;
        }
        let Some(source) = self.expression_type(expression) else {
            return false;
        };
        let source = self.indexed_erased_type(&source);
        let target = self.indexed_erased_type(target);
        source.zip(target).is_some_and(|(source, target)| {
            source.is_reference()
                && target.is_reference()
                && (source == target
                    || self
                        .generic_projection
                        .is_some_and(|projection| projection.is_subtype(&source, &target)))
        })
    }

    fn expression_fits(
        &self,
        expression: &SemanticExpression,
        requirement: &KotlinType,
        relations: &KotlinTypeRelations<'_>,
    ) -> bool {
        if requirement == &KotlinType::boolean()
            && self.boolean_storage_expression(expression, &mut BTreeSet::new())
        {
            return true;
        }
        match expression {
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                self.expression_fits(when_true, requirement, relations)
                    && self.expression_fits(when_false, requirement, relations)
            }
            expression if Self::is_null(expression) => true,
            expression => self
                .expression_type(expression)
                .is_some_and(|ty| relations.is_assignable(&ty, requirement)),
        }
    }

    fn constrain_boolean_predicates(&mut self) {
        let Some(boolean) = self.resolved_type(&ArgType::BOOLEAN) else {
            return;
        };
        for test in self.predicate_tests.clone() {
            if !matches!(
                test.payload.if_op,
                Some(crate::ir::IfOp::Eq | crate::ir::IfOp::Ne)
            ) {
                continue;
            }
            let [left, right] = test.operands() else {
                continue;
            };
            let value = if matches!(Self::constant(right), Some(0) | Some(1)) {
                left
            } else if matches!(Self::constant(left), Some(0) | Some(1)) {
                right
            } else {
                continue;
            };
            if self.boolean_storage_expression(value, &mut BTreeSet::new())
                && self.boolean_evidence(value, &mut BTreeSet::new())
            {
                self.constrain_expression_context(value, boolean.clone());
            }
        }
    }

    fn constrain_runtime_type_tests(&mut self) {
        let tests = self.runtime_type_tests.clone();
        for operation in tests {
            let Some(value) = operation.operands().first() else {
                continue;
            };
            let target = match operation.insn_type {
                InsnType::InstanceOf => operation.payload.class_type.as_ref(),
                InsnType::CheckCast => operation.conversion_type(),
                _ => None,
            };
            let Some((target_erasure, target)) =
                target.and_then(|target| self.resolved_type(target).map(|source| (target, source)))
            else {
                continue;
            };
            let Some(principal) = self.expression_principal_type(value) else {
                continue;
            };
            let Some(principal_erasure) = self.indexed_erased_type(&principal) else {
                continue;
            };
            let cast_convertible = self.generic_projection.is_none_or(|projection| {
                projection.is_cast_convertible(&principal_erasure, target_erasure)
            });
            if cast_convertible {
                continue;
            }
            let declaration = Self::least_common_source_type(
                self.source_types,
                self.type_variable_erasures,
                self.generic_projection,
                &principal,
                &target,
            );
            if let Some(declaration) = declaration {
                self.constrain_expression_with(value, declaration, TypeConstraintKind::Declaration);
            }
        }
    }

    fn boolean_storage_expression(
        &self,
        expression: &SemanticExpression,
        visiting: &mut BTreeSet<(Option<SsaVar>, Option<u32>)>,
    ) -> bool {
        if self.expression_type(expression) == Some(KotlinType::boolean()) {
            return true;
        }
        match expression {
            SemanticExpression::Literal(_) => {
                matches!(Self::constant(expression), Some(0) | Some(1))
            }
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                self.boolean_storage_expression(when_true, visiting)
                    && self.boolean_storage_expression(when_false, visiting)
            }
            SemanticExpression::Operation(operation)
                if matches!(operation.insn_type, InsnType::Const | InsnType::Move) =>
            {
                operation
                    .operands()
                    .first()
                    .is_some_and(|value| self.boolean_storage_expression(value, visiting))
            }
            SemanticExpression::Operation(operation)
                if operation.insn_type == InsnType::Arith
                    && matches!(
                        operation.payload.arith_op,
                        Some(
                            crate::ir::ArithOp::And
                                | crate::ir::ArithOp::Or
                                | crate::ir::ArithOp::Xor
                        )
                    ) =>
            {
                operation.operands().len() == 2
                    && operation
                        .operands()
                        .iter()
                        .all(|value| self.boolean_storage_expression(value, visiting))
            }
            SemanticExpression::Operation(operation) => operation
                .result
                .as_ref()
                .is_some_and(|result| result.ty == ArgType::BOOLEAN),
            SemanticExpression::Register(register) => {
                register.ty == ArgType::BOOLEAN
                    || self.register_definition_property(
                        register,
                        visiting,
                        |flow, value, visiting| flow.boolean_storage_expression(value, visiting),
                    )
            }
        }
    }

    fn boolean_evidence(
        &self,
        expression: &SemanticExpression,
        visiting: &mut BTreeSet<(Option<SsaVar>, Option<u32>)>,
    ) -> bool {
        if self.expression_type(expression) == Some(KotlinType::boolean()) {
            return true;
        }
        match expression {
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                self.boolean_evidence(when_true, visiting)
                    || self.boolean_evidence(when_false, visiting)
            }
            SemanticExpression::Operation(operation) => {
                operation
                    .result
                    .as_ref()
                    .is_some_and(|result| result.ty == ArgType::BOOLEAN)
                    || operation
                        .payload
                        .reference
                        .as_ref()
                        .and_then(|reference| match reference {
                            MemberReference::Method(method) => Some(&method.descriptor.return_type),
                            MemberReference::Field(field) => Some(&field.field_type),
                        })
                        == Some(&ArgType::BOOLEAN)
            }
            SemanticExpression::Register(register) => {
                register.ty == ArgType::BOOLEAN
                    || self.register_definition_property(
                        register,
                        visiting,
                        |flow, value, visiting| flow.boolean_evidence(value, visiting),
                    )
            }
            SemanticExpression::Literal(_) => false,
        }
    }

    fn register_definition_property(
        &self,
        register: &RegisterArg,
        visiting: &mut BTreeSet<(Option<SsaVar>, Option<u32>)>,
        property: impl Fn(&Self, &SemanticExpression, &mut BTreeSet<(Option<SsaVar>, Option<u32>)>) -> bool
            + Copy,
    ) -> bool {
        let identity = SsaVar::from_reg(register);
        let key = (identity, register.code_var);
        if !visiting.insert(key) {
            return false;
        }
        let fact = identity
            .map(SourceTypeFact::Value)
            .or_else(|| register.code_var.map(SourceTypeFact::Variable));
        let mut definitions = fact
            .into_iter()
            .flat_map(|fact| self.equations_for_fact(fact));
        let result = definitions.next().is_some_and(|first| {
            property(self, &first.value, visiting)
                && definitions.all(|equation| property(self, &equation.value, visiting))
        });
        visiting.remove(&key);
        result
    }

    fn merge_state<K: Ord>(
        source_types: &BTreeMap<ArgType, KotlinType>,
        type_variable_erasures: &BTreeMap<KotlinIdentifier, ArgType>,
        generic_projection: Option<&dyn GenericTypeProjection>,
        states: &mut BTreeMap<K, TypeState>,
        identity: K,
        incoming: KotlinType,
    ) -> bool {
        match states.get(&identity) {
            None => {
                states.insert(identity, TypeState::Exact(incoming));
                true
            }
            Some(TypeState::Exact(current)) if current == &incoming => false,
            Some(TypeState::Exact(current)) => {
                let next = Self::reconcile_types(
                    source_types,
                    type_variable_erasures,
                    generic_projection,
                    current,
                    &incoming,
                )
                .map(TypeState::Exact)
                .unwrap_or(TypeState::Conflict);
                if states.get(&identity) == Some(&next) {
                    false
                } else {
                    states.insert(identity, next);
                    true
                }
            }
            Some(TypeState::Conflict) => false,
        }
    }

    fn join_type_state(
        source_types: &BTreeMap<ArgType, KotlinType>,
        type_variable_erasures: &BTreeMap<KotlinIdentifier, ArgType>,
        generic_projection: Option<&dyn GenericTypeProjection>,
        current: Option<&TypeState>,
        incoming: KotlinType,
    ) -> TypeState {
        match current {
            None => TypeState::Exact(incoming),
            Some(TypeState::Exact(current)) if current == &incoming => TypeState::Exact(incoming),
            Some(TypeState::Exact(current)) => Self::least_common_source_type(
                source_types,
                type_variable_erasures,
                generic_projection,
                current,
                &incoming,
            )
            .map(TypeState::Exact)
            .unwrap_or(TypeState::Conflict),
            Some(TypeState::Conflict) => TypeState::Conflict,
        }
    }

    fn merge_requirement<K: Ord>(
        source_types: &BTreeMap<ArgType, KotlinType>,
        type_variable_erasures: &BTreeMap<KotlinIdentifier, ArgType>,
        generic_projection: Option<&dyn GenericTypeProjection>,
        requirements: &mut BTreeMap<K, TypeState>,
        identity: K,
        incoming: KotlinType,
    ) -> bool {
        let next = match requirements.get(&identity) {
            None => TypeState::Exact(incoming),
            Some(TypeState::Exact(current)) if current == &incoming => return false,
            Some(TypeState::Exact(current)) => {
                let current_erasure =
                    Self::erased_type(source_types, type_variable_erasures, current);
                let incoming_erasure =
                    Self::erased_type(source_types, type_variable_erasures, &incoming);
                let same_arguments = Self::same_type_arguments(current, &incoming);
                let current_is_subtype = same_arguments
                    && generic_projection.is_some_and(|projection| {
                        current_erasure
                            .as_ref()
                            .zip(incoming_erasure.as_ref())
                            .is_some_and(|(current, incoming)| {
                                projection.is_subtype(current, incoming)
                            })
                    });
                let incoming_is_subtype = same_arguments
                    && generic_projection.is_some_and(|projection| {
                        incoming_erasure
                            .as_ref()
                            .zip(current_erasure.as_ref())
                            .is_some_and(|(incoming, current)| {
                                projection.is_subtype(incoming, current)
                            })
                    });
                if current_is_subtype && !incoming_is_subtype {
                    return false;
                }
                let same_erasure = current_erasure == incoming_erasure;
                let current_symbolic = Self::contains_type_variable(current);
                let incoming_symbolic = Self::contains_type_variable(&incoming);
                let refined = same_erasure
                    .then(|| {
                        GenericTypeEvidence::reconcile_type(
                            current,
                            &incoming,
                            source_types.get(&ArgType::object("java/lang/Object")),
                        )
                    })
                    .flatten()
                    .filter(|ty| Self::type_is_well_formed(ty, type_variable_erasures));
                if incoming_is_subtype && !current_is_subtype {
                    TypeState::Exact(incoming)
                } else if let Some(refined) = refined {
                    if &refined == current {
                        return false;
                    }
                    TypeState::Exact(refined)
                } else if same_erasure && !current_symbolic && incoming_symbolic {
                    TypeState::Exact(incoming)
                } else if same_erasure && current_symbolic && !incoming_symbolic {
                    return false;
                } else {
                    let relations = KotlinTypeRelations::new(
                        source_types,
                        type_variable_erasures,
                        generic_projection,
                    );
                    let incoming_to_current = relations.is_assignable(&incoming, current);
                    let current_to_incoming = relations.is_assignable(current, &incoming);
                    match (incoming_to_current, current_to_incoming) {
                        (true, true)
                            if !Self::has_source_specific_type(current)
                                && Self::has_source_specific_type(&incoming) =>
                        {
                            TypeState::Exact(incoming)
                        }
                        (true, false) => TypeState::Exact(incoming),
                        (false, true) | (true, true) => return false,
                        (false, false) => TypeState::Conflict,
                    }
                }
            }
            Some(TypeState::Conflict) => return false,
        };
        requirements.insert(identity, next);
        true
    }

    fn merge_receiver_requirement<K: Ord>(
        source_types: &BTreeMap<ArgType, KotlinType>,
        type_variable_erasures: &BTreeMap<KotlinIdentifier, ArgType>,
        generic_projection: Option<&dyn GenericTypeProjection>,
        requirements: &mut BTreeMap<K, TypeState>,
        identity: K,
        incoming: KotlinType,
    ) -> bool {
        Self::merge_requirement(
            source_types,
            type_variable_erasures,
            generic_projection,
            requirements,
            identity,
            incoming,
        )
    }

    fn contains_type_variable(ty: &KotlinType) -> bool {
        match ty {
            KotlinType::Variable(_) => true,
            KotlinType::Array(element) => Self::contains_type_variable(element),
            KotlinType::Class(class) => class.segments.iter().any(|segment| {
                segment.arguments.iter().any(|argument| match argument {
                    KotlinTypeArgument::Any => false,
                    KotlinTypeArgument::Exact(ty)
                    | KotlinTypeArgument::Extends(ty)
                    | KotlinTypeArgument::Super(ty) => Self::contains_type_variable(ty),
                })
            }),
            KotlinType::Primitive(_) => false,
        }
    }

    fn same_type_arguments(left: &KotlinType, right: &KotlinType) -> bool {
        let (KotlinType::Class(left), KotlinType::Class(right)) = (left, right) else {
            return false;
        };
        left.segments
            .iter()
            .flat_map(|segment| &segment.arguments)
            .eq(right.segments.iter().flat_map(|segment| &segment.arguments))
    }

    fn merge_constraint<K: Ord>(
        source_types: &BTreeMap<ArgType, KotlinType>,
        type_variable_erasures: &BTreeMap<KotlinIdentifier, ArgType>,
        generic_projection: Option<&dyn GenericTypeProjection>,
        states: &mut BTreeMap<K, TypeState>,
        identity: K,
        incoming: KotlinType,
        kind: TypeConstraintKind,
    ) -> bool {
        if kind == TypeConstraintKind::Definition {
            return Self::merge_state(
                source_types,
                type_variable_erasures,
                generic_projection,
                states,
                identity,
                incoming,
            );
        }
        let replace = match states.get(&identity) {
            None => true,
            Some(TypeState::Conflict) => false,
            Some(TypeState::Exact(current)) => {
                let relations = KotlinTypeRelations::new(
                    source_types,
                    type_variable_erasures,
                    generic_projection,
                );
                !relations.is_assignable(current, &incoming)
                    && !Self::has_source_specific_type(current)
                    && Self::has_source_specific_type(&incoming)
            }
        };
        if replace {
            states.insert(identity, TypeState::Exact(incoming));
        }
        replace
    }

    fn reconcile_types(
        source_types: &BTreeMap<ArgType, KotlinType>,
        type_variable_erasures: &BTreeMap<KotlinIdentifier, ArgType>,
        generic_projection: Option<&dyn GenericTypeProjection>,
        left: &KotlinType,
        right: &KotlinType,
    ) -> Option<KotlinType> {
        if left == right {
            return Some(left.clone());
        }
        if let (KotlinType::Array(left), KotlinType::Array(right)) = (left, right) {
            return Self::reconcile_types(
                source_types,
                type_variable_erasures,
                generic_projection,
                left,
                right,
            )
            .map(KotlinType::array);
        }
        let left_erased = Self::erased_type(source_types, type_variable_erasures, left)?;
        let right_erased = Self::erased_type(source_types, type_variable_erasures, right)?;
        if left_erased == right_erased {
            match (
                Self::has_source_specific_type(left),
                Self::has_source_specific_type(right),
            ) {
                (true, false) if Self::type_is_well_formed(left, type_variable_erasures) => {
                    return Some(left.clone());
                }
                (false, true) if Self::type_is_well_formed(right, type_variable_erasures) => {
                    return Some(right.clone());
                }
                _ => {}
            }
            if let Some(merged) = GenericTypeEvidence::join_type(
                left,
                right,
                source_types.get(&ArgType::object("java/lang/Object")),
            )
            .filter(|merged| Self::type_is_well_formed(merged, type_variable_erasures))
            {
                return Some(merged);
            }
            return match (
                Self::has_source_specific_type(left)
                    && Self::type_is_well_formed(left, type_variable_erasures),
                Self::has_source_specific_type(right)
                    && Self::type_is_well_formed(right, type_variable_erasures),
            ) {
                (true, false) => Some(left.clone()),
                (false, true) => Some(right.clone()),
                _ => None,
            };
        }
        if let Some(projection) = generic_projection {
            if projection.is_subtype(&left_erased, &right_erased) {
                return Some(right.clone());
            }
            if projection.is_subtype(&right_erased, &left_erased) {
                return Some(left.clone());
            }
            if let Some(projected) =
                projection
                    .project_supertype(left, &right_erased)
                    .filter(|projected| {
                        Self::erased_type(source_types, type_variable_erasures, projected).as_ref()
                            == Some(&right_erased)
                    })
            {
                let reconciled = Self::reconcile_types(
                    source_types,
                    type_variable_erasures,
                    generic_projection,
                    &projected,
                    right,
                );
                return reconciled
                    .filter(|ty| Self::type_is_well_formed(ty, type_variable_erasures))
                    .or_else(|| {
                        Self::type_is_well_formed(right, type_variable_erasures)
                            .then(|| right.clone())
                    });
            }
            if let Some(projected) =
                projection
                    .project_supertype(right, &left_erased)
                    .filter(|projected| {
                        Self::erased_type(source_types, type_variable_erasures, projected).as_ref()
                            == Some(&left_erased)
                    })
            {
                let reconciled = Self::reconcile_types(
                    source_types,
                    type_variable_erasures,
                    generic_projection,
                    left,
                    &projected,
                );
                return reconciled
                    .filter(|ty| Self::type_is_well_formed(ty, type_variable_erasures))
                    .or_else(|| {
                        Self::type_is_well_formed(left, type_variable_erasures)
                            .then(|| left.clone())
                    });
            }
            if let Some(common) = projection.least_common_supertype(&left_erased, &right_erased) {
                let left = projection
                    .project_supertype(left, &common)
                    .filter(|ty| Self::type_is_well_formed(ty, type_variable_erasures));
                let right = projection
                    .project_supertype(right, &common)
                    .filter(|ty| Self::type_is_well_formed(ty, type_variable_erasures));
                if let (Some(left), Some(right)) = (left, right) {
                    if let Some(joined) = Self::reconcile_types(
                        source_types,
                        type_variable_erasures,
                        generic_projection,
                        &left,
                        &right,
                    ) {
                        return Some(joined);
                    }
                }
                return source_types
                    .get(&common)
                    .cloned()
                    .or_else(|| projection.resolve_type(&common));
            }
        }
        let object = ArgType::object("java/lang/Object");
        match (left_erased == object, right_erased == object) {
            (true, false) if right_erased.is_reference() => Some(right.clone()),
            (false, true) if left_erased.is_reference() => Some(left.clone()),
            _ => None,
        }
    }

    fn erased_type(
        source_types: &BTreeMap<ArgType, KotlinType>,
        type_variable_erasures: &BTreeMap<KotlinIdentifier, ArgType>,
        ty: &KotlinType,
    ) -> Option<ArgType> {
        match ty {
            KotlinType::Array(element) => Some(ArgType::array(Self::erased_type(
                source_types,
                type_variable_erasures,
                element,
            )?)),
            KotlinType::Class(class) => source_types.iter().find_map(|(erased, source)| {
                let KotlinType::Class(source) = source else {
                    return None;
                };
                (source.name() == class.name()).then(|| erased.clone())
            }),
            KotlinType::Variable(variable) => type_variable_erasures
                .get(variable)
                .cloned()
                .or_else(|| Some(ArgType::object("java/lang/Object"))),
            KotlinType::Primitive(_) => source_types
                .iter()
                .find_map(|(erased, source)| (source == ty).then(|| erased.clone())),
        }
    }

    fn erased_source_type(&self, ty: &KotlinType) -> Option<ArgType> {
        self.indexed_erased_type(ty).or_else(|| {
            self.generic_projection
                .and_then(|projection| projection.erasure_of(ty))
        })
    }

    fn indexed_erased_type(&self, ty: &KotlinType) -> Option<ArgType> {
        self.source_erasures
            .erasure_of(ty, self.type_variable_erasures)
    }

    fn constrain_invocation(&mut self, operation: &SemanticOperation) -> bool {
        let Some(MemberReference::Method(method)) = operation.payload.reference.as_ref() else {
            return false;
        };
        let operand_receiver = Self::operand_receiver(operation);
        let source_receiver = Self::source_receiver(operation);
        let generic = self.invocation_solver(operation);
        let receiver_is_refinable =
            operation
                .operands()
                .first()
                .is_some_and(|receiver| match receiver {
                    SemanticExpression::Register(register) => register
                        .code_var
                        .is_none_or(|variable| !self.fixed.contains(&variable)),
                    SemanticExpression::Operation(_) | SemanticExpression::Select { .. } => true,
                    SemanticExpression::Literal(_) => false,
                });
        let receiver_has_evidence = operation
            .operands()
            .first()
            .and_then(|receiver| self.expression_principal_type(receiver))
            .is_some_and(|receiver| self.has_generic_argument_evidence(&receiver))
            || operation
                .operands()
                .first()
                .is_some_and(|receiver| self.expression_declares_concrete_generic_type(receiver));
        let argument_owner = (receiver_is_refinable && !receiver_has_evidence)
            .then(|| {
                generic.as_ref().and_then(|(_, _, contract)| {
                    self.owner_inferred_from_arguments(operation, contract)
                })
            })
            .flatten();
        let mut changed = if source_receiver {
            let receiver = operation.operands().first();
            receiver
                .and_then(|receiver| {
                    argument_owner
                        .clone()
                        // An owner reconstructed from this receiver is not an
                        // independent backward constraint. Feeding it back
                        // creates a recursive type equation for fluent APIs.
                        .or_else(|| self.resolved_type(&method.owner))
                        .map(|expected| (receiver, expected))
                })
                .is_some_and(|(receiver, expected)| {
                    self.constrain_expression_receiver(receiver, expected)
                })
        } else {
            false
        };
        let constraints = if let Some((solver, arguments, contract)) = generic {
            let expected = contract
                .signature
                .parameter_types
                .iter()
                .zip(&method.descriptor.parameters)
                .zip(arguments.iter().copied())
                .filter_map(|((formal, erased), actual)| {
                    solver
                        .invocation_input_type(formal)
                        .or_else(|| self.resolved_type(erased))
                        .map(|expected| (actual.clone(), expected))
                });
            contract
                .signature
                .parameter_types
                .iter()
                .zip(arguments.iter().copied())
                .flat_map(|(formal, actual)| {
                    self.poly_argument_constraints(&solver, formal, actual)
                })
                .chain(expected)
                .collect::<Vec<_>>()
        } else {
            method
                .descriptor
                .parameters
                .iter()
                .zip(
                    operation
                        .operands()
                        .iter()
                        .skip(usize::from(operand_receiver)),
                )
                .filter_map(|(erased, actual)| {
                    self.resolved_type(erased)
                        .map(|expected| (actual.clone(), expected))
                })
                .collect::<Vec<_>>()
        };
        changed |= constraints
            .into_iter()
            .fold(false, |changed, (actual, expected)| {
                self.constrain_expression_context(&actual, expected) || changed
            });
        changed
    }

    fn owner_inferred_from_arguments(
        &self,
        operation: &SemanticOperation,
        contract: &GenericMethodContract,
    ) -> Option<KotlinType> {
        if operation.payload.invoke_type == Some(crate::ir::InvokeType::Static) {
            return None;
        }
        let method = match operation.payload.reference.as_ref()? {
            MemberReference::Method(method) => method,
            MemberReference::Field(_) => return None,
        };
        let mut solver = self.solver(&contract.owner, &contract.signature.type_parameters);
        for ((formal, erased), actual) in contract
            .signature
            .parameter_types
            .iter()
            .zip(&method.descriptor.parameters)
            .zip(operation.operands().iter().skip(1))
        {
            self.constrain_invocation_argument(&mut solver, formal, erased, actual);
        }
        solver.complete_with_bounds(&contract.signature.type_parameters);
        solver
            .evidenced_owner_type(&contract.owner)
            .or_else(|| solver.argument_inferred_owner_type(&contract.owner))
    }

    fn invocation_solver<'operation>(
        &self,
        operation: &'operation SemanticOperation,
    ) -> Option<(
        GenericTypeSolver<'a>,
        Vec<&'operation SemanticExpression>,
        &'a GenericMethodContract,
    )> {
        let MemberReference::Method(method) = operation.payload.reference.as_ref()? else {
            return None;
        };
        let contract = self.generic_methods.get(method)?;
        let operand_receiver = Self::operand_receiver(operation);
        let source_receiver = Self::source_receiver(operation);
        let mut solver = self.solver(&contract.owner, &contract.signature.type_parameters);
        if source_receiver {
            let receiver = operation.operands().first()?;
            self.constrain_receiver_owner(&mut solver, &method.owner, &contract.owner, receiver);
        }
        let arguments = operation
            .operands()
            .iter()
            .skip(usize::from(operand_receiver))
            .collect::<Vec<_>>();
        for ((formal, erased), actual) in contract
            .signature
            .parameter_types
            .iter()
            .zip(&method.descriptor.parameters)
            .zip(arguments.iter().copied())
        {
            self.constrain_invocation_argument(&mut solver, formal, erased, actual);
        }
        if let Some(target) = operation
            .result
            .as_ref()
            .and_then(|result| self.result_requirement(result))
        {
            let result = invocation_expression_signature(operation, contract);
            solver.constrain_context(result.as_ref(), target);
        }
        Some((solver, arguments, contract))
    }

    fn result_requirement(&self, result: &RegisterArg) -> Option<&KotlinType> {
        let state = match result.code_var {
            Some(variable) => {
                let requirement = self
                    .requirements
                    .get(&variable)
                    .or_else(|| self.receiver_requirements.get(&variable))?;
                if self.erased_boundary_variables.contains(&variable)
                    && matches!(requirement, TypeState::Exact(ty) if Self::has_source_specific_type(ty))
                {
                    return None;
                }
                Some(requirement)
            }
            None => SsaVar::from_reg(result).and_then(|value| {
                self.value_requirements
                    .get(&value)
                    .or_else(|| self.receiver_value_requirements.get(&value))
            }),
        }?;
        match state {
            TypeState::Exact(target) => Some(target),
            TypeState::Conflict => None,
        }
    }

    fn expression_principal_type(&self, expression: &SemanticExpression) -> Option<KotlinType> {
        match expression {
            SemanticExpression::Register(register) => self.register_principal_type(register),
            SemanticExpression::Operation(operation) => operation
                .result
                .as_ref()
                .and_then(|result| self.register_principal_type(result))
                .or_else(|| {
                    matches!(operation.insn_type, InsnType::Move | InsnType::CheckCast)
                        .then(|| operation.operands().first())
                        .flatten()
                        .and_then(|operand| self.expression_principal_type(operand))
                }),
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                let left = self.expression_principal_type(when_true)?;
                let right = self.expression_principal_type(when_false)?;
                (left == right).then_some(left)
            }
            SemanticExpression::Literal(_) => None,
        }
    }

    fn register_principal_type(&self, register: &RegisterArg) -> Option<KotlinType> {
        if let Some(variable) = register
            .code_var
            .filter(|variable| self.abi_fixed.contains(variable))
        {
            return self.exact(variable).cloned();
        }
        SsaVar::from_reg(register)
            .and_then(|value| match self.value_definition_states.get(&value) {
                Some(TypeState::Exact(ty)) => Some(ty.clone()),
                Some(TypeState::Conflict) | None => None,
            })
            .or_else(|| {
                register.code_var.and_then(|variable| {
                    self.definition_states
                        .get(&variable)
                        .and_then(|state| match state {
                            TypeState::Exact(ty) => Some(ty.clone()),
                            TypeState::Conflict => None,
                        })
                })
            })
            .or_else(|| {
                register
                    .code_var
                    .and_then(|variable| self.value_principal_type(variable))
            })
    }

    fn has_generic_argument_evidence(&self, ty: &KotlinType) -> bool {
        let KotlinType::Class(class) = ty else {
            return Self::has_source_specific_type(ty);
        };
        class.segments.iter().any(|segment| {
            segment.arguments.iter().any(|argument| match argument {
                KotlinTypeArgument::Any => false,
                KotlinTypeArgument::Exact(value)
                | KotlinTypeArgument::Extends(value)
                | KotlinTypeArgument::Super(value) => self.type_argument_has_evidence(value),
            })
        })
    }

    fn expression_declares_concrete_generic_type(&self, expression: &SemanticExpression) -> bool {
        self.expression_has_declared_generic_type(expression, &mut BTreeSet::new())
    }

    fn expression_has_declared_generic_type(
        &self,
        expression: &SemanticExpression,
        visiting: &mut BTreeSet<(Option<SsaVar>, Option<u32>)>,
    ) -> bool {
        match expression {
            SemanticExpression::Register(register) => {
                self.register_definition_property(register, visiting, |flow, value, visiting| {
                    flow.expression_has_declared_generic_type(value, visiting)
                })
            }
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                self.expression_has_declared_generic_type(when_true, visiting)
                    && self.expression_has_declared_generic_type(when_false, visiting)
            }
            SemanticExpression::Operation(operation)
                if matches!(operation.insn_type, InsnType::Move | InsnType::CheckCast) =>
            {
                operation.operands().first().is_some_and(|operand| {
                    self.expression_has_declared_generic_type(operand, visiting)
                })
            }
            SemanticExpression::Operation(operation) => {
                let Some(reference) = operation.payload.reference.as_ref() else {
                    return false;
                };
                match reference {
                    MemberReference::Method(method)
                        if matches!(
                            operation.insn_type,
                            InsnType::Invoke | InsnType::Constructor
                        ) =>
                    {
                        self.generic_methods.get(method).is_some_and(|contract| {
                            GenericInvocationCompatibility::has_concrete_type_argument(
                                invocation_expression_signature(operation, contract).as_ref(),
                            )
                        })
                    }
                    MemberReference::Field(field)
                        if matches!(operation.insn_type, InsnType::Iget | InsnType::Sget) =>
                    {
                        self.generic_fields.get(field).is_some_and(|contract| {
                            GenericInvocationCompatibility::has_concrete_type_argument(
                                &contract.signature,
                            )
                        })
                    }
                    MemberReference::Method(_) | MemberReference::Field(_) => false,
                }
            }
            SemanticExpression::Literal(_) => false,
        }
    }

    fn type_argument_has_evidence(&self, ty: &KotlinType) -> bool {
        match ty {
            KotlinType::Variable(_) | KotlinType::Primitive(_) => true,
            KotlinType::Array(element) => self.type_argument_has_evidence(element),
            KotlinType::Class(class) => {
                let parameterized = class
                    .segments
                    .iter()
                    .any(|segment| !segment.arguments.is_empty());
                if parameterized {
                    self.has_generic_argument_evidence(ty)
                } else {
                    self.indexed_erased_type(ty) != Some(ArgType::object("java/lang/Object"))
                }
            }
        }
    }

    fn is_raw_generic_type(&self, ty: &KotlinType) -> bool {
        match ty {
            KotlinType::Array(element) => self.is_raw_generic_type(element),
            KotlinType::Class(class) => {
                let Some(erased) = self.indexed_erased_type(ty) else {
                    return false;
                };
                self.generic_projection
                    .and_then(|projection| projection.declared_type_parameters(&erased))
                    .is_some_and(|parameters| {
                        !parameters.is_empty()
                            && class
                                .segments
                                .last()
                                .is_some_and(|segment| segment.arguments.is_empty())
                    })
            }
            KotlinType::Variable(_) | KotlinType::Primitive(_) => false,
        }
    }

    fn solver(
        &self,
        owner: &ClassTypeSignature,
        parameters: &[TypeParameter],
    ) -> GenericTypeSolver<'a> {
        let solver = GenericTypeSolver::new(self.source_types)
            .with_erasure_index(Some(Arc::clone(&self.source_erasures)))
            .with_local_owner_variables(owner)
            .with_inference_variables(parameters)
            .with_lexical_scope(
                self.current_type,
                owner,
                self.type_variable_erasures,
                self.type_variable_bounds,
            )
            .with_projection(self.generic_projection);
        solver
    }

    fn constrain_receiver_owner(
        &self,
        solver: &mut GenericTypeSolver<'_>,
        erased_owner: &ArgType,
        owner: &ClassTypeSignature,
        receiver: &SemanticExpression,
    ) {
        let is_current_instance = self.this_variable.is_some_and(|this_variable| {
            receiver
                .as_register()
                .and_then(|receiver| receiver.code_var)
                == Some(this_variable)
        });
        if is_current_instance {
            if self.current_type == Some(erased_owner) {
                let declared_owner = JvmTypeSignature::ClassType(owner.clone()).erased();
                if &declared_owner == erased_owner {
                    solver.constrain_current_owner(owner);
                } else if let Some(projected) = self.source_current_type.and_then(|current| {
                    self.generic_projection.and_then(|projection| {
                        projection.project_supertype(current, &declared_owner)
                    })
                }) {
                    solver.constrain_owner(owner, &projected);
                }
            } else if let Some(projected) = self.source_current_type.and_then(|current| {
                self.generic_projection
                    .and_then(|projection| projection.project_supertype(current, erased_owner))
            }) {
                solver.constrain_owner(owner, &projected);
            }
            solver.assume_raw_owner_if_unbound(owner);
            return;
        }
        if let Some(actual) = self.expression_type(receiver) {
            solver.constrain_owner(owner, &actual);
        }
        solver.assume_raw_owner_if_unbound(owner);
    }

    fn field_type(
        &self,
        field: &FieldReference,
        receiver: Option<&SemanticExpression>,
    ) -> Option<KotlinType> {
        if let Some(contract) = self.generic_fields.get(field) {
            let mut solver = self.solver(&contract.owner, &[]);
            if let Some(receiver) = receiver {
                self.constrain_receiver_owner(&mut solver, &field.owner, &contract.owner, receiver);
            }
            if solver.owner_is_raw(&contract.owner) {
                return self.resolved_type(&field.field_type);
            }
            if let Some(ty) = solver.instantiate(&contract.signature) {
                return Some(ty);
            }
        }
        self.fields
            .get(field)
            .cloned()
            .or_else(|| self.resolved_type(&field.field_type))
    }

    fn constrain_invocation_argument(
        &self,
        solver: &mut GenericTypeSolver<'_>,
        formal: &JvmTypeSignature,
        erased_formal: &ArgType,
        expression: &SemanticExpression,
    ) {
        if erased_formal.is_reference() && Self::constant(expression) == Some(0) {
            return;
        }
        // A function-object construction is a poly expression: its target SAM
        // type is determined by the enclosing invocation. Its generated class
        // signature often contains only erased bridge types, which are not
        // valid inference evidence for the enclosing generic method.
        let direct = self
            .generic_argument_type(expression)
            .filter(|ty| !self.is_raw_generic_type(ty));
        if let SemanticExpression::Operation(operation) = expression {
            if let Some((mut nested, _, contract)) = self.invocation_solver(operation) {
                let result = invocation_expression_signature(operation, contract);
                GenericTypeRelation::converge(solver, formal, &mut nested, result.as_ref());
                if let Some(actual) = nested.instantiate(result.as_ref()) {
                    solver.constrain(formal, &actual);
                    if Self::has_source_specific_type(&actual) {
                        return;
                    }
                }
            }
        }
        if let Some(actual) = direct {
            solver.constrain(formal, &actual);
        }
    }

    fn generic_argument_type(&self, expression: &SemanticExpression) -> Option<KotlinType> {
        let value = expression
            .as_register()
            .or_else(|| {
                expression
                    .as_operation()
                    .and_then(|operation| operation.result.as_ref())
            })
            .and_then(SsaVar::from_reg);
        self.expression_type(expression)
            .or_else(|| {
                value.and_then(|value| match self.value_states.get(&value) {
                    Some(TypeState::Exact(ty)) => Some(ty.clone()),
                    Some(TypeState::Conflict) | None => None,
                })
            })
            .or_else(|| self.expression_principal_type(expression))
    }

    fn poly_argument_constraints(
        &self,
        parent: &GenericTypeSolver<'_>,
        parent_formal: &JvmTypeSignature,
        expression: &SemanticExpression,
    ) -> Vec<(SemanticExpression, KotlinType)> {
        let SemanticExpression::Operation(operation) = expression else {
            return Vec::new();
        };
        let Some((mut nested, arguments, contract)) = self.invocation_solver(operation) else {
            return Vec::new();
        };
        let mut parent = parent.clone();
        let result = invocation_expression_signature(operation, contract);
        GenericTypeRelation::converge(&mut parent, parent_formal, &mut nested, result.as_ref());
        let arguments = arguments.into_iter().cloned().collect::<Vec<_>>();
        let formals = contract.signature.parameter_types.clone();
        let mut constraints = formals
            .iter()
            .zip(&arguments)
            .filter_map(|(formal, actual)| {
                nested
                    .invocation_input_type(formal)
                    .map(|expected| (actual.clone(), expected))
            })
            .collect::<Vec<_>>();
        for (formal, actual) in formals.iter().zip(&arguments) {
            constraints.extend(self.poly_argument_constraints(&nested, formal, actual));
        }
        constraints
    }

    fn constrain_expression_context(
        &mut self,
        expression: &SemanticExpression,
        ty: KotlinType,
    ) -> bool {
        self.constrain_expression_with(expression, ty, TypeConstraintKind::Context)
    }

    fn constrain_expression_receiver(
        &mut self,
        expression: &SemanticExpression,
        ty: KotlinType,
    ) -> bool {
        self.constrain_expression_with(expression, ty, TypeConstraintKind::Receiver)
    }

    fn constrain_expression_with(
        &mut self,
        expression: &SemanticExpression,
        ty: KotlinType,
        kind: TypeConstraintKind,
    ) -> bool {
        match expression {
            SemanticExpression::Register(register) => {
                self.constrain_register_with(register, ty, kind)
            }
            SemanticExpression::Operation(operation) => {
                let mut changed = operation
                    .result
                    .as_ref()
                    .is_some_and(|result| self.constrain_register_with(result, ty.clone(), kind));
                if operation.insn_type == InsnType::Move {
                    changed |= operation
                        .operands()
                        .first()
                        .is_some_and(|operand| self.constrain_expression_with(operand, ty, kind));
                }
                changed
            }
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                let left = self.constrain_expression_with(when_true, ty.clone(), kind);
                self.constrain_expression_with(when_false, ty, kind) || left
            }
            SemanticExpression::Literal(_) => false,
        }
    }

    fn constrain_register(&mut self, register: &RegisterArg, ty: KotlinType) -> bool {
        self.constrain_register_with(register, ty, TypeConstraintKind::Definition)
    }

    fn constrain_register_with(
        &mut self,
        register: &RegisterArg,
        ty: KotlinType,
        kind: TypeConstraintKind,
    ) -> bool {
        if !self.source_type_is_well_formed(&ty) {
            return false;
        }
        let Some(erased) = self.erased_source_type(&ty) else {
            return false;
        };
        let object = ArgType::object("java/lang/Object");
        if erased == object
            && !Self::has_source_specific_type(&ty)
            && kind != TypeConstraintKind::Declaration
        {
            return false;
        }
        let value = SsaVar::from_reg(register);
        let definition_erasure = value
            .and_then(|value| self.value_erased_types.get(&value))
            .unwrap_or(&register.ty);
        let declared_erasure = if matches!(definition_erasure, ArgType::Unknown(_))
            && !matches!(register.ty, ArgType::Unknown(_))
        {
            &register.ty
        } else {
            definition_erasure
        };
        let unknown_reference = matches!(
            declared_erasure,
            ArgType::Unknown(types)
                if types
                    .iter()
                    .all(|ty| matches!(ty, PrimitiveType::Object | PrimitiveType::Array))
        );
        let ty = if let Some(function_type) = self.object_types.get(declared_erasure) {
            let same_function_interface = Self::erased_type(
                self.source_types,
                self.type_variable_erasures,
                function_type,
            ) == Some(erased.clone());
            if same_function_interface {
                GenericTypeEvidence::reconcile_type(
                    function_type,
                    &ty,
                    self.source_types.get(&ArgType::object("java/lang/Object")),
                )
                .unwrap_or_else(|| function_type.clone())
            } else {
                function_type.clone()
            }
        } else if kind != TypeConstraintKind::Definition
            && declared_erasure.is_reference()
            && erased.is_reference()
        {
            // A use constrains the capabilities required from a value. Keep
            // that target type intact; specializing it back to the verifier's
            // concrete register type loses the principal declaration type.
            // definitions_fit validates every reaching definition before the
            // requirement can replace the local's source type.
            ty
        } else if erased == *declared_erasure
            || (*declared_erasure == object && erased.is_reference() && erased != object)
            || (unknown_reference && erased.is_reference())
        {
            ty
        } else if kind != TypeConstraintKind::Definition
            && erased == ArgType::BOOLEAN
            && self.boolean_storage_expression(
                &SemanticExpression::Register(register.clone()),
                &mut BTreeSet::new(),
            )
        {
            ty
        } else if let Some(projected) = self
            .generic_projection
            .and_then(|projection| {
                projection
                    .specialize_subtype(declared_erasure, &ty)
                    .or_else(|| projection.infer_subtype(declared_erasure, &ty))
            })
            .filter(|projected| {
                self.indexed_erased_type(projected).as_ref() == Some(declared_erasure)
            })
        {
            projected
        } else if kind != TypeConstraintKind::Definition
            && register.code_var.is_some_and(|variable| {
                !self.fixed.contains(&variable)
                    && self
                        .equation_graph
                        .outputs
                        .contains_key(&SourceTypeFact::Variable(variable))
            })
            && declared_erasure.is_reference()
            && erased.is_reference()
        {
            // DEX verifier joins can erase a value to one of several unrelated
            // interfaces. Source requirements are validated against every
            // definition before replacing the local declaration.
            ty
        } else {
            return false;
        };
        let mut changed = false;
        if kind != TypeConstraintKind::Definition {
            let abi_fixed = register
                .code_var
                .is_some_and(|variable| self.abi_fixed.contains(&variable));
            if let Some(value) = value.filter(|_| !abi_fixed) {
                self.contextual_values.insert(value);
                if kind == TypeConstraintKind::Declaration {
                    self.declaration_values.insert(value);
                }
                let requirements = if kind == TypeConstraintKind::Receiver {
                    &mut self.receiver_value_requirements
                } else {
                    &mut self.value_requirements
                };
                let value_changed = if kind == TypeConstraintKind::Receiver {
                    Self::merge_receiver_requirement(
                        self.source_types,
                        self.type_variable_erasures,
                        self.generic_projection,
                        requirements,
                        value,
                        ty.clone(),
                    )
                } else {
                    Self::merge_requirement(
                        self.source_types,
                        self.type_variable_erasures,
                        self.generic_projection,
                        requirements,
                        value,
                        ty.clone(),
                    )
                };
                if value_changed {
                    self.equation_graph
                        .mark_changed(SourceTypeFact::Value(value));
                }
                changed |= value_changed;
            }
            if let Some(variable) = register.code_var {
                self.contextual_variables.insert(variable);
                if kind == TypeConstraintKind::Declaration {
                    self.declaration_variables.insert(variable);
                }
                if self.collect_diagnostics {
                    self.requirement_candidates
                        .entry(variable)
                        .or_default()
                        .insert(format!("{ty} = {ty:?}"));
                }
                let requirements = if kind == TypeConstraintKind::Receiver {
                    &mut self.receiver_requirements
                } else {
                    &mut self.requirements
                };
                let variable_changed = if kind == TypeConstraintKind::Receiver {
                    Self::merge_receiver_requirement(
                        self.source_types,
                        self.type_variable_erasures,
                        self.generic_projection,
                        requirements,
                        variable,
                        ty.clone(),
                    )
                } else {
                    Self::merge_requirement(
                        self.source_types,
                        self.type_variable_erasures,
                        self.generic_projection,
                        requirements,
                        variable,
                        ty.clone(),
                    )
                };
                if variable_changed {
                    self.equation_graph
                        .mark_changed(SourceTypeFact::Variable(variable));
                }
                changed |= variable_changed;
            }
            return changed;
        }
        if let Some(value) = value {
            let value_changed = Self::merge_constraint(
                self.source_types,
                self.type_variable_erasures,
                self.generic_projection,
                &mut self.value_states,
                value,
                ty.clone(),
                kind,
            );
            if value_changed {
                self.equation_graph
                    .mark_changed(SourceTypeFact::Value(value));
            }
            changed |= value_changed;
        }
        if let Some(variable) = register
            .code_var
            .filter(|variable| !self.fixed.contains(variable))
        {
            let variable_changed = Self::merge_constraint(
                self.source_types,
                self.type_variable_erasures,
                self.generic_projection,
                &mut self.states,
                variable,
                ty,
                kind,
            );
            if variable_changed {
                self.equation_graph
                    .mark_changed(SourceTypeFact::Variable(variable));
            }
            changed |= variable_changed;
        }
        changed
    }

    fn record_equation(&mut self, result: &RegisterArg, value: &SemanticExpression) {
        if let Some(identity) = SsaVar::from_reg(result) {
            self.value_erased_types
                .entry(identity)
                .or_insert_with(|| result.ty.clone());
        }
        if matches!(value, SemanticExpression::Select { .. }) {
            self.join_variables.extend(result.code_var);
        }
        self.equations.push(TypeEquation {
            result: result.clone(),
            value: value.clone(),
        });
    }

    fn expression_type(&self, value: &SemanticExpression) -> Option<KotlinType> {
        match value {
            SemanticExpression::Register(register) => self.register_type(register).cloned(),
            SemanticExpression::Literal(_) => None,
            SemanticExpression::Operation(operation) => self.operation_type(operation),
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => self.join_expressions(when_true, when_false),
        }
    }

    fn expression_type_for_result(
        &self,
        value: &SemanticExpression,
        erased_result: &ArgType,
    ) -> Option<KotlinType> {
        let SemanticExpression::Select {
            when_true,
            when_false,
            ..
        } = value
        else {
            let inferred = self.expression_type(value)?;
            let inferred_erasure = self.indexed_erased_type(&inferred);
            let invocation_erasure_mismatch = value
                .as_operation()
                .is_some_and(|operation| operation.insn_type == InsnType::Invoke)
                && inferred_erasure.as_ref() != Some(erased_result)
                && !inferred_erasure.as_ref().is_some_and(|inferred| {
                    self.generic_projection
                        .is_some_and(|projection| projection.is_subtype(inferred, erased_result))
                });
            return if invocation_erasure_mismatch {
                self.resolved_type(erased_result)
            } else {
                Some(inferred)
            };
        };
        if erased_result == &ArgType::BOOLEAN
            && [when_true.as_ref(), when_false.as_ref()]
                .into_iter()
                .all(|branch| matches!(Self::constant(branch), Some(0) | Some(1)))
        {
            return self.resolved_type(&ArgType::BOOLEAN);
        }
        if let Some(joined) = self.join_expressions(when_true, when_false) {
            if self.source_type_is_well_formed(&joined) {
                return Some(joined);
            }
        }
        let mut evidence = [when_true.as_ref(), when_false.as_ref()]
            .into_iter()
            .filter_map(|branch| self.expression_type(branch))
            .filter(|ty| {
                self.source_type_is_well_formed(ty)
                    && Self::has_source_specific_type(ty)
                    && self.indexed_erased_type(ty).as_ref() == Some(erased_result)
            });
        if let Some(candidate) = evidence.next() {
            if evidence.next().is_none() {
                return Some(candidate);
            }
        }
        self.select_erased_type(when_true, when_false, erased_result)
    }

    fn select_erased_type(
        &self,
        when_true: &SemanticExpression,
        when_false: &SemanticExpression,
        erased_result: &ArgType,
    ) -> Option<KotlinType> {
        if !erased_result.is_reference() {
            return None;
        }
        let branches_are_references = [when_true, when_false].into_iter().all(|branch| {
            Self::is_null(branch)
                || self.expression_type(branch).is_some_and(|ty| {
                    self.indexed_erased_type(&ty)
                        .is_some_and(|erased| erased.is_reference())
                })
        });
        branches_are_references
            .then(|| self.resolved_type(erased_result))
            .flatten()
    }

    fn operation_type(&self, operation: &SemanticOperation) -> Option<KotlinType> {
        let inferred = match operation.insn_type {
            InsnType::Iget | InsnType::Sget => {
                operation
                    .payload
                    .reference
                    .as_ref()
                    .and_then(|reference| match reference {
                        MemberReference::Field(field) => {
                            self.field_type(field, operation.operands().first())
                        }
                        MemberReference::Method(_) => None,
                    })
            }
            InsnType::Move => operation
                .operands()
                .first()
                .and_then(|operand| self.expression_type(operand)),
            InsnType::CheckCast => {
                let target = operation.conversion_type()?;
                let source = operation
                    .operands()
                    .first()
                    .and_then(|operand| self.expression_type(operand));
                source
                    .filter(|source| self.indexed_erased_type(source).as_ref() == Some(target))
                    .or_else(|| self.source_types.get(target).cloned())
            }
            InsnType::Aget => operation
                .operands()
                .first()
                .and_then(|array| self.expression_type(array))
                .and_then(|array| match array {
                    KotlinType::Array(element) => Some(element.into_type()),
                    _ => None,
                }),
            InsnType::NewArray | InsnType::FilledNewArray => operation
                .payload
                .class_type
                .as_ref()
                .and_then(|ty| self.resolved_type(ty)),
            InsnType::ConstClass => operation
                .payload
                .class_type
                .as_ref()
                .and_then(|represented| self.class_literal_type(represented)),
            InsnType::Invoke => self.invocation_type(operation),
            InsnType::Constructor => operation
                .allocation_type()
                .and_then(|owner| self.object_types.get(owner))
                .cloned()
                .or_else(|| self.constructor_type(operation)),
            _ => None,
        };
        inferred.or_else(|| {
            operation
                .result
                .as_ref()
                .and_then(|result| self.resolved_type(&result.ty))
        })
    }

    fn invocation_type(&self, operation: &SemanticOperation) -> Option<KotlinType> {
        let MemberReference::Method(method) = operation.payload.reference.as_ref()? else {
            return None;
        };
        let Some((mut solver, arguments, contract)) = self.invocation_solver(operation) else {
            return self.resolved_type(&method.descriptor.return_type);
        };
        let return_depends_on_type_variables =
            GenericInvocationCompatibility::has_type_variable(&contract.signature.return_type);
        let raw_owner_affects_return =
            solver.owner_is_raw(&contract.owner) && return_depends_on_type_variables;
        let unchecked_input_affects_return = return_depends_on_type_variables
            && contract
                .signature
                .parameter_types
                .iter()
                .zip(arguments)
                .any(|(formal, actual)| {
                    self.expression_type(actual).is_some_and(|actual| {
                        GenericInvocationCompatibility::requires_unchecked_conversion(
                            formal,
                            &actual,
                            contract,
                            self.source_types,
                        )
                    })
                });
        if raw_owner_affects_return || unchecked_input_affects_return {
            return self.resolved_type(&method.descriptor.return_type);
        }
        if !solver.satisfies_declared_bounds(&contract.signature.type_parameters) {
            return self.resolved_type(&method.descriptor.return_type);
        }
        // A type variable's declared bound is not evidence for its invocation
        // type. Publishing bound completion here makes a poly expression
        // prematurely exact and feeds that default back into its enclosing
        // invocation. Keep the result unresolved until arguments or target
        // context provide a real substitution.
        solver
            .instantiate(&contract.signature.return_type)
            .filter(|ty| solver.valid_source_type(ty))
    }

    fn iterable_element_type(&self, iterable: &SemanticExpression) -> Option<KotlinType> {
        let ty = self.expression_type(iterable)?;
        if let KotlinType::Array(element) = ty {
            return Some(element.into_type());
        }
        let iterable = self
            .generic_projection
            .and_then(|projection| {
                projection.project_supertype(&ty, &ArgType::object("java/lang/Iterable"))
            })
            .or_else(|| match &ty {
                KotlinType::Class(class)
                    if class
                        .segments
                        .last()
                        .is_some_and(|segment| segment.name.to_string() == "Iterable") =>
                {
                    Some(ty.clone())
                }
                _ => None,
            })?;
        let KotlinType::Class(class) = iterable else {
            return None;
        };
        match class.segments.last()?.arguments.as_slice() {
            [KotlinTypeArgument::Exact(element) | KotlinTypeArgument::Extends(element)] => {
                Some(element.clone())
            }
            [KotlinTypeArgument::Any | KotlinTypeArgument::Super(_)] | _ => None,
        }
    }

    fn iterable_context_type(
        &self,
        iterable: &SemanticExpression,
        element: KotlinType,
    ) -> Option<KotlinType> {
        match self.expression_type(iterable)? {
            KotlinType::Array(_) => Some(KotlinType::array(element)),
            KotlinType::Class(_) => {
                let KotlinType::Class(mut iterable) = self
                    .resolved_type(&ArgType::object("java/lang/Iterable"))?
                    .into_raw()
                else {
                    return None;
                };
                iterable.segments.last_mut()?.arguments = vec![KotlinTypeArgument::Exact(element)];
                Some(KotlinType::Class(iterable))
            }
            KotlinType::Variable(_) | KotlinType::Primitive(_) => None,
        }
    }

    fn constructor_type(&self, operation: &SemanticOperation) -> Option<KotlinType> {
        let MemberReference::Method(method) = operation.payload.reference.as_ref()? else {
            return None;
        };
        if let Some(allocation) = operation
            .allocation_type()
            .filter(|allocation| *allocation != &method.owner)
        {
            return self.resolved_type(allocation);
        }
        self.invocation_solver(operation)
            .and_then(|(solver, _, contract)| {
                solver
                    .satisfies_declared_bounds(&contract.owner_parameters)
                    .then(|| solver.owner_type(&contract.owner))
                    .flatten()
            })
            .or_else(|| self.resolved_type(&method.owner))
    }

    fn class_literal_type(&self, represented: &ArgType) -> Option<KotlinType> {
        let represented = self.resolved_type(represented)?.into_raw();
        let KotlinType::Class(mut class) = self
            .resolved_type(&ArgType::object("java/lang/Class"))?
            .into_raw()
        else {
            return None;
        };
        class.segments.last_mut()?.arguments = vec![KotlinTypeArgument::Exact(represented)];
        Some(KotlinType::Class(class))
    }

    fn resolved_type(&self, ty: &ArgType) -> Option<KotlinType> {
        self.source_types.get(ty).cloned().or_else(|| match ty {
            ArgType::Array(element) => self.resolved_type(element).map(KotlinType::array),
            ArgType::Primitive(_) | ArgType::Object(_) | ArgType::Unknown(_) => None,
        })
    }

    fn join_expressions(
        &self,
        left: &SemanticExpression,
        right: &SemanticExpression,
    ) -> Option<KotlinType> {
        let left_type = self.expression_type(left);
        let right_type = self.expression_type(right);
        if left_type
            .as_ref()
            .is_some_and(|ty| !matches!(ty, KotlinType::Primitive(_)))
            && Self::constant(right) == Some(0)
        {
            return left_type;
        }
        if right_type
            .as_ref()
            .is_some_and(|ty| !matches!(ty, KotlinType::Primitive(_)))
            && Self::constant(left) == Some(0)
        {
            return right_type;
        }
        match (left_type, right_type) {
            (Some(left), Some(right)) => Self::reconcile_types(
                self.source_types,
                self.type_variable_erasures,
                self.generic_projection,
                &left,
                &right,
            ),
            (Some(ty), None) if Self::is_null(right) => Some(ty),
            (None, Some(ty)) if Self::is_null(left) => Some(ty),
            _ => None,
        }
    }

    fn exact(&self, variable: u32) -> Option<&KotlinType> {
        match self.states.get(&variable) {
            Some(TypeState::Exact(ty)) => Some(ty),
            Some(TypeState::Conflict) | None => None,
        }
    }

    fn register_type(&self, register: &RegisterArg) -> Option<&KotlinType> {
        SsaVar::from_reg(register)
            .and_then(|value| match self.value_states.get(&value) {
                Some(TypeState::Exact(ty)) => Some(ty),
                Some(TypeState::Conflict) | None => None,
            })
            .or_else(|| register.code_var.and_then(|variable| self.exact(variable)))
    }

    fn is_null(value: &SemanticExpression) -> bool {
        matches!(
            value,
            SemanticExpression::Literal(literal)
                if literal.value == 0 && literal.ty.is_object()
        )
    }

    fn constant(value: &SemanticExpression) -> Option<i64> {
        let mut current = value;
        loop {
            match current {
                SemanticExpression::Literal(literal) => return Some(literal.value),
                SemanticExpression::Operation(operation)
                    if matches!(operation.insn_type, InsnType::Const | InsnType::Move) =>
                {
                    current = operation.operands().first()?;
                }
                SemanticExpression::Register(_)
                | SemanticExpression::Operation(_)
                | SemanticExpression::Select { .. } => return None,
            }
        }
    }

    fn record_erased_generic_boundaries(&mut self, operation: &SemanticOperation) {
        let Some(MemberReference::Method(method)) = operation.payload.reference.as_ref() else {
            return;
        };
        let Some(projection) = self.generic_projection else {
            return;
        };
        let contract = self.generic_methods.get(method);
        let operand_receiver = Self::operand_receiver(operation);
        for (index, (erased, argument)) in method
            .descriptor
            .parameters
            .iter()
            .zip(
                operation
                    .operands()
                    .iter()
                    .skip(usize::from(operand_receiver)),
            )
            .enumerate()
        {
            if contract
                .and_then(|contract| contract.signature.parameter_types.get(index))
                .is_some_and(GenericInvocationCompatibility::is_parameterized)
            {
                continue;
            }
            if !projection
                .declared_type_parameters(erased)
                .is_some_and(|parameters| !parameters.is_empty())
            {
                continue;
            }
            if let Some(variable) = Self::storage_variable(argument) {
                self.erased_boundary_variables.insert(variable);
            }
        }
    }

    fn operand_receiver(operation: &SemanticOperation) -> bool {
        operation.payload.invoke_type != Some(crate::ir::InvokeType::Static)
    }

    fn source_receiver(operation: &SemanticOperation) -> bool {
        Self::operand_receiver(operation) && operation.insn_type != InsnType::Constructor
    }

    fn storage_variable(expression: &SemanticExpression) -> Option<u32> {
        match expression {
            SemanticExpression::Register(register) => register.code_var,
            SemanticExpression::Operation(operation)
                if matches!(operation.insn_type, InsnType::Move | InsnType::CheckCast) =>
            {
                operation
                    .operands()
                    .first()
                    .and_then(Self::storage_variable)
            }
            SemanticExpression::Literal(_)
            | SemanticExpression::Operation(_)
            | SemanticExpression::Select { .. } => None,
        }
    }
}

#[cfg_attr(feature = "profiling", hotpath::measure_all)]
impl SemanticVisitor for SourceTypeFlow<'_> {
    fn enter_node(&mut self, node: &SemanticNode) {
        match node {
            SemanticNode::ForEach {
                variable, iterable, ..
            } => self.elements.push(ElementEquation {
                variable: variable.clone(),
                iterable: iterable.value.clone(),
            }),
            SemanticNode::Try { catches, .. } => {
                for catch in catches {
                    let Some(exception) = catch.exception_value.as_ref() else {
                        continue;
                    };
                    let ty = match catch.exception_types.as_slice() {
                        [ty] => self.resolved_type(ty),
                        [] => None,
                        [_, ..] => self.resolved_type(&ArgType::object("java/lang/Throwable")),
                    };
                    if let Some(ty) = ty {
                        self.constrain_register(exception, ty);
                    }
                }
            }
            SemanticNode::Leave(leave) => {
                if let (Some(return_type), SemanticLeaveKind::Return(Some(value))) =
                    (self.return_type, &leave.kind)
                {
                    self.constrain_expression_context(value, return_type.clone());
                }
            }
            _ => {}
        }
    }

    fn visit_statement(&mut self, statement: &SemanticStatement) {
        match &statement.kind {
            SemanticStatementKind::Definition { result, value, .. } => {
                self.record_equation(result, value);
                self.visit_expression(value);
            }
            SemanticStatementKind::Instruction(operation) => {
                if matches!(operation.insn_type, InsnType::Iput | InsnType::Sput) {
                    let field_type = operation
                        .payload
                        .reference
                        .as_ref()
                        .and_then(|reference| match reference {
                            MemberReference::Field(field) => Some((
                                field,
                                (operation.insn_type == InsnType::Iput)
                                    .then(|| operation.operands().get(1))
                                    .flatten(),
                            )),
                            MemberReference::Method(_) => None,
                        })
                        .and_then(|(field, receiver)| self.field_type(field, receiver));
                    if let (Some(value), Some(field_type)) =
                        (operation.operands().first(), field_type)
                    {
                        self.constrain_expression_context(value, field_type);
                    }
                }
                self.visit_operation(operation);
            }
        }
    }

    fn enter_operation(&mut self, operation: &SemanticOperation) {
        if let Some(result) = &operation.result {
            self.record_equation(
                result,
                &SemanticExpression::Operation(Box::new(operation.clone())),
            );
        }
        self.record_erased_generic_boundaries(operation);
        if matches!(
            operation.insn_type,
            InsnType::Invoke | InsnType::Constructor
        ) {
            self.invocations.push(Arc::new(operation.clone()));
        }
        if operation.insn_type == InsnType::If {
            self.predicate_tests.push(operation.clone());
        }
        if matches!(
            operation.insn_type,
            InsnType::InstanceOf | InsnType::CheckCast
        ) {
            self.runtime_type_tests.push(operation.clone());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug)]
    struct ParentProjection;

    impl GenericTypeProjection for ParentProjection {
        fn specialize_subtype(
            &self,
            _subtype: &ArgType,
            _expected_supertype: &KotlinType,
        ) -> Option<KotlinType> {
            None
        }

        fn project_supertype(
            &self,
            subtype: &KotlinType,
            expected_supertype: &ArgType,
        ) -> Option<KotlinType> {
            (SourceTypeFlow::erased_type(&test_source_types(), &BTreeMap::new(), subtype)
                == Some(ArgType::object("example/Child"))
                && expected_supertype == &ArgType::object("example/Parent"))
                .then(|| {
                    class(
                        "example/Parent",
                        vec![KotlinTypeArgument::Exact(class(
                            "java/lang/String",
                            Vec::new(),
                        ))],
                    )
                })
        }

        fn is_subtype(&self, subtype: &ArgType, supertype: &ArgType) -> bool {
            subtype == &ArgType::object("example/Child")
                && supertype == &ArgType::object("example/Parent")
        }
    }

    fn test_source_types() -> BTreeMap<ArgType, KotlinType> {
        [
            "java/lang/Object",
            "java/lang/String",
            "example/Child",
            "example/Parent",
        ]
        .into_iter()
        .map(|name| (ArgType::object(name), class(name, Vec::new())))
        .collect()
    }

    fn class(name: &str, arguments: Vec<KotlinTypeArgument>) -> KotlinType {
        let mut ty = match KotlinType::source_class(&name.replace('/', ".")) {
            KotlinType::Class(ty) => ty,
            _ => unreachable!(),
        };
        ty.segments.last_mut().unwrap().arguments = arguments;
        KotlinType::Class(ty)
    }

    fn variable(name: &str) -> KotlinType {
        KotlinType::Variable(KotlinIdentifier::from_dex(name))
    }

    fn owner(name: &str, parameters: &[&str]) -> ClassTypeSignature {
        ClassTypeSignature {
            raw_name: name.to_string(),
            type_arguments: parameters
                .iter()
                .map(|parameter| {
                    TypeArgument::Exact(JvmTypeSignature::TypeVariable((*parameter).to_string()))
                })
                .collect(),
            inner_segments: Vec::new(),
        }
    }

    #[test]
    fn generic_evidence_preserves_covariant_capture() {
        let parameter = variable("E");
        assert_eq!(
            GenericTypeEvidence::join(
                &KotlinTypeArgument::Extends(parameter.clone()),
                &KotlinTypeArgument::Exact(parameter.clone()),
                None,
            ),
            Some(KotlinTypeArgument::Extends(parameter)),
        );
    }

    #[test]
    fn generic_evidence_joins_opposite_variance_to_unbounded() {
        let parameter = variable("E");
        assert_eq!(
            GenericTypeEvidence::join(
                &KotlinTypeArgument::Extends(parameter.clone()),
                &KotlinTypeArgument::Super(parameter),
                None,
            ),
            Some(KotlinTypeArgument::Any),
        );
    }

    #[test]
    fn source_type_join_projects_subtype_to_common_supertype() {
        let source_types = test_source_types();
        let child = class("example/Child", Vec::new());
        let parent = class("example/Parent", vec![KotlinTypeArgument::Any]);
        let joined = SourceTypeFlow::reconcile_types(
            &source_types,
            &BTreeMap::new(),
            Some(&ParentProjection),
            &child,
            &parent,
        )
        .expect("subtype and parent must have a denotable least upper bound");

        assert_eq!(
            SourceTypeFlow::erased_type(&source_types, &BTreeMap::new(), &joined),
            Some(ArgType::object("example/Parent"))
        );
    }

    #[test]
    fn concrete_subclass_is_not_treated_as_raw_generic_supertype() {
        let source_types = test_source_types();
        let variables = BTreeMap::new();
        let relations =
            KotlinTypeRelations::new(&source_types, &variables, Some(&ParentProjection));
        let child = class("example/Child", Vec::new());
        let target = class(
            "example/Parent",
            vec![KotlinTypeArgument::Exact(variable("T"))],
        );

        assert!(!relations.is_assignable(&child, &target));
    }

    #[test]
    fn nested_inference_variable_is_not_concrete_generic_evidence() {
        let entry = JvmTypeSignature::ClassType(ClassTypeSignature {
            raw_name: "java/util/Map$Entry".to_string(),
            type_arguments: vec![
                TypeArgument::Exact(JvmTypeSignature::TypeVariable("K".to_string())),
                TypeArgument::Unbounded,
            ],
            inner_segments: Vec::new(),
        });
        let ordering = JvmTypeSignature::ClassType(ClassTypeSignature {
            raw_name: "example/Ordering".to_string(),
            type_arguments: vec![TypeArgument::Exact(entry)],
            inner_segments: Vec::new(),
        });

        assert!(!GenericInvocationCompatibility::has_concrete_type_argument(
            &ordering
        ));
    }

    #[test]
    fn lexical_variable_bound_proves_wildcard_assignability() {
        let object = class("java/lang/Object", Vec::new());
        let enum_type = class("java/lang/Enum", Vec::new());
        let class_type = class("java/lang/Class", Vec::new());
        let source_types = BTreeMap::from([
            (ArgType::object("java/lang/Object"), object),
            (ArgType::object("java/lang/Enum"), enum_type),
            (ArgType::object("java/lang/Class"), class_type),
        ]);
        let erasures = BTreeMap::from([(
            KotlinIdentifier::from_dex("T"),
            ArgType::object("java/lang/Enum"),
        )]);
        let bounds = BTreeMap::from([(
            KotlinIdentifier::from_dex("T"),
            class(
                "java/lang/Enum",
                vec![KotlinTypeArgument::Exact(variable("T"))],
            ),
        )]);
        let relations = KotlinTypeRelations::new(&source_types, &erasures, None)
            .with_variable_bounds(Some(&bounds));
        let source = class(
            "java/lang/Class",
            vec![KotlinTypeArgument::Exact(variable("T"))],
        );
        let target = class(
            "java/lang/Class",
            vec![KotlinTypeArgument::Extends(class(
                "java/lang/Enum",
                vec![KotlinTypeArgument::Any],
            ))],
        );

        assert!(relations.is_assignable(&source, &target));
    }

    #[test]
    fn use_context_does_not_widen_definition_type() {
        let entry_erasure = ArgType::object("example/Entry");
        let mut source_types = BTreeMap::new();
        source_types.insert(entry_erasure, class("example/Entry", Vec::new()));
        let erasures = ["K", "V"]
            .into_iter()
            .map(|name| {
                (
                    KotlinIdentifier::from_dex(name),
                    ArgType::object("java/lang/Object"),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let precise = class(
            "example/Entry",
            vec![
                KotlinTypeArgument::Exact(variable("K")),
                KotlinTypeArgument::Exact(variable("V")),
            ],
        );
        let accepted = class(
            "example/Entry",
            vec![KotlinTypeArgument::Any, KotlinTypeArgument::Any],
        );
        let mut states = BTreeMap::from([(0u32, TypeState::Exact(precise.clone()))]);

        assert!(!SourceTypeFlow::merge_constraint(
            &source_types,
            &erasures,
            None,
            &mut states,
            0,
            accepted,
            TypeConstraintKind::Context,
        ));
        assert_eq!(states.get(&0), Some(&TypeState::Exact(precise)));
    }

    #[test]
    fn lexical_type_variable_is_rigid() {
        let source_types = BTreeMap::new();
        let variables = BTreeMap::from([(
            KotlinIdentifier::from_dex("K"),
            ArgType::object("java/lang/Object"),
        )]);
        let mut solver = GenericTypeSolver::new(&source_types).with_visible_variables(&variables);

        solver.constrain(
            &JvmTypeSignature::TypeVariable("K".to_string()),
            &class("java/lang/String", Vec::new()),
        );

        assert_eq!(solver.get("K"), Some(variable("K")));
    }

    #[test]
    fn lexical_type_variable_participates_in_compound_substitution() {
        let pair_erasure = ArgType::object("example/Pair");
        let source_types = BTreeMap::from([(pair_erasure, class("example/Pair", Vec::new()))]);
        let variables = BTreeMap::from([(
            KotlinIdentifier::from_dex("K"),
            ArgType::object("java/lang/Object"),
        )]);
        let mut solver = GenericTypeSolver::new(&source_types).with_visible_variables(&variables);
        solver.bind(
            "V",
            GenericTypeValue::inferred(
                KotlinTypeArgument::Exact(class("java/lang/String", Vec::new())),
                false,
            ),
            GenericConstraintOrigin::Owner,
        );

        assert_eq!(
            solver.invocation_input_type(&JvmTypeSignature::ClassType(owner(
                "example/Pair",
                &["K", "V"],
            ))),
            Some(class(
                "example/Pair",
                vec![
                    KotlinTypeArgument::Exact(variable("K")),
                    KotlinTypeArgument::Exact(class("java/lang/String", Vec::new())),
                ],
            )),
        );
    }

    #[test]
    fn lexical_type_variable_bound_instantiates_receiver_owner() {
        let receiver_erasure = ArgType::object("example/Element");
        let source_types = BTreeMap::from([(
            receiver_erasure.clone(),
            class("example/Element", Vec::new()),
        )]);
        let variables = BTreeMap::from([(KotlinIdentifier::from_dex("T"), receiver_erasure)]);
        let bounds = BTreeMap::from([(
            KotlinIdentifier::from_dex("T"),
            class(
                "example/Element",
                vec![KotlinTypeArgument::Exact(variable("T"))],
            ),
        )]);
        let receiver_owner = owner("example/Element", &["E"]);
        let mut solver = GenericTypeSolver::new(&source_types)
            .with_visible_variables(&variables)
            .with_visible_bounds(&bounds)
            .with_local_owner_variables(&receiver_owner);

        solver.constrain_owner(&receiver_owner, &variable("T"));

        assert_eq!(solver.get("E"), Some(variable("T")));
    }

    #[test]
    fn method_inference_variable_shadows_lexical_name() {
        let source_types = BTreeMap::new();
        let variables = BTreeMap::from([(
            KotlinIdentifier::from_dex("K"),
            ArgType::object("java/lang/Object"),
        )]);
        let parameter = TypeParameter {
            name: "K".to_string(),
            class_bound: None,
            interface_bounds: Vec::new(),
        };
        let mut solver = GenericTypeSolver::new(&source_types)
            .with_visible_variables(&variables)
            .with_inference_variables(&[parameter]);
        let string = class("java/lang/String", Vec::new());

        solver.constrain(&JvmTypeSignature::TypeVariable("K".to_string()), &string);

        assert_eq!(solver.get("K"), Some(string));
    }

    #[test]
    fn recursive_inference_binding_fails_occurs_check() {
        let source_types = BTreeMap::new();
        let parameter = TypeParameter {
            name: "T".to_string(),
            class_bound: None,
            interface_bounds: Vec::new(),
        };
        let mut solver =
            GenericTypeSolver::new(&source_types).with_inference_variables(&[parameter]);

        solver.bind(
            "T",
            GenericTypeValue::inferred(
                KotlinTypeArgument::Exact(class(
                    "example/Box",
                    vec![KotlinTypeArgument::Exact(variable("T"))],
                )),
                false,
            ),
            GenericConstraintOrigin::Argument,
        );

        assert!(matches!(
            solver.values.get("T"),
            Some(GenericTypeBinding::Conflict {
                origin: GenericConstraintOrigin::Argument
            })
        ));
    }

    #[test]
    fn indirect_recursive_inference_binding_fails_occurs_check() {
        let source_types = BTreeMap::new();
        let parameters = ["T", "U"].map(|name| TypeParameter {
            name: name.to_string(),
            class_bound: None,
            interface_bounds: Vec::new(),
        });
        let mut solver =
            GenericTypeSolver::new(&source_types).with_inference_variables(&parameters);
        solver.bind(
            "T",
            GenericTypeValue::inferred(KotlinTypeArgument::Exact(variable("U")), false),
            GenericConstraintOrigin::Argument,
        );

        solver.bind(
            "U",
            GenericTypeValue::inferred(
                KotlinTypeArgument::Exact(class(
                    "example/Box",
                    vec![KotlinTypeArgument::Exact(variable("T"))],
                )),
                false,
            ),
            GenericConstraintOrigin::Argument,
        );

        assert!(matches!(
            solver.values.get("U"),
            Some(GenericTypeBinding::Conflict {
                origin: GenericConstraintOrigin::Argument
            })
        ));
    }

    #[test]
    fn symbolic_identity_binding_is_not_recursive() {
        let source_types = BTreeMap::new();
        let parameter = TypeParameter {
            name: "T".to_string(),
            class_bound: None,
            interface_bounds: Vec::new(),
        };
        let mut solver =
            GenericTypeSolver::new(&source_types).with_inference_variables(&[parameter]);

        solver.bind(
            "T",
            GenericTypeValue::inferred(KotlinTypeArgument::Exact(variable("T")), false),
            GenericConstraintOrigin::Owner,
        );

        assert_eq!(solver.get("T"), Some(variable("T")));
    }

    #[test]
    fn owner_variable_shadows_same_named_lexical_variable() {
        let owner_erasure = ArgType::object("example/Owner");
        let source_types = BTreeMap::from([(owner_erasure, class("example/Owner", Vec::new()))]);
        let variables = BTreeMap::from([(
            KotlinIdentifier::from_dex("T"),
            ArgType::object("java/lang/Object"),
        )]);
        let owner = owner("example/Owner", &["T"]);
        let mut solver = GenericTypeSolver::new(&source_types)
            .with_local_owner_variables(&owner)
            .with_visible_variables(&variables);
        let contextual = variable("U");

        solver.constrain_owner(
            &owner,
            &class(
                "example/Owner",
                vec![KotlinTypeArgument::Exact(contextual.clone())],
            ),
        );

        assert_eq!(solver.get("T"), Some(contextual));
    }

    #[test]
    fn receiver_capture_is_not_refined_by_method_arguments() {
        let stream_erasure = ArgType::object("java/util/stream/Stream");
        let mut source_types = BTreeMap::new();
        source_types.insert(stream_erasure, class("java/util/stream/Stream", Vec::new()));
        let mut solver = GenericTypeSolver::new(&source_types);
        let stream_owner = owner("java/util/stream/Stream", &["T"]);
        solver.constrain_owner(
            &stream_owner,
            &class("java/util/stream/Stream", vec![KotlinTypeArgument::Any]),
        );
        solver.bind(
            "T",
            GenericTypeValue::declared(KotlinTypeArgument::Exact(variable("E"))),
            GenericConstraintOrigin::Argument,
        );

        assert_eq!(
            solver.owner_type(&stream_owner),
            Some(class(
                "java/util/stream/Stream",
                vec![KotlinTypeArgument::Any]
            ))
        );
    }

    #[test]
    fn argument_capture_is_not_replaced_by_target_context() {
        let source_types = BTreeMap::new();
        let mut solver = GenericTypeSolver::new(&source_types);
        solver.bind(
            "T",
            GenericTypeValue::declared(KotlinTypeArgument::Any),
            GenericConstraintOrigin::Argument,
        );
        solver.bind(
            "T",
            GenericTypeValue::declared(KotlinTypeArgument::Extends(variable("E"))),
            GenericConstraintOrigin::Context,
        );

        assert!(matches!(
            solver.binding("T"),
            Some(GenericTypeValue {
                argument: KotlinTypeArgument::Any,
                captured: true,
            })
        ));
    }

    #[test]
    fn captured_owner_projects_a_denotable_contravariant_input() {
        let iterable = ArgType::object("java/lang/Iterable");
        let consumer = ArgType::object("java/util/function/Consumer");
        let mut source_types = BTreeMap::new();
        source_types.insert(iterable, class("java/lang/Iterable", Vec::new()));
        source_types.insert(consumer, class("java/util/function/Consumer", Vec::new()));
        let mut solver = GenericTypeSolver::new(&source_types);
        let iterable_owner = owner("java/lang/Iterable", &["T"]);
        solver.constrain_owner(
            &iterable_owner,
            &class(
                "java/lang/Iterable",
                vec![KotlinTypeArgument::Extends(variable("E"))],
            ),
        );
        let input = JvmTypeSignature::ClassType(ClassTypeSignature {
            raw_name: "java/util/function/Consumer".to_string(),
            type_arguments: vec![TypeArgument::Super(JvmTypeSignature::TypeVariable(
                "T".to_string(),
            ))],
            inner_segments: Vec::new(),
        });

        assert!(!solver.owner_requires_capture_conversion(&iterable_owner, &[input.clone()]));
        assert_eq!(
            solver.invocation_input_type(&input),
            Some(class(
                "java/util/function/Consumer",
                vec![KotlinTypeArgument::Super(variable("E"))],
            ))
        );
    }

    #[test]
    fn covariant_formal_reduces_wildcard_to_inference_bound() {
        let source_types = BTreeMap::new();
        let mut solver = GenericTypeSolver::new(&source_types);
        solver.constrain_argument(
            &TypeArgument::Extends(JvmTypeSignature::TypeVariable("C".to_string())),
            &KotlinTypeArgument::Extends(variable("V")),
            GenericConstraintOrigin::Argument,
        );

        assert_eq!(
            solver.binding("C"),
            Some(&GenericTypeValue::inferred(
                KotlinTypeArgument::Exact(variable("V")),
                false,
            ))
        );
    }

    #[test]
    fn contravariant_argument_constrains_inference_variable_to_its_bound() {
        let source_types = BTreeMap::new();
        let mut solver = GenericTypeSolver::new(&source_types);
        solver.constrain_argument(
            &TypeArgument::Super(JvmTypeSignature::TypeVariable("C".to_string())),
            &KotlinTypeArgument::Super(variable("V")),
            GenericConstraintOrigin::Argument,
        );

        assert_eq!(
            solver.binding("C"),
            Some(&GenericTypeValue::inferred(
                KotlinTypeArgument::Exact(variable("V")),
                false,
            ))
        );
    }

    #[test]
    fn raw_receiver_is_not_parameterized_from_method_arguments() {
        let stream_erasure = ArgType::object("java/util/stream/Stream");
        let mut source_types = BTreeMap::new();
        source_types.insert(
            stream_erasure.clone(),
            class("java/util/stream/Stream", Vec::new()),
        );
        let mut solver = GenericTypeSolver::new(&source_types);
        let stream_owner = owner("java/util/stream/Stream", &["T"]);
        solver.constrain_owner(&stream_owner, &class("java/util/stream/Stream", Vec::new()));
        solver.bind(
            "T",
            GenericTypeValue::declared(KotlinTypeArgument::Exact(variable("E"))),
            GenericConstraintOrigin::Argument,
        );

        assert_eq!(
            solver.owner_type(&stream_owner),
            Some(class("java/util/stream/Stream", Vec::new()))
        );
    }
}
