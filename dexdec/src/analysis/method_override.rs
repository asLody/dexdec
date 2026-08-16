use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::io;

use std::sync::{Arc, OnceLock};

use crate::frontend::{
    AccessInfo, AnalysisDiagnostic, AnalysisLocation, ClassNode, DexFileReader, MethodNode,
    MethodOverrideSemantics, MethodReference,
};
use crate::ir::analysis::{ClassHierarchyIndex, ReferenceTypeInfo};
use crate::ir::generic_types::{
    ClassSignature, ClassTypeSignature, GenericMethodContract, GenericSignatures, JvmTypeSignature,
    MethodSignature, SignatureSubstitutionError, TypeArgument, TypeParameter, TypeSubstitution,
};
use crate::ir::ty::ArgType;
use crate::platform_symbols::{default_platform_symbols, PlatformClass, PlatformSymbolSet};

#[derive(Debug)]
pub enum OverrideAnalysisError {
    PlatformSymbols(io::Error),
    GenericSubstitution(SignatureSubstitutionError),
    UnresolvedType(ArgType),
    MissingErasedParent {
        class: String,
        index: usize,
    },
    GenericArity {
        class: String,
        expected: usize,
        actual: usize,
    },
}

impl std::fmt::Display for OverrideAnalysisError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PlatformSymbols(source) => {
                write!(formatter, "platform symbol metadata failed: {source}")
            }
            Self::GenericSubstitution(source) => source.fmt(formatter),
            Self::UnresolvedType(ty) => {
                write!(formatter, "class hierarchy contains unresolved type {ty}")
            }
            Self::MissingErasedParent { class, index } => {
                write!(
                    formatter,
                    "{class} has no generic form for erased parent {index}"
                )
            }
            Self::GenericArity {
                class,
                expected,
                actual,
            } => write!(
                formatter,
                "generic instantiation of {class} has {actual} arguments, expected {expected}"
            ),
        }
    }
}

impl std::error::Error for OverrideAnalysisError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::PlatformSymbols(source) => Some(source),
            Self::GenericSubstitution(source) => Some(source),
            Self::UnresolvedType(_)
            | Self::MissingErasedParent { .. }
            | Self::GenericArity { .. } => None,
        }
    }
}

impl From<io::Error> for OverrideAnalysisError {
    fn from(source: io::Error) -> Self {
        Self::PlatformSymbols(source)
    }
}

impl From<SignatureSubstitutionError> for OverrideAnalysisError {
    fn from(source: SignatureSubstitutionError) -> Self {
        Self::GenericSubstitution(source)
    }
}

type OverrideResult<T> = Result<T, OverrideAnalysisError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MethodDetails {
    reference: MethodReference,
    params: Vec<ArgType>,
    return_type: ArgType,
    generic_signature: Option<MethodSignature>,
    throws: Vec<ArgType>,
    access_flags: AccessInfo,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ClassDetails {
    descriptor: String,
    package: String,
    access_flags: AccessInfo,
    parents: Vec<ArgType>,
    generic_parents: Vec<JvmTypeSignature>,
    generic_signature: Option<ClassSignature>,
    instantiated_self: Option<ClassTypeSignature>,
    methods: Vec<MethodDetails>,
}

pub(crate) trait ClassHierarchy {
    fn class_details(&self, ty: &ArgType) -> Option<ClassDetails>;
}

pub(crate) fn collect_instantiated_super_types<H: ClassHierarchy>(
    hierarchy: &H,
    class: &ClassDetails,
) -> OverrideResult<Vec<ClassDetails>> {
    let mut out = Vec::new();
    let mut queue = VecDeque::new();
    for (idx, ty) in class.parents.iter().enumerate() {
        let generic = class.generic_parents.get(idx).cloned().ok_or_else(|| {
            OverrideAnalysisError::MissingErasedParent {
                class: class.descriptor.clone(),
                index: idx,
            }
        })?;
        queue.push_back((ty.clone(), generic));
    }
    let mut seen = BTreeSet::new();
    while let Some((ty, instantiated_parent)) = queue.pop_front() {
        let Some(details) = hierarchy.class_details(&ty) else {
            continue;
        };
        if !seen.insert(details.descriptor.clone()) {
            continue;
        }
        let Ok(instantiated) = bind_class(hierarchy, &details, &instantiated_parent) else {
            continue;
        };
        for (idx, parent_ty) in instantiated.parents.iter().enumerate() {
            let Some(generic) = instantiated.generic_parents.get(idx).cloned() else {
                continue;
            };
            queue.push_back((parent_ty.clone(), generic));
        }
        out.push(instantiated);
    }
    Ok(out)
}

pub(crate) trait OverrideAnalysisTarget {
    fn set_method_override(
        &mut self,
        declaring_class: &str,
        method_short_id: &str,
        semantics: Option<MethodOverrideSemantics>,
    );
}

pub(crate) struct MethodOverrideAnalyzer<'a, H> {
    hierarchy: &'a H,
}

impl<'a, H> MethodOverrideAnalyzer<'a, H>
where
    H: ClassHierarchy,
{
    pub fn new(hierarchy: &'a H) -> Self {
        Self { hierarchy }
    }

    pub fn analyze<T>(&self, target: &mut T, classes: &[ClassDetails]) -> OverrideResult<()>
    where
        T: OverrideAnalysisTarget,
    {
        for class in classes {
            let Ok(ancestors) = self.collect_super_types(class) else {
                continue;
            };
            for method in &class.methods {
                let Ok(semantics) = self.analyze_method(class, method, &ancestors) else {
                    continue;
                };
                target.set_method_override(
                    &method.reference.declaring_class,
                    &method.reference.short_id,
                    semantics,
                );
            }
        }
        Ok(())
    }

    fn analyze_method(
        &self,
        class: &ClassDetails,
        method: &MethodDetails,
        ancestors: &[ClassDetails],
    ) -> OverrideResult<Option<MethodOverrideSemantics>> {
        if method_is_not_overridable(method) {
            return Ok(None);
        }

        let mut overridden = Vec::new();
        let mut bases = Vec::new();
        let mut inherited_signature = None;
        let mut inherited_throws: Option<BTreeSet<ArgType>> = None;
        for ancestor in ancestors {
            let Some((ancestor_method, instantiated_signature)) =
                self.find_overridden_method(ancestor, method, class)?
            else {
                continue;
            };
            overridden.push(ancestor_method.reference.clone());
            if self.is_base_method(&ancestor, method)? {
                bases.push(ancestor_method.reference);
                if inherited_signature.is_none() {
                    inherited_signature = instantiated_signature;
                }
                let throws = ancestor_method.throws.into_iter().collect::<BTreeSet<_>>();
                inherited_throws = Some(match inherited_throws {
                    Some(current) => current.intersection(&throws).cloned().collect(),
                    None => throws,
                });
            }
        }

        if overridden.is_empty() {
            return Ok(None);
        }
        if bases.is_empty() {
            let Some(base) = overridden.last() else {
                return Ok(None);
            };
            bases.push(base.clone());
        }
        Ok(Some(MethodOverrideSemantics {
            overridden_methods: overridden,
            base_methods: bases,
            inherited_signature,
            inherited_throws: inherited_throws.unwrap_or_default().into_iter().collect(),
        }))
    }

    fn collect_super_types(&self, class: &ClassDetails) -> OverrideResult<Vec<ClassDetails>> {
        collect_instantiated_super_types(self.hierarchy, class)
    }

    fn find_overridden_method(
        &self,
        ancestor: &ClassDetails,
        method: &MethodDetails,
        owner: &ClassDetails,
    ) -> OverrideResult<Option<(MethodDetails, Option<MethodSignature>)>> {
        let mut best: Option<(&MethodDetails, Option<MethodSignature>)> = None;
        for candidate in &ancestor.methods {
            if candidate.access_flags.is_static()
                || !method_visible_from(candidate, ancestor, owner)
                || method_name(&candidate.reference.short_id)
                    != method_name(&method.reference.short_id)
                || candidate.params.len() != method.params.len()
            {
                continue;
            }
            let candidate_signature = candidate
                .generic_signature
                .as_ref()
                .filter(|_| !ancestor.is_raw_instantiation())
                .map(|signature| instantiate_method_signature(ancestor, signature))
                .transpose()?;
            if !self.instantiated_signature_matches(candidate, candidate_signature.as_ref(), method)
            {
                continue;
            }
            let Some((current, _)) = best else {
                best = Some((candidate, candidate_signature));
                continue;
            };
            if self.prefer_override_candidate(candidate, current, method) {
                best = Some((candidate, candidate_signature));
            }
        }
        Ok(best.map(|(candidate, signature)| (candidate.clone(), signature)))
    }

    fn instantiated_signature_matches(
        &self,
        candidate: &MethodDetails,
        signature: Option<&MethodSignature>,
        method: &MethodDetails,
    ) -> bool {
        let instantiated_parameters = signature
            .map(MethodSignature::parameter_erasures)
            .unwrap_or_else(|| candidate.params.clone());
        instantiated_parameters
            .iter()
            .zip(&method.params)
            .all(|(left, right)| {
                matches!(
                    (erased_type_key(left), erased_type_key(right)),
                    (Some(left), Some(right)) if left == right
                )
            })
            && self.return_type_compatible(
                &signature.map_or_else(
                    || candidate.return_type.clone(),
                    MethodSignature::return_erasure,
                ),
                &method.return_type,
            )
    }

    fn is_base_method(
        &self,
        ancestor: &ClassDetails,
        method: &MethodDetails,
    ) -> OverrideResult<bool> {
        for parent in &ancestor.parents {
            let Some(parent) = self.hierarchy.class_details(parent) else {
                continue;
            };
            if self
                .find_overridden_method(&parent, method, ancestor)?
                .is_some()
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn same_erased_signature(&self, left: &MethodDetails, right: &MethodDetails) -> bool {
        method_name(&left.reference.short_id) == method_name(&right.reference.short_id)
            && left.params.len() == right.params.len()
            && left.params.iter().zip(&right.params).all(|(left, right)| {
                matches!(
                    (erased_type_key(left), erased_type_key(right)),
                    (Some(left), Some(right)) if left == right
                )
            })
            && self.return_type_compatible(&left.return_type, &right.return_type)
    }

    fn prefer_override_candidate(
        &self,
        candidate: &MethodDetails,
        current: &MethodDetails,
        method: &MethodDetails,
    ) -> bool {
        let candidate_exact = candidate.reference.short_id == method.reference.short_id;
        let current_exact = current.reference.short_id == method.reference.short_id;
        if candidate_exact != current_exact {
            return candidate_exact;
        }

        let candidate_bridge = candidate.access_flags.is_bridge();
        let current_bridge = current.access_flags.is_bridge();
        if candidate_bridge != current_bridge {
            return !candidate_bridge;
        }

        false
    }

    fn return_type_compatible(&self, base: &ArgType, method: &ArgType) -> bool {
        if base == method {
            return true;
        }
        match (base, method) {
            (ArgType::Object(base), ArgType::Object(method)) => {
                base == "java/lang/Object" || self.is_subtype(method, base)
            }
            (ArgType::Object(base), ArgType::Array(_)) => base == "java/lang/Object",
            _ => false,
        }
    }

    fn is_subtype(&self, ty: &str, base: &str) -> bool {
        let mut queue = VecDeque::from([ArgType::object(ty)]);
        let mut seen = BTreeSet::new();
        while let Some(next) = queue.pop_front() {
            let Some(details) = self.hierarchy.class_details(&next) else {
                continue;
            };
            if !seen.insert(details.descriptor.clone()) {
                continue;
            }
            if details.descriptor == format!("L{base};") {
                return true;
            }
            queue.extend(details.parents);
        }
        false
    }
}

impl ClassDetails {
    fn is_raw_instantiation(&self) -> bool {
        self.instantiated_self
            .as_ref()
            .is_some_and(|instantiated| class_is_raw_instantiation(self, instantiated))
    }
}

fn method_is_not_overridable(method: &MethodDetails) -> bool {
    method.reference.short_id.starts_with("<init>(")
        || method.reference.short_id.starts_with("<clinit>(")
        || method.access_flags.is_static()
        || method.access_flags.is_private()
        || method.access_flags.is_bridge()
}

fn method_name(short_id: &str) -> &str {
    short_id.split_once('(').map_or(short_id, |(name, _)| name)
}

fn erased_type_key(ty: &ArgType) -> Option<String> {
    match ty {
        ArgType::Object(name) => Some(format!("L{name};")),
        ArgType::Unknown(_) => None,
        ArgType::Array(element) => Some(format!("[{}", erased_type_key(element)?)),
        ArgType::Primitive(_) => Some(ty.to_descriptor()),
    }
}

pub(crate) fn bind_class<H: ClassHierarchy>(
    hierarchy: &H,
    class: &ClassDetails,
    instantiated_self: &JvmTypeSignature,
) -> OverrideResult<ClassDetails> {
    let raw_instantiation = class_type_signature_from_java_signature(instantiated_self)
        .is_some_and(|instantiated| class_is_raw_instantiation(class, instantiated));
    let substitutions = class_type_substitution(hierarchy, class, instantiated_self)?;
    let generic_parents = if raw_instantiation {
        class
            .parents
            .iter()
            .map(arg_type_to_signature)
            .collect::<OverrideResult<Vec<_>>>()?
    } else {
        class
            .generic_parents
            .iter()
            .map(|parent| parent.substitute(&substitutions))
            .collect::<Result<Vec<_>, _>>()?
    };
    let parents = generic_parents
        .iter()
        .map(signature_erased_arg_type)
        .collect::<Vec<_>>();
    let methods = class
        .methods
        .iter()
        .map(|method| {
            Ok(MethodDetails {
                reference: method.reference.clone(),
                params: method.params.clone(),
                return_type: method.return_type.clone(),
                generic_signature: if raw_instantiation {
                    None
                } else {
                    method
                        .generic_signature
                        .as_ref()
                        .map(|signature| signature.substitute(&substitutions))
                        .transpose()?
                },
                throws: method.throws.clone(),
                access_flags: method.access_flags,
            })
        })
        .collect::<OverrideResult<Vec<_>>>()?;

    Ok(ClassDetails {
        descriptor: class.descriptor.clone(),
        package: class.package.clone(),
        access_flags: class.access_flags,
        parents,
        generic_parents,
        generic_signature: class.generic_signature.clone(),
        instantiated_self: class_type_signature_from_java_signature(instantiated_self).cloned(),
        methods,
    })
}

fn class_is_raw_instantiation(class: &ClassDetails, instantiated: &ClassTypeSignature) -> bool {
    class
        .generic_signature
        .as_ref()
        .is_some_and(|signature| !signature.type_parameters.is_empty())
        && instantiated
            .owner_scopes()
            .find(|scope| format!("L{};", scope.erased_name()) == class.descriptor)
            .is_some_and(|scope| scope.type_arguments().is_empty())
}

fn instantiate_method_signature(
    class: &ClassDetails,
    signature: &MethodSignature,
) -> Result<MethodSignature, SignatureSubstitutionError> {
    let substitutions = class_self_substitution(class);
    signature.substitute(&substitutions)
}

fn class_type_substitution<H: ClassHierarchy>(
    hierarchy: &H,
    class: &ClassDetails,
    instantiated_self: &JvmTypeSignature,
) -> OverrideResult<TypeSubstitution> {
    let mut substitutions = TypeSubstitution::new();
    let JvmTypeSignature::ClassType(instantiated) = instantiated_self else {
        return Ok(substitutions);
    };

    for scope in instantiated.owner_scopes() {
        let descriptor = format!("L{};", scope.erased_name());
        if descriptor == class.descriptor {
            collect_scope_type_parameters(class, scope.type_arguments(), &mut substitutions)?;
        } else if let Some(owner) = hierarchy.class_details(&ArgType::object(scope.erased_name())) {
            collect_scope_type_parameters(&owner, scope.type_arguments(), &mut substitutions)?;
        }
    }
    Ok(substitutions)
}

fn collect_scope_type_parameters(
    declared: &ClassDetails,
    type_arguments: &[TypeArgument],
    substitutions: &mut TypeSubstitution,
) -> OverrideResult<()> {
    let Some(signature) = declared.generic_signature.as_ref() else {
        return Ok(());
    };
    let expected = signature.type_parameters.len();
    let actual = type_arguments.len();
    // Kotlin FunctionN and some SAM/lambda signatures omit a type
    // argument (commonly the return type). Keep analysis going as a
    // raw instantiation instead of failing the whole archive.
    if actual != 0 && actual != expected {
        return Ok(());
    }
    collect_instantiated_class_type_parameters(signature, type_arguments, substitutions)
}

fn class_self_substitution(class: &ClassDetails) -> TypeSubstitution {
    let mut substitutions = TypeSubstitution::new();
    let Some(class_signature) = class.generic_signature.as_ref() else {
        return substitutions;
    };
    collect_declared_class_type_parameters(class_signature, &mut substitutions);
    substitutions
}

fn collect_declared_class_type_parameters(
    declared: &ClassSignature,
    substitutions: &mut TypeSubstitution,
) {
    for type_parameter in &declared.type_parameters {
        substitutions.insert(
            type_parameter.name.clone(),
            TypeArgument::Exact(type_parameter.class_bound.clone().unwrap_or_else(|| {
                JvmTypeSignature::ClassType(parse_class_type_signature("java/lang/Object"))
            })),
        );
    }
}

fn collect_instantiated_class_type_parameters(
    declared: &ClassSignature,
    type_arguments: &[TypeArgument],
    substitutions: &mut TypeSubstitution,
) -> OverrideResult<()> {
    for (type_parameter, arg) in declared.type_parameters.iter().zip(type_arguments) {
        substitutions.insert(type_parameter.name.clone(), arg.clone());
    }
    Ok(())
}

fn arg_type_to_signature(ty: &ArgType) -> OverrideResult<JvmTypeSignature> {
    Ok(match ty {
        ArgType::Primitive(
            primitive @ (crate::ir::PrimitiveType::Object | crate::ir::PrimitiveType::Array),
        ) => {
            return Err(OverrideAnalysisError::UnresolvedType(ArgType::Primitive(
                *primitive,
            )));
        }
        ArgType::Primitive(primitive) => JvmTypeSignature::BaseType(*primitive),
        ArgType::Object(name) => JvmTypeSignature::ClassType(parse_class_type_signature(name)),
        ArgType::Array(element) => {
            JvmTypeSignature::Array(Box::new(arg_type_to_signature(element)?))
        }
        ArgType::Unknown(_) => return Err(OverrideAnalysisError::UnresolvedType(ty.clone())),
    })
}

fn validate_hierarchy_type(ty: &ArgType) -> OverrideResult<()> {
    match ty {
        ArgType::Object(_) => Ok(()),
        _ => Err(OverrideAnalysisError::UnresolvedType(ty.clone())),
    }
}

fn validate_concrete_type(ty: &ArgType) -> OverrideResult<()> {
    match ty {
        ArgType::Primitive(crate::ir::PrimitiveType::Object | crate::ir::PrimitiveType::Array) => {
            Err(OverrideAnalysisError::UnresolvedType(ty.clone()))
        }
        ArgType::Primitive(_) | ArgType::Object(_) => Ok(()),
        ArgType::Array(element) => validate_concrete_type(element),
        ArgType::Unknown(_) => Err(OverrideAnalysisError::UnresolvedType(ty.clone())),
    }
}

fn signature_erased_arg_type(signature: &JvmTypeSignature) -> ArgType {
    signature.erased()
}

fn parse_class_type_signature(raw_name: &str) -> crate::ir::generic_types::ClassTypeSignature {
    crate::ir::generic_types::ClassTypeSignature {
        raw_name: raw_name.to_string(),
        type_arguments: Vec::new(),
        inner_segments: Vec::new(),
    }
}

fn class_type_signature_from_java_signature(
    signature: &JvmTypeSignature,
) -> Option<&ClassTypeSignature> {
    match signature {
        JvmTypeSignature::ClassType(class_type) => Some(class_type),
        _ => None,
    }
}

fn method_visible_from(
    method: &MethodDetails,
    declaring_class: &ClassDetails,
    owner: &ClassDetails,
) -> bool {
    if method.access_flags.is_private() {
        return false;
    }
    if owner.access_flags.is_interface() && declaring_class.descriptor == "Ljava/lang/Object;" {
        return method.access_flags.is_public();
    }
    if method.access_flags.is_public() || method.access_flags.is_protected() {
        return true;
    }
    declaring_class.package == owner.package
}

#[derive(Debug, Clone, Default)]
pub(crate) struct LoadedClassHierarchy {
    classes: BTreeMap<String, ClassDetails>,
}

impl LoadedClassHierarchy {
    fn decode(reader: &DexFileReader) -> OverrideResult<(Self, Vec<AnalysisDiagnostic>)> {
        Self::decode_classes(reader.classes())
    }

    fn decode_classes<'a>(
        classes: impl IntoIterator<Item = &'a ClassNode>,
    ) -> OverrideResult<(Self, Vec<AnalysisDiagnostic>)> {
        let mut decoder = MetadataDecoder::default();
        let classes = classes
            .into_iter()
            .map(|class| decoder.class(class))
            .collect::<OverrideResult<Vec<_>>>()?
            .into_iter()
            .map(|class| (class.descriptor.clone(), class))
            .collect();
        Ok((Self { classes }, decoder.diagnostics))
    }
}

#[derive(Debug, Clone)]
pub(crate) struct GenericTypeHierarchy {
    hierarchy: CompositeClassHierarchy,
}

impl GenericTypeHierarchy {
    pub(crate) fn from_classes<'a>(
        classes: impl IntoIterator<Item = &'a ClassNode>,
    ) -> OverrideResult<Self> {
        let (loaded, _) = LoadedClassHierarchy::decode_classes(classes)?;
        Ok(Self {
            hierarchy: CompositeClassHierarchy::from_loaded(loaded)?,
        })
    }

    pub(crate) fn inherited_method_signature(
        &self,
        instantiated_type: &JvmTypeSignature,
        method: &crate::ir::MethodReference,
    ) -> Option<MethodSignature> {
        let declared = self.hierarchy.class_details(&instantiated_type.erased())?;
        let bound = bind_class(&self.hierarchy, &declared, instantiated_type).ok()?;
        let mut classes = vec![bound.clone()];
        classes.extend(
            collect_instantiated_super_types(&self.hierarchy, &bound)
                .ok()?
                .into_iter(),
        );
        let owner = method.owner.to_descriptor();
        let short_id = format!("{}{}", method.name, method.descriptor);
        classes
            .into_iter()
            .find(|class| class.descriptor == owner)
            .and_then(|class| {
                class
                    .methods
                    .into_iter()
                    .find(|candidate| candidate.reference.short_id == short_id)
            })
            .and_then(|method| method.generic_signature)
    }

    pub(crate) fn declared_type_parameters(&self, ty: &ArgType) -> Option<Vec<TypeParameter>> {
        self.hierarchy.class_details(ty).map(|class| {
            class
                .generic_signature
                .map(|signature| signature.type_parameters)
                .unwrap_or_default()
        })
    }

    pub(crate) fn is_subtype(&self, subtype: &ArgType, supertype: &ArgType) -> bool {
        let mut pending = VecDeque::from([subtype.clone()]);
        let mut visited = BTreeSet::new();
        while let Some(candidate) = pending.pop_front() {
            if candidate == *supertype {
                return true;
            }
            if !visited.insert(candidate.clone()) {
                continue;
            }
            let Some(declared) = self.hierarchy.class_details(&candidate) else {
                continue;
            };
            pending.extend(declared.parents);
        }
        false
    }

    pub(crate) fn functional_interface(
        &self,
        interfaces: &[ArgType],
        implementation_name: &str,
        implementation_parameters: &[ArgType],
    ) -> Option<ArgType> {
        let implementation = (
            implementation_name.to_string(),
            implementation_parameters.to_vec(),
        );
        let object_methods = self.instance_method_keys(&ArgType::object("java/lang/Object"));
        let mut candidates = interfaces
            .iter()
            .filter(|interface| {
                let methods = self.interface_methods(interface);
                let abstract_methods = methods
                    .into_iter()
                    .filter_map(|(key, is_abstract)| {
                        (is_abstract && !object_methods.contains(&key)).then_some(key)
                    })
                    .collect::<BTreeSet<_>>();
                abstract_methods.len() == 1 && abstract_methods.contains(&implementation)
            })
            .cloned();
        let interface = candidates.next()?;
        candidates.next().is_none().then_some(interface)
    }

    fn interface_methods(&self, interface: &ArgType) -> BTreeMap<(String, Vec<ArgType>), bool> {
        let mut methods = BTreeMap::new();
        let mut pending = VecDeque::from([interface.clone()]);
        let mut visited = BTreeSet::new();
        while let Some(candidate) = pending.pop_front() {
            if !visited.insert(candidate.clone()) {
                continue;
            }
            let Some(declared) = self.hierarchy.class_details(&candidate) else {
                continue;
            };
            for method in declared.methods {
                if method.access_flags.is_static() || method.access_flags.is_private() {
                    continue;
                }
                let Some(reference) = Self::ir_method_reference(&method.reference) else {
                    continue;
                };
                methods
                    .entry((reference.name, reference.descriptor.parameters))
                    .or_insert_with(|| method.access_flags.is_abstract());
            }
            pending.extend(declared.parents);
        }
        methods
    }

    fn instance_method_keys(&self, owner: &ArgType) -> BTreeSet<(String, Vec<ArgType>)> {
        self.hierarchy
            .class_details(owner)
            .into_iter()
            .flat_map(|declared| declared.methods)
            .filter(|method| {
                !method.access_flags.is_static()
                    && !method.access_flags.is_private()
                    && !method.access_flags.is_constructor()
            })
            .filter_map(|method| {
                let reference = Self::ir_method_reference(&method.reference)?;
                Some((reference.name, reference.descriptor.parameters))
            })
            .collect()
    }

    fn ir_method_reference(
        reference: &crate::frontend::MethodReference,
    ) -> Option<crate::ir::MethodReference> {
        format!("{}->{}", reference.declaring_class, reference.short_id)
            .parse()
            .ok()
    }

    pub(crate) fn method_overloads(
        &self,
        method: &crate::ir::MethodReference,
    ) -> Vec<crate::ir::MethodReference> {
        let mut overloads = BTreeSet::new();
        let mut pending = vec![method.owner.clone()];
        let mut visited = BTreeSet::new();
        while let Some(owner) = pending.pop() {
            if !visited.insert(owner.clone()) {
                continue;
            }
            let Some(declared) = self.hierarchy.class_details(&owner) else {
                continue;
            };
            overloads.extend(
                declared
                    .methods
                    .iter()
                    .filter_map(|candidate| Self::ir_method_reference(&candidate.reference))
                    .filter(|candidate| {
                        candidate.name == method.name
                            && candidate.descriptor.parameters.len()
                                == method.descriptor.parameters.len()
                    })
                    .map(|candidate| crate::ir::MethodReference {
                        owner: method.owner.clone(),
                        name: candidate.name,
                        descriptor: candidate.descriptor,
                    }),
            );
            pending.extend(declared.parents);
        }
        overloads.into_iter().collect()
    }

    pub(crate) fn method_contract(
        &self,
        method: &crate::ir::MethodReference,
    ) -> Option<GenericMethodContract> {
        let declared = self.hierarchy.class_details(&method.owner)?;
        let owner_parameters = declared
            .generic_signature
            .as_ref()
            .map(|signature| signature.type_parameters.clone())
            .unwrap_or_default();
        let owner_type_parameters = declared
            .generic_signature
            .as_ref()
            .map(|signature| {
                signature
                    .type_parameters
                    .iter()
                    .map(|parameter| parameter.name.clone())
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let raw_name = method.owner.as_object()?.to_string();
        let open_owner = ClassTypeSignature {
            raw_name,
            type_arguments: owner_type_parameters
                .iter()
                .map(|parameter| {
                    TypeArgument::Exact(JvmTypeSignature::TypeVariable(parameter.clone()))
                })
                .collect(),
            inner_segments: Vec::new(),
        };
        let bound = bind_class(
            &self.hierarchy,
            &declared,
            &JvmTypeSignature::ClassType(open_owner.clone()),
        )
        .ok()?;
        let mut classes = vec![bound.clone()];
        if !method.is_constructor() {
            classes.extend(collect_instantiated_super_types(&self.hierarchy, &bound).ok()?);
        }
        let short_id = format!("{}{}", method.name, method.descriptor);
        let signature = classes.into_iter().find_map(|class| {
            class
                .methods
                .into_iter()
                .find(|candidate| candidate.reference.short_id == short_id)
                .and_then(|method| method.generic_signature)
        });
        signature
            .map(|signature| GenericMethodContract {
                signature,
                owner: open_owner.clone(),
                owner_parameters: owner_parameters.clone(),
            })
            .or_else(|| {
                method.is_constructor().then(|| {
                    GenericMethodContract::erased_constructor(
                        open_owner,
                        owner_parameters,
                        &method.descriptor.parameters,
                        &[],
                    )
                })?
            })
    }

    pub(crate) fn specialize_subtype(
        &self,
        subtype: &ArgType,
        expected_supertype: &JvmTypeSignature,
    ) -> Option<JvmTypeSignature> {
        self.solve_subtype(subtype, expected_supertype, true)
    }

    pub(crate) fn infer_subtype(
        &self,
        subtype: &ArgType,
        expected_supertype: &JvmTypeSignature,
    ) -> Option<JvmTypeSignature> {
        self.solve_subtype(subtype, expected_supertype, false)
    }

    fn solve_subtype(
        &self,
        subtype: &ArgType,
        expected_supertype: &JvmTypeSignature,
        complete: bool,
    ) -> Option<JvmTypeSignature> {
        let raw_name = subtype.as_object()?.to_string();
        let declared = self.hierarchy.class_details(subtype)?;
        let parameters = declared
            .generic_signature
            .as_ref()?
            .type_parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect::<Vec<_>>();
        if parameters.is_empty() {
            return None;
        }
        let mut occupied = BTreeSet::new();
        GenericHierarchyUnifier::collect_variables(expected_supertype, &mut occupied);
        let inference_parameters = parameters
            .iter()
            .enumerate()
            .map(|(index, _)| {
                let mut suffix = 0usize;
                loop {
                    let candidate = format!("__dexdec_subtype_{index}_{suffix}");
                    if occupied.insert(candidate.clone()) {
                        break candidate;
                    }
                    suffix += 1;
                }
            })
            .collect::<Vec<_>>();
        let open_subtype = JvmTypeSignature::ClassType(ClassTypeSignature {
            raw_name,
            type_arguments: inference_parameters
                .iter()
                .map(|parameter| {
                    TypeArgument::Exact(JvmTypeSignature::TypeVariable(parameter.clone()))
                })
                .collect(),
            inner_segments: Vec::new(),
        });
        let bound = bind_class(&self.hierarchy, &declared, &open_subtype).ok()?;
        let expected_erasure = expected_supertype.erased();
        let mut hierarchy = vec![bound.clone()];
        hierarchy.extend(collect_instantiated_super_types(&self.hierarchy, &bound).ok()?);
        let projected = hierarchy
            .into_iter()
            .find(|candidate| {
                candidate
                    .instantiated_self
                    .as_ref()
                    .is_some_and(|candidate| {
                        JvmTypeSignature::ClassType(candidate.clone()).erased() == expected_erasure
                    })
            })?
            .instantiated_self
            .map(JvmTypeSignature::ClassType)?;
        let variables = inference_parameters
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut substitutions = TypeSubstitution::new();
        if !GenericHierarchyUnifier::relate(
            &projected,
            expected_supertype,
            &variables,
            &mut substitutions,
        ) {
            return None;
        }
        if complete {
            return inference_parameters
                .iter()
                .all(|parameter| substitutions.contains_key(parameter))
                .then(|| open_subtype.substitute(&substitutions).ok())
                .flatten();
        }
        let JvmTypeSignature::ClassType(open_subtype) = open_subtype else {
            return None;
        };
        Some(JvmTypeSignature::ClassType(ClassTypeSignature {
            raw_name: open_subtype.raw_name,
            type_arguments: inference_parameters
                .into_iter()
                .map(|parameter| {
                    substitutions
                        .remove(&parameter)
                        .unwrap_or(TypeArgument::Unbounded)
                })
                .collect(),
            inner_segments: open_subtype.inner_segments,
        }))
    }

    pub(crate) fn project_supertype(
        &self,
        subtype: &JvmTypeSignature,
        expected_supertype: &ArgType,
    ) -> Option<JvmTypeSignature> {
        let declared = self.hierarchy.class_details(&subtype.erased())?;
        let declared_parameters = declared
            .generic_signature
            .as_ref()
            .map(|signature| signature.type_parameters.len())
            .unwrap_or_default();
        let supplied_arguments = match subtype {
            JvmTypeSignature::ClassType(class) => {
                class.type_arguments.len()
                    + class
                        .inner_segments
                        .iter()
                        .map(|segment| segment.type_arguments.len())
                        .sum::<usize>()
            }
            JvmTypeSignature::TypeVariable(_)
            | JvmTypeSignature::Array(_)
            | JvmTypeSignature::BaseType(_) => 0,
        };
        if supplied_arguments < declared_parameters {
            return None;
        }
        let bound = bind_class(&self.hierarchy, &declared, subtype).ok()?;
        let super_types = collect_instantiated_super_types(&self.hierarchy, &bound).ok()?;
        std::iter::once(bound)
            .chain(super_types)
            .find_map(|candidate| {
                candidate
                    .instantiated_self
                    .filter(|candidate| {
                        JvmTypeSignature::ClassType(candidate.clone()).erased()
                            == *expected_supertype
                    })
                    .map(JvmTypeSignature::ClassType)
            })
    }

    pub(crate) fn project_member_type(
        &self,
        instantiated_owner: &JvmTypeSignature,
        declaring_owner: &ClassTypeSignature,
        member_type: &JvmTypeSignature,
    ) -> Option<JvmTypeSignature> {
        member_type
            .substitute(&self.member_substitution(instantiated_owner, declaring_owner)?)
            .ok()
    }

    pub(crate) fn project_method_signature(
        &self,
        instantiated_owner: &JvmTypeSignature,
        declaring_owner: &ClassTypeSignature,
        signature: &MethodSignature,
    ) -> Option<MethodSignature> {
        signature
            .substitute(&self.member_substitution(instantiated_owner, declaring_owner)?)
            .ok()
    }

    fn member_substitution(
        &self,
        instantiated_owner: &JvmTypeSignature,
        declaring_owner: &ClassTypeSignature,
    ) -> Option<TypeSubstitution> {
        let owner = self.hierarchy.class_details(&instantiated_owner.erased())?;
        let bound = bind_class(&self.hierarchy, &owner, instantiated_owner).ok()?;
        let super_types = collect_instantiated_super_types(&self.hierarchy, &bound).ok()?;
        let declaring_erasure = JvmTypeSignature::ClassType(declaring_owner.clone()).erased();
        let projected_owner = std::iter::once(bound)
            .chain(super_types)
            .find_map(|candidate| {
                candidate.instantiated_self.filter(|candidate| {
                    JvmTypeSignature::ClassType(candidate.clone()).erased() == declaring_erasure
                })
            })?;
        let declaration = self.hierarchy.class_details(&declaring_erasure)?;
        let substitutions = class_type_substitution(
            &self.hierarchy,
            &declaration,
            &JvmTypeSignature::ClassType(projected_owner),
        )
        .ok()?;
        Some(substitutions)
    }
}

struct GenericHierarchyUnifier;

impl GenericHierarchyUnifier {
    fn collect_variables(signature: &JvmTypeSignature, variables: &mut BTreeSet<String>) {
        let mut pending = vec![signature];
        while let Some(signature) = pending.pop() {
            match signature {
                JvmTypeSignature::TypeVariable(variable) => {
                    variables.insert(variable.clone());
                }
                JvmTypeSignature::Array(element) => pending.push(element),
                JvmTypeSignature::ClassType(class) => {
                    pending.extend(
                        class
                            .type_arguments
                            .iter()
                            .chain(
                                class
                                    .inner_segments
                                    .iter()
                                    .flat_map(|segment| &segment.type_arguments),
                            )
                            .filter_map(|argument| match argument {
                                TypeArgument::Unbounded => None,
                                TypeArgument::Exact(ty)
                                | TypeArgument::Extends(ty)
                                | TypeArgument::Super(ty) => Some(ty),
                            }),
                    );
                }
                JvmTypeSignature::BaseType(_) => {}
            }
        }
    }

    fn relate(
        template: &JvmTypeSignature,
        actual: &JvmTypeSignature,
        variables: &BTreeSet<String>,
        substitutions: &mut TypeSubstitution,
    ) -> bool {
        match (template, actual) {
            (JvmTypeSignature::TypeVariable(variable), actual) if variables.contains(variable) => {
                let actual = TypeArgument::Exact(actual.clone());
                match substitutions.get(variable) {
                    Some(current) => current == &actual,
                    None => {
                        substitutions.insert(variable.clone(), actual);
                        true
                    }
                }
            }
            (JvmTypeSignature::Array(template), JvmTypeSignature::Array(actual)) => {
                Self::relate(template, actual, variables, substitutions)
            }
            (JvmTypeSignature::ClassType(template), JvmTypeSignature::ClassType(actual))
                if template.erased_name() == actual.erased_name() =>
            {
                let template_arguments = std::iter::once(template.type_arguments.as_slice()).chain(
                    template
                        .inner_segments
                        .iter()
                        .map(|segment| segment.type_arguments.as_slice()),
                );
                let actual_arguments = std::iter::once(actual.type_arguments.as_slice()).chain(
                    actual
                        .inner_segments
                        .iter()
                        .map(|segment| segment.type_arguments.as_slice()),
                );
                template_arguments.zip(actual_arguments).all(
                    |(template_arguments, actual_arguments)| {
                        template_arguments.len() == actual_arguments.len()
                            && template_arguments.iter().zip(actual_arguments).all(
                                |(template, actual)| {
                                    Self::relate_argument(
                                        template,
                                        actual,
                                        variables,
                                        substitutions,
                                    )
                                },
                            )
                    },
                )
            }
            (JvmTypeSignature::BaseType(template), JvmTypeSignature::BaseType(actual)) => {
                template == actual
            }
            _ => template == actual,
        }
    }

    fn relate_argument(
        template: &TypeArgument,
        actual: &TypeArgument,
        variables: &BTreeSet<String>,
        substitutions: &mut TypeSubstitution,
    ) -> bool {
        let template = match template {
            TypeArgument::Unbounded => return true,
            TypeArgument::Exact(template)
            | TypeArgument::Extends(template)
            | TypeArgument::Super(template) => template,
        };
        let actual = match actual {
            TypeArgument::Unbounded => return true,
            TypeArgument::Exact(actual)
            | TypeArgument::Extends(actual)
            | TypeArgument::Super(actual) => actual,
        };
        Self::relate(template, actual, variables, substitutions)
    }
}

pub fn platform_generic_method_contract(
    method: &crate::ir::MethodReference,
) -> Result<Option<GenericMethodContract>, OverrideAnalysisError> {
    let hierarchy = GenericTypeHierarchy::from_classes(std::iter::empty::<&ClassNode>())?;
    Ok(hierarchy.method_contract(method))
}

impl ClassHierarchy for LoadedClassHierarchy {
    fn class_details(&self, ty: &ArgType) -> Option<ClassDetails> {
        let descriptor = ty.to_descriptor();
        self.classes.get(&descriptor).cloned()
    }
}

#[derive(Debug, Clone)]
pub(crate) struct CompositeClassHierarchy {
    loaded: LoadedClassHierarchy,
    platform: Option<Arc<PlatformClassSet>>,
}

impl CompositeClassHierarchy {
    fn from_loaded(loaded: LoadedClassHierarchy) -> OverrideResult<Self> {
        Ok(Self {
            loaded,
            platform: Some(PlatformClassSet::default_cached()?),
        })
    }
}

impl ClassHierarchy for CompositeClassHierarchy {
    fn class_details(&self, ty: &ArgType) -> Option<ClassDetails> {
        self.loaded.class_details(ty).or_else(|| {
            self.platform
                .as_ref()
                .and_then(|platform| platform.class_details(ty))
        })
    }
}

#[derive(Debug, Clone)]
pub(crate) struct PlatformClassSet {
    symbols: Arc<PlatformSymbolSet>,
    details: Arc<std::sync::RwLock<BTreeMap<String, ClassDetails>>>,
}

impl PlatformClassSet {
    pub fn load_default() -> io::Result<Self> {
        Ok(Self {
            symbols: default_platform_symbols()?,
            details: Arc::new(std::sync::RwLock::new(BTreeMap::new())),
        })
    }

    pub fn default_cached() -> io::Result<Arc<Self>> {
        static DEFAULT_SYMBOLS: OnceLock<Arc<PlatformClassSet>> = OnceLock::new();
        if let Some(platform) = DEFAULT_SYMBOLS.get() {
            return Ok(Arc::clone(platform));
        }
        let platform = Arc::new(Self::load_default()?);
        match DEFAULT_SYMBOLS.set(Arc::clone(&platform)) {
            Ok(()) => Ok(platform),
            Err(_) => DEFAULT_SYMBOLS.get().map(Arc::clone).ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::Other,
                    "platform symbol cache publication failed",
                )
            }),
        }
    }

    fn class_details(&self, ty: &ArgType) -> Option<ClassDetails> {
        let descriptor = ty.to_descriptor();
        if let Some(details) = self
            .details
            .read()
            .ok()
            .and_then(|details| details.get(&descriptor).cloned())
        {
            return Some(details);
        }
        let details = platform_class_details(self.symbols.class(&descriptor)?).ok()?;
        if let Ok(mut cache) = self.details.write() {
            cache.entry(descriptor).or_insert_with(|| details.clone());
        }
        Some(details)
    }
}

fn platform_class_details(class: &PlatformClass) -> io::Result<ClassDetails> {
    let generic_signature = class
        .signature
        .as_deref()
        .map(GenericSignatures::class)
        .transpose()
        .map_err(platform_signature_error)?;
    let parents = class
        .super_class
        .iter()
        .chain(&class.interfaces)
        .map(|descriptor| parse_platform_type(descriptor))
        .collect::<io::Result<Vec<_>>>()?;
    let generic_parents = if let Some(signature) = &generic_signature {
        std::iter::once(&signature.super_class)
            .chain(&signature.super_interfaces)
            .cloned()
            .map(JvmTypeSignature::ClassType)
            .collect()
    } else {
        parents
            .iter()
            .map(platform_type_signature)
            .collect::<io::Result<Vec<_>>>()?
    };
    if parents.len() != generic_parents.len() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "{} has inconsistent erased and generic parent lists",
                class.descriptor
            ),
        ));
    }
    let methods = class
        .methods
        .iter()
        .map(|method| {
            let descriptor = method
                .descriptor
                .parse::<crate::ir::MethodDescriptor>()
                .map_err(|source| {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!(
                            "{}->{}{} has an invalid descriptor: {source}",
                            class.descriptor, method.name, method.descriptor
                        ),
                    )
                })?;
            let generic_signature = method
                .signature
                .as_deref()
                .map(GenericSignatures::method)
                .transpose()
                .map_err(platform_signature_error)?;
            let throws = method
                .exceptions
                .iter()
                .map(|descriptor| parse_platform_type(descriptor))
                .collect::<io::Result<Vec<_>>>()?;
            let mut access_flags = method.access_flags;
            if method.name == "<init>" {
                access_flags |= crate::frontend::access_flags::CONSTRUCTOR;
            }
            Ok(MethodDetails {
                reference: MethodReference {
                    declaring_class: class.descriptor.clone(),
                    short_id: format!("{}{}", method.name, method.descriptor),
                },
                params: descriptor.parameters,
                return_type: descriptor.return_type,
                generic_signature,
                throws,
                access_flags: AccessInfo::for_method(access_flags),
            })
        })
        .collect::<io::Result<Vec<_>>>()?;
    Ok(ClassDetails {
        descriptor: class.descriptor.clone(),
        package: platform_package(&class.descriptor),
        access_flags: AccessInfo::for_class(class.access_flags),
        parents,
        generic_parents,
        generic_signature,
        instantiated_self: None,
        methods,
    })
}

fn parse_platform_type(descriptor: &str) -> io::Result<ArgType> {
    descriptor.parse::<ArgType>().map_err(|source| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("invalid platform type descriptor {descriptor}: {source}"),
        )
    })
}

fn platform_type_signature(ty: &ArgType) -> io::Result<JvmTypeSignature> {
    match ty {
        ArgType::Object(name) => Ok(JvmTypeSignature::ClassType(parse_class_type_signature(
            name,
        ))),
        _ => Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("platform hierarchy parent {ty} is not a class type"),
        )),
    }
}

fn platform_signature_error(source: impl std::fmt::Display) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!("invalid platform generic signature: {source}"),
    )
}

fn platform_package(descriptor: &str) -> String {
    descriptor
        .strip_prefix('L')
        .and_then(|value| value.strip_suffix(';'))
        .unwrap_or(descriptor)
        .rsplit_once('/')
        .map(|(package, _)| package.replace('/', "."))
        .unwrap_or_default()
}

pub(crate) fn platform_exception_contracts(
) -> io::Result<Arc<BTreeMap<crate::ir::MethodReference, Vec<ArgType>>>> {
    static CONTRACTS: OnceLock<Arc<BTreeMap<crate::ir::MethodReference, Vec<ArgType>>>> =
        OnceLock::new();
    if let Some(contracts) = CONTRACTS.get() {
        return Ok(Arc::clone(contracts));
    }
    let platform = default_platform_symbols()?;
    let contracts = Arc::new(
        platform
            .classes()
            .flat_map(|class| {
                class.methods.iter().filter_map(move |method| {
                    (!method.exceptions.is_empty()).then(|| {
                        let owner = class.descriptor.parse().ok()?;
                        let descriptor = method.descriptor.parse().ok()?;
                        let throws = method
                            .exceptions
                            .iter()
                            .map(|exception| exception.parse())
                            .collect::<Result<Vec<_>, _>>()
                            .ok()?;
                        Some((
                            crate::ir::MethodReference {
                                owner,
                                name: method.name.clone(),
                                descriptor,
                            },
                            throws,
                        ))
                    })?
                })
            })
            .collect(),
    );
    match CONTRACTS.set(Arc::clone(&contracts)) {
        Ok(()) => Ok(contracts),
        Err(_) => CONTRACTS.get().map(Arc::clone).ok_or_else(|| {
            io::Error::new(io::ErrorKind::Other, "contract cache publication failed")
        }),
    }
}

pub(crate) fn preload_platform_symbols() -> OverrideResult<()> {
    default_platform_symbols()?;
    platform_hierarchy_index()?;
    platform_exception_contracts()?;
    Ok(())
}

fn platform_hierarchy_index() -> OverrideResult<Arc<ClassHierarchyIndex>> {
    static PLATFORM_HIERARCHY: OnceLock<Arc<ClassHierarchyIndex>> = OnceLock::new();
    PLATFORM_HIERARCHY
        .get()
        .map(Arc::clone)
        .map(Ok)
        .unwrap_or_else(|| {
            let platform = default_platform_symbols()?;
            let mut index = ClassHierarchyIndex::default();
            for class in platform.classes() {
                let class_name = hierarchy_object_name(&class.descriptor)?;
                let parents = class
                    .super_class
                    .iter()
                    .chain(&class.interfaces)
                    .map(|parent| hierarchy_object_name(parent))
                    .collect::<OverrideResult<Vec<_>>>()?;
                index.add_declared_type(
                    class_name,
                    parents,
                    ReferenceTypeInfo {
                        is_interface: class.access_flags & 0x0200 != 0,
                        is_final: class.access_flags & 0x0010 != 0,
                    },
                );
            }
            let index = Arc::new(index);
            match PLATFORM_HIERARCHY.set(Arc::clone(&index)) {
                Ok(()) => Ok(index),
                Err(_) => PLATFORM_HIERARCHY.get().map(Arc::clone).ok_or_else(|| {
                    OverrideAnalysisError::PlatformSymbols(io::Error::new(
                        io::ErrorKind::Other,
                        "hierarchy cache publication failed",
                    ))
                }),
            }
        })
}

pub(crate) fn type_hierarchy_index(reader: &DexFileReader) -> OverrideResult<ClassHierarchyIndex> {
    let platform = platform_hierarchy_index()?;
    let mut index = ClassHierarchyIndex::layered(platform);
    let declarations = reader
        .hierarchy_declarations()
        .map(|(class, superclass, interfaces, access)| {
            Ok((
                hierarchy_object_name(class)?,
                superclass
                    .into_iter()
                    .chain(interfaces.iter().map(String::as_str))
                    .map(hierarchy_object_name)
                    .collect::<OverrideResult<Vec<_>>>()?,
                ReferenceTypeInfo {
                    is_interface: access.is_interface(),
                    is_final: access.is_final(),
                },
            ))
        })
        .collect::<OverrideResult<Vec<_>>>()?;
    index.extend_declared_types(declarations);
    Ok(index)
}

fn hierarchy_object_name(descriptor: &str) -> OverrideResult<String> {
    descriptor
        .strip_prefix('L')
        .and_then(|name| name.strip_suffix(';'))
        .filter(|name| !name.is_empty())
        .map(str::to_string)
        .ok_or_else(|| {
            OverrideAnalysisError::PlatformSymbols(io::Error::new(
                io::ErrorKind::InvalidData,
                "invalid class descriptor",
            ))
        })
}

impl ClassHierarchy for PlatformClassSet {
    fn class_details(&self, ty: &ArgType) -> Option<ClassDetails> {
        PlatformClassSet::class_details(self, ty)
    }
}

impl OverrideAnalysisTarget for DexFileReader {
    fn set_method_override(
        &mut self,
        declaring_class: &str,
        method_short_id: &str,
        semantics: Option<MethodOverrideSemantics>,
    ) {
        let Some(class) = self.get_class_mut(declaring_class) else {
            return;
        };
        let Some(method) = class.find_method_mut(method_short_id) else {
            return;
        };
        method.override_semantics = semantics;
    }
}

#[derive(Default)]
struct MetadataDecoder {
    diagnostics: Vec<AnalysisDiagnostic>,
}

impl MetadataDecoder {
    fn class(&mut self, class: &ClassNode) -> OverrideResult<ClassDetails> {
        let generic_signature = self.class_signature(class);
        let mut parents = Vec::new();
        let mut generic_parents = Vec::new();
        if let Some(super_class) = &class.super_class {
            parents.push(super_class.clone());
            let candidate = generic_signature
                .as_ref()
                .map(|signature| &signature.super_class);
            generic_parents.push(Self::aligned_parent(super_class, candidate)?);
        }
        for interface in &class.interfaces {
            let candidate = generic_signature.as_ref().and_then(|signature| {
                signature
                    .super_interfaces
                    .iter()
                    .find(|candidate| ArgType::object(&candidate.erased_name()) == *interface)
            });
            parents.push(interface.clone());
            generic_parents.push(Self::aligned_parent(interface, candidate)?);
        }
        validate_hierarchy_type(class.class_type())?;
        for parent in &parents {
            validate_hierarchy_type(parent)?;
        }
        let methods = class
            .methods()
            .iter()
            .map(|method| self.method(method))
            .collect::<OverrideResult<Vec<_>>>()?;
        Ok(ClassDetails {
            descriptor: class.type_descriptor().to_string(),
            package: class.package().to_string(),
            access_flags: class.access_flags,
            parents,
            generic_parents,
            generic_signature,
            instantiated_self: None,
            methods,
        })
    }

    fn aligned_parent(
        erased: &ArgType,
        candidate: Option<&ClassTypeSignature>,
    ) -> OverrideResult<JvmTypeSignature> {
        if let Some(candidate) = candidate {
            if JvmTypeSignature::ClassType(candidate.clone()).erased() == *erased {
                return Ok(JvmTypeSignature::ClassType(candidate.clone()));
            }
        }
        arg_type_to_signature(erased)
    }

    fn method(&mut self, method: &MethodNode) -> OverrideResult<MethodDetails> {
        let reference = MethodReference {
            declaring_class: method.declaring_class().to_string(),
            short_id: method.short_id(),
        };
        let generic_signature = method.signature.as_deref().and_then(|signature| {
            match GenericSignatures::method(signature) {
                Ok(parsed) => {
                    let parameters_match = parsed.parameter_types.len()
                        == method.param_types().len()
                        && parsed
                            .parameter_types
                            .iter()
                            .map(JvmTypeSignature::erased)
                            .eq(method.param_types().iter().cloned());
                    let return_matches =
                        parsed.return_type.erased() == method.return_type().clone();
                    if parameters_match && return_matches {
                        Some(parsed)
                    } else {
                        self.diagnostics
                            .push(AnalysisDiagnostic::InconsistentGenericSignature {
                                location: AnalysisLocation::Method(reference.clone()),
                                signature: signature.to_string(),
                                reason: "erasure does not match the method descriptor".to_string(),
                            });
                        None
                    }
                }
                Err(error) => {
                    self.diagnostics
                        .push(AnalysisDiagnostic::InvalidGenericSignature {
                            location: AnalysisLocation::Method(reference.clone()),
                            signature: signature.to_string(),
                            offset: error.offset,
                        });
                    None
                }
            }
        });
        for parameter in method.param_types() {
            validate_concrete_type(parameter)?;
        }
        validate_concrete_type(method.return_type())?;
        Ok(MethodDetails {
            reference,
            params: method.param_types().to_vec(),
            return_type: method.return_type().clone(),
            generic_signature,
            throws: method.throws().to_vec(),
            access_flags: method.access_flags,
        })
    }

    fn class_signature(&mut self, class: &ClassNode) -> Option<ClassSignature> {
        class
            .signature
            .as_deref()
            .and_then(|signature| match GenericSignatures::class(signature) {
                Ok(parsed) => {
                    let erased = std::iter::once(&parsed.super_class)
                        .chain(&parsed.super_interfaces)
                        .map(|parent| JvmTypeSignature::ClassType(parent.clone()).erased());
                    let declared = class.super_class.iter().chain(&class.interfaces).cloned();
                    if erased.eq(declared) {
                        Some(parsed)
                    } else {
                        self.diagnostics
                            .push(AnalysisDiagnostic::InconsistentGenericSignature {
                                location: AnalysisLocation::Class(
                                    class.type_descriptor().to_string(),
                                ),
                                signature: signature.to_string(),
                                reason: "erasure does not match the declared parents".to_string(),
                            });
                        Some(parsed)
                    }
                }
                Err(error) => {
                    self.diagnostics
                        .push(AnalysisDiagnostic::InvalidGenericSignature {
                            location: AnalysisLocation::Class(class.type_descriptor().to_string()),
                            signature: signature.to_string(),
                            offset: error.offset,
                        });
                    None
                }
            })
    }
}

pub fn analyze_loaded_method_overrides(reader: &mut DexFileReader) -> OverrideResult<()> {
    let (loaded, diagnostics) = crate::profile_scope!(
        "override.loaded_hierarchy",
        LoadedClassHierarchy::decode(reader)
    )?;
    let classes = loaded.classes.values().cloned().collect::<Vec<_>>();
    let hierarchy = crate::profile_scope!(
        "override.composite_hierarchy",
        CompositeClassHierarchy::from_loaded(loaded)
    )?;
    crate::profile_scope!(
        "override.method_analysis",
        MethodOverrideAnalyzer::new(&hierarchy).analyze(reader, &classes)
    )?;
    reader.replace_analysis_diagnostics(diagnostics);
    Ok(())
}

#[cfg(test)]
#[path = "method_override/tests.rs"]
mod tests;
