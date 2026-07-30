use crate::analysis::{MethodRecoveryFailure, MethodRecoveryStage};
use crate::ir::generic_types::{ClassSignature, JvmTypeSignature, MethodSignature};
use crate::ir::ty::ArgType;
use crate::language::kotlin::{
    KotlinAnnotation, KotlinAssignOp, KotlinAstRewriter, KotlinAstTransform, KotlinClassName,
    KotlinClassType, KotlinCompilationUnit, KotlinExpr, KotlinExtensionReceiver,
    KotlinExtensionReceiverLowering, KotlinFieldDeclaration, KotlinFieldSymbol, KotlinIdentifier,
    KotlinLiteral, KotlinLocalBindingAnalysis, KotlinMemberNames, KotlinMethodBody,
    KotlinMethodDeclaration, KotlinMethodDeclarationKind, KotlinMethodParameter,
    KotlinMethodSymbol, KotlinModifier, KotlinMutableParameterLowering, KotlinNameUseAnalysis,
    KotlinNullabilityFacts, KotlinPropertyDeclaration, KotlinSmartCastLowering, KotlinStmt,
    KotlinType, KotlinTypeArgument, KotlinTypeDeclaration, KotlinTypeDeclarationKind,
};
use rayon::prelude::*;

use super::anonymous_lowering::{
    AnonymousClassRecovery, EnumConstantBodyRecovery, FunctionContract, LoweredNestedType,
    NestedTypeLiveness,
};
use super::constants::KotlinConstantLowering;
use super::constructor_syntax::ConstructorSyntaxRecovery;
use super::enum_lowering::{EnumDeclarationRecovery, EnumSwitchRecovery};
use super::function_object_types::FunctionObjectTypeCatalog;
use super::kotlin_model::method::{
    KotlinMethodDeclarationKind as MethodModelKind, KotlinMethodModel,
};
use super::kotlin_model::{KotlinClassKind, KotlinFieldDeclaration as FieldModel};
use super::kotlin_model::{KotlinClassModel, KotlinMethodDeclaration as MethodModel};
use super::member_names::ClassMemberNames;
use super::static_initialization::StaticInitializationRecovery;
use super::synthetic_members::SyntheticMemberRecovery;
use super::type_names::KotlinTypeNameResolver;
use super::type_uses::{ClassTypeUses, GenericTypeUses};
use super::KotlinDecompilerError;

pub(super) struct KotlinCompilationUnitLowering;

impl KotlinCompilationUnitLowering {
    pub(super) fn lower(
        class: &KotlinClassModel,
        source_abi: &std::sync::Arc<super::KotlinSourceAbi>,
        hierarchy: std::sync::Arc<crate::ir::analysis::ClassHierarchyIndex>,
        observer: std::sync::Arc<dyn crate::ir::AnalysisObserver>,
    ) -> Result<KotlinCompilationUnit, KotlinDecompilerError> {
        let package_name = class.declaration.package.clone();
        let package = package_name.as_ref().map(ToString::to_string);
        let current_type = class.declaration.current_type();
        let (field_references, method_references) =
            crate::profile_scope!("kotlin_backend.lower.references", {
                (class.field_references(), class.method_references())
            });
        let (
            generic_fields,
            generic_methods,
            method_nullability,
            referenced_overloads,
            referenced_constructors,
        ) = crate::profile_scope!("kotlin_backend.lower.abi", {
            (
                source_abi.generic_fields(field_references.iter()),
                source_abi.generic_methods(method_references.iter()),
                source_abi.referenced_nullability(method_references.iter()),
                source_abi.referenced_overloads(method_references.iter()),
                source_abi.referenced_constructors(method_references.iter()),
            )
        });
        let type_uses = crate::profile_scope!("kotlin_backend.lower.type_uses", {
            let mut type_uses = ClassTypeUses::collect(class);
            if let Some(owner) = current_type.as_ref() {
                type_uses.extend(source_abi.declared_source_types(owner));
            }
            type_uses.extend(source_abi.symbolic_constant_owner_types(method_references.iter()));
            for contract in generic_fields.values() {
                GenericTypeUses::field_contract(contract, &mut type_uses);
            }
            for contract in generic_methods.values() {
                GenericTypeUses::method_contract(contract, &mut type_uses);
            }
            type_uses
        });
        let names = crate::profile_scope!("kotlin_backend.lower.type_names", {
            KotlinTypeNameResolver::for_class(
                class,
                package.as_deref(),
                current_type.as_ref(),
                type_uses,
            )
        })?;
        let members = crate::profile_scope!("kotlin_backend.lower.member_names", {
            std::sync::Arc::new(
                ClassMemberNames::collect(class)
                    .with_source_names(source_abi.declared_source_names())
                    .with_property_accessors(
                        source_abi.declared_property_getters(),
                        source_abi.declared_property_setters(),
                    )
                    .with_constructor_layouts(referenced_constructors)
                    .with_overloads(referenced_overloads),
            )
        });
        let source_field_types = generic_fields
            .iter()
            .map(|(field, contract)| {
                Ok((
                    field.clone(),
                    names
                        .resolve_generic_type(&contract.signature)
                        .map_err(KotlinDecompilerError::from)?,
                ))
            })
            .collect::<Result<_, KotlinDecompilerError>>()?;
        let source_object_types = FunctionObjectTypeCatalog::collect(class)
            .into_iter()
            .map(|(identity, interface)| Ok((identity, names.resolve_generic_type(&interface)?)))
            .collect::<Result<_, KotlinDecompilerError>>()?;
        let outer_instances = source_abi
            .outer_instances()
            .chain(class.outer_instances())
            .map(|(field, outer)| (field.clone(), outer.clone()))
            .collect();
        let mut imports = names
            .imports()
            .filter(|import| source_abi.import_is_accessible(import))
            .collect();
        let mut declaration = crate::profile_scope!("kotlin_backend.lower.declaration", {
            KotlinTypeLowering::new(
                &names,
                members.as_ref(),
                members.clone(),
                source_abi.as_ref(),
                source_abi.clone(),
                hierarchy,
                source_field_types,
                generic_fields,
                generic_methods,
                method_nullability,
                source_object_types,
                outer_instances,
                observer,
            )
            .lower(class)
        })?;
        crate::language::kotlin::KotlinImportAnalysis::retain_used(&mut imports, &mut declaration);
        Ok(KotlinCompilationUnit {
            package: package_name,
            imports,
            declaration,
        })
    }
}

pub(super) struct KotlinSingleMethodLowering;

enum LoweredClassMember {
    Method {
        reference: Option<crate::ir::MethodReference>,
        invokes: std::collections::BTreeSet<crate::ir::MethodReference>,
        declaration: KotlinMethodDeclaration,
    },
    Property(KotlinPropertyDeclaration),
}

impl KotlinSingleMethodLowering {
    pub(super) fn lower(
        method: &KotlinMethodModel,
        current_package: Option<&str>,
        current_type: Option<&ArgType>,
        type_uses: impl IntoIterator<Item = ArgType>,
        source_abi: &std::sync::Arc<super::KotlinSourceAbi>,
        hierarchy: std::sync::Arc<crate::ir::analysis::ClassHierarchyIndex>,
        observer: std::sync::Arc<dyn crate::ir::AnalysisObserver>,
    ) -> Result<KotlinMethodDeclaration, KotlinDecompilerError> {
        let field_references = method
            .body
            .as_ref()
            .map(super::kotlin_model::method::KotlinMethodBody::field_references)
            .unwrap_or_default();
        let generic_fields = source_abi.generic_fields(field_references.iter());
        let method_references = method
            .body
            .as_ref()
            .map(super::kotlin_model::method::KotlinMethodBody::method_references)
            .unwrap_or_default();
        let generic_methods = source_abi.generic_methods(method_references.iter());
        let method_nullability = source_abi.referenced_nullability(method_references.iter());
        let referenced_overloads = source_abi.referenced_overloads(method_references.iter());
        let referenced_constructors = source_abi.referenced_constructors(method_references.iter());
        let mut type_uses = type_uses.into_iter().collect::<Vec<_>>();
        if let Some(owner) = current_type {
            type_uses.extend(source_abi.declared_source_types(owner));
        }
        for contract in generic_fields.values() {
            GenericTypeUses::field_contract(contract, &mut type_uses);
        }
        for contract in generic_methods.values() {
            GenericTypeUses::method_contract(contract, &mut type_uses);
        }
        let names = KotlinTypeNameResolver::new(current_package, current_type, type_uses)?;
        let members = std::sync::Arc::new(
            ClassMemberNames::method_only(current_type, method)
                .with_source_names(source_abi.declared_source_names())
                .with_property_accessors(
                    source_abi.declared_property_getters(),
                    source_abi.declared_property_setters(),
                )
                .with_constructor_layouts(referenced_constructors)
                .with_overloads(referenced_overloads),
        );
        let source_field_types = generic_fields
            .iter()
            .map(|(field, contract)| {
                Ok((
                    field.clone(),
                    names
                        .resolve_generic_type(&contract.signature)
                        .map_err(KotlinDecompilerError::from)?,
                ))
            })
            .collect::<Result<_, KotlinDecompilerError>>()?;
        let mut outer_instances = source_abi
            .outer_instances()
            .map(|(field, outer)| (field.clone(), outer.clone()))
            .collect::<std::collections::BTreeMap<_, _>>();
        if let Some((field, outer)) = method
            .body
            .as_ref()
            .and_then(super::kotlin_model::method::KotlinMethodBody::outer_instance_field)
        {
            outer_instances.insert(field.clone(), outer.clone());
        }
        let lowering = KotlinTypeLowering::new(
            &names,
            members.as_ref(),
            members.clone(),
            source_abi.as_ref(),
            source_abi.clone(),
            hierarchy,
            source_field_types,
            generic_fields,
            generic_methods,
            method_nullability,
            std::collections::BTreeMap::new(),
            outer_instances,
            observer,
        );
        lowering.method(
            method,
            current_type,
            None,
            None,
            &lowering.source_field_types,
        )
    }
}

struct KotlinTypeLowering<'a> {
    names: &'a KotlinTypeNameResolver,
    members: &'a KotlinMemberNames,
    shared_members: std::sync::Arc<KotlinMemberNames>,
    source_abi: &'a super::KotlinSourceAbi,
    constants: KotlinConstantLowering<'a>,
    source_field_types:
        std::sync::Arc<std::collections::BTreeMap<crate::ir::FieldReference, KotlinType>>,
    generic_fields: std::sync::Arc<
        std::collections::BTreeMap<
            crate::ir::FieldReference,
            crate::ir::generic_types::GenericFieldContract,
        >,
    >,
    generic_methods: std::sync::Arc<
        std::collections::BTreeMap<
            crate::ir::MethodReference,
            crate::ir::generic_types::GenericMethodContract,
        >,
    >,
    method_nullability: std::sync::Arc<
        std::collections::BTreeMap<
            crate::ir::MethodReference,
            crate::language::kotlin::KotlinMethodNullability,
        >,
    >,
    source_object_types: std::sync::Arc<std::collections::BTreeMap<ArgType, KotlinType>>,
    outer_instances: std::collections::BTreeMap<crate::ir::FieldReference, ArgType>,
    generic_type_projection: std::sync::Arc<dyn crate::language::kotlin::GenericTypeProjection>,
    observer: std::sync::Arc<dyn crate::ir::AnalysisObserver>,
}

#[derive(Debug)]
struct SourceGenericTypeProjection {
    names: KotlinTypeNameResolver,
    source_abi: std::sync::Arc<super::KotlinSourceAbi>,
    hierarchy: std::sync::Arc<crate::ir::analysis::ClassHierarchyIndex>,
    cache: GenericProjectionCache,
}

#[derive(Debug, Default)]
struct GenericProjectionCache {
    specialized: PairCache<ArgType, KotlinType, Option<KotlinType>>,
    inferred: PairCache<ArgType, KotlinType, Option<KotlinType>>,
    projected: PairCache<KotlinType, ArgType, Option<KotlinType>>,
    subtypes: PairCache<ArgType, ArgType, bool>,
    common_types: PairCache<ArgType, ArgType, Option<ArgType>>,
    resolved: std::sync::Mutex<std::collections::BTreeMap<ArgType, KotlinType>>,
}

#[derive(Debug)]
struct PairCache<K1, K2, V> {
    values: std::sync::RwLock<std::collections::HashMap<K1, std::collections::HashMap<K2, V>>>,
}

impl<K1, K2, V> Default for PairCache<K1, K2, V> {
    fn default() -> Self {
        Self {
            values: std::sync::RwLock::new(std::collections::HashMap::new()),
        }
    }
}

impl<K1, K2, V> PairCache<K1, K2, V>
where
    K1: std::hash::Hash + Eq + Clone,
    K2: std::hash::Hash + Eq + Clone,
    V: Clone,
{
    fn get(&self, first: &K1, second: &K2) -> Option<V> {
        let values = match self.values.read() {
            Ok(values) => values,
            Err(poisoned) => poisoned.into_inner(),
        };
        values
            .get(first)
            .and_then(|values| values.get(second))
            .cloned()
    }

    fn insert(&self, first: &K1, second: &K2, value: V) {
        let mut values = match self.values.write() {
            Ok(values) => values,
            Err(poisoned) => poisoned.into_inner(),
        };
        values
            .entry(first.clone())
            .or_default()
            .insert(second.clone(), value);
    }
}

impl SourceGenericTypeProjection {
    fn reference_cast_convertible(&self, source: &ArgType, target: &ArgType) -> bool {
        match (source, target) {
            (ArgType::Array(source), ArgType::Array(target)) => match (&**source, &**target) {
                (ArgType::Primitive(source), ArgType::Primitive(target)) => source == target,
                (source, target) if source.is_reference() && target.is_reference() => {
                    self.reference_cast_convertible(source, target)
                }
                _ => false,
            },
            (ArgType::Object(source), ArgType::Array(_))
            | (ArgType::Array(_), ArgType::Object(source)) => matches!(
                source.as_str(),
                "java/lang/Object" | "java/lang/Cloneable" | "java/io/Serializable"
            ),
            (ArgType::Object(source), ArgType::Object(target)) => {
                self.hierarchy.is_cast_convertible(source, target)
            }
            _ => false,
        }
    }
}

impl crate::language::kotlin::GenericTypeProjection for SourceGenericTypeProjection {
    fn specialize_subtype(
        &self,
        subtype: &ArgType,
        expected_supertype: &KotlinType,
    ) -> Option<KotlinType> {
        if let Some(result) = self.cache.specialized.get(subtype, expected_supertype) {
            return result;
        }
        let result = self
            .names
            .source_signature(expected_supertype)
            .and_then(|expected| self.source_abi.specialize_subtype(subtype, &expected))
            .and_then(|specialized| self.names.resolve_generic_type(&specialized).ok());
        self.cache
            .specialized
            .insert(subtype, expected_supertype, result.clone());
        result
    }

    fn infer_subtype(
        &self,
        subtype: &ArgType,
        expected_supertype: &KotlinType,
    ) -> Option<KotlinType> {
        if let Some(result) = self.cache.inferred.get(subtype, expected_supertype) {
            return result;
        }
        let result = self
            .names
            .source_signature(expected_supertype)
            .and_then(|expected| self.source_abi.infer_subtype(subtype, &expected))
            .and_then(|inferred| self.names.resolve_generic_type(&inferred).ok());
        self.cache
            .inferred
            .insert(subtype, expected_supertype, result.clone());
        result
    }

    fn project_supertype(
        &self,
        subtype: &KotlinType,
        expected_supertype: &ArgType,
    ) -> Option<KotlinType> {
        if let Some(result) = self.cache.projected.get(subtype, expected_supertype) {
            return result;
        }
        let result = self
            .names
            .source_signature(subtype)
            .and_then(|subtype| {
                self.source_abi
                    .project_supertype(&subtype, expected_supertype)
            })
            .and_then(|projected| self.names.resolve_generic_type(&projected).ok());
        self.cache
            .projected
            .insert(subtype, expected_supertype, result.clone());
        result
    }

    fn is_subtype(&self, subtype: &ArgType, supertype: &ArgType) -> bool {
        use crate::ir::analysis::TypeHierarchy;
        if let Some(result) = self.cache.subtypes.get(subtype, supertype) {
            return result;
        }
        let result = self.source_abi.is_subtype(subtype, supertype)
            || self
                .names
                .resolve_type(subtype)
                .ok()
                .map(KotlinType::into_raw)
                .and_then(|subtype| self.names.source_signature(&subtype))
                .and_then(|subtype| self.source_abi.project_supertype(&subtype, supertype))
                .is_some()
            || matches!(
                (subtype.as_object(), supertype.as_object()),
                (Some(subtype), Some(supertype)) if self.hierarchy.is_subtype(subtype, supertype)
            );
        self.cache.subtypes.insert(subtype, supertype, result);
        result
    }

    fn uses_mapped_collection_size(&self, owner: &ArgType) -> bool {
        self.source_abi.is_mapped_collection_size_owner(owner)
    }

    fn least_common_supertype(&self, left: &ArgType, right: &ArgType) -> Option<ArgType> {
        use crate::ir::analysis::TypeHierarchy;
        let (first, second) = if left <= right {
            (left, right)
        } else {
            (right, left)
        };
        if let Some(result) = self.cache.common_types.get(first, second) {
            return result;
        }
        let result = match (left.as_object(), right.as_object()) {
            (Some(left), Some(right)) => self
                .hierarchy
                .least_common_supertype(left, right)
                .map(|name| ArgType::object(&name)),
            _ => None,
        };
        self.cache
            .common_types
            .insert(first, second, result.clone());
        result
    }

    fn is_cast_convertible(&self, source: &ArgType, target: &ArgType) -> bool {
        self.reference_cast_convertible(source, target)
    }

    fn resolve_type(&self, ty: &ArgType) -> Option<KotlinType> {
        if let Some(resolved) = self
            .cache
            .resolved
            .lock()
            .ok()
            .and_then(|cache| cache.get(ty).cloned())
        {
            return Some(resolved);
        }
        let resolved = self.names.resolve_type(ty).ok()?;
        if let Ok(mut cache) = self.cache.resolved.lock() {
            cache.insert(ty.clone(), resolved.clone());
        }
        Some(resolved)
    }

    fn erasure_of(&self, ty: &KotlinType) -> Option<ArgType> {
        self.cache
            .resolved
            .lock()
            .ok()
            .and_then(|cache| {
                cache
                    .iter()
                    .find_map(|(erased, source)| (source == ty).then(|| erased.clone()))
            })
            .or_else(|| {
                self.names
                    .source_signature(ty)
                    .map(|signature| signature.erased())
            })
    }

    fn declared_type_parameters(
        &self,
        ty: &ArgType,
    ) -> Option<Vec<crate::ir::generic_types::TypeParameter>> {
        self.source_abi.class_type_parameters(ty)
    }
}

impl<'a> KotlinTypeLowering<'a> {
    fn new(
        names: &'a KotlinTypeNameResolver,
        members: &'a KotlinMemberNames,
        shared_members: std::sync::Arc<KotlinMemberNames>,
        source_abi: &'a super::KotlinSourceAbi,
        shared_source_abi: std::sync::Arc<super::KotlinSourceAbi>,
        hierarchy: std::sync::Arc<crate::ir::analysis::ClassHierarchyIndex>,
        source_field_types: std::collections::BTreeMap<crate::ir::FieldReference, KotlinType>,
        generic_fields: std::collections::BTreeMap<
            crate::ir::FieldReference,
            crate::ir::generic_types::GenericFieldContract,
        >,
        generic_methods: std::collections::BTreeMap<
            crate::ir::MethodReference,
            crate::ir::generic_types::GenericMethodContract,
        >,
        method_nullability: std::collections::BTreeMap<
            crate::ir::MethodReference,
            crate::language::kotlin::KotlinMethodNullability,
        >,
        source_object_types: std::collections::BTreeMap<ArgType, KotlinType>,
        outer_instances: std::collections::BTreeMap<crate::ir::FieldReference, ArgType>,
        observer: std::sync::Arc<dyn crate::ir::AnalysisObserver>,
    ) -> Self {
        Self {
            names,
            members,
            shared_members,
            source_abi,
            constants: KotlinConstantLowering::new(names, members),
            source_field_types: std::sync::Arc::new(source_field_types),
            generic_fields: std::sync::Arc::new(generic_fields),
            generic_methods: std::sync::Arc::new(generic_methods),
            method_nullability: std::sync::Arc::new(method_nullability),
            source_object_types: std::sync::Arc::new(source_object_types),
            outer_instances,
            generic_type_projection: std::sync::Arc::new(SourceGenericTypeProjection {
                names: names.clone(),
                source_abi: shared_source_abi,
                hierarchy,
                cache: GenericProjectionCache::default(),
            }),
            observer,
        }
    }

    fn lower(
        &self,
        class: &KotlinClassModel,
    ) -> Result<KotlinTypeDeclaration, KotlinDecompilerError> {
        let mut pending = vec![(class, false)];
        let mut results: Vec<LoweredNestedType> = Vec::new();
        while let Some((class, exiting)) = pending.pop() {
            if !exiting {
                pending.push((class, true));
                pending.extend(class.nested.iter().rev().map(|nested| (nested, false)));
                continue;
            }
            let start = results
                .len()
                .checked_sub(class.nested.len())
                .ok_or(KotlinDecompilerError::MalformedDeclarationStack)?;
            let nested = results.drain(start..).collect();
            results.push(self.lower_type(class, nested)?);
        }
        if results.len() != 1 {
            return Err(KotlinDecompilerError::MalformedDeclarationStack);
        }
        let lowered = results
            .pop()
            .ok_or(KotlinDecompilerError::MalformedDeclarationStack)?;
        let mut declaration = lowered.declaration;
        let recovered_functions = lowered.liveness.apply(&mut declaration);
        let outer_aliases = self
            .outer_instances
            .iter()
            .map(|(field, outer)| {
                Ok((
                    self.names.resolve_type(&field.owner)?,
                    self.members.field(field),
                    self.names.resolve_type(outer)?,
                ))
            })
            .collect::<Result<Vec<_>, KotlinDecompilerError>>()?;
        super::lexical_owners::LexicalOwners::recover_outer_aliases(
            &mut declaration,
            outer_aliases,
        );
        SyntheticMemberRecovery::apply(&mut declaration, &recovered_functions);
        // The access check has to go before nullability is inferred: while it
        // stands, the value it guards looks like something observed null.
        super::parameter_checks::KotlinParameterChecks::apply(&mut declaration);
        // Promotion reads the constructor as it was written, before anything
        // rewrites the parameter references inside it.
        super::primary_constructor::KotlinPrimaryConstructor::apply(&mut declaration);
        super::lateinit_access::KotlinLateinitAccess::apply(&mut declaration);
        super::nullability_inference::KotlinNullabilityInference::apply(&mut declaration);
        super::type_variable_closure::TypeVariableClosure::close(&mut declaration);
        super::lexical_owners::LexicalOwners::qualify(&mut declaration);
        Ok(declaration)
    }

    fn lower_type(
        &self,
        class: &KotlinClassModel,
        mut nested: Vec<LoweredNestedType>,
    ) -> Result<LoweredNestedType, KotlinDecompilerError> {
        let owner = class.declaration.current_type();
        let object_declaration = owner.as_ref().is_some_and(|owner| {
            self.source_abi.declared_class_kind(owner)
                == Some(crate::frontend::kotlin_metadata::ClassKind::Object)
        });
        let identity = owner
            .as_ref()
            .map(|ty| self.names.resolve_type(ty))
            .transpose()?
            .unwrap_or_else(|| {
                KotlinType::Class(KotlinClassType::raw(KotlinClassName::simple(
                    class.declaration.name.clone(),
                )))
            });
        let mut source_field_types = self.source_field_types.as_ref().clone();
        if let Some(owner) = &owner {
            let lexical_field_types = class
                .fields
                .iter()
                .filter_map(|field| {
                    field.signature.as_ref().map(|signature| {
                        Ok((
                            crate::ir::FieldReference {
                                owner: owner.clone(),
                                name: field.name.to_string(),
                                field_type: field.field_type.clone(),
                            },
                            self.names.resolve_generic_type(signature)?,
                        ))
                    })
                })
                .collect::<Result<std::collections::BTreeMap<_, _>, KotlinDecompilerError>>()?;
            source_field_types.extend(lexical_field_types);
        }
        let source_field_types = std::sync::Arc::new(source_field_types);
        let source_constructor_count = class
            .methods
            .iter()
            .filter(|method| {
                method.declaration.kind == MethodModelKind::Constructor
                    && !method.declaration.source_bridge
            })
            .count();
        let source_super_type = match (
            class.declaration.signature.as_ref(),
            class.declaration.extends.as_ref(),
        ) {
            (Some(signature), Some(_)) => Some(self.names.resolve_generic_type(
                &JvmTypeSignature::ClassType(signature.super_class.clone()),
            )?),
            (None, Some(erased)) => Some(self.names.resolve_type(erased)?),
            (_, None) => None,
        };
        let lower = |method: &KotlinMethodModel| {
            self.lower_class_method(
                class,
                method,
                owner.as_ref(),
                source_super_type.as_ref(),
                &source_field_types,
                source_constructor_count,
            )
        };
        let lowered = if class.methods.len() < 8 {
            class.methods.iter().map(lower).collect::<Vec<_>>()
        } else {
            class.methods.par_iter().map(lower).collect::<Vec<_>>()
        };
        let members = lowered
            .into_iter()
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        let mut methods = Vec::new();
        let mut properties = Vec::new();
        for member in members {
            match member {
                LoweredClassMember::Method {
                    reference,
                    invokes,
                    declaration,
                } => methods.push((reference, invokes, declaration)),
                LoweredClassMember::Property(property) => properties.push(property),
            }
        }
        super::default_arguments::KotlinDefaultArguments::new(self.source_abi)
            .recover(&mut methods);
        let methods = methods
            .into_iter()
            .map(|(_, _, declaration)| declaration)
            .collect();
        let singleton_fields = if object_declaration {
            class
                .fields
                .iter()
                .filter_map(|field| {
                    let owner = owner.as_ref()?;
                    let reference = crate::ir::FieldReference {
                        owner: owner.clone(),
                        name: field.name.dex_name().to_string(),
                        field_type: field.field_type.clone(),
                    };
                    self.source_abi
                        .is_singleton_instance(&reference)
                        .then(|| (reference.clone(), self.members.field(&reference)))
                })
                .collect::<std::collections::BTreeMap<_, _>>()
        } else {
            std::collections::BTreeMap::new()
        };
        let field_models = class
            .fields
            .iter()
            .filter(|field| {
                let Some(owner) = owner.as_ref() else {
                    return true;
                };
                !singleton_fields.contains_key(&crate::ir::FieldReference {
                    owner: owner.clone(),
                    name: field.name.dex_name().to_string(),
                    field_type: field.field_type.clone(),
                })
            })
            .collect::<Vec<_>>();
        let mut fields = crate::profile_scope!("kotlin_backend.lower.fields", {
            field_models
                .iter()
                .map(|field| self.field(field, owner.as_ref()))
                .collect::<Result<Vec<_>, _>>()
        })?;
        let synthetic_final_fields = field_models
            .iter()
            .zip(&fields)
            .filter_map(|(model, lowered)| {
                (model.access_flags.is_synthetic() && model.access_flags.is_final())
                    .then_some(lowered.name.clone())
            })
            .collect();
        let enum_declaration = EnumDeclarationRecovery::apply(class, fields, methods);
        let constant_implementations = enum_declaration.constant_implementations;

        let mut declaration = KotlinTypeDeclaration {
            annotations: self.constants.annotations(&class.declaration.annotations)?,
            modifiers: {
                let owner = class.declaration.current_type();
                let mut modifiers = Self::declared_visibility(
                    class.declaration.modifiers.clone(),
                    owner
                        .as_ref()
                        .and_then(|owner| self.source_abi.declared_class_visibility(owner)),
                );
                // A sealed class is abstract to the JVM; the source said which.
                if owner
                    .as_ref()
                    .is_some_and(|owner| self.source_abi.is_sealed_class(owner))
                {
                    modifiers.retain(|modifier| *modifier != KotlinModifier::Abstract);
                    modifiers.push(KotlinModifier::Sealed);
                }
                modifiers
            },
            kind: if object_declaration {
                KotlinTypeDeclarationKind::Object
            } else {
                type_kind(class.declaration.kind)
            },
            name: class.declaration.name.clone(),
            type_parameters: class
                .declaration
                .signature
                .as_ref()
                .map(|signature| {
                    self.names
                        .resolve_header_type_parameters(&signature.type_parameters)
                })
                .transpose()?
                .unwrap_or_default(),
            extends: self.extends(class)?,
            implements: self.implements(class)?,
            enum_constants: enum_declaration.constants,
            primary_parameters: Vec::new(),
            superclass_arguments: Vec::new(),
            fields: enum_declaration.fields,
            properties,
            methods: enum_declaration.methods,
            nested: Vec::new(),
        };
        Self::assign_nested_names(&declaration, &mut nested);
        let liveness = NestedTypeLiveness::from_nested(&nested);
        let nested =
            EnumConstantBodyRecovery::apply(&mut declaration, &constant_implementations, nested);
        let nested = EnumSwitchRecovery::apply(&mut declaration, nested);
        let recovery = AnonymousClassRecovery::apply(
            &mut declaration,
            &identity,
            nested,
            self.names,
            self.source_abi,
        );
        StaticInitializationRecovery::apply(&mut declaration);
        if object_declaration {
            KotlinObjectDeclaration::lower(
                &mut declaration,
                &identity,
                singleton_fields.values().cloned().collect(),
            );
        }
        Self::remove_implicit_field_modifiers(class.declaration.kind, &mut declaration.fields);
        super::compiler_checks::KotlinCompilerChecks::apply(&mut declaration);
        ConstructorSyntaxRecovery::apply(&mut declaration);
        super::field_initialization::FieldInitializationFacts::refresh_tree(
            &mut declaration,
            object_declaration.then_some(&identity),
        );
        if let Some(owner) = owner.as_ref() {
            for field in &class.fields {
                let reference = crate::ir::FieldReference {
                    owner: owner.clone(),
                    name: field.name.dex_name().to_string(),
                    field_type: field.field_type.clone(),
                };
                if !self.source_abi.field_is_mutable(&reference) {
                    continue;
                }
                let source_name = self.members.field(&reference);
                if let Some(declared) = declaration
                    .fields
                    .iter_mut()
                    .find(|declared| declared.name == source_name)
                {
                    declared
                        .modifiers
                        .retain(|modifier| *modifier != KotlinModifier::Final);
                }
            }
        }
        super::mapped_members::KotlinMappedMembers::apply(class, self.source_abi, &mut declaration);
        let function_contract = self.function_contract(class);
        let function_type = class
            .function_interface()
            .map(|interface| self.names.resolve_generic_type(interface))
            .transpose()?;
        let lexical_type_variables = owner
            .as_ref()
            .into_iter()
            .flat_map(|owner| self.source_abi.lexical_type_variables(owner))
            .map(KotlinIdentifier::from_dex)
            .collect();
        Ok(LoweredNestedType {
            identity: Some(identity),
            lexical_type_variables,
            is_anonymous: class.declaration.is_anonymous,
            is_function_object: class.function_object,
            function_type,
            function_contract,
            synthetic_final_fields,
            liveness: liveness
                .with_removable(recovery.removable_types)
                .with_recovered_functions(recovery.recovered_functions),
            declaration,
        })
    }

    fn lower_class_method(
        &self,
        class: &KotlinClassModel,
        method: &KotlinMethodModel,
        owner: Option<&ArgType>,
        source_super_type: Option<&KotlinType>,
        source_field_types: &std::sync::Arc<
            std::collections::BTreeMap<crate::ir::FieldReference, KotlinType>,
        >,
        source_constructor_count: usize,
    ) -> Result<Option<LoweredClassMember>, KotlinDecompilerError> {
        if method.declaration.kind == MethodModelKind::Constructor
            && owner.is_some_and(|owner| {
                self.source_abi.declared_class_kind(owner)
                    == Some(crate::frontend::kotlin_metadata::ClassKind::Object)
            })
        {
            return Ok(None);
        }
        if method.declaration.source_bridge {
            return Ok(None);
        }
        if owner
            .map(|owner| method_reference(owner, &method.declaration))
            .is_some_and(|reference| self.source_abi.is_default_property_accessor(&reference))
        {
            return Ok(None);
        }
        let lowered = crate::profile_scope!("kotlin_backend.lower.method", {
            self.method(
                method,
                owner,
                class.declaration.signature.as_ref(),
                source_super_type,
                source_field_types,
            )
        });
        let lowered = match lowered {
            Ok(lowered) => lowered,
            Err(error) if error.is_cancelled() => return Err(error),
            Err(error) => {
                let descriptor = crate::ir::MethodDescriptor {
                    parameters: method
                        .declaration
                        .parameters
                        .iter()
                        .map(|parameter| parameter.ty.clone())
                        .collect(),
                    return_type: method
                        .declaration
                        .return_type
                        .clone()
                        .unwrap_or(ArgType::VOID),
                }
                .to_string();
                let failure =
                    MethodRecoveryFailure::new(MethodRecoveryStage::SourceLowering, error);
                let class_name = owner
                    .map(ArgType::to_descriptor)
                    .unwrap_or_else(|| class.declaration.binary_name.clone());
                failure.observe(
                    self.observer.as_ref(),
                    &class_name,
                    method.declaration.name.as_str(),
                    &descriptor,
                );
                let failed = method.clone().with_failure(failure);
                self.method(
                    &failed,
                    owner,
                    class.declaration.signature.as_ref(),
                    source_super_type,
                    source_field_types,
                )?
            }
        };
        let default_constructor = method.body.as_ref().is_some_and(|_| {
            lowered.body.as_ref().is_some_and(|body| {
                source_constructor_count == 1
                    && method.is_default_constructor(
                        &class.declaration.name,
                        &class.declaration.modifiers,
                        body,
                    )
            })
        });
        if default_constructor {
            return Ok(None);
        }
        let computed_property = owner
            .map(|owner| method_reference(owner, &method.declaration))
            .and_then(|reference| {
                self.source_abi
                    .declared_computed_property(&reference)
                    .cloned()
            });
        if let Some(name) = computed_property {
            if lowered.kind == KotlinMethodDeclarationKind::Method
                && lowered.receiver.is_none()
                && lowered.parameters.is_empty()
                && lowered.throws.is_empty()
            {
                if let Some(ty) = lowered.return_type {
                    return Ok(Some(LoweredClassMember::Property(
                        KotlinPropertyDeclaration {
                            annotations: lowered.annotations,
                            modifiers: lowered.modifiers,
                            ty,
                            name,
                            nullable: lowered.return_nullable,
                            getter: lowered.body,
                        },
                    )));
                }
            }
        }
        Ok(Some(LoweredClassMember::Method {
            reference: owner.map(|owner| method_reference(owner, &method.declaration)),
            invokes: method
                .body
                .as_ref()
                .map(super::kotlin_model::method::KotlinMethodBody::method_references)
                .unwrap_or_default(),
            declaration: lowered,
        }))
    }

    fn assign_nested_names(owner: &KotlinTypeDeclaration, nested: &mut [LoweredNestedType]) {
        let mut scope = crate::language::kotlin::KotlinNameScope::default();
        scope.reserve(owner.name.clone());
        for parameter in &owner.type_parameters {
            scope.reserve(parameter.name.clone());
        }
        for nested in nested {
            let previous = nested.declaration.name.clone();
            let assigned = scope.claim(previous.clone());
            nested.declaration.rename(assigned.clone());
            nested.liveness.rename_owner(&previous, &assigned);
        }
    }

    fn function_contract(&self, class: &KotlinClassModel) -> Option<FunctionContract> {
        if !class.function_object {
            return None;
        }
        class
            .methods
            .iter()
            .find_map(|method| {
                method
                    .declaration
                    .override_semantics
                    .as_ref()?
                    .base_methods
                    .iter()
                    .find_map(|base| {
                        let reference = format!("{}->{}", base.declaring_class, base.short_id)
                            .parse::<crate::ir::MethodReference>()
                            .ok()?;
                        self.source_abi.generic_method(&reference)?;
                        Some(FunctionContract { method: reference })
                    })
            })
            .or_else(|| {
                let owner = class.declaration.current_type()?;
                class.methods.iter().find_map(|method| {
                    let declaration = &method.declaration;
                    declaration.function_interface.as_ref()?;
                    Some(FunctionContract {
                        method: crate::ir::MethodReference {
                            owner: owner.clone(),
                            name: declaration.name.to_string(),
                            descriptor: crate::ir::MethodDescriptor {
                                parameters: declaration
                                    .parameters
                                    .iter()
                                    .map(|parameter| parameter.ty.clone())
                                    .collect(),
                                return_type: declaration.return_type.clone()?,
                            },
                        },
                    })
                })
            })
    }

    fn remove_implicit_field_modifiers(
        kind: KotlinClassKind,
        fields: &mut [KotlinFieldDeclaration],
    ) {
        if !matches!(
            kind,
            KotlinClassKind::Interface | KotlinClassKind::Annotation
        ) {
            return;
        }
        for field in fields {
            field.modifiers.retain(|modifier| {
                !matches!(
                    modifier,
                    KotlinModifier::Public | KotlinModifier::Static | KotlinModifier::Final
                )
            });
        }
    }

    fn extends(
        &self,
        class: &KotlinClassModel,
    ) -> Result<Option<KotlinType>, KotlinDecompilerError> {
        let Some(erased) = &class.declaration.extends else {
            return Ok(None);
        };
        match &class.declaration.signature {
            Some(signature) => Ok(Some(self.names.resolve_header_generic_type(
                &JvmTypeSignature::ClassType(signature.super_class.clone()),
            )?)),
            None => Ok(Some(self.names.resolve_header_type(erased)?)),
        }
    }

    fn implements(
        &self,
        class: &KotlinClassModel,
    ) -> Result<Vec<KotlinType>, KotlinDecompilerError> {
        let proven = class
            .methods
            .iter()
            .filter_map(|method| method.declaration.function_interface.as_ref())
            .map(|signature| (signature.erased(), signature))
            .collect::<std::collections::BTreeMap<_, _>>();
        if !proven.is_empty() {
            return class
                .declaration
                .implements
                .iter()
                .map(|interface| match proven.get(interface) {
                    Some(signature) => self
                        .names
                        .resolve_header_generic_type(signature)
                        .map_err(KotlinDecompilerError::from),
                    None => self
                        .names
                        .resolve_header_type(interface)
                        .map_err(KotlinDecompilerError::from),
                })
                .collect();
        }
        if let Some(signature) = &class.declaration.signature {
            if signature.super_interfaces.iter().any(|interface| {
                !interface.type_arguments.is_empty()
                    || interface
                        .inner_segments
                        .iter()
                        .any(|segment| !segment.type_arguments.is_empty())
            }) {
                return signature
                    .super_interfaces
                    .iter()
                    .map(|interface| {
                        self.names
                            .resolve_header_generic_type(&JvmTypeSignature::ClassType(
                                interface.clone(),
                            ))
                            .map_err(KotlinDecompilerError::from)
                    })
                    .collect();
            }
        }
        if let Some(signature) = &class.declaration.signature {
            if !signature.super_interfaces.is_empty() {
                return signature
                    .super_interfaces
                    .iter()
                    .map(|interface| {
                        self.names
                            .resolve_header_generic_type(&JvmTypeSignature::ClassType(
                                interface.clone(),
                            ))
                            .map_err(KotlinDecompilerError::from)
                    })
                    .collect();
            }
        }
        class
            .declaration
            .implements
            .iter()
            .map(|interface| {
                self.names
                    .resolve_header_type(interface)
                    .map_err(KotlinDecompilerError::from)
            })
            .collect()
    }

    /// Replaces the access-flag visibility with the one the class declared.
    ///
    /// `internal` compiles to a public member, so the flags alone always read
    /// public. Only a declaration that states otherwise changes the modifier,
    /// and only where the flags left it public.
    fn declared_visibility(
        mut modifiers: Vec<KotlinModifier>,
        declared: Option<crate::frontend::kotlin_metadata::Visibility>,
    ) -> Vec<KotlinModifier> {
        if declared != Some(crate::frontend::kotlin_metadata::Visibility::Internal) {
            return modifiers;
        }
        if !modifiers.contains(&KotlinModifier::Public) {
            return modifiers;
        }
        for modifier in &mut modifiers {
            if *modifier == KotlinModifier::Public {
                *modifier = KotlinModifier::Internal;
            }
        }
        modifiers
    }

    fn field(
        &self,
        field: &FieldModel,
        owner: Option<&ArgType>,
    ) -> Result<KotlinFieldDeclaration, KotlinDecompilerError> {
        let field_reference = owner.map(|owner| crate::ir::FieldReference {
            owner: owner.clone(),
            name: field.name.to_string(),
            field_type: field.field_type.clone(),
        });
        let lateinit = field_reference
            .as_ref()
            .is_some_and(|field| self.source_abi.field_is_lateinit(field));
        let initializer = field
            .initializer
            .as_ref()
            .map(|value| self.constants.field_initializer(&field.field_type, value))
            .transpose()?;
        // `const` is only sayable on a property that states its value, and it
        // implies the property is read-only.
        let constant = initializer.is_some()
            && field.modifiers.contains(&KotlinModifier::Final)
            && field_reference
                .as_ref()
                .is_some_and(|field| self.source_abi.is_constant_field(field));
        Ok(KotlinFieldDeclaration {
            annotations: self.constants.annotations(&field.annotations)?,
            modifiers: {
                let mut modifiers = Self::declared_visibility(
                    field.modifiers.clone(),
                    field_reference
                        .as_ref()
                        .and_then(|field| self.source_abi.declared_field_visibility(field)),
                );
                if lateinit {
                    modifiers.push(KotlinModifier::Lateinit);
                }
                if constant {
                    modifiers.push(KotlinModifier::Const);
                }
                modifiers
            },
            ty: match &field.signature {
                Some(signature) => self.names.resolve_generic_type(signature)?,
                None => self.names.resolve_type(&field.field_type)?,
            },
            name: owner
                .map(|owner| {
                    self.members.field_symbol(&KotlinFieldSymbol::new(
                        owner.clone(),
                        field.name.clone(),
                        field.field_type.clone(),
                    ))
                })
                .unwrap_or_else(|| field.name.clone()),
            // A field carries its declared non-null type once something has to
            // assign it: a final field, which the constructor must, or a
            // `lateinit` one, which the language requires before any read.
            // A plain `var` may still be observed null before assignment.
            nullable: !(field_reference
                .as_ref()
                .is_some_and(|field| self.source_abi.field_is_non_null(field))
                && (field.modifiers.contains(&KotlinModifier::Final) || lateinit)),
            initializer,
        })
    }

    fn method(
        &self,
        method: &KotlinMethodModel,
        owner: Option<&ArgType>,
        class_signature: Option<&ClassSignature>,
        source_super_type: Option<&KotlinType>,
        source_field_types: &std::sync::Arc<
            std::collections::BTreeMap<crate::ir::FieldReference, KotlinType>,
        >,
    ) -> Result<KotlinMethodDeclaration, KotlinDecompilerError> {
        let declaration = &method.declaration;
        let signature = declaration.signature.as_ref();
        let annotations = self.method_annotations(declaration)?;
        // The contract is keyed by the DEX member, so the reference has to be
        // rebuilt from the DEX name rather than from the Kotlin identifier the
        // model already renamed and escaped.
        let method_reference = owner.map(|owner| crate::ir::MethodReference {
            owner: owner.clone(),
            name: match declaration.kind {
                MethodModelKind::Constructor => "<init>".to_string(),
                MethodModelKind::ClassInitializer => "<clinit>".to_string(),
                MethodModelKind::Method => declaration.name.dex_name().to_string(),
            },
            descriptor: crate::ir::MethodDescriptor {
                parameters: declaration
                    .parameters
                    .iter()
                    .map(|parameter| parameter.ty.clone())
                    .collect(),
                return_type: declaration.return_type.clone().unwrap_or(ArgType::VOID),
            },
        });
        let nullability_contract = method_reference
            .as_ref()
            .and_then(|method| self.source_abi.method_nullability(method));
        let extension_receiver_index = method_reference
            .as_ref()
            .and_then(|method| self.source_abi.declared_extension_receiver(method));
        let suspend_declaration = method_reference
            .as_ref()
            .and_then(|method| self.source_abi.declared_suspend_function(method))
            .cloned();
        let mut name_scope = crate::language::kotlin::KotlinNameScope::default();
        let parameter_naming = super::semantic_naming::ParameterNameRecovery::new(self.names);
        let mut visible_parameter = 0usize;
        let parameter_names = declaration
            .parameters
            .iter()
            .enumerate()
            .map(|(index, parameter)| {
                let generated = if parameter.hidden {
                    format!("synthetic{index}")
                } else {
                    let name = format!("p{visible_parameter}");
                    visible_parameter += 1;
                    name
                };
                // A Kotlin class records what it called each parameter, which
                // beats a name derived from the parameter's type. Debug names
                // still come first: both are source names, and preferring the
                // existing one keeps non-Kotlin classes untouched.
                let declared = method_reference.as_ref().and_then(|method| {
                    self.source_abi
                        .declared_parameter_name(method, index)
                        .map(KotlinIdentifier::from_dex)
                });
                name_scope.claim(
                    parameter
                        .name
                        .clone()
                        .or(declared)
                        .or_else(|| {
                            (!parameter.hidden)
                                .then(|| parameter_naming.candidate(&parameter.ty))
                                .flatten()
                        })
                        .unwrap_or_else(|| KotlinIdentifier::from_dex(&generated)),
                )
            })
            .collect::<Vec<_>>();
        let mut visible_index = 0usize;
        let parameters = declaration
            .parameters
            .iter()
            .enumerate()
            .filter(|(_, parameter)| !parameter.hidden)
            .map(|(parameter_index, parameter)| {
                let signature_index = visible_index;
                visible_index += 1;
                let declared_type = method_reference.as_ref().and_then(|method| {
                    self.source_abi
                        .declared_parameter_type(method, parameter_index)
                });
                let vararg_element_nullable = method_reference.as_ref().and_then(|method| {
                    self.source_abi
                        .declared_vararg_element_nullable(method, parameter_index)
                });
                let mut ty = self.method_parameter_type(
                    signature,
                    signature_index,
                    &parameter.ty,
                    declaration
                        .source_parameter_types
                        .get(parameter_index)
                        .and_then(Option::as_ref),
                )?;
                if let Some(declared_type) = declared_type {
                    Self::apply_declared_type_qualifiers(&mut ty, declared_type);
                }
                Ok(KotlinMethodParameter {
                    annotations: self.constants.annotations(&parameter.annotations)?,
                    ty,
                    name: parameter_names[parameter_index].clone(),
                    nullable: vararg_element_nullable.unwrap_or_else(|| {
                        !nullability_contract
                            .is_some_and(|contract| contract.parameter_is_non_null(parameter_index))
                    }),
                    varargs: parameter.varargs || vararg_element_nullable.is_some(),
                    default_value: None,
                })
            })
            .collect::<Result<Vec<_>, KotlinDecompilerError>>()?;
        let extension_receiver_position = extension_receiver_index
            .and_then(|receiver| visible_parameter_position(&declaration.parameters, receiver));
        let suspend_continuation_position = suspend_declaration.as_ref().and_then(|suspend| {
            visible_parameter_position(&declaration.parameters, suspend.continuation_parameter)
        });
        let declared_return_type = method_reference
            .as_ref()
            .and_then(|method| self.source_abi.declared_return_type(method));
        let mut return_type = self.method_return_type(declaration, signature)?;
        if let (Some(return_type), Some(declared_type)) =
            (return_type.as_mut(), declared_return_type)
        {
            Self::apply_declared_type_qualifiers(return_type, declared_type);
        }
        let throws = self.method_throws(declaration, signature)?;
        let instance_scope = declaration.kind != MethodModelKind::ClassInitializer
            && !declaration.modifiers.contains(&KotlinModifier::Static);
        let lexical_owner = instance_scope.then_some(owner).flatten();
        let lexical_class_signature = instance_scope.then_some(class_signature).flatten();
        let source_current_type =
            self.source_current_type(lexical_owner, lexical_class_signature)?;
        let source_type_erasures =
            self.type_variable_erasures(lexical_owner, lexical_class_signature, signature);
        let source_type_bounds =
            self.type_variable_bounds(lexical_owner, lexical_class_signature, signature)?;
        let generic_throw_types = self.generic_throw_types(signature, lexical_class_signature)?;
        let mut visible_parameters = parameters.iter();
        let source_parameter_types = declaration
            .parameters
            .iter()
            .map(|parameter| {
                (!parameter.hidden)
                    .then(|| {
                        visible_parameters
                            .next()
                            .map(|parameter| parameter.ty.clone())
                    })
                    .flatten()
            })
            .collect::<Vec<_>>();
        let mut body = method
            .failure
            .as_ref()
            .map(Self::failure_body)
            .map(Ok)
            .or_else(|| {
                method.body.as_ref().map(|body| {
                    let mut outer_instances = self
                        .outer_instances
                        .iter()
                        .map(|(field, outer)| {
                            let source =
                                self.source_abi
                                    .owner_type(outer)
                                    .map(|outer| {
                                        self.names.resolve_generic_type(
                                            &JvmTypeSignature::ClassType(outer.clone()),
                                        )
                                    })
                                    .transpose()?
                                    .map(Ok)
                                    .unwrap_or_else(|| self.names.resolve_type(outer))?;
                            Ok((field.clone(), source))
                        })
                        .collect::<Result<std::collections::BTreeMap<_, _>, KotlinDecompilerError>>(
                        )?;
                    if let Some((field, outer)) = body.outer_instance_field() {
                        let source = self
                            .source_abi
                            .owner_type(outer)
                            .map(|outer| {
                                self.names
                                    .resolve_generic_type(&JvmTypeSignature::ClassType(
                                        outer.clone(),
                                    ))
                            })
                            .transpose()?
                            .map(Ok)
                            .unwrap_or_else(|| self.names.resolve_type(outer))?;
                        outer_instances.insert(field.clone(), source);
                    }
                    crate::profile_scope!("kotlin_backend.lower.method_body", {
                        body.lower(
                            &parameter_names,
                            self.names,
                            self.shared_members.clone(),
                            source_field_types.clone(),
                            self.generic_fields.clone(),
                            self.generic_methods.clone(),
                            self.method_nullability.clone(),
                            self.source_abi.declared_extension_receivers(),
                            self.source_abi.declared_default_calls(),
                            self.source_abi.declared_vararg_parameters(),
                            self.source_abi.platform_symbols(),
                            self.source_abi.non_null_fields(),
                            self.source_abi.singleton_types(),
                            self.source_abi.singleton_instances(),
                            self.source_object_types.clone(),
                            self.generic_type_projection.clone(),
                            source_current_type.clone(),
                            source_super_type.cloned(),
                            &source_parameter_types,
                            return_type.clone(),
                            source_type_erasures.clone(),
                            source_type_bounds.clone(),
                            generic_throw_types.clone(),
                            outer_instances,
                            declaration
                                .kind
                                .is_class_initializer()
                                .then(|| owner.map(|owner| self.members.field_names(owner)))
                                .flatten()
                                .unwrap_or_default(),
                            declaration.kind.is_class_initializer(),
                            self.observer.clone(),
                        )
                    })
                })
            })
            .transpose()?;
        if let Some(body) = body.as_mut() {
            let mut mutable_parameters = KotlinMutableParameterLowering::new(
                parameters
                    .iter()
                    .map(|parameter| (parameter.name.clone(), parameter.ty.clone())),
            );
            mutable_parameters
                .apply(body)
                .map_err(crate::language::kotlin::KotlinLoweringError::from)?;
            KotlinLocalBindingAnalysis
                .apply(body)
                .map_err(crate::language::kotlin::KotlinLoweringError::from)?;
            let mut smart_casts = KotlinSmartCastLowering::new(
                parameters.iter().map(|parameter| parameter.name.clone()),
            );
            smart_casts
                .apply(body)
                .map_err(crate::language::kotlin::KotlinLoweringError::from)?;
            if let Some(receiver) =
                extension_receiver_position.and_then(|position| parameters.get(position))
            {
                KotlinExtensionReceiverLowering::new(receiver.name.clone(), receiver.nullable)
                    .apply(body)
                    .map_err(crate::language::kotlin::KotlinLoweringError::from)?;
            }
            let mut normalizer = crate::language::kotlin::KotlinAstNormalizer;
            normalizer
                .apply(body)
                .map_err(crate::language::kotlin::KotlinLoweringError::from)?;
        }
        let suspend_recovered = suspend_declaration.is_some()
            && suspend_continuation_position.is_some()
            && body.as_ref().is_none_or(|body| {
                suspend_continuation_position
                    .and_then(|position| parameters.get(position))
                    .is_some_and(|continuation| {
                        !KotlinNameUseAnalysis::contains(body, &continuation.name)
                    })
            });
        if suspend_recovered {
            return_type = suspend_declaration
                .as_ref()
                .map(|suspend| self.names.resolve_type(&suspend.return_type))
                .transpose()?;
        }
        let receiver = extension_receiver_position
            .and_then(|position| parameters.get(position))
            .map(|parameter| KotlinExtensionReceiver {
                ty: parameter.ty.clone(),
                nullable: parameter.nullable,
            });
        let parameters = parameters
            .into_iter()
            .enumerate()
            .filter_map(|(position, parameter)| {
                (Some(position) != extension_receiver_position
                    && (!suspend_recovered || Some(position) != suspend_continuation_position))
                    .then_some(parameter)
            })
            .collect();
        let inferred_non_null_return = body
            .as_ref()
            .is_some_and(|body| KotlinNullabilityFacts::of(body).all_value_returns_non_null(body));
        Ok(KotlinMethodDeclaration {
            annotations,
            modifiers: {
                let mut modifiers = Self::declared_visibility(
                    declaration.modifiers.clone(),
                    method_reference
                        .as_ref()
                        .and_then(|method| self.source_abi.declared_method_visibility(method)),
                );
                if suspend_recovered {
                    modifiers.push(KotlinModifier::Suspend);
                }
                modifiers
            },
            compiler_generated: declaration.access_flags.is_synthetic(),
            kind: method_kind(declaration.kind),
            type_parameters: signature
                .map(|signature| {
                    self.names
                        .resolve_type_parameters(&signature.type_parameters)
                })
                .transpose()?
                .unwrap_or_default(),
            return_type,
            return_nullable: !inferred_non_null_return
                && !nullability_contract.is_some_and(|contract| contract.return_is_non_null())
                && !super::kotlin_contracts::KotlinOverrideContracts::has_non_null_return(
                    declaration.override_semantics.as_ref(),
                ),
            name: (!declaration.kind.is_class_initializer()).then(|| {
                if declaration.kind == MethodModelKind::Method {
                    owner
                        .map(|owner| {
                            self.members.method_symbol(&KotlinMethodSymbol::new(
                                owner.clone(),
                                declaration.name.clone(),
                                crate::ir::MethodDescriptor {
                                    parameters: declaration
                                        .parameters
                                        .iter()
                                        .map(|parameter| parameter.ty.clone())
                                        .collect(),
                                    return_type: declaration
                                        .return_type
                                        .clone()
                                        .unwrap_or(ArgType::VOID),
                                },
                            ))
                        })
                        .unwrap_or_else(|| declaration.name.clone())
                } else {
                    declaration.name.clone()
                }
            }),
            receiver,
            parameters,
            throws,
            body,
        })
    }

    fn failure_body(failure: &MethodRecoveryFailure) -> KotlinMethodBody {
        KotlinMethodBody {
            root: KotlinStmt::Block(vec![KotlinStmt::Throw(KotlinExpr::New {
                enclosing: None,
                ty: KotlinType::source_class("UnsupportedOperationException"),
                target_type: None,
                args: vec![KotlinExpr::Literal(KotlinLiteral::String(
                    failure.summary().into(),
                ))],
                anonymous_body: None,
            })]),
        }
    }

    fn method_annotations(
        &self,
        declaration: &MethodModel,
    ) -> Result<Vec<KotlinAnnotation>, KotlinDecompilerError> {
        Ok(self.constants.annotations(
            &declaration
                .annotations
                .iter()
                .filter(|annotation| {
                    annotation.annotation_type != ArgType::object("java/lang/Override")
                })
                .cloned()
                .collect::<Vec<_>>(),
        )?)
    }

    fn method_parameter_type(
        &self,
        signature: Option<&MethodSignature>,
        index: usize,
        erased: &ArgType,
        inferred: Option<&ArgType>,
    ) -> Result<KotlinType, KotlinDecompilerError> {
        if let Some(signature) =
            signature.and_then(|signature| signature.parameter_types.get(index))
        {
            return Ok(self.names.resolve_generic_type(signature)?);
        }
        self.names
            .resolve_type(inferred.unwrap_or(erased))
            .map_err(KotlinDecompilerError::from)
    }

    fn apply_declared_type_qualifiers(
        ty: &mut KotlinType,
        declared: &crate::frontend::kotlin_metadata::TypeReference,
    ) {
        let KotlinType::Array(element) = ty else {
            return;
        };
        let Some(declared_element) = declared.arguments.first() else {
            return;
        };
        element.set_declared_nullability(declared_element.nullable);
        Self::apply_declared_type_qualifiers(element.as_type_mut(), declared_element);
    }

    fn method_return_type(
        &self,
        declaration: &MethodModel,
        signature: Option<&MethodSignature>,
    ) -> Result<Option<KotlinType>, KotlinDecompilerError> {
        if !matches!(declaration.kind, MethodModelKind::Method) {
            return Ok(None);
        }
        if let Some(return_type) = declaration.source_return_type.as_ref() {
            return self
                .names
                .resolve_type(return_type)
                .map(Some)
                .map_err(KotlinDecompilerError::from);
        }
        if let Some(signature) = signature {
            return Ok(Some(
                self.names.resolve_generic_type(&signature.return_type)?,
            ));
        }
        declaration
            .return_type
            .as_ref()
            .map(|ty| {
                self.names
                    .resolve_type(ty)
                    .map_err(KotlinDecompilerError::from)
            })
            .transpose()
    }

    fn method_throws(
        &self,
        declaration: &MethodModel,
        signature: Option<&MethodSignature>,
    ) -> Result<Vec<KotlinType>, KotlinDecompilerError> {
        if let Some(signature) = signature {
            if !signature.throws.is_empty() {
                return signature
                    .throws
                    .iter()
                    .map(|ty| {
                        self.names
                            .resolve_generic_type(ty)
                            .map_err(KotlinDecompilerError::from)
                    })
                    .collect();
            }
        }
        declaration
            .throws
            .iter()
            .map(|ty| {
                self.names
                    .resolve_type(ty)
                    .map_err(KotlinDecompilerError::from)
            })
            .collect()
    }

    fn generic_throw_types(
        &self,
        signature: Option<&MethodSignature>,
        class_signature: Option<&ClassSignature>,
    ) -> Result<Vec<crate::language::kotlin::KotlinSourceErasure>, KotlinDecompilerError> {
        let Some(signature) = signature else {
            return Ok(Vec::new());
        };
        signature
            .throws
            .iter()
            .filter_map(|exception| {
                let crate::ir::generic_types::JvmTypeSignature::TypeVariable(name) = exception
                else {
                    return None;
                };
                let parameter = signature
                    .type_parameters
                    .iter()
                    .find(|parameter| parameter.name == *name)
                    .or_else(|| {
                        class_signature?
                            .type_parameters
                            .iter()
                            .find(|parameter| parameter.name == *name)
                    })?;
                let erased = parameter
                    .class_bound
                    .as_ref()
                    .or_else(|| parameter.interface_bounds.first())
                    .map(crate::ir::generic_types::JvmTypeSignature::erased)
                    .unwrap_or_else(|| ArgType::object("java/lang/Object"));
                Some(
                    self.names
                        .resolve_generic_type(exception)
                        .map(|source| {
                            crate::language::kotlin::KotlinSourceErasure::new(source, erased)
                        })
                        .map_err(KotlinDecompilerError::from),
                )
            })
            .collect()
    }

    fn type_variable_erasures(
        &self,
        owner: Option<&ArgType>,
        class_signature: Option<&ClassSignature>,
        signature: Option<&MethodSignature>,
    ) -> std::collections::BTreeMap<KotlinIdentifier, ArgType> {
        owner
            .into_iter()
            .flat_map(|owner| self.source_abi.lexical_type_erasures(owner))
            .map(|(name, erased)| (KotlinIdentifier::from_dex(name), erased))
            .chain(
                class_signature
                    .into_iter()
                    .flat_map(|signature| &signature.type_parameters)
                    .map(Self::type_parameter_erasure),
            )
            .chain(
                signature
                    .into_iter()
                    .flat_map(|signature| &signature.type_parameters)
                    .map(Self::type_parameter_erasure),
            )
            .collect()
    }

    fn type_variable_bounds(
        &self,
        owner: Option<&ArgType>,
        class_signature: Option<&ClassSignature>,
        signature: Option<&MethodSignature>,
    ) -> Result<std::collections::BTreeMap<KotlinIdentifier, KotlinType>, KotlinDecompilerError>
    {
        let mut bounds = std::collections::BTreeMap::new();
        for (name, bound) in owner
            .into_iter()
            .flat_map(|owner| self.source_abi.lexical_type_bounds(owner))
        {
            bounds.insert(
                KotlinIdentifier::from_dex(name),
                self.names.resolve_generic_type(bound)?,
            );
        }
        for parameter in class_signature
            .into_iter()
            .flat_map(|signature| &signature.type_parameters)
            .chain(
                signature
                    .into_iter()
                    .flat_map(|signature| &signature.type_parameters),
            )
        {
            let Some(bound) = parameter
                .class_bound
                .as_ref()
                .or_else(|| parameter.interface_bounds.first())
            else {
                continue;
            };
            bounds.insert(
                KotlinIdentifier::from_dex(&parameter.name),
                self.names.resolve_generic_type(bound)?,
            );
        }
        Ok(bounds)
    }

    fn type_parameter_erasure(
        parameter: &crate::ir::generic_types::TypeParameter,
    ) -> (KotlinIdentifier, ArgType) {
        let erased = parameter
            .class_bound
            .as_ref()
            .or_else(|| parameter.interface_bounds.first())
            .map(crate::ir::generic_types::JvmTypeSignature::erased)
            .unwrap_or_else(|| ArgType::object("java/lang/Object"));
        (KotlinIdentifier::from_dex(&parameter.name), erased)
    }

    fn source_current_type(
        &self,
        owner: Option<&ArgType>,
        class_signature: Option<&ClassSignature>,
    ) -> Result<Option<KotlinType>, KotlinDecompilerError> {
        let Some(owner) = owner else {
            return Ok(None);
        };
        if let Some(owner) = self.source_abi.owner_type(owner) {
            return self
                .names
                .resolve_generic_type(&JvmTypeSignature::ClassType(owner.clone()))
                .map(Some)
                .map_err(KotlinDecompilerError::from);
        }
        let mut ty = self.names.resolve_type(owner)?;
        if let (Some(signature), KotlinType::Class(class)) = (class_signature, &mut ty) {
            if let Some(segment) = class.segments.last_mut() {
                segment.arguments = signature
                    .type_parameters
                    .iter()
                    .map(|parameter| {
                        KotlinTypeArgument::Exact(KotlinType::Variable(KotlinIdentifier::from_dex(
                            &parameter.name,
                        )))
                    })
                    .collect();
            }
        }
        Ok(Some(ty))
    }
}

struct KotlinObjectDeclaration;

impl KotlinObjectDeclaration {
    fn lower(
        declaration: &mut KotlinTypeDeclaration,
        identity: &KotlinType,
        instance_fields: std::collections::BTreeSet<KotlinIdentifier>,
    ) {
        let mut identity_lowering = ObjectIdentityLowering {
            owner: identity,
            fields: &instance_fields,
            bindings: std::collections::BTreeSet::new(),
        };
        for method in &mut declaration.methods {
            if method.kind == KotlinMethodDeclarationKind::ClassInitializer {
                if let Some(body) = method.body.as_mut() {
                    identity_lowering.bindings = ObjectIdentityLowering::recover_bindings(
                        &body.root,
                        identity,
                        &instance_fields,
                    );
                    identity_lowering.rewrite_body(body);
                }
            }
        }
        declaration.methods.retain(|method| {
            method.kind != KotlinMethodDeclarationKind::ClassInitializer
                || method
                    .body
                    .as_ref()
                    .is_some_and(|body| !Self::empty_statement(&body.root))
        });
        declaration.modifiers.retain(|modifier| {
            !matches!(
                modifier,
                KotlinModifier::Abstract
                    | KotlinModifier::Final
                    | KotlinModifier::Open
                    | KotlinModifier::Sealed
                    | KotlinModifier::Static
            )
        });
        for field in &mut declaration.fields {
            field
                .modifiers
                .retain(|modifier| *modifier != KotlinModifier::Static);
        }
        for property in &mut declaration.properties {
            property
                .modifiers
                .retain(|modifier| *modifier != KotlinModifier::Static);
        }
        for method in &mut declaration.methods {
            method
                .modifiers
                .retain(|modifier| *modifier != KotlinModifier::Static);
        }
    }

    fn empty_statement(statement: &KotlinStmt) -> bool {
        match statement {
            KotlinStmt::Empty => true,
            KotlinStmt::Block(statements) => statements.iter().all(Self::empty_statement),
            _ => false,
        }
    }
}

/// Rebinds the JVM allocation stored in a metadata-proven singleton field to
/// Kotlin's already-constructed object identity.
struct ObjectIdentityLowering<'a> {
    owner: &'a KotlinType,
    fields: &'a std::collections::BTreeSet<KotlinIdentifier>,
    bindings: std::collections::BTreeSet<KotlinIdentifier>,
}

impl ObjectIdentityLowering<'_> {
    fn recover_bindings(
        root: &KotlinStmt,
        owner: &KotlinType,
        fields: &std::collections::BTreeSet<KotlinIdentifier>,
    ) -> std::collections::BTreeSet<KotlinIdentifier> {
        let KotlinStmt::Block(statements) = root else {
            return std::collections::BTreeSet::new();
        };
        let allocations = statements
            .iter()
            .filter_map(|statement| {
                let KotlinStmt::Variable {
                    binding,
                    name,
                    value: Some(value),
                    ..
                } = statement
                else {
                    return None;
                };
                (!binding.mutable && Self::is_self_allocation(value, owner)).then(|| name.clone())
            })
            .collect::<std::collections::BTreeSet<_>>();
        statements
            .iter()
            .filter_map(|statement| {
                let KotlinStmt::Assign {
                    target,
                    op: KotlinAssignOp::Assign,
                    value,
                } = statement
                else {
                    return None;
                };
                let KotlinExpr::StaticField {
                    owner: field_owner,
                    name: field,
                } = target
                else {
                    return None;
                };
                if field_owner != owner || !fields.contains(field) {
                    return None;
                }
                let KotlinExpr::Name(binding) = Self::proof_value(value) else {
                    return None;
                };
                allocations.contains(binding).then(|| binding.clone())
            })
            .collect()
    }

    fn is_self_allocation(value: &KotlinExpr, owner: &KotlinType) -> bool {
        matches!(
            Self::proof_value(value),
            KotlinExpr::New {
                enclosing: None,
                ty,
                args,
                anonymous_body: None,
                ..
            } if ty == owner && args.is_empty()
        )
    }

    fn proof_value(mut value: &KotlinExpr) -> &KotlinExpr {
        while let KotlinExpr::SmartCast(inner) | KotlinExpr::NonNullAssertion(inner) = value {
            value = inner;
        }
        value
    }
}

impl KotlinAstRewriter for ObjectIdentityLowering<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match expression {
            KotlinExpr::Name(name) if self.bindings.contains(&name) => KotlinExpr::This,
            expression => expression,
        }
    }

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        match &statement {
            KotlinStmt::Variable {
                name,
                value: Some(value),
                ..
            } if self.bindings.contains(name) && Self::is_self_allocation(value, self.owner) => {
                KotlinStmt::Empty
            }
            KotlinStmt::Assign {
                target: crate::language::kotlin::KotlinExpr::StaticField { owner, name },
                ..
            } if owner == self.owner && self.fields.contains(name) => KotlinStmt::Empty,
            _ => statement,
        }
    }
}

fn type_kind(kind: KotlinClassKind) -> KotlinTypeDeclarationKind {
    match kind {
        KotlinClassKind::Class => KotlinTypeDeclarationKind::Class,
        KotlinClassKind::Interface => KotlinTypeDeclarationKind::Interface,
        KotlinClassKind::Enum => KotlinTypeDeclarationKind::Enum,
        KotlinClassKind::Annotation => KotlinTypeDeclarationKind::Annotation,
    }
}

fn method_kind(kind: MethodModelKind) -> KotlinMethodDeclarationKind {
    match kind {
        MethodModelKind::Method => KotlinMethodDeclarationKind::Method,
        MethodModelKind::Constructor => KotlinMethodDeclarationKind::Constructor,
        MethodModelKind::ClassInitializer => KotlinMethodDeclarationKind::ClassInitializer,
    }
}

fn visible_parameter_position(
    parameters: &[super::kotlin_model::method::KotlinMethodParameter],
    dex_index: usize,
) -> Option<usize> {
    parameters
        .get(dex_index)
        .is_some_and(|parameter| !parameter.hidden)
        .then(|| {
            parameters[..dex_index]
                .iter()
                .filter(|parameter| !parameter.hidden)
                .count()
        })
}

fn method_reference(owner: &ArgType, declaration: &MethodModel) -> crate::ir::MethodReference {
    crate::ir::MethodReference {
        owner: owner.clone(),
        name: match declaration.kind {
            MethodModelKind::Constructor => "<init>".to_string(),
            MethodModelKind::ClassInitializer => "<clinit>".to_string(),
            MethodModelKind::Method => declaration.name.dex_name().to_string(),
        },
        descriptor: crate::ir::MethodDescriptor {
            parameters: declaration
                .parameters
                .iter()
                .map(|parameter| parameter.ty.clone())
                .collect(),
            return_type: declaration.return_type.clone().unwrap_or(ArgType::VOID),
        },
    }
}
