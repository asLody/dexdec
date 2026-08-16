use crate::analysis::{MethodRecoveryFailure, MethodRecoveryStage};
use crate::ir::generic_types::{ClassSignature, JvmTypeSignature, MethodSignature};
use crate::ir::ty::ArgType;
use crate::language::java::{
    JavaAnnotation, JavaClassName, JavaClassType, JavaCompilationUnit, JavaExpr,
    JavaFieldDeclaration, JavaFieldSymbol, JavaIdentifier, JavaLiteral, JavaMemberNames,
    JavaMethodBody, JavaMethodDeclaration, JavaMethodDeclarationKind, JavaMethodParameter,
    JavaMethodSymbol, JavaModifier, JavaStmt, JavaType, JavaTypeArgument, JavaTypeDeclaration,
    JavaTypeDeclarationKind, JavaTypeParameter,
};

use super::anonymous_lowering::{
    AnonymousClassRecovery, EnumConstantBodyRecovery, FunctionContract, LoweredNestedType,
    NestedTypeLiveness,
};
use super::constants::JavaConstantLowering;
use super::constructor_syntax::{ConstructorMethodReturnTypes, ConstructorSyntaxRecovery};
use super::enum_lowering::{EnumDeclarationRecovery, EnumSwitchRecovery};
use super::function_object_types::FunctionObjectTypeCatalog;
use super::java_model::method::{JavaMethodDeclarationKind as MethodModelKind, JavaMethodModel};
use super::java_model::{JavaClassKind, JavaFieldDeclaration as FieldModel};
use super::java_model::{JavaClassModel, JavaMethodDeclaration as MethodModel};
use super::member_names::ClassMemberNames;
use super::static_initialization::StaticInitializationRecovery;
use super::synthetic_members::SyntheticMemberRecovery;
use super::type_names::JavaTypeNameResolver;
use super::type_uses::{ClassTypeUses, GenericTypeUses};
use super::JavaDecompilerError;

pub(super) struct JavaCompilationUnitLowering;

impl JavaCompilationUnitLowering {
    fn constructor_factory_erased_return_is_safe(return_type: &JvmTypeSignature) -> bool {
        match return_type {
            JvmTypeSignature::ClassType(_) | JvmTypeSignature::BaseType(_) => true,
            JvmTypeSignature::Array(component) => {
                Self::constructor_factory_erased_return_is_safe(component)
            }
            JvmTypeSignature::TypeVariable(_) => false,
        }
    }

    fn normalize_annotation_header(declaration: &mut JavaTypeDeclaration) {
        if declaration.kind != JavaTypeDeclarationKind::Annotation {
            return;
        }
        // JVM annotation interfaces carry java.lang.annotation.Annotation as
        // an implemented interface and may retain generic Signature metadata,
        // but neither relation is legal in a Java @interface declaration.
        declaration.type_parameters.clear();
        declaration.extends = None;
        declaration.implements.clear();
    }

    pub(super) fn lower(
        class: &JavaClassModel,
        source_abi: &std::sync::Arc<super::JavaSourceAbi>,
        hierarchy: std::sync::Arc<crate::ir::analysis::ClassHierarchyIndex>,
        observer: std::sync::Arc<dyn crate::ir::AnalysisObserver>,
    ) -> Result<JavaCompilationUnit, JavaDecompilerError> {
        let package_name = class.declaration.package.clone();
        let package = package_name.as_ref().map(ToString::to_string);
        let current_type = class.declaration.current_type();
        let (field_references, method_references) =
            crate::profile_scope!("java_backend.lower.references", {
                (class.field_references(), class.method_references())
            });
        let (generic_fields, generic_methods, referenced_overloads, referenced_constructors) =
            crate::profile_scope!("java_backend.lower.abi", {
                (
                    source_abi.generic_fields(field_references.iter()),
                    source_abi.generic_methods(method_references.iter()),
                    source_abi.referenced_overloads(method_references.iter()),
                    source_abi.referenced_constructors(method_references.iter()),
                )
            });
        let type_uses = crate::profile_scope!("java_backend.lower.type_uses", {
            let mut type_uses = ClassTypeUses::collect(class);
            for contract in generic_fields.values() {
                GenericTypeUses::field_contract(contract, &mut type_uses);
            }
            for contract in generic_methods.values() {
                GenericTypeUses::method_contract(contract, &mut type_uses);
            }
            type_uses
        });
        let names = crate::profile_scope!("java_backend.lower.type_names", {
            JavaTypeNameResolver::for_class(
                class,
                package.as_deref(),
                current_type.as_ref(),
                type_uses,
            )
        })?;
        let members = crate::profile_scope!("java_backend.lower.member_names", {
            std::sync::Arc::new(
                ClassMemberNames::collect(class)
                    .with_constructor_layouts(referenced_constructors)
                    .with_overloads(referenced_overloads),
            )
        });
        let constructor_method_return_types = method_references
            .iter()
            .filter(|reference| {
                reference.name != "<init>"
                    && reference.descriptor.return_type != ArgType::VOID
                    && generic_methods.get(*reference).is_none_or(|contract| {
                        Self::constructor_factory_erased_return_is_safe(
                            &contract.signature.return_type,
                        )
                    })
            })
            .try_fold(
                ConstructorMethodReturnTypes::new(),
                |mut types, reference| -> Result<_, JavaDecompilerError> {
                    let key = (
                        names.resolve_type(&reference.owner)?.into_raw(),
                        members.method(reference),
                        reference.descriptor.parameters.len(),
                    );
                    let return_type = names
                        .resolve_type(&reference.descriptor.return_type)?
                        .into_raw();
                    types
                        .entry(key)
                        .and_modify(|existing| {
                            if existing.as_ref() != Some(&return_type) {
                                *existing = None;
                            }
                        })
                        .or_insert(Some(return_type));
                    Ok(types)
                },
            )?;
        let source_field_types = generic_fields
            .iter()
            .map(|(field, contract)| {
                Ok((
                    field.clone(),
                    names
                        .resolve_generic_type(&contract.signature)
                        .map_err(JavaDecompilerError::from)?,
                ))
            })
            .collect::<Result<_, JavaDecompilerError>>()?;
        let local_function_object_types = FunctionObjectTypeCatalog::collect(class);
        let source_object_types = source_abi
            .function_object_types()
            .map(|(identity, interface)| (identity.clone(), interface.clone()))
            .chain(local_function_object_types)
            .map(|(identity, interface)| Ok((identity, names.resolve_generic_type(&interface)?)))
            .collect::<Result<_, JavaDecompilerError>>()?;
        let outer_instances = source_abi
            .outer_instances()
            .chain(class.outer_instances())
            .map(|(field, outer)| (field.clone(), outer.clone()))
            .collect();
        let imports = names
            .imports()
            .filter(|import| source_abi.import_is_accessible(import))
            .collect();
        let declaration = crate::profile_scope!("java_backend.lower.declaration", {
            JavaTypeLowering::new(
                &names,
                members.as_ref(),
                members.clone(),
                source_abi.as_ref(),
                source_abi.clone(),
                hierarchy,
                source_field_types,
                generic_fields,
                generic_methods,
                constructor_method_return_types,
                source_object_types,
                outer_instances,
                observer,
            )
            .lower(class)
        })?;
        Ok(JavaCompilationUnit {
            package: package_name,
            imports,
            declaration,
        })
    }
}

pub(super) struct JavaSingleMethodLowering;

impl JavaSingleMethodLowering {
    pub(super) fn lower(
        method: &JavaMethodModel,
        current_package: Option<&str>,
        current_type: Option<&ArgType>,
        type_uses: impl IntoIterator<Item = ArgType>,
        source_abi: &std::sync::Arc<super::JavaSourceAbi>,
        hierarchy: std::sync::Arc<crate::ir::analysis::ClassHierarchyIndex>,
        observer: std::sync::Arc<dyn crate::ir::AnalysisObserver>,
    ) -> Result<JavaMethodDeclaration, JavaDecompilerError> {
        let field_references = method
            .body
            .as_ref()
            .map(super::java_model::method::JavaMethodBody::field_references)
            .unwrap_or_default();
        let generic_fields = source_abi.generic_fields(field_references.iter());
        let method_references = method
            .body
            .as_ref()
            .map(super::java_model::method::JavaMethodBody::method_references)
            .unwrap_or_default();
        let generic_methods = source_abi.generic_methods(method_references.iter());
        let referenced_overloads = source_abi.referenced_overloads(method_references.iter());
        let referenced_constructors = source_abi.referenced_constructors(method_references.iter());
        let mut type_uses = type_uses.into_iter().collect::<Vec<_>>();
        for contract in generic_fields.values() {
            GenericTypeUses::field_contract(contract, &mut type_uses);
        }
        for contract in generic_methods.values() {
            GenericTypeUses::method_contract(contract, &mut type_uses);
        }
        let names = JavaTypeNameResolver::new(current_package, current_type, type_uses)?;
        let members = std::sync::Arc::new(
            ClassMemberNames::method_only(current_type, method)
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
                        .map_err(JavaDecompilerError::from)?,
                ))
            })
            .collect::<Result<_, JavaDecompilerError>>()?;
        let mut outer_instances = source_abi
            .outer_instances()
            .map(|(field, outer)| (field.clone(), outer.clone()))
            .collect::<std::collections::BTreeMap<_, _>>();
        if let Some((field, outer)) = method
            .body
            .as_ref()
            .and_then(super::java_model::method::JavaMethodBody::outer_instance_field)
        {
            outer_instances.insert(field.clone(), outer.clone());
        }
        let lowering = JavaTypeLowering::new(
            &names,
            members.as_ref(),
            members.clone(),
            source_abi.as_ref(),
            source_abi.clone(),
            hierarchy,
            source_field_types,
            generic_fields,
            generic_methods,
            ConstructorMethodReturnTypes::new(),
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

struct JavaTypeLowering<'a> {
    names: &'a JavaTypeNameResolver,
    members: &'a JavaMemberNames,
    shared_members: std::sync::Arc<JavaMemberNames>,
    source_abi: &'a super::JavaSourceAbi,
    constants: JavaConstantLowering<'a>,
    source_field_types:
        std::sync::Arc<std::collections::BTreeMap<crate::ir::FieldReference, JavaType>>,
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
    constructor_method_return_types: ConstructorMethodReturnTypes,
    source_object_types: std::sync::Arc<std::collections::BTreeMap<ArgType, JavaType>>,
    outer_instances: std::collections::BTreeMap<crate::ir::FieldReference, ArgType>,
    generic_type_projection: std::sync::Arc<dyn crate::language::java::GenericTypeProjection>,
    observer: std::sync::Arc<dyn crate::ir::AnalysisObserver>,
}

#[derive(Debug)]
struct SourceGenericTypeProjection {
    names: JavaTypeNameResolver,
    source_abi: std::sync::Arc<super::JavaSourceAbi>,
    hierarchy: std::sync::Arc<crate::ir::analysis::ClassHierarchyIndex>,
    cache: GenericProjectionCache,
}

#[derive(Debug, Default)]
struct GenericProjectionCache {
    specialized:
        std::sync::Mutex<std::collections::BTreeMap<(ArgType, JavaType), Option<JavaType>>>,
    inferred: std::sync::Mutex<std::collections::BTreeMap<(ArgType, JavaType), Option<JavaType>>>,
    projected: std::sync::Mutex<std::collections::BTreeMap<(JavaType, ArgType), Option<JavaType>>>,
    subtype_relations: std::sync::Mutex<
        std::collections::BTreeMap<(ArgType, ArgType), crate::ir::analysis::SubtypeRelation>,
    >,
    common_types: std::sync::Mutex<std::collections::BTreeMap<(ArgType, ArgType), Option<ArgType>>>,
    resolved: std::sync::Mutex<std::collections::BTreeMap<ArgType, JavaType>>,
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

impl crate::language::java::GenericTypeProjection for SourceGenericTypeProjection {
    fn specialize_subtype(
        &self,
        subtype: &ArgType,
        expected_supertype: &JavaType,
    ) -> Option<JavaType> {
        let key = (subtype.clone(), expected_supertype.clone());
        if let Some(result) = self.cache.specialized.lock().ok()?.get(&key).cloned() {
            return result;
        }
        let result = self
            .names
            .source_signature(expected_supertype)
            .and_then(|expected| self.source_abi.specialize_subtype(subtype, &expected))
            .and_then(|specialized| self.names.resolve_generic_type(&specialized).ok());
        self.cache
            .specialized
            .lock()
            .ok()?
            .insert(key, result.clone());
        result
    }

    fn infer_subtype(&self, subtype: &ArgType, expected_supertype: &JavaType) -> Option<JavaType> {
        let key = (subtype.clone(), expected_supertype.clone());
        if let Some(result) = self.cache.inferred.lock().ok()?.get(&key).cloned() {
            return result;
        }
        let result = self
            .names
            .source_signature(expected_supertype)
            .and_then(|expected| self.source_abi.infer_subtype(subtype, &expected))
            .and_then(|inferred| self.names.resolve_generic_type(&inferred).ok());
        self.cache.inferred.lock().ok()?.insert(key, result.clone());
        result
    }

    fn project_supertype(
        &self,
        subtype: &JavaType,
        expected_supertype: &ArgType,
    ) -> Option<JavaType> {
        let key = (subtype.clone(), expected_supertype.clone());
        if let Some(result) = self.cache.projected.lock().ok()?.get(&key).cloned() {
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
            .lock()
            .ok()?
            .insert(key, result.clone());
        result
    }

    fn subtype_relation(
        &self,
        subtype: &ArgType,
        supertype: &ArgType,
    ) -> crate::ir::analysis::SubtypeRelation {
        use crate::ir::analysis::{SubtypeRelation, TypeHierarchy};
        let key = (subtype.clone(), supertype.clone());
        if let Some(result) = self
            .cache
            .subtype_relations
            .lock()
            .ok()
            .and_then(|cache| cache.get(&key).copied())
        {
            return result;
        }
        let source_relation = (self.source_abi.is_subtype(subtype, supertype)
            || self
                .names
                .resolve_type(subtype)
                .ok()
                .map(JavaType::into_raw)
                .and_then(|subtype| self.names.source_signature(&subtype))
                .and_then(|subtype| self.source_abi.project_supertype(&subtype, supertype))
                .is_some())
        .then_some(SubtypeRelation::Yes);
        let result =
            source_relation.unwrap_or_else(|| match (subtype.as_object(), supertype.as_object()) {
                (Some(subtype), Some(supertype)) => {
                    self.hierarchy.subtype_relation(subtype, supertype)
                }
                _ => SubtypeRelation::Unknown,
            });
        if let Ok(mut cache) = self.cache.subtype_relations.lock() {
            cache.insert(key, result);
        }
        result
    }

    fn least_common_supertype(&self, left: &ArgType, right: &ArgType) -> Option<ArgType> {
        use crate::ir::analysis::TypeHierarchy;
        let key = if left <= right {
            (left.clone(), right.clone())
        } else {
            (right.clone(), left.clone())
        };
        if let Some(result) = self.cache.common_types.lock().ok()?.get(&key).cloned() {
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
            .lock()
            .ok()?
            .insert(key, result.clone());
        result
    }

    fn is_cast_convertible(&self, source: &ArgType, target: &ArgType) -> bool {
        self.reference_cast_convertible(source, target)
    }

    fn resolve_type(&self, ty: &ArgType) -> Option<JavaType> {
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

    fn erasure_of(&self, ty: &JavaType) -> Option<ArgType> {
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

impl<'a> JavaTypeLowering<'a> {
    fn new(
        names: &'a JavaTypeNameResolver,
        members: &'a JavaMemberNames,
        shared_members: std::sync::Arc<JavaMemberNames>,
        source_abi: &'a super::JavaSourceAbi,
        shared_source_abi: std::sync::Arc<super::JavaSourceAbi>,
        hierarchy: std::sync::Arc<crate::ir::analysis::ClassHierarchyIndex>,
        source_field_types: std::collections::BTreeMap<crate::ir::FieldReference, JavaType>,
        generic_fields: std::collections::BTreeMap<
            crate::ir::FieldReference,
            crate::ir::generic_types::GenericFieldContract,
        >,
        generic_methods: std::collections::BTreeMap<
            crate::ir::MethodReference,
            crate::ir::generic_types::GenericMethodContract,
        >,
        constructor_method_return_types: ConstructorMethodReturnTypes,
        source_object_types: std::collections::BTreeMap<ArgType, JavaType>,
        outer_instances: std::collections::BTreeMap<crate::ir::FieldReference, ArgType>,
        observer: std::sync::Arc<dyn crate::ir::AnalysisObserver>,
    ) -> Self {
        Self {
            names,
            members,
            shared_members,
            source_abi,
            constants: JavaConstantLowering::new(names, members),
            source_field_types: std::sync::Arc::new(source_field_types),
            generic_fields: std::sync::Arc::new(generic_fields),
            generic_methods: std::sync::Arc::new(generic_methods),
            constructor_method_return_types,
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

    fn lower(&self, class: &JavaClassModel) -> Result<JavaTypeDeclaration, JavaDecompilerError> {
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
                .ok_or(JavaDecompilerError::MalformedDeclarationStack)?;
            let nested = results.drain(start..).collect();
            results.push(self.lower_type(class, nested)?);
        }
        if results.len() != 1 {
            return Err(JavaDecompilerError::MalformedDeclarationStack);
        }
        let lowered = results
            .pop()
            .ok_or(JavaDecompilerError::MalformedDeclarationStack)?;
        let mut declaration = lowered.declaration;
        let recovered_functions = lowered.liveness.apply(&mut declaration);
        // Resolved simple owner names can collide across unrelated classes;
        // only aliases owned by this lexical model may rewrite its fields.
        let outer_aliases = class
            .outer_instances()
            .map(|(field, outer)| {
                Ok((
                    self.names.resolve_type(&field.owner)?,
                    self.members.field(field),
                    self.names.resolve_type(outer)?,
                ))
            })
            .collect::<Result<Vec<_>, JavaDecompilerError>>()?;
        super::lexical_owners::LexicalOwners::recover_outer_aliases(
            &mut declaration,
            outer_aliases,
        );
        SyntheticMemberRecovery::apply(&mut declaration, &recovered_functions);
        super::type_variable_closure::TypeVariableClosure::close(&mut declaration);
        super::lexical_owners::LexicalOwners::qualify(&mut declaration);
        Ok(declaration)
    }

    fn lower_type(
        &self,
        class: &JavaClassModel,
        mut nested: Vec<LoweredNestedType>,
    ) -> Result<LoweredNestedType, JavaDecompilerError> {
        let owner = class.declaration.current_type();
        let identity = owner
            .as_ref()
            .map(|ty| self.names.resolve_type(ty))
            .transpose()?
            .unwrap_or_else(|| {
                JavaType::Class(JavaClassType::raw(JavaClassName::simple(
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
                .collect::<Result<std::collections::BTreeMap<_, _>, JavaDecompilerError>>()?;
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
        let mut methods = Vec::with_capacity(class.methods.len());
        for method in &class.methods {
            if method.declaration.source_bridge {
                continue;
            }
            let lowered = crate::profile_scope!("java_backend.lower.method", {
                self.method(
                    method,
                    owner.as_ref(),
                    class.declaration.signature.as_ref(),
                    source_super_type.as_ref(),
                    &source_field_types,
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
                        .as_ref()
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
                        owner.as_ref(),
                        class.declaration.signature.as_ref(),
                        source_super_type.as_ref(),
                        &source_field_types,
                    )?
                }
            };
            if method.body.as_ref().is_some_and(|_| {
                lowered.body.as_ref().is_some_and(|body| {
                    source_constructor_count == 1
                        && method.is_default_constructor(
                            &class.declaration.name,
                            &class.declaration.modifiers,
                            body,
                        )
                })
            }) {
                continue;
            }
            methods.push(lowered);
        }
        let mut fields = crate::profile_scope!("java_backend.lower.fields", {
            class
                .fields
                .iter()
                .map(|field| self.field(field, owner.as_ref()))
                .collect::<Result<Vec<_>, _>>()
        })?;
        let synthetic_final_fields = class
            .fields
            .iter()
            .zip(&fields)
            .filter_map(|(model, lowered)| {
                (model.access_flags.is_synthetic() && model.access_flags.is_final())
                    .then_some(lowered.name.clone())
            })
            .collect();
        let enum_declaration = EnumDeclarationRecovery::apply(class, fields, methods);
        let constant_implementations = enum_declaration.constant_implementations;

        let mut modifiers = class.declaration.modifiers.clone();
        if owner
            .as_ref()
            .is_some_and(|owner| self.source_abi.nested_type_requires_external_access(owner))
        {
            modifiers.retain(|modifier| *modifier != JavaModifier::Private);
        }
        let mut declaration = JavaTypeDeclaration {
            annotations: self.constants.annotations(&class.declaration.annotations)?,
            modifiers,
            kind: type_kind(class.declaration.kind),
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
            fields: enum_declaration.fields,
            methods: enum_declaration.methods,
            nested: Vec::new(),
        };
        JavaCompilationUnitLowering::normalize_annotation_header(&mut declaration);
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
        Self::remove_implicit_field_modifiers(class.declaration.kind, &mut declaration.fields);
        ConstructorSyntaxRecovery::apply_with_method_returns(
            &mut declaration,
            &self.constructor_method_return_types,
        );
        let initialization =
            super::field_initialization::FieldInitializationFacts::analyze(&declaration);
        initialization.apply(&mut declaration);
        let function_contract = self.function_contract(class);
        let function_type = class
            .function_interface()
            .map(|interface| self.names.resolve_generic_type(interface))
            .transpose()?;
        let lexical_type_variables = owner
            .as_ref()
            .into_iter()
            .flat_map(|owner| self.source_abi.lexical_type_variables(owner))
            .map(JavaIdentifier::from_dex)
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

    fn assign_nested_names(owner: &JavaTypeDeclaration, nested: &mut [LoweredNestedType]) {
        let mut scope = crate::language::java::JavaNameScope::default();
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

    fn function_contract(&self, class: &JavaClassModel) -> Option<FunctionContract> {
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

    fn remove_implicit_field_modifiers(kind: JavaClassKind, fields: &mut [JavaFieldDeclaration]) {
        if !matches!(kind, JavaClassKind::Interface | JavaClassKind::Annotation) {
            return;
        }
        for field in fields {
            field.modifiers.retain(|modifier| {
                !matches!(
                    modifier,
                    JavaModifier::Public | JavaModifier::Static | JavaModifier::Final
                )
            });
        }
    }

    fn extends(&self, class: &JavaClassModel) -> Result<Option<JavaType>, JavaDecompilerError> {
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

    fn implements(&self, class: &JavaClassModel) -> Result<Vec<JavaType>, JavaDecompilerError> {
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
                        .map_err(JavaDecompilerError::from),
                    None => self
                        .names
                        .resolve_header_type(interface)
                        .map_err(JavaDecompilerError::from),
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
                            .map_err(JavaDecompilerError::from)
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
                            .map_err(JavaDecompilerError::from)
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
                    .map_err(JavaDecompilerError::from)
            })
            .collect()
    }

    fn field(
        &self,
        field: &FieldModel,
        owner: Option<&ArgType>,
    ) -> Result<JavaFieldDeclaration, JavaDecompilerError> {
        Ok(JavaFieldDeclaration {
            annotations: self.constants.annotations(&field.annotations)?,
            modifiers: field.modifiers.clone(),
            ty: match &field.signature {
                Some(signature) => self.names.resolve_generic_type(signature)?,
                None => self.names.resolve_type(&field.field_type)?,
            },
            name: owner
                .map(|owner| {
                    self.members.field_symbol(&JavaFieldSymbol::new(
                        owner.clone(),
                        field.name.clone(),
                        field.field_type.clone(),
                    ))
                })
                .unwrap_or_else(|| field.name.clone()),
            initializer: field
                .initializer
                .as_ref()
                .map(|value| self.constants.field_initializer(&field.field_type, value))
                .transpose()?,
        })
    }

    fn method(
        &self,
        method: &JavaMethodModel,
        owner: Option<&ArgType>,
        class_signature: Option<&ClassSignature>,
        source_super_type: Option<&JavaType>,
        source_field_types: &std::sync::Arc<
            std::collections::BTreeMap<crate::ir::FieldReference, JavaType>,
        >,
    ) -> Result<JavaMethodDeclaration, JavaDecompilerError> {
        let declaration = &method.declaration;
        let signature = declaration.signature.as_ref();
        let annotations = self.method_annotations(declaration)?;
        let mut name_scope = crate::language::java::JavaNameScope::default();
        let reserved_type_qualifiers = method
            .body
            .as_ref()
            .into_iter()
            .flat_map(super::java_model::method::JavaMethodBody::static_owner_types)
            .map(|owner| self.names.resolve_type(&owner))
            .collect::<Result<Vec<_>, _>>()?
            .iter()
            .filter_map(source_type_qualifier)
            .collect::<std::collections::BTreeSet<_>>();
        for qualifier in &reserved_type_qualifiers {
            name_scope.reserve(qualifier.clone());
        }
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
                name_scope.claim(
                    parameter
                        .name
                        .clone()
                        .or_else(|| {
                            (!parameter.hidden)
                                .then(|| parameter_naming.candidate(&parameter.ty))
                                .flatten()
                        })
                        .unwrap_or_else(|| JavaIdentifier::from_dex(&generated)),
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
                Ok(JavaMethodParameter {
                    annotations: self.constants.annotations(&parameter.annotations)?,
                    ty: self.method_parameter_type(
                        signature,
                        signature_index,
                        &parameter.ty,
                        declaration
                            .source_parameter_types
                            .get(parameter_index)
                            .and_then(Option::as_ref),
                    )?,
                    name: parameter_names[parameter_index].clone(),
                    varargs: parameter.varargs,
                })
            })
            .collect::<Result<Vec<_>, JavaDecompilerError>>()?;
        let return_type = self.method_return_type(declaration, signature)?;
        let mut throws = self.method_throws(declaration, signature)?;
        let mut type_parameters = signature
            .map(|signature| {
                self.names
                    .resolve_type_parameters(&signature.type_parameters)
            })
            .transpose()?
            .unwrap_or_default();
        let instance_scope = declaration.kind != MethodModelKind::ClassInitializer
            && !declaration.modifiers.contains(&JavaModifier::Static);
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
                        .collect::<Result<std::collections::BTreeMap<_, _>, JavaDecompilerError>>(
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
                    crate::profile_scope!("java_backend.lower.method_body", {
                        body.lower(
                            &parameter_names,
                            self.names,
                            self.shared_members.clone(),
                            source_field_types.clone(),
                            self.generic_fields.clone(),
                            self.generic_methods.clone(),
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
                            {
                                let mut reserved = reserved_type_qualifiers.clone();
                                if declaration.kind.is_class_initializer() {
                                    reserved.extend(
                                        owner
                                            .map(|owner| self.members.field_names(owner))
                                            .unwrap_or_default(),
                                    );
                                }
                                reserved
                            },
                            declaration.kind.is_class_initializer(),
                            self.observer.clone(),
                        )
                    })
                })
            })
            .transpose()?;
        if declaration.override_semantics.is_none()
            && (declaration.kind == MethodModelKind::Constructor
                || declaration.modifiers.iter().any(|modifier| {
                    matches!(
                        modifier,
                        JavaModifier::Final | JavaModifier::Private | JavaModifier::Static
                    )
                }))
        {
            if let Some(body) = body.as_mut() {
                let throwable = self.names.resolve_type(&ArgType::throwable())?;
                if !throws.contains(&throwable)
                    && MergedThrowableRethrow::contains(body, &throwable)
                {
                    for parameter in &type_parameters {
                        name_scope.reserve(parameter.name.clone());
                    }
                    let name = name_scope.claim(JavaIdentifier::from_hint("$dex$Thrown"));
                    let variable = JavaType::Variable(name.clone());
                    MergedThrowableRethrow::rewrite(body, &throwable, &variable);
                    type_parameters.push(JavaTypeParameter {
                        name,
                        bounds: vec![throwable],
                    });
                    throws.push(variable);
                }
            }
        }
        Ok(JavaMethodDeclaration {
            annotations,
            modifiers: declaration.modifiers.clone(),
            compiler_generated: declaration.access_flags.is_synthetic(),
            kind: method_kind(declaration.kind),
            type_parameters,
            return_type,
            name: (!declaration.kind.is_class_initializer()).then(|| {
                if declaration.kind == MethodModelKind::Method {
                    owner
                        .map(|owner| {
                            self.members.method_symbol(&JavaMethodSymbol::new(
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
            parameters,
            throws,
            body,
        })
    }

    fn failure_body(failure: &MethodRecoveryFailure) -> JavaMethodBody {
        JavaMethodBody {
            root: JavaStmt::Block(vec![JavaStmt::Throw(JavaExpr::New {
                enclosing: None,
                ty: JavaType::source_class("UnsupportedOperationException"),
                target_type: None,
                args: vec![JavaExpr::Literal(JavaLiteral::String(
                    failure.summary().into(),
                ))],
                anonymous_body: None,
            })]),
        }
    }

    fn method_annotations(
        &self,
        declaration: &MethodModel,
    ) -> Result<Vec<JavaAnnotation>, JavaDecompilerError> {
        let mut annotations = self.constants.annotations(&declaration.annotations)?;
        let has_override = declaration
            .annotations
            .iter()
            .any(|annotation| annotation.annotation_type == ArgType::object("java/lang/Override"));
        if declaration.override_semantics.is_some()
            && !declaration.kind.is_constructor()
            && !declaration.kind.is_class_initializer()
            && !has_override
        {
            annotations.insert(
                0,
                JavaAnnotation {
                    ty: self
                        .names
                        .resolve_type(&ArgType::object("java/lang/Override"))?,
                    elements: Vec::new(),
                },
            );
        }
        Ok(annotations)
    }

    fn method_parameter_type(
        &self,
        signature: Option<&MethodSignature>,
        index: usize,
        erased: &ArgType,
        inferred: Option<&ArgType>,
    ) -> Result<JavaType, JavaDecompilerError> {
        if let Some(signature) =
            signature.and_then(|signature| signature.parameter_types.get(index))
        {
            return Ok(self.names.resolve_generic_type(signature)?);
        }
        self.names
            .resolve_type(inferred.unwrap_or(erased))
            .map_err(JavaDecompilerError::from)
    }

    fn method_return_type(
        &self,
        declaration: &MethodModel,
        signature: Option<&MethodSignature>,
    ) -> Result<Option<JavaType>, JavaDecompilerError> {
        if !matches!(declaration.kind, MethodModelKind::Method) {
            return Ok(None);
        }
        if let Some(return_type) = declaration.source_return_type.as_ref() {
            return self
                .names
                .resolve_type(return_type)
                .map(Some)
                .map_err(JavaDecompilerError::from);
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
                    .map_err(JavaDecompilerError::from)
            })
            .transpose()
    }

    fn method_throws(
        &self,
        declaration: &MethodModel,
        signature: Option<&MethodSignature>,
    ) -> Result<Vec<JavaType>, JavaDecompilerError> {
        if let Some(signature) = signature {
            if !signature.throws.is_empty() {
                return signature
                    .throws
                    .iter()
                    .map(|ty| {
                        self.names
                            .resolve_generic_type(ty)
                            .map_err(JavaDecompilerError::from)
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
                    .map_err(JavaDecompilerError::from)
            })
            .collect()
    }

    fn generic_throw_types(
        &self,
        signature: Option<&MethodSignature>,
        class_signature: Option<&ClassSignature>,
    ) -> Result<Vec<crate::language::java::JavaSourceErasure>, JavaDecompilerError> {
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
                        .map(|source| crate::language::java::JavaSourceErasure::new(source, erased))
                        .map_err(JavaDecompilerError::from),
                )
            })
            .collect()
    }

    fn type_variable_erasures(
        &self,
        owner: Option<&ArgType>,
        class_signature: Option<&ClassSignature>,
        signature: Option<&MethodSignature>,
    ) -> std::collections::BTreeMap<JavaIdentifier, ArgType> {
        owner
            .into_iter()
            .flat_map(|owner| self.source_abi.lexical_type_erasures(owner))
            .map(|(name, erased)| (JavaIdentifier::from_dex(name), erased))
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
    ) -> Result<std::collections::BTreeMap<JavaIdentifier, JavaType>, JavaDecompilerError> {
        let mut bounds = std::collections::BTreeMap::new();
        for (name, bound) in owner
            .into_iter()
            .flat_map(|owner| self.source_abi.lexical_type_bounds(owner))
        {
            bounds.insert(
                JavaIdentifier::from_dex(name),
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
                JavaIdentifier::from_dex(&parameter.name),
                self.names.resolve_generic_type(bound)?,
            );
        }
        Ok(bounds)
    }

    fn type_parameter_erasure(
        parameter: &crate::ir::generic_types::TypeParameter,
    ) -> (JavaIdentifier, ArgType) {
        let erased = parameter
            .class_bound
            .as_ref()
            .or_else(|| parameter.interface_bounds.first())
            .map(crate::ir::generic_types::JvmTypeSignature::erased)
            .unwrap_or_else(|| ArgType::object("java/lang/Object"));
        (JavaIdentifier::from_dex(&parameter.name), erased)
    }

    fn source_current_type(
        &self,
        owner: Option<&ArgType>,
        class_signature: Option<&ClassSignature>,
    ) -> Result<Option<JavaType>, JavaDecompilerError> {
        let Some(owner) = owner else {
            return Ok(None);
        };
        if let Some(owner) = self.source_abi.owner_type(owner) {
            return self
                .names
                .resolve_generic_type(&JvmTypeSignature::ClassType(owner.clone()))
                .map(Some)
                .map_err(JavaDecompilerError::from);
        }
        let mut ty = self.names.resolve_type(owner)?;
        if let (Some(signature), JavaType::Class(class)) = (class_signature, &mut ty) {
            if let Some(segment) = class.segments.last_mut() {
                segment.arguments = signature
                    .type_parameters
                    .iter()
                    .map(|parameter| {
                        JavaTypeArgument::Exact(JavaType::Variable(JavaIdentifier::from_dex(
                            &parameter.name,
                        )))
                    })
                    .collect();
            }
        }
        Ok(Some(ty))
    }
}

/// Legalizes a DEX catch-all value that crosses several handler scopes before
/// being rethrown. Java's precise-rethrow rule only applies to catch parameters,
/// so the merged `Throwable` local otherwise requires `throws Throwable` even
/// when the original method has a narrower source contract.
struct MergedThrowableRethrow;

impl MergedThrowableRethrow {
    fn contains(body: &JavaMethodBody, throwable: &JavaType) -> bool {
        let mut locals = std::collections::BTreeSet::new();
        Self::collect_locals(&body.root, throwable, &mut locals);
        Self::contains_throw(&body.root, &locals)
    }

    fn rewrite(body: &mut JavaMethodBody, throwable: &JavaType, target: &JavaType) {
        let mut locals = std::collections::BTreeSet::new();
        Self::collect_locals(&body.root, throwable, &mut locals);
        Self::rewrite_throws(&mut body.root, &locals, target);
    }

    fn collect_locals(
        statement: &JavaStmt,
        throwable: &JavaType,
        locals: &mut std::collections::BTreeSet<JavaIdentifier>,
    ) {
        if let JavaStmt::Variable { ty, name, .. } = statement {
            if ty == throwable {
                locals.insert(name.clone());
            }
        }
        Self::visit_children(statement, &mut |child| {
            Self::collect_locals(child, throwable, locals)
        });
    }

    fn contains_throw(
        statement: &JavaStmt,
        locals: &std::collections::BTreeSet<JavaIdentifier>,
    ) -> bool {
        if matches!(statement, JavaStmt::Throw(JavaExpr::Name(name)) if locals.contains(name)) {
            return true;
        }
        let mut found = false;
        Self::visit_children(statement, &mut |child| {
            found |= Self::contains_throw(child, locals)
        });
        found
    }

    fn rewrite_throws(
        statement: &mut JavaStmt,
        locals: &std::collections::BTreeSet<JavaIdentifier>,
        target: &JavaType,
    ) {
        if let JavaStmt::Throw(JavaExpr::Name(name)) = statement {
            if locals.contains(name) {
                let value = JavaExpr::Name(name.clone());
                *statement = JavaStmt::Throw(JavaExpr::Cast {
                    ty: target.clone(),
                    value: Box::new(value),
                });
                return;
            }
        }
        Self::visit_children_mut(statement, &mut |child| {
            Self::rewrite_throws(child, locals, target)
        });
    }

    fn visit_children(statement: &JavaStmt, visit: &mut impl FnMut(&JavaStmt)) {
        match statement {
            JavaStmt::Block(statements) => statements.iter().for_each(visit),
            JavaStmt::Labeled { body, .. }
            | JavaStmt::While { body, .. }
            | JavaStmt::DoWhile { body, .. }
            | JavaStmt::For { body, .. }
            | JavaStmt::ForEach { body, .. }
            | JavaStmt::Synchronized { body, .. } => visit(body),
            JavaStmt::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                visit(then_stmt);
                if let Some(else_stmt) = else_stmt {
                    visit(else_stmt);
                }
            }
            JavaStmt::Switch { cases, .. } => {
                cases.iter().flat_map(|case| &case.body).for_each(visit);
            }
            JavaStmt::Try {
                body,
                catches,
                finally,
            } => {
                visit(body);
                catches
                    .iter()
                    .map(|catch| &catch.body)
                    .for_each(&mut *visit);
                if let Some(finally) = finally {
                    visit(finally);
                }
            }
            JavaStmt::Empty
            | JavaStmt::Variable { .. }
            | JavaStmt::Expression(_)
            | JavaStmt::ConstructorInvocation { .. }
            | JavaStmt::Assign { .. }
            | JavaStmt::Return(_)
            | JavaStmt::Throw(_)
            | JavaStmt::Break(_)
            | JavaStmt::Continue(_) => {}
        }
    }

    fn visit_children_mut(statement: &mut JavaStmt, visit: &mut impl FnMut(&mut JavaStmt)) {
        match statement {
            JavaStmt::Block(statements) => statements.iter_mut().for_each(visit),
            JavaStmt::Labeled { body, .. }
            | JavaStmt::While { body, .. }
            | JavaStmt::DoWhile { body, .. }
            | JavaStmt::For { body, .. }
            | JavaStmt::ForEach { body, .. }
            | JavaStmt::Synchronized { body, .. } => visit(body),
            JavaStmt::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                visit(then_stmt);
                if let Some(else_stmt) = else_stmt {
                    visit(else_stmt);
                }
            }
            JavaStmt::Switch { cases, .. } => {
                cases
                    .iter_mut()
                    .flat_map(|case| &mut case.body)
                    .for_each(visit);
            }
            JavaStmt::Try {
                body,
                catches,
                finally,
            } => {
                visit(body);
                catches
                    .iter_mut()
                    .map(|catch| &mut catch.body)
                    .for_each(&mut *visit);
                if let Some(finally) = finally {
                    visit(finally);
                }
            }
            JavaStmt::Empty
            | JavaStmt::Variable { .. }
            | JavaStmt::Expression(_)
            | JavaStmt::ConstructorInvocation { .. }
            | JavaStmt::Assign { .. }
            | JavaStmt::Return(_)
            | JavaStmt::Throw(_)
            | JavaStmt::Break(_)
            | JavaStmt::Continue(_) => {}
        }
    }
}

fn type_kind(kind: JavaClassKind) -> JavaTypeDeclarationKind {
    match kind {
        JavaClassKind::Class => JavaTypeDeclarationKind::Class,
        JavaClassKind::Interface => JavaTypeDeclarationKind::Interface,
        JavaClassKind::Enum => JavaTypeDeclarationKind::Enum,
        JavaClassKind::Annotation => JavaTypeDeclarationKind::Annotation,
    }
}

/// The first source component is the expression qualifier that a static
/// member access must keep visible. Reserving it prevents a local binding from
/// turning `Owner.field` into an access through an unrelated local variable.
fn source_type_qualifier(ty: &JavaType) -> Option<JavaIdentifier> {
    let JavaType::Class(class) = ty else {
        return None;
    };
    class.segments.first().map(|segment| segment.name.clone())
}

fn method_kind(kind: MethodModelKind) -> JavaMethodDeclarationKind {
    match kind {
        MethodModelKind::Method => JavaMethodDeclarationKind::Method,
        MethodModelKind::Constructor => JavaMethodDeclarationKind::Constructor,
        MethodModelKind::ClassInitializer => JavaMethodDeclarationKind::ClassInitializer,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::generic_types::GenericSignatures;
    use crate::language::java::GenericTypeProjection;

    #[test]
    fn static_type_qualifier_is_reserved_from_local_names() {
        let owner = JavaType::source_class("a");
        let owner = source_type_qualifier(&owner).expect("owner qualifier");
        let mut names = crate::language::java::JavaNameScope::default();
        names.reserve(owner);

        assert_eq!(
            names.claim(JavaIdentifier::from_dex("a")),
            JavaIdentifier::from_dex("a2")
        );
    }

    #[test]
    fn merged_throwable_rethrow_uses_generic_cast_but_catch_parameter_does_not() {
        let throwable = JavaType::source_class("Throwable");
        let merged = JavaIdentifier::from_hint("merged");
        let caught = JavaIdentifier::from_hint("caught");
        let target = JavaType::Variable(JavaIdentifier::from_hint("T"));
        let mut body = JavaMethodBody {
            root: JavaStmt::Block(vec![
                JavaStmt::Variable {
                    ty: throwable.clone(),
                    name: merged.clone(),
                    value: None,
                },
                JavaStmt::Try {
                    body: Box::new(JavaStmt::Throw(JavaExpr::Name(merged.clone()))),
                    catches: vec![crate::language::java::JavaCatch {
                        types: vec![throwable.clone()],
                        variable: caught.clone(),
                        body: JavaStmt::Throw(JavaExpr::Name(caught.clone())),
                    }],
                    finally: None,
                },
            ]),
        };

        assert!(MergedThrowableRethrow::contains(&body, &throwable));
        MergedThrowableRethrow::rewrite(&mut body, &throwable, &target);

        let JavaStmt::Block(statements) = &body.root else {
            panic!("expected method block");
        };
        let JavaStmt::Try {
            body: try_body,
            catches,
            ..
        } = &statements[1]
        else {
            panic!("expected try statement");
        };
        assert_eq!(
            try_body.as_ref(),
            &JavaStmt::Throw(JavaExpr::Cast {
                ty: target,
                value: Box::new(JavaExpr::Name(merged)),
            })
        );
        assert_eq!(catches[0].body, JavaStmt::Throw(JavaExpr::Name(caught)));
    }

    #[test]
    fn annotation_header_omits_jvm_generics_and_marker_interface() {
        let mut declaration = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Annotation,
            name: JavaIdentifier::from_dex("RunInScope"),
            type_parameters: vec![crate::language::java::JavaTypeParameter {
                name: JavaIdentifier::from_dex("T"),
                bounds: vec![JavaType::source_class("example.Scope")],
            }],
            extends: Some(JavaType::source_class("java.lang.Object")),
            implements: vec![JavaType::source_class("java.lang.annotation.Annotation")],
            enum_constants: Vec::new(),
            fields: Vec::new(),
            methods: Vec::new(),
            nested: Vec::new(),
        };

        JavaCompilationUnitLowering::normalize_annotation_header(&mut declaration);

        assert!(declaration.type_parameters.is_empty());
        assert!(declaration.extends.is_none());
        assert!(declaration.implements.is_empty());
    }

    #[test]
    fn constructor_factory_accepts_safe_generic_return_erasure() {
        let collection = GenericSignatures::method(
            "<T:Ljava/lang/Object;>(Ljava/lang/Iterable<+TT;>;)Ljava/util/Set<TT;>;",
        )
        .expect("generic collection method");
        let identity = GenericSignatures::method("<T:Ljava/lang/Object;>(TT;)TT;")
            .expect("generic identity method");
        let array = GenericSignatures::method("<T:Ljava/lang/Object;>(TT;)[TT;")
            .expect("generic array method");

        assert!(
            JavaCompilationUnitLowering::constructor_factory_erased_return_is_safe(
                &collection.return_type,
            )
        );
        assert!(
            !JavaCompilationUnitLowering::constructor_factory_erased_return_is_safe(
                &identity.return_type,
            )
        );
        assert!(
            !JavaCompilationUnitLowering::constructor_factory_erased_return_is_safe(
                &array.return_type,
            )
        );
    }

    #[test]
    fn source_projection_infers_platform_subtype_with_relative_nested_argument() {
        let current = ArgType::object("pkg/Outer$Builder");
        let names = JavaTypeNameResolver::new(
            Some("pkg"),
            Some(&current),
            [
                ArgType::object("java/util/List"),
                ArgType::object("java/util/ArrayList"),
                ArgType::object("pkg/Outer$TypeMatcher"),
            ],
        )
        .expect("type names");
        let source_abi = std::sync::Arc::new(super::super::JavaSourceAbi::analyze(
            std::iter::empty::<&crate::frontend::ClassNode>(),
            |_| (Vec::new(), None),
        ));
        let projection = SourceGenericTypeProjection {
            names: names.clone(),
            source_abi,
            hierarchy: std::sync::Arc::new(crate::ir::analysis::ClassHierarchyIndex::default()),
            cache: GenericProjectionCache::default(),
        };
        let expected = names
            .resolve_generic_type(
                &GenericSignatures::field("Ljava/util/List<Lpkg/Outer$TypeMatcher;>;")
                    .expect("List signature"),
            )
            .expect("source List type");

        assert_eq!(
            projection.infer_subtype(&ArgType::object("java/util/ArrayList"), &expected),
            Some(
                names
                    .resolve_generic_type(
                        &GenericSignatures::field(
                            "Ljava/util/ArrayList<Lpkg/Outer$TypeMatcher;>;",
                        )
                        .expect("ArrayList signature"),
                    )
                    .expect("source ArrayList type"),
            )
        );
    }
}
