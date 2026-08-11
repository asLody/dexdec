use std::collections::{BTreeMap, BTreeSet};

use crate::language::java::{
    JavaAnonymousClassBody, JavaAssignOp, JavaAstRewriter, JavaClassName, JavaClassType,
    JavaClassTypeSegment, JavaConstructorTarget, JavaExpr, JavaIdentifier, JavaMethodDeclaration,
    JavaMethodDeclarationKind, JavaModifier, JavaNameScope, JavaStmt, JavaType, JavaTypeArgument,
    JavaTypeDeclaration,
};

use super::java_model::JavaSourceAbi;
use super::type_names::JavaTypeNameResolver;

#[derive(Clone)]
pub(super) struct LoweredNestedType {
    pub identity: Option<JavaType>,
    pub lexical_type_variables: BTreeSet<JavaIdentifier>,
    pub is_anonymous: bool,
    pub is_function_object: bool,
    pub function_type: Option<JavaType>,
    pub function_contract: Option<FunctionContract>,
    pub synthetic_final_fields: BTreeSet<JavaIdentifier>,
    pub liveness: NestedTypeLiveness,
    pub declaration: JavaTypeDeclaration,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct RecoveredFunction {
    pub owner: JavaIdentifier,
    pub name: JavaIdentifier,
    pub arity: usize,
}

#[derive(Clone, Default)]
pub(super) struct NestedTypeLiveness {
    removable: BTreeSet<JavaIdentifier>,
    recovered_functions: BTreeSet<RecoveredFunction>,
    children: BTreeMap<JavaIdentifier, Self>,
}

impl NestedTypeLiveness {
    pub(super) fn from_nested(nested: &[LoweredNestedType]) -> Self {
        Self {
            removable: BTreeSet::new(),
            recovered_functions: BTreeSet::new(),
            children: nested
                .iter()
                .map(|nested| (nested.declaration.name.clone(), nested.liveness.clone()))
                .collect(),
        }
    }

    pub(super) fn with_removable(
        mut self,
        removable: impl IntoIterator<Item = JavaIdentifier>,
    ) -> Self {
        self.removable.extend(removable);
        self
    }

    pub(super) fn with_recovered_functions(
        mut self,
        recovered: impl IntoIterator<Item = RecoveredFunction>,
    ) -> Self {
        self.recovered_functions.extend(recovered);
        self
    }

    pub(super) fn rename_owner(&mut self, from: &JavaIdentifier, to: &JavaIdentifier) {
        if from == to {
            return;
        }
        self.recovered_functions = std::mem::take(&mut self.recovered_functions)
            .into_iter()
            .map(|mut function| {
                if &function.owner == from {
                    function.owner = to.clone();
                }
                function
            })
            .collect();
    }

    pub(super) fn apply(
        mut self,
        declaration: &mut JavaTypeDeclaration,
    ) -> BTreeSet<RecoveredFunction> {
        let mut recovered = std::mem::take(&mut self.recovered_functions);
        for nested in &mut declaration.nested {
            if let Some(liveness) = self.children.remove(&nested.name) {
                recovered.extend(liveness.apply(nested));
            }
        }
        let live = self
            .removable
            .iter()
            .filter(|name| AnonymousClassRecovery::construction_name_count(declaration, name) != 0)
            .cloned()
            .collect::<BTreeSet<_>>();
        declaration
            .nested
            .retain(|nested| !self.removable.contains(&nested.name) || live.contains(&nested.name));
        recovered
    }
}

#[derive(Clone)]
pub(super) struct FunctionContract {
    pub method: crate::ir::MethodReference,
}

pub(super) struct AnonymousClassRecovery;

pub(super) struct EnumConstantBodyRecovery;

pub(super) struct AnonymousRecoveryFacts {
    pub removable_types: BTreeSet<JavaIdentifier>,
    pub recovered_functions: BTreeSet<RecoveredFunction>,
}

impl EnumConstantBodyRecovery {
    pub(super) fn apply(
        declaration: &mut JavaTypeDeclaration,
        implementations: &[Option<JavaType>],
        nested: Vec<LoweredNestedType>,
    ) -> Vec<LoweredNestedType> {
        let mut nested = nested.into_iter().map(Some).collect::<Vec<_>>();
        for (constant, implementation) in declaration.enum_constants.iter_mut().zip(implementations)
        {
            let Some(implementation) = implementation else {
                continue;
            };
            let Some(index) = nested.iter().position(|candidate| {
                candidate.as_ref().is_some_and(|candidate| {
                    candidate.is_anonymous && candidate.identity.as_ref() == Some(implementation)
                })
            }) else {
                continue;
            };
            let Some(candidate) = nested[index].as_ref() else {
                continue;
            };
            let Some(instance) = AnonymousInstance::recover(
                candidate,
                constant.arguments.clone(),
                None,
                &BTreeSet::new(),
                &BTreeMap::new(),
            ) else {
                continue;
            };
            constant.body = Some(instance.body);
            nested[index] = None;
        }
        nested.into_iter().flatten().collect()
    }
}

impl AnonymousClassRecovery {
    pub(super) fn apply(
        declaration: &mut JavaTypeDeclaration,
        owner: &JavaType,
        mut nested: Vec<LoweredNestedType>,
        names: &JavaTypeNameResolver,
        source_abi: &JavaSourceAbi,
    ) -> AnonymousRecoveryFacts {
        for candidate in &mut nested {
            let recovered = candidate.liveness.clone().apply(&mut candidate.declaration);
            super::synthetic_members::SyntheticMemberRecovery::remove_recovered_functions(
                &mut candidate.declaration,
                &recovered,
            );
        }
        let mut forest = nested.into_iter().map(Some).collect::<Vec<_>>();
        let mut removed = Vec::new();
        let mut recovered_functions = BTreeSet::new();
        let mut parameter_names = FunctionParameterNames::new();
        parameter_names.reserve_declaration(declaration);
        for nested in forest.iter_mut().flatten() {
            parameter_names.reserve_declaration(&mut nested.declaration);
        }
        for index in 0..forest.len() {
            let Some(mut candidate) = forest[index].take() else {
                continue;
            };
            if (!candidate.is_anonymous && !candidate.is_function_object)
                || candidate.identity.is_none()
            {
                RetainedFunctionObjectAbi::apply(&mut candidate, names);
                forest[index] = Some(candidate);
                continue;
            }
            let identity = candidate.identity.as_ref().unwrap();
            let construction_count = Self::construction_count(declaration, identity)
                + forest
                    .iter_mut()
                    .flatten()
                    .map(|nested| Self::construction_count(&mut nested.declaration, identity))
                    .sum::<usize>();
            if construction_count == 0 && Self::is_empty_synthetic_type(&candidate.declaration) {
                removed.push((index, candidate));
                continue;
            }
            if construction_count == 0 || (!candidate.is_function_object && construction_count != 1)
            {
                RetainedFunctionObjectAbi::apply(&mut candidate, names);
                forest[index] = Some(candidate);
                continue;
            }
            let mut rewritten_declaration = declaration.clone();
            let mut rewritten_forest = forest.clone();
            let mut rewritten_functions = BTreeSet::new();
            let mut replaced = 0usize;
            while replaced < construction_count {
                let bound = Self::bind_construction(
                    &mut rewritten_declaration,
                    owner,
                    None,
                    &candidate,
                    names,
                    source_abi,
                    &mut parameter_names,
                    &mut rewritten_functions,
                ) || rewritten_forest.iter_mut().flatten().any(|nested| {
                    let lexical_type_variables = nested.lexical_type_variables.clone();
                    Self::bind_construction(
                        &mut nested.declaration,
                        nested.identity.as_ref().unwrap_or(owner),
                        Some(&lexical_type_variables),
                        &candidate,
                        names,
                        source_abi,
                        &mut parameter_names,
                        &mut rewritten_functions,
                    )
                });
                if !bound {
                    break;
                }
                replaced += 1;
            }
            let remaining = Self::construction_count(&mut rewritten_declaration, identity)
                + rewritten_forest
                    .iter_mut()
                    .flatten()
                    .map(|nested| Self::construction_count(&mut nested.declaration, identity))
                    .sum::<usize>();
            if replaced == construction_count && remaining == 0 {
                if let Some(replacement) = AnonymousInstance::base_type(&candidate) {
                    let mut binding = RecoveredAnonymousTypeBinding {
                        identity,
                        replacement: &replacement,
                    };
                    Self::rewrite_tree(&mut rewritten_declaration, &mut binding);
                    for nested in rewritten_forest.iter_mut().flatten() {
                        Self::rewrite_tree(&mut nested.declaration, &mut binding);
                    }
                }
                *declaration = rewritten_declaration;
                forest = rewritten_forest;
                recovered_functions.extend(rewritten_functions);
                removed.push((index, candidate));
            } else {
                RetainedFunctionObjectAbi::apply(&mut candidate, names);
                forest[index] = Some(candidate);
            }
        }
        let mut removable = BTreeSet::new();
        for (index, candidate) in removed {
            removable.insert(candidate.declaration.name.clone());
            forest[index] = Some(candidate);
        }
        let retained_types = forest
            .iter()
            .flatten()
            .filter_map(|candidate| {
                candidate.identity.clone().map(|identity| {
                    (
                        identity,
                        JavaType::Class(JavaClassType::raw(JavaClassName::simple(
                            candidate.declaration.name.clone(),
                        ))),
                    )
                })
            })
            .collect::<Vec<_>>();
        declaration.nested = forest
            .into_iter()
            .flatten()
            .map(|candidate| candidate.declaration)
            .collect();
        for (identity, lexical_type) in retained_types {
            Self::rewrite_tree(
                declaration,
                &mut NestedTypeReferenceBinding {
                    identity: &identity,
                    lexical_type: &lexical_type,
                },
            );
        }
        AnonymousRecoveryFacts {
            removable_types: removable,
            recovered_functions,
        }
    }

    fn is_empty_synthetic_type(declaration: &JavaTypeDeclaration) -> bool {
        declaration.enum_constants.is_empty()
            && declaration.fields.is_empty()
            && declaration.methods.is_empty()
            && declaration.nested.is_empty()
    }

    fn construction_count(declaration: &mut JavaTypeDeclaration, identity: &JavaType) -> usize {
        let mut counter = AnonymousConstructionCounter { identity, count: 0 };
        Self::rewrite_tree(declaration, &mut counter);
        counter.count
    }

    fn construction_name_count(
        declaration: &mut JavaTypeDeclaration,
        name: &JavaIdentifier,
    ) -> usize {
        let mut counter = NestedConstructionCounter { name, count: 0 };
        Self::rewrite_tree(declaration, &mut counter);
        counter.count
    }

    fn bind_construction(
        declaration: &mut JavaTypeDeclaration,
        owner: &JavaType,
        lexical_type_variables: Option<&BTreeSet<JavaIdentifier>>,
        candidate: &LoweredNestedType,
        names: &JavaTypeNameResolver,
        source_abi: &JavaSourceAbi,
        parameter_names: &mut FunctionParameterNames,
        recovered_functions: &mut BTreeSet<RecoveredFunction>,
    ) -> bool {
        let summaries = FunctionSummary::collect(declaration, owner);
        let mut owner_variables = lexical_type_variables.cloned().unwrap_or_else(|| {
            names
                .source_signature(owner)
                .into_iter()
                .flat_map(|owner| source_abi.lexical_type_variables(&owner.erased()))
                .map(JavaIdentifier::from_dex)
                .collect()
        });
        owner_variables.extend(
            declaration
                .type_parameters
                .iter()
                .map(|parameter| parameter.name.clone()),
        );
        let fields_are_static = declaration.kind.is_interface();
        for field in &mut declaration.fields {
            let type_variables =
                if fields_are_static || field.modifiers.contains(&JavaModifier::Static) {
                    BTreeSet::new()
                } else {
                    owner_variables.clone()
                };
            let mut binder = AnonymousConstructionBinder::new(
                candidate,
                owner.clone(),
                names,
                source_abi,
                &summaries,
                parameter_names,
                &type_variables,
                recovered_functions,
                BTreeSet::new(),
                BTreeMap::new(),
                BTreeMap::new(),
            );
            field.initializer = field
                .initializer
                .take()
                .map(|expression| binder.rewrite_expression(expression));
            if binder.replaced {
                return true;
            }
        }
        for method in &mut declaration.methods {
            let mut type_variables = method
                .type_parameters
                .iter()
                .map(|parameter| parameter.name.clone())
                .collect::<BTreeSet<_>>();
            let instance_member = method.kind == JavaMethodDeclarationKind::Constructor
                || (method.kind == JavaMethodDeclarationKind::Method
                    && !method.modifiers.contains(&JavaModifier::Static));
            if instance_member {
                type_variables.extend(owner_variables.iter().cloned());
            }
            let mutable_names = method
                .body
                .as_ref()
                .map(|body| MutableLocals::collect(&body.root))
                .unwrap_or_default();
            let variable_targets = method
                .body
                .as_ref()
                .zip(candidate.identity.as_ref())
                .map(|(body, identity)| {
                    FunctionVariableTargets::analyze(&body.root, identity, &type_variables)
                })
                .unwrap_or_default();
            let value_types = LexicalValueTypes::collect(method);
            let mut binder = AnonymousConstructionBinder::new(
                candidate,
                owner.clone(),
                names,
                source_abi,
                &summaries,
                parameter_names,
                &type_variables,
                recovered_functions,
                mutable_names,
                variable_targets,
                value_types,
            );
            if let Some(body) = &mut method.body {
                binder.rewrite_body(body);
            }
            if binder.replaced {
                return true;
            }
        }
        declaration.nested.iter_mut().any(|nested| {
            let nested_owner = Self::nested_owner(
                owner,
                &nested.name,
                nested.modifiers.contains(&JavaModifier::Static),
            );
            Self::bind_construction(
                nested,
                &nested_owner,
                None,
                candidate,
                names,
                source_abi,
                parameter_names,
                recovered_functions,
            )
        })
    }

    fn nested_owner(owner: &JavaType, name: &JavaIdentifier, is_static: bool) -> JavaType {
        let JavaType::Class(owner) = owner else {
            return JavaType::Class(JavaClassType::raw(JavaClassName::simple(name.clone())));
        };
        let mut nested = owner.clone();
        if is_static {
            for segment in &mut nested.segments {
                segment.arguments.clear();
            }
        }
        nested.segments.push(JavaClassTypeSegment {
            name: name.clone(),
            arguments: Vec::new(),
        });
        JavaType::Class(nested)
    }

    fn rewrite_tree(declaration: &mut JavaTypeDeclaration, rewriter: &mut impl JavaAstRewriter) {
        Self::rewrite_members(declaration, rewriter);
        for nested in &mut declaration.nested {
            Self::rewrite_tree(nested, rewriter);
        }
    }

    fn rewrite_members(declaration: &mut JavaTypeDeclaration, rewriter: &mut impl JavaAstRewriter) {
        for field in &mut declaration.fields {
            field.initializer = field
                .initializer
                .take()
                .map(|expression| rewriter.rewrite_expression(expression));
        }
        for method in &mut declaration.methods {
            if let Some(body) = &mut method.body {
                rewriter.rewrite_body(body);
            }
        }
    }
}

struct RetainedFunctionObjectAbi;

impl RetainedFunctionObjectAbi {
    fn apply(candidate: &mut LoweredNestedType, names: &JavaTypeNameResolver) {
        if !candidate.is_function_object {
            return;
        }
        let declaration = &mut candidate.declaration;
        declaration.extends = declaration.extends.take().map(JavaType::into_raw);
        declaration.implements = std::mem::take(&mut declaration.implements)
            .into_iter()
            .map(JavaType::into_raw)
            .collect();
        let Some(contract) = candidate.function_contract.as_ref() else {
            return;
        };
        let Some(parameter_types) = contract
            .method
            .descriptor
            .parameters
            .iter()
            .map(|ty| names.resolve_type(ty).ok())
            .collect::<Option<Vec<_>>>()
        else {
            return;
        };
        let Ok(return_type) = names.resolve_type(&contract.method.descriptor.return_type) else {
            return;
        };
        for method in declaration.methods.iter_mut().filter(|method| {
            method
                .name
                .as_ref()
                .is_some_and(|name| name.to_string() == contract.method.name)
                && method.parameters.len() == parameter_types.len()
        }) {
            for (parameter, ty) in method.parameters.iter_mut().zip(&parameter_types) {
                parameter.ty = ty.clone();
            }
            method.return_type = Some(return_type.clone());
        }
    }
}

struct AnonymousConstructionCounter<'a> {
    identity: &'a JavaType,
    count: usize,
}

struct NestedTypeReferenceBinding<'a> {
    identity: &'a JavaType,
    lexical_type: &'a JavaType,
}

impl JavaAstRewriter for NestedTypeReferenceBinding<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        match expression {
            JavaExpr::New {
                enclosing,
                ty,
                target_type,
                args,
                anonymous_body,
            } if &ty == self.identity => JavaExpr::New {
                enclosing,
                ty: self.lexical_type.clone(),
                target_type,
                args,
                anonymous_body,
            },
            expression => expression,
        }
    }
}

impl JavaAstRewriter for AnonymousConstructionCounter<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        if matches!(&expression, JavaExpr::New { ty, .. } if AnonymousTypeIdentity::matches(self.identity, ty))
        {
            self.count += 1;
        }
        expression
    }
}

struct NestedConstructionCounter<'a> {
    name: &'a JavaIdentifier,
    count: usize,
}

impl JavaAstRewriter for NestedConstructionCounter<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        if matches!(
            &expression,
            JavaExpr::New {
                ty: JavaType::Class(ty),
                ..
            } if ty.name().components().last() == Some(self.name)
        ) {
            self.count += 1;
        }
        expression
    }
}

struct AnonymousTypeIdentity;

impl AnonymousTypeIdentity {
    fn matches(expected: &JavaType, actual: &JavaType) -> bool {
        match (expected, actual) {
            (JavaType::Class(expected), JavaType::Class(actual)) => {
                expected.name() == actual.name() || Self::unqualified_matches(expected, actual)
            }
            _ => expected == actual,
        }
    }

    fn unqualified_matches(qualified: &JavaClassType, unqualified: &JavaClassType) -> bool {
        let [actual] = unqualified.segments.as_slice() else {
            return false;
        };
        qualified
            .segments
            .last()
            .is_some_and(|expected| expected.name == actual.name)
    }
}

#[cfg(test)]
mod anonymous_type_identity_tests {
    use super::*;

    #[test]
    fn qualified_identity_accepts_its_unqualified_reference() {
        let identity = JavaType::Class(JavaClassType::from_source("example.Owner.Callback"));
        let reference = JavaType::Class(JavaClassType::from_source("Callback"));

        assert!(AnonymousTypeIdentity::matches(&identity, &reference));
    }

    #[test]
    fn unqualified_identity_rejects_an_external_type_with_the_same_simple_name() {
        let identity = JavaType::Class(JavaClassType::from_source("b"));
        let external = JavaType::Class(JavaClassType::from_source("example.external.b"));

        assert!(!AnonymousTypeIdentity::matches(&identity, &external));
    }
}

struct RecoveredAnonymousTypeBinding<'a> {
    identity: &'a JavaType,
    replacement: &'a JavaType,
}

impl RecoveredAnonymousTypeBinding<'_> {
    fn ty(&self, ty: JavaType) -> JavaType {
        if AnonymousTypeIdentity::matches(self.identity, &ty) {
            return self.replacement.clone();
        }
        match ty {
            JavaType::Array(element) => JavaType::Array(Box::new(self.ty(*element))),
            JavaType::Class(mut class) => {
                for argument in class
                    .segments
                    .iter_mut()
                    .flat_map(|segment| &mut segment.arguments)
                {
                    *argument = match std::mem::replace(argument, JavaTypeArgument::Any) {
                        JavaTypeArgument::Any => JavaTypeArgument::Any,
                        JavaTypeArgument::Exact(value) => JavaTypeArgument::Exact(self.ty(value)),
                        JavaTypeArgument::Extends(value) => {
                            JavaTypeArgument::Extends(self.ty(value))
                        }
                        JavaTypeArgument::Super(value) => JavaTypeArgument::Super(self.ty(value)),
                    };
                }
                JavaType::Class(class)
            }
            JavaType::Primitive(_) | JavaType::Variable(_) => ty,
        }
    }
}

impl JavaAstRewriter for RecoveredAnonymousTypeBinding<'_> {
    fn finish_statement(&mut self, statement: JavaStmt) -> JavaStmt {
        match statement {
            JavaStmt::Variable { ty, name, value } => JavaStmt::Variable {
                ty: self.ty(ty),
                name,
                value,
            },
            JavaStmt::ForEach {
                label,
                ty,
                variable,
                iterable,
                body,
            } => JavaStmt::ForEach {
                label,
                ty: self.ty(ty),
                variable,
                iterable,
                body,
            },
            statement => statement,
        }
    }

    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        match expression {
            JavaExpr::Call {
                receiver,
                owner,
                type_arguments,
                method,
                args,
            } => JavaExpr::Call {
                receiver,
                owner: owner.map(|owner| self.ty(owner)),
                type_arguments: type_arguments
                    .into_iter()
                    .map(|argument| self.ty(argument))
                    .collect(),
                method,
                args,
            },
            JavaExpr::StaticField { owner, name } => JavaExpr::StaticField {
                owner: self.ty(owner),
                name,
            },
            JavaExpr::New {
                enclosing,
                ty,
                target_type,
                args,
                anonymous_body,
            } => JavaExpr::New {
                enclosing,
                ty: self.ty(ty),
                target_type: target_type.map(|target| self.ty(target)),
                args,
                anonymous_body,
            },
            JavaExpr::NewArray {
                element_type,
                dimensions,
                initializer,
            } => JavaExpr::NewArray {
                element_type: self.ty(element_type),
                dimensions,
                initializer,
            },
            JavaExpr::Cast { ty, value } => JavaExpr::Cast {
                ty: self.ty(ty),
                value,
            },
            JavaExpr::InstanceOf { value, ty } => JavaExpr::InstanceOf {
                value,
                ty: self.ty(ty),
            },
            JavaExpr::ClassLiteral(ty) => JavaExpr::ClassLiteral(self.ty(ty)),
            expression => expression,
        }
    }
}

struct FunctionParameterNames {
    scope: JavaNameScope,
}

impl FunctionParameterNames {
    fn new() -> Self {
        Self {
            scope: JavaNameScope::default(),
        }
    }

    fn reserve_declaration(&mut self, declaration: &mut JavaTypeDeclaration) {
        for method in &declaration.methods {
            for parameter in &method.parameters {
                self.scope.reserve(parameter.name.clone());
            }
        }
        AnonymousClassRecovery::rewrite_members(
            declaration,
            &mut LexicalNameInventory {
                scope: &mut self.scope,
            },
        );
        for nested in &mut declaration.nested {
            self.reserve_declaration(nested);
        }
    }

    fn allocate(&mut self, arity: usize) -> Vec<JavaIdentifier> {
        (0..arity)
            .map(|index| {
                let preferred = match (arity, index) {
                    (1, _) => "value".to_string(),
                    (2, 0) => "left".to_string(),
                    (2, _) => "right".to_string(),
                    (_, index) => format!("argument{}", index + 1),
                };
                self.scope.claim(JavaIdentifier::from_dex(&preferred))
            })
            .collect()
    }
}

struct LexicalNameInventory<'a> {
    scope: &'a mut JavaNameScope,
}

impl JavaAstRewriter for LexicalNameInventory<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        match &expression {
            JavaExpr::Name(name) => {
                self.scope.reserve(name.clone());
            }
            JavaExpr::Lambda { parameters, .. } => {
                for parameter in parameters {
                    self.scope.reserve(parameter.clone());
                }
            }
            _ => {}
        }
        expression
    }

    fn finish_statement(&mut self, statement: JavaStmt) -> JavaStmt {
        match &statement {
            JavaStmt::Variable { name, .. } => {
                self.scope.reserve(name.clone());
            }
            JavaStmt::ForEach { variable, .. } => {
                self.scope.reserve(variable.clone());
            }
            JavaStmt::Try { catches, .. } => {
                for catch in catches {
                    self.scope.reserve(catch.variable.clone());
                }
            }
            _ => {}
        }
        statement
    }
}

struct AnonymousConstructionBinder<'a> {
    candidate: &'a LoweredNestedType,
    owner: JavaType,
    names: &'a JavaTypeNameResolver,
    source_abi: &'a JavaSourceAbi,
    summaries: &'a [FunctionSummary],
    parameter_names: &'a mut FunctionParameterNames,
    type_variables: &'a BTreeSet<JavaIdentifier>,
    recovered_functions: &'a mut BTreeSet<RecoveredFunction>,
    mutable_names: BTreeSet<JavaIdentifier>,
    variable_targets: BTreeMap<JavaIdentifier, JavaType>,
    value_types: BTreeMap<JavaIdentifier, LexicalValueType>,
    replaced: bool,
    conversion_open: bool,
    functional_type: Option<JavaType>,
}

impl<'a> AnonymousConstructionBinder<'a> {
    fn new(
        candidate: &'a LoweredNestedType,
        owner: JavaType,
        names: &'a JavaTypeNameResolver,
        source_abi: &'a JavaSourceAbi,
        summaries: &'a [FunctionSummary],
        parameter_names: &'a mut FunctionParameterNames,
        type_variables: &'a BTreeSet<JavaIdentifier>,
        recovered_functions: &'a mut BTreeSet<RecoveredFunction>,
        mutable_names: BTreeSet<JavaIdentifier>,
        variable_targets: BTreeMap<JavaIdentifier, JavaType>,
        value_types: BTreeMap<JavaIdentifier, LexicalValueType>,
    ) -> Self {
        Self {
            candidate,
            owner,
            names,
            source_abi,
            summaries,
            parameter_names,
            type_variables,
            recovered_functions,
            mutable_names,
            variable_targets,
            value_types,
            replaced: false,
            conversion_open: false,
            functional_type: None,
        }
    }
}

impl JavaAstRewriter for AnonymousConstructionBinder<'_> {
    fn finish_statement(&mut self, statement: JavaStmt) -> JavaStmt {
        let statement = match statement {
            JavaStmt::Variable {
                ty,
                name,
                value: Some(value),
            } if (self
                .candidate
                .identity
                .as_ref()
                .is_some_and(|identity| AnonymousTypeIdentity::matches(identity, &ty))
                || self.variable_targets.contains_key(&name))
                && self.functional_type.is_some() =>
            {
                let functional = self.functional_type.clone().unwrap_or(ty.clone());
                let target = self
                    .variable_targets
                    .get(&name)
                    .map(|target| FunctionTargetContract::reconcile(&functional, target))
                    .unwrap_or(functional);
                return JavaStmt::Variable {
                    ty: target.clone(),
                    name,
                    value: Some(Self::retarget_function(value, &target)),
                };
            }
            statement => statement,
        };
        let JavaStmt::Variable {
            ty,
            name,
            value:
                Some(JavaExpr::New {
                    enclosing,
                    ty: allocation_type,
                    target_type,
                    args,
                    anonymous_body,
                }),
        } = statement
        else {
            return statement;
        };
        let variable_type = if self
            .candidate
            .identity
            .as_ref()
            .is_some_and(|identity| AnonymousTypeIdentity::matches(identity, &ty))
            && anonymous_body.is_some()
        {
            allocation_type.clone()
        } else {
            ty
        };
        JavaStmt::Variable {
            ty: variable_type,
            name,
            value: Some(JavaExpr::New {
                enclosing,
                ty: allocation_type,
                target_type,
                args,
                anonymous_body,
            }),
        }
    }

    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        if self.replaced {
            if self.conversion_open {
                let JavaExpr::Cast { ty, value } = expression else {
                    self.conversion_open = false;
                    return expression;
                };
                let functional = self
                    .functional_type
                    .clone()
                    .expect("a recovered function has a functional type");
                let target = FunctionTargetContract::reconcile(&functional, &ty);
                let value = match *value {
                    JavaExpr::Cast { ty, value } if ty == target => value,
                    value => Box::new(value),
                };
                return JavaExpr::Cast { ty: target, value };
            }
            return expression;
        }
        let JavaExpr::New {
            enclosing,
            ty,
            target_type,
            args,
            anonymous_body: None,
        } = expression
        else {
            return expression;
        };
        if !self
            .candidate
            .identity
            .as_ref()
            .is_some_and(|identity| AnonymousTypeIdentity::matches(identity, &ty))
        {
            return JavaExpr::New {
                enclosing,
                ty,
                target_type,
                args,
                anonymous_body: None,
            };
        }
        let arguments = args
            .iter()
            .cloned()
            .map(|argument| match argument {
                JavaExpr::This => JavaExpr::QualifiedThis(self.owner.clone()),
                argument => argument,
            })
            .collect();
        let contextual_target = target_type.as_ref();
        let Some(mut instance) = AnonymousInstance::recover(
            self.candidate,
            arguments,
            contextual_target,
            &self.mutable_names,
            &self.value_types,
        ) else {
            return JavaExpr::New {
                enclosing,
                ty,
                target_type,
                args,
                anonymous_body: None,
            };
        };
        let target = contextual_target
            .filter(|target| FunctionTargetContract::well_formed(target))
            .map(|contextual| {
                let resolved = FunctionTargetContract::reconcile(&instance.base, contextual);
                let inherited = &resolved == contextual;
                (resolved, inherited)
            });
        let base = target
            .as_ref()
            .map(|(target, _)| target.clone())
            .unwrap_or_else(|| instance.base.clone());
        AnonymousMethodContracts::apply(
            &base,
            &mut instance.body,
            self.names,
            self.source_abi,
            self.type_variables,
        );
        if self.candidate.is_function_object {
            if let Some(mut expression) = FunctionExpression::recover(
                &instance.body,
                self.summaries,
                self.parameter_names,
                self.recovered_functions,
            ) {
                let mut explicit_target = FunctionTargetContract::has_type_arguments(&base)
                    && (contextual_target.is_none()
                        || target.as_ref().is_some_and(|(_, inherited)| !inherited));
                explicit_target |= matches!(expression, JavaExpr::BlockLambda { .. })
                    && contextual_target.is_none();
                if let Some(contract) = &self.candidate.function_contract {
                    expression = contract.adapt_expression(
                        &base,
                        expression,
                        self.names,
                        self.source_abi,
                        self.type_variables,
                        self.parameter_names,
                    );
                    explicit_target |= target.is_none()
                        && contract.requires_explicit_target(
                            &base,
                            self.names,
                            self.source_abi,
                            self.type_variables,
                        );
                }
                if explicit_target {
                    expression = JavaExpr::Cast {
                        ty: base.clone(),
                        value: Box::new(expression),
                    };
                }
                self.functional_type = Some(base);
                self.replaced = true;
                self.conversion_open = true;
                return expression;
            }
        }
        if let (Some(contract), Some((target, _))) =
            (&self.candidate.function_contract, target.as_ref())
        {
            contract.specialize(
                target,
                &mut instance.body,
                self.names,
                self.source_abi,
                self.type_variables,
            );
        }
        self.functional_type = Some(base.clone());
        self.replaced = true;
        self.conversion_open = true;
        JavaExpr::New {
            enclosing,
            ty: base,
            target_type: None,
            args: instance.super_arguments,
            anonymous_body: Some(Box::new(instance.body)),
        }
    }
}

impl AnonymousConstructionBinder<'_> {
    fn retarget_function(expression: JavaExpr, target: &JavaType) -> JavaExpr {
        match expression {
            JavaExpr::Cast { ty, value } if FunctionTargetContract::compatible(&ty, target) => {
                JavaExpr::Cast {
                    ty: target.clone(),
                    value,
                }
            }
            expression => expression,
        }
    }
}

struct FunctionVariableTargets<'a> {
    identity: &'a JavaType,
    type_variables: &'a BTreeSet<JavaIdentifier>,
    allocations: BTreeSet<JavaIdentifier>,
    targets: BTreeMap<JavaIdentifier, JavaType>,
}

impl<'a> FunctionVariableTargets<'a> {
    fn analyze(
        root: &JavaStmt,
        identity: &'a JavaType,
        type_variables: &'a BTreeSet<JavaIdentifier>,
    ) -> BTreeMap<JavaIdentifier, JavaType> {
        let mut analysis = Self {
            identity,
            type_variables,
            allocations: BTreeSet::new(),
            targets: BTreeMap::new(),
        };
        analysis.rewrite_statement(root.clone());
        analysis
            .targets
            .retain(|name, _| analysis.allocations.contains(name));
        analysis.targets
    }

    fn allocates_identity(&self, expression: &JavaExpr) -> bool {
        matches!(
            FunctionExpression::without_casts(expression),
            JavaExpr::New { ty, .. } if AnonymousTypeIdentity::matches(self.identity, ty)
        )
    }
}

impl JavaAstRewriter for FunctionVariableTargets<'_> {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        if let JavaExpr::Cast { ty, value } = &expression {
            if FunctionTargetContract::well_formed(ty)
                && FunctionTargetContract::valid_in_scope(ty, self.type_variables)
            {
                if let JavaExpr::Name(name) = FunctionExpression::without_casts(value) {
                    self.targets
                        .entry(name.clone())
                        .and_modify(|current| {
                            *current = FunctionTargetContract::reconcile(current, ty)
                        })
                        .or_insert_with(|| ty.clone());
                }
            }
        }
        expression
    }

    fn finish_statement(&mut self, statement: JavaStmt) -> JavaStmt {
        if let JavaStmt::Variable {
            name,
            value: Some(value),
            ..
        } = &statement
        {
            if self.allocates_identity(value) {
                self.allocations.insert(name.clone());
            }
        }
        statement
    }
}

struct AnonymousMethodContracts;

impl AnonymousMethodContracts {
    fn apply(
        base: &JavaType,
        body: &mut JavaAnonymousClassBody,
        names: &JavaTypeNameResolver,
        source_abi: &JavaSourceAbi,
        type_variables: &BTreeSet<JavaIdentifier>,
    ) {
        let Some(base_signature) = names.source_signature(base) else {
            return;
        };
        let owner = base_signature.erased();
        for method in &mut body.methods {
            let Some(name) = method.name.as_ref() else {
                continue;
            };
            let Some(parameters) = method
                .parameters
                .iter()
                .map(|parameter| names.source_signature(&parameter.ty).map(|ty| ty.erased()))
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            let Some(return_type) = method
                .return_type
                .as_ref()
                .and_then(|ty| names.source_signature(ty))
                .map(|ty| ty.erased())
            else {
                continue;
            };
            let reference = crate::ir::MethodReference {
                owner: owner.clone(),
                name: name.to_string(),
                descriptor: crate::ir::MethodDescriptor {
                    parameters,
                    return_type,
                },
            };
            let Some(signature) =
                source_abi.inherited_method_signature(&base_signature, &reference)
            else {
                continue;
            };
            let Some(parameter_types) = signature
                .parameter_types
                .iter()
                .map(|ty| names.resolve_generic_type(ty).ok())
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            let Ok(return_type) = names.resolve_generic_type(&signature.return_type) else {
                continue;
            };
            if parameter_types.len() != method.parameters.len()
                || !parameter_types
                    .iter()
                    .chain(std::iter::once(&return_type))
                    .all(|ty| FunctionTargetContract::valid_in_scope(ty, type_variables))
            {
                continue;
            }
            for (parameter, ty) in method.parameters.iter_mut().zip(parameter_types) {
                parameter.ty = ty;
            }
            let previous_return_type = method.return_type.replace(return_type.clone());
            if previous_return_type.as_ref() != Some(&return_type) {
                if let Some(body) = &mut method.body {
                    ReturnTypeAdapter {
                        expected: return_type,
                    }
                    .rewrite_body(body);
                }
            }
        }
    }
}

struct FunctionSummary {
    owner: JavaType,
    owner_name: JavaIdentifier,
    name: JavaIdentifier,
    parameters: Vec<JavaIdentifier>,
    parameter_types: Vec<JavaType>,
    expression: Option<JavaExpr>,
    body: JavaStmt,
    dispatch: FunctionDispatch,
    compiler_generated: bool,
}

#[derive(Clone, Copy)]
enum FunctionDispatch {
    Static,
    Instance,
}

struct FunctionReceiver;

impl FunctionReceiver {
    fn normalize(receiver: &JavaExpr, owner: &JavaType) -> JavaExpr {
        match receiver {
            JavaExpr::Cast { ty, value }
                if ty == owner
                    && matches!(value.as_ref(), JavaExpr::QualifiedThis(qualified) if qualified == owner) =>
            {
                value.as_ref().clone()
            }
            receiver => receiver.clone(),
        }
    }
}

impl FunctionSummary {
    fn key(&self) -> RecoveredFunction {
        RecoveredFunction {
            owner: self.owner_name.clone(),
            name: self.name.clone(),
            arity: self.parameters.len(),
        }
    }

    fn collect(declaration: &JavaTypeDeclaration, owner: &JavaType) -> Vec<Self> {
        declaration
            .methods
            .iter()
            .filter(|method| {
                method.compiler_generated && method.kind == JavaMethodDeclarationKind::Method
            })
            .filter_map(|method| {
                let body = method.body.as_ref()?.root.clone();
                Some(Self {
                    owner: owner.clone(),
                    owner_name: declaration.name.clone(),
                    name: method.name.clone()?,
                    parameters: method
                        .parameters
                        .iter()
                        .map(|parameter| parameter.name.clone())
                        .collect(),
                    parameter_types: method
                        .parameters
                        .iter()
                        .map(|parameter| parameter.ty.clone())
                        .collect(),
                    expression: FunctionExpression::summary_expression(method),
                    body,
                    dispatch: if method.modifiers.contains(&JavaModifier::Static) {
                        FunctionDispatch::Static
                    } else {
                        FunctionDispatch::Instance
                    },
                    compiler_generated: method.compiler_generated,
                })
            })
            .collect()
    }

    fn expand(
        &self,
        expression: &JavaExpr,
        recovered: &mut BTreeSet<RecoveredFunction>,
    ) -> Option<JavaExpr> {
        let site = FunctionCallSite::analyze(expression);
        let implementation = self.expression.clone()?;
        let result = self.bind(site.call)?.expression(implementation);
        recovered.insert(self.key());
        Some(site.rebuild(result))
    }

    fn expand_body(
        &self,
        expression: &JavaExpr,
        recovered: &mut BTreeSet<RecoveredFunction>,
    ) -> Option<JavaStmt> {
        let site = FunctionCallSite::analyze(expression);
        let result = self.bind(site.call)?.statement(self.body.clone());
        recovered.insert(self.key());
        Some(site.rebuild_returns(result))
    }

    fn bind(&self, expression: &JavaExpr) -> Option<FunctionCallBinding<'_>> {
        let JavaExpr::Call {
            receiver,
            owner,
            method,
            args,
            ..
        } = expression
        else {
            return None;
        };
        if method != &self.name || args.len() != self.parameters.len() {
            return None;
        }
        let receiver = match self.dispatch {
            FunctionDispatch::Static
                if receiver.is_none() && owner.as_ref() == Some(&self.owner) =>
            {
                None
            }
            FunctionDispatch::Instance
                if receiver.is_some()
                    && owner
                        .as_ref()
                        .map(|owner| owner == &self.owner)
                        .unwrap_or(true) =>
            {
                receiver.as_deref()
            }
            FunctionDispatch::Static | FunctionDispatch::Instance => return None,
        };
        let receiver = receiver.map(|receiver| FunctionReceiver::normalize(receiver, &self.owner));
        let values: BTreeMap<_, _> =
            self.parameters
                .iter()
                .cloned()
                .zip(args.iter().cloned().zip(&self.parameter_types).map(
                    |(argument, parameter)| {
                        FunctionArgument::remove_transport_cast(argument, parameter)
                    },
                ))
                .collect();
        Some(FunctionCallBinding {
            owner: &self.owner,
            receiver,
            values,
        })
    }
}

struct FunctionCallBinding<'a> {
    owner: &'a JavaType,
    receiver: Option<JavaExpr>,
    values: BTreeMap<JavaIdentifier, JavaExpr>,
}

impl FunctionCallBinding<'_> {
    fn expression(&self, expression: JavaExpr) -> JavaExpr {
        self.rewriter().rewrite_expression(expression)
    }

    fn statement(&self, statement: JavaStmt) -> JavaStmt {
        self.rewriter().rewrite_statement(statement)
    }

    fn rewriter(&self) -> FunctionBinding<'_> {
        FunctionBinding {
            owner: self.owner,
            receiver: self.receiver.as_ref(),
            parameters: ParameterSubstitution {
                values: &self.values,
            },
        }
    }
}

impl FunctionSummary {
    fn is_expression_body(&self) -> bool {
        self.expression.is_some()
    }

    fn is_adapter_for(&self, expression: &JavaExpr, function: &JavaMethodDeclaration) -> bool {
        let site = FunctionCallSite::analyze(expression);
        if self.bind(site.call).is_none() {
            return false;
        }
        self.compiler_generated
            || !FunctionExpression::forwards_parameters(
                FunctionExpression::call_arguments(site.call),
                function,
            )
            || self.constructs_value()
    }

    fn constructs_value(&self) -> bool {
        let mut expression = self.expression.as_ref();
        while let Some(JavaExpr::Cast { value, .. }) = expression {
            expression = Some(value);
        }
        matches!(expression, Some(JavaExpr::New { .. }))
    }
}

struct FunctionCallSite<'a> {
    call: &'a JavaExpr,
    conversions: Vec<JavaType>,
}

impl<'a> FunctionCallSite<'a> {
    fn analyze(mut expression: &'a JavaExpr) -> Self {
        let mut conversions = Vec::new();
        while let JavaExpr::Cast { ty, value } = expression {
            conversions.push(ty.clone());
            expression = value;
        }
        Self {
            call: expression,
            conversions,
        }
    }

    fn rebuild(self, mut expression: JavaExpr) -> JavaExpr {
        FunctionReturnConversion::convert(expression, &self.conversions)
    }

    fn rebuild_returns(self, statement: JavaStmt) -> JavaStmt {
        FunctionReturnConversion {
            conversions: &self.conversions,
        }
        .statement(statement)
    }
}

struct FunctionReturnConversion<'a> {
    conversions: &'a [JavaType],
}

impl FunctionReturnConversion<'_> {
    fn convert(mut expression: JavaExpr, conversions: &[JavaType]) -> JavaExpr {
        for ty in conversions.iter().rev() {
            expression = JavaExpr::Cast {
                ty: ty.clone(),
                value: Box::new(expression),
            };
        }
        expression
    }

    fn statement(&self, statement: JavaStmt) -> JavaStmt {
        match statement {
            JavaStmt::Block(statements) => JavaStmt::Block(
                statements
                    .into_iter()
                    .map(|statement| self.statement(statement))
                    .collect(),
            ),
            JavaStmt::Labeled { label, body } => JavaStmt::Labeled {
                label,
                body: Box::new(self.statement(*body)),
            },
            JavaStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => JavaStmt::If {
                condition,
                then_stmt: Box::new(self.statement(*then_stmt)),
                else_stmt: else_stmt.map(|statement| Box::new(self.statement(*statement))),
            },
            JavaStmt::While {
                label,
                condition,
                body,
            } => JavaStmt::While {
                label,
                condition,
                body: Box::new(self.statement(*body)),
            },
            JavaStmt::DoWhile {
                label,
                body,
                condition,
            } => JavaStmt::DoWhile {
                label,
                body: Box::new(self.statement(*body)),
                condition,
            },
            JavaStmt::For {
                label,
                init,
                condition,
                update,
                body,
            } => JavaStmt::For {
                label,
                init,
                condition,
                update,
                body: Box::new(self.statement(*body)),
            },
            JavaStmt::ForEach {
                label,
                ty,
                variable,
                iterable,
                body,
            } => JavaStmt::ForEach {
                label,
                ty,
                variable,
                iterable,
                body: Box::new(self.statement(*body)),
            },
            JavaStmt::Switch {
                label,
                selector,
                cases,
            } => JavaStmt::Switch {
                label,
                selector,
                cases: cases
                    .into_iter()
                    .map(|mut case| {
                        case.body = case
                            .body
                            .into_iter()
                            .map(|statement| self.statement(statement))
                            .collect();
                        case
                    })
                    .collect(),
            },
            JavaStmt::Try {
                body,
                catches,
                finally,
            } => JavaStmt::Try {
                body: Box::new(self.statement(*body)),
                catches: catches
                    .into_iter()
                    .map(|mut catch| {
                        catch.body = self.statement(catch.body);
                        catch
                    })
                    .collect(),
                finally: finally.map(|statement| Box::new(self.statement(*statement))),
            },
            JavaStmt::Synchronized { lock, body } => JavaStmt::Synchronized {
                lock,
                body: Box::new(self.statement(*body)),
            },
            JavaStmt::Return(Some(expression)) => {
                JavaStmt::Return(Some(Self::convert(expression, self.conversions)))
            }
            statement => statement,
        }
    }
}

struct FunctionArgument;

impl FunctionArgument {
    fn remove_transport_cast(mut argument: JavaExpr, parameter: &JavaType) -> JavaExpr {
        while matches!(&argument, JavaExpr::Cast { ty, .. } if ty == parameter) {
            let JavaExpr::Cast { value, .. } = argument else {
                break;
            };
            argument = *value;
        }
        argument
    }
}

pub(super) struct FunctionExpression;

impl FunctionExpression {
    fn recover(
        body: &JavaAnonymousClassBody,
        summaries: &[FunctionSummary],
        parameter_names: &mut FunctionParameterNames,
        recovered: &mut BTreeSet<RecoveredFunction>,
    ) -> Option<JavaExpr> {
        if !body.fields.is_empty() || !body.nested.is_empty() {
            return None;
        }
        let [method] = body.methods.as_slice() else {
            return None;
        };
        let expression = Self::summary_expression(method);
        let forwarding_call = expression
            .is_none()
            .then(|| VoidFunctionBody::forwarded_call(&method.body.as_ref()?.root))
            .flatten();
        if expression.is_none() && forwarding_call.is_none() {
            return None;
        }
        let parameters = parameter_names.allocate(method.parameters.len());
        let values = method
            .parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .zip(parameters.iter().cloned().map(JavaExpr::Name))
            .collect::<BTreeMap<_, _>>();
        let mut substitution = ParameterSubstitution { values: &values };
        if let Some(forwarding_call) = forwarding_call {
            if let Some(statement) = summaries
                .iter()
                .filter(|summary| summary.is_adapter_for(forwarding_call, method))
                .find_map(|summary| summary.expand_body(forwarding_call, recovered))
            {
                return Some(JavaExpr::BlockLambda {
                    parameters,
                    body: Box::new(substitution.rewrite_statement(statement)),
                });
            }
            if let Some(reference) = Self::method_reference(forwarding_call, method) {
                return Some(reference);
            }
            return Some(JavaExpr::Lambda {
                parameters,
                body: Box::new(substitution.rewrite_expression(forwarding_call.clone())),
            });
        }
        let mut expression = expression?;
        if let Some(reference) = Self::method_reference(&expression, method) {
            return Some(reference);
        }
        if let Some(expanded) = summaries
            .iter()
            .filter(|summary| summary.is_adapter_for(&expression, method))
            .find_map(|summary| summary.expand(&expression, recovered))
        {
            expression = expanded;
        }
        for _ in 0..summaries.len().max(1) {
            let Some(expanded) = summaries
                .iter()
                .filter(|summary| summary.compiler_generated && summary.is_expression_body())
                .find_map(|summary| summary.expand(&expression, recovered))
            else {
                break;
            };
            expression = expanded;
        }
        if let Some(reference) = Self::method_reference(&expression, method) {
            return Some(reference);
        }
        if let Some(statement) = summaries
            .iter()
            .filter(|summary| summary.is_adapter_for(&expression, method))
            .find_map(|summary| summary.expand_body(&expression, recovered))
        {
            return Some(JavaExpr::BlockLambda {
                parameters,
                body: Box::new(substitution.rewrite_statement(statement)),
            });
        }
        Some(JavaExpr::Lambda {
            parameters,
            body: Box::new(substitution.rewrite_expression(expression)),
        })
    }

    pub(super) fn summary_expression(method: &JavaMethodDeclaration) -> Option<JavaExpr> {
        ReturnExpression::recover(&method.body.as_ref()?.root)
    }

    fn body_expression(method: &JavaMethodDeclaration) -> Option<&JavaExpr> {
        let root = &method.body.as_ref()?.root;
        match root {
            JavaStmt::Return(Some(expression)) => Some(expression),
            JavaStmt::Block(statements) => match statements.as_slice() {
                [JavaStmt::Return(Some(expression))] => Some(expression),
                _ => None,
            },
            _ => None,
        }
    }

    fn forwards_parameters(args: &[JavaExpr], method: &JavaMethodDeclaration) -> bool {
        args.len() == method.parameters.len()
            && args
                .iter()
                .zip(&method.parameters)
                .all(|(argument, parameter)| {
                    Self::without_casts(argument) == &JavaExpr::Name(parameter.name.clone())
                })
    }

    fn call_arguments(expression: &JavaExpr) -> &[JavaExpr] {
        match expression {
            JavaExpr::Call { args, .. } => args,
            _ => &[],
        }
    }

    fn method_reference(expression: &JavaExpr, method: &JavaMethodDeclaration) -> Option<JavaExpr> {
        let JavaExpr::Call {
            receiver: Some(receiver),
            method: referenced_method,
            args,
            ..
        } = expression
        else {
            return None;
        };
        Self::forwards_parameters(args, method).then(|| JavaExpr::MethodReference {
            receiver: receiver.clone(),
            method: referenced_method.clone(),
        })
    }

    pub(super) fn without_casts(mut expression: &JavaExpr) -> &JavaExpr {
        while let JavaExpr::Cast { value, .. } = expression {
            expression = value;
        }
        expression
    }
}

struct VoidFunctionBody;

impl VoidFunctionBody {
    fn forwarded_call(root: &JavaStmt) -> Option<&JavaExpr> {
        let mut call = None;
        let mut pending = vec![root];
        while let Some(statement) = pending.pop() {
            match statement {
                JavaStmt::Empty | JavaStmt::Return(None) => {}
                JavaStmt::Block(statements) => pending.extend(statements.iter().rev()),
                JavaStmt::Expression(expression @ JavaExpr::Call { .. }) if call.is_none() => {
                    call = Some(expression);
                }
                _ => return None,
            }
        }
        call
    }
}

struct ReturnExpression;

impl ReturnExpression {
    fn recover(statement: &JavaStmt) -> Option<JavaExpr> {
        Self::with_continuation(statement, None)
    }

    fn with_continuation(statement: &JavaStmt, continuation: Option<JavaExpr>) -> Option<JavaExpr> {
        match statement {
            JavaStmt::Return(Some(expression)) => Some(expression.clone()),
            JavaStmt::Empty => continuation,
            JavaStmt::Block(statements) => {
                statements
                    .iter()
                    .rev()
                    .try_fold(continuation, |continuation, statement| {
                        Self::with_continuation(statement, continuation).map(Some)
                    })?
            }
            JavaStmt::Assign { target, op, value } if continuation.as_ref() == Some(value) => {
                Some(JavaExpr::Assignment {
                    target: Box::new(target.clone()),
                    op: *op,
                    value: Box::new(value.clone()),
                })
            }
            JavaStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => {
                let when_true = Self::with_continuation(then_stmt, continuation.clone())?;
                let when_false = match else_stmt {
                    Some(else_stmt) => Self::with_continuation(else_stmt, continuation)?,
                    None => continuation?,
                };
                Some(Self::select(condition.clone(), when_true, when_false))
            }
            JavaStmt::Variable { .. }
            | JavaStmt::Expression(_)
            | JavaStmt::Assign { .. }
            | JavaStmt::ConstructorInvocation { .. }
            | JavaStmt::While { .. }
            | JavaStmt::DoWhile { .. }
            | JavaStmt::For { .. }
            | JavaStmt::ForEach { .. }
            | JavaStmt::Switch { .. }
            | JavaStmt::Try { .. }
            | JavaStmt::Synchronized { .. }
            | JavaStmt::Break(_)
            | JavaStmt::Continue(_)
            | JavaStmt::Throw(_)
            | JavaStmt::Return(None)
            | JavaStmt::Labeled { .. } => None,
        }
    }

    fn select(condition: JavaExpr, when_true: JavaExpr, when_false: JavaExpr) -> JavaExpr {
        match (&when_true, &when_false) {
            (
                JavaExpr::Literal(crate::language::java::JavaLiteral::Boolean(true)),
                JavaExpr::Literal(crate::language::java::JavaLiteral::Boolean(false)),
            ) => condition,
            (
                JavaExpr::Literal(crate::language::java::JavaLiteral::Boolean(false)),
                JavaExpr::Literal(crate::language::java::JavaLiteral::Boolean(true)),
            ) => JavaExpr::Unary {
                op: crate::language::java::JavaUnaryOp::LogicalNot,
                operand: Box::new(condition),
            },
            _ => JavaExpr::Conditional {
                condition: Box::new(condition),
                when_true: Box::new(when_true),
                when_false: Box::new(when_false),
            },
        }
    }
}

struct FunctionTargetContract;

impl FunctionTargetContract {
    fn valid_in_scope(ty: &JavaType, type_variables: &BTreeSet<JavaIdentifier>) -> bool {
        match ty {
            JavaType::Variable(variable) => type_variables.contains(variable),
            JavaType::Array(element) => Self::valid_in_scope(element, type_variables),
            JavaType::Class(class) => class.segments.iter().all(|segment| {
                segment.arguments.iter().all(|argument| match argument {
                    JavaTypeArgument::Any => true,
                    JavaTypeArgument::Exact(value)
                    | JavaTypeArgument::Extends(value)
                    | JavaTypeArgument::Super(value) => Self::valid_in_scope(value, type_variables),
                })
            }),
            JavaType::Primitive(_) => true,
        }
    }

    fn reconcile(declared: &JavaType, contextual: &JavaType) -> JavaType {
        if !Self::well_formed(contextual) || !Self::compatible(declared, contextual) {
            return declared.clone();
        }
        // A contextual target may complete erased portions of a function
        // object's declared signature, but it must not replace equally
        // specific declaration evidence with a circular use-site inference.
        if Self::information(contextual) > Self::information(declared) {
            contextual.clone()
        } else {
            declared.clone()
        }
    }

    fn well_formed(ty: &JavaType) -> bool {
        match ty {
            JavaType::Primitive(_) => false,
            JavaType::Variable(_) => true,
            JavaType::Array(_) => true,
            JavaType::Class(class) => class.segments.iter().all(|segment| {
                segment.arguments.iter().all(|argument| match argument {
                    JavaTypeArgument::Any => true,
                    JavaTypeArgument::Exact(value)
                    | JavaTypeArgument::Extends(value)
                    | JavaTypeArgument::Super(value) => Self::well_formed(value),
                })
            }),
        }
    }

    fn compatible(left: &JavaType, right: &JavaType) -> bool {
        match (left, right) {
            (JavaType::Variable(_), _) | (_, JavaType::Variable(_)) => true,
            (JavaType::Array(left), JavaType::Array(right)) => Self::compatible(left, right),
            (JavaType::Class(left), JavaType::Class(right)) => {
                left.name() == right.name() && left.segments.len() == right.segments.len()
            }
            (JavaType::Primitive(left), JavaType::Primitive(right)) => left == right,
            _ => false,
        }
    }

    fn information(ty: &JavaType) -> usize {
        match ty {
            JavaType::Primitive(_) => 0,
            JavaType::Variable(_) => 2,
            JavaType::Array(element) => 1 + Self::information(element),
            JavaType::Class(class) => {
                1 + class
                    .segments
                    .iter()
                    .flat_map(|segment| &segment.arguments)
                    .map(|argument| match argument {
                        JavaTypeArgument::Any => 0,
                        JavaTypeArgument::Exact(value) => 2 + Self::information(value),
                        JavaTypeArgument::Extends(value) | JavaTypeArgument::Super(value) => {
                            1 + Self::information(value)
                        }
                    })
                    .sum::<usize>()
            }
        }
    }

    fn has_type_arguments(ty: &JavaType) -> bool {
        match ty {
            JavaType::Class(class) => class
                .segments
                .iter()
                .any(|segment| !segment.arguments.is_empty()),
            JavaType::Array(element) => Self::has_type_arguments(element),
            JavaType::Primitive(_) | JavaType::Variable(_) => false,
        }
    }
}

struct AnonymousInstance {
    base: JavaType,
    super_arguments: Vec<JavaExpr>,
    body: JavaAnonymousClassBody,
}

impl AnonymousInstance {
    fn base_type(candidate: &LoweredNestedType) -> Option<JavaType> {
        if candidate.is_function_object {
            return candidate.function_type.clone();
        }
        match (
            &candidate.declaration.extends,
            candidate.declaration.implements.as_slice(),
        ) {
            (Some(base), []) | (None, [base]) => Some(base.clone()),
            _ => None,
        }
    }

    fn recover(
        candidate: &LoweredNestedType,
        arguments: Vec<JavaExpr>,
        _target: Option<&JavaType>,
        mutable_names: &BTreeSet<JavaIdentifier>,
        value_types: &BTreeMap<JavaIdentifier, LexicalValueType>,
    ) -> Option<Self> {
        let declaration = &candidate.declaration;
        if candidate.is_anonymous && !declaration.nested.is_empty() {
            return None;
        }
        let base = Self::base_type(candidate)?;
        let constructors = declaration
            .methods
            .iter()
            .filter(|method| {
                method.kind == JavaMethodDeclarationKind::Constructor
                    && method.parameters.len() == arguments.len()
            })
            .collect::<Vec<_>>();
        let constructor = match constructors.as_slice() {
            [constructor] => Some(*constructor),
            [] if arguments.is_empty() => None,
            _ => return None,
        };

        let mut captures = BTreeMap::new();
        let mut super_arguments = Vec::new();
        let mut initialized_fields = Vec::new();
        if let Some(constructor) = constructor {
            let parameters = constructor
                .parameters
                .iter()
                .zip(arguments)
                .map(|(parameter, argument)| {
                    (
                        parameter.name.clone(),
                        FunctionArgument::remove_transport_cast(argument, &parameter.ty),
                    )
                })
                .collect::<BTreeMap<_, _>>();
            let statements = match &constructor.body.as_ref()?.root {
                JavaStmt::Block(statements) => statements.as_slice(),
                statement => std::slice::from_ref(statement),
            };
            let mut super_invocations = 0usize;
            for statement in statements {
                match statement {
                    JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        args,
                    } => {
                        super_invocations += 1;
                        let mut substitution = ParameterSubstitution {
                            values: &parameters,
                        };
                        super_arguments = args
                            .iter()
                            .cloned()
                            .map(|argument| substitution.rewrite_expression(argument))
                            .collect();
                    }
                    JavaStmt::Assign {
                        target: JavaExpr::Field { owner, name: field },
                        op: JavaAssignOp::Assign,
                        value: JavaExpr::Name(parameter),
                    } if matches!(owner.as_ref(), JavaExpr::This)
                        && candidate.synthetic_final_fields.contains(field) =>
                    {
                        let value = parameters.get(parameter)?.clone();
                        captures.insert(field.clone(), value);
                    }
                    JavaStmt::Assign {
                        target: JavaExpr::Field { owner, name: field },
                        op: JavaAssignOp::Assign,
                        value,
                    } if matches!(owner.as_ref(), JavaExpr::This)
                        && declaration.fields.iter().any(|declaration| {
                            &declaration.name == field
                                && !declaration.modifiers.contains(&JavaModifier::Static)
                                && declaration.initializer.is_none()
                        }) =>
                    {
                        if initialized_fields
                            .iter()
                            .any(|(initialized, _)| initialized == field)
                        {
                            return None;
                        }
                        let mut substitution = ParameterSubstitution {
                            values: &parameters,
                        };
                        initialized_fields.push((
                            field.clone(),
                            substitution.rewrite_expression(value.clone()),
                        ));
                    }
                    JavaStmt::Empty => {}
                    _ => return None,
                }
            }
            if super_invocations > 1 || captures.len() != candidate.synthetic_final_fields.len() {
                return None;
            }
            if captures
                .values()
                .any(|value| !CaptureValue::stable(value, mutable_names))
            {
                return None;
            }
        }

        let initialized_names = initialized_fields
            .iter()
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();
        let mut fields = declaration
            .fields
            .iter()
            .filter(|field| {
                !captures.contains_key(&field.name)
                    && !initialized_names.contains(&field.name)
                    && field.initializer.is_some()
            })
            .cloned()
            .collect::<Vec<_>>();
        fields.extend(
            initialized_fields
                .into_iter()
                .filter_map(|(name, initializer)| {
                    let mut field = declaration
                        .fields
                        .iter()
                        .find(|field| field.name == name)?
                        .clone();
                    field.initializer = Some(initializer);
                    Some(field)
                }),
        );
        fields.extend(
            declaration
                .fields
                .iter()
                .filter(|field| {
                    !captures.contains_key(&field.name)
                        && !initialized_names.contains(&field.name)
                        && field.initializer.is_none()
                })
                .cloned(),
        );
        let mut body = JavaAnonymousClassBody {
            fields,
            methods: declaration
                .methods
                .iter()
                .filter(|method| method.kind != JavaMethodDeclarationKind::Constructor)
                .cloned()
                .collect(),
            nested: declaration.nested.clone(),
        };
        CaptureSubstitution {
            values: captures,
            identity: candidate.identity.as_ref(),
            value_types,
        }
        .rewrite_anonymous_body(&mut body);
        if let Some(identity) = candidate.identity.as_ref() {
            AnonymousIdentitySubstitution { identity }.rewrite_anonymous_body(&mut body);
        }
        Some(Self {
            base,
            super_arguments,
            body,
        })
    }
}

struct CaptureValue;

impl CaptureValue {
    fn stable(value: &JavaExpr, mutable_names: &BTreeSet<JavaIdentifier>) -> bool {
        match value {
            JavaExpr::Name(name) => !mutable_names.contains(name),
            JavaExpr::This
            | JavaExpr::QualifiedThis(_)
            | JavaExpr::Literal(_)
            | JavaExpr::ClassLiteral(_) => true,
            _ => false,
        }
    }
}

#[derive(Default)]
struct LexicalValueTypes {
    types: BTreeMap<JavaIdentifier, LexicalValueType>,
    conflicts: BTreeSet<JavaIdentifier>,
}

struct LexicalValueType {
    ty: JavaType,
    authoritative: bool,
}

impl LexicalValueTypes {
    fn collect(method: &JavaMethodDeclaration) -> BTreeMap<JavaIdentifier, LexicalValueType> {
        let mut values = Self::default();
        for parameter in &method.parameters {
            values.record(parameter.name.clone(), parameter.ty.clone(), true);
        }
        if let Some(body) = &method.body {
            values.rewrite_statement(body.root.clone());
        }
        values.types
    }

    fn record(&mut self, name: JavaIdentifier, ty: JavaType, authoritative: bool) {
        if self.conflicts.contains(&name) {
            return;
        }
        match self.types.get(&name) {
            Some(current) if current.ty != ty => {
                self.types.remove(&name);
                self.conflicts.insert(name);
            }
            Some(_) => {}
            None => {
                self.types
                    .insert(name, LexicalValueType { ty, authoritative });
            }
        }
    }
}

impl JavaAstRewriter for LexicalValueTypes {
    fn finish_statement(&mut self, statement: JavaStmt) -> JavaStmt {
        match &statement {
            JavaStmt::Variable { ty, name, .. } => self.record(name.clone(), ty.clone(), false),
            JavaStmt::ForEach { ty, variable, .. } => {
                self.record(variable.clone(), ty.clone(), false);
            }
            _ => {}
        }
        statement
    }
}

#[derive(Default)]
struct MutableLocals {
    names: BTreeSet<JavaIdentifier>,
}

impl MutableLocals {
    fn collect(root: &JavaStmt) -> BTreeSet<JavaIdentifier> {
        let mut collector = Self::default();
        collector.rewrite_statement(root.clone());
        collector.names
    }
}

impl JavaAstRewriter for MutableLocals {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        if let JavaExpr::Update { target, .. } = &expression {
            if let JavaExpr::Name(name) = target.as_ref() {
                self.names.insert(name.clone());
            }
        }
        expression
    }

    fn finish_statement(&mut self, statement: JavaStmt) -> JavaStmt {
        if let JavaStmt::Assign {
            target: JavaExpr::Name(name),
            ..
        } = &statement
        {
            self.names.insert(name.clone());
        }
        statement
    }
}

struct ResolvedFunctionContract {
    parameter_types: Vec<JavaType>,
    return_type: JavaType,
}

struct FunctionParameterAdapter<'a> {
    parameters: BTreeMap<JavaIdentifier, JavaType>,
    names: &'a JavaTypeNameResolver,
    source_abi: &'a JavaSourceAbi,
}

impl<'a> FunctionParameterAdapter<'a> {
    fn new(
        parameters: &[JavaIdentifier],
        types: &[JavaType],
        names: &'a JavaTypeNameResolver,
        source_abi: &'a JavaSourceAbi,
    ) -> Self {
        Self {
            parameters: parameters
                .iter()
                .cloned()
                .zip(types.iter().cloned())
                .collect(),
            names,
            source_abi,
        }
    }

    fn erasure(&self, ty: &JavaType) -> Option<crate::ir::ArgType> {
        self.names.source_signature(ty).map(|ty| ty.erased())
    }

    fn parameter_satisfies(&self, parameter: &JavaIdentifier, target: &JavaType) -> bool {
        let Some(source) = self
            .parameters
            .get(parameter)
            .and_then(|source| self.erasure(source))
        else {
            return false;
        };
        let Some(target) = self.erasure(target) else {
            return false;
        };
        source == target || self.source_abi.is_subtype(&source, &target)
    }
}

impl JavaAstRewriter for FunctionParameterAdapter<'_> {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        match expression {
            JavaExpr::Cast { ty, value }
                if matches!(value.as_ref(), JavaExpr::Name(parameter)
                    if self.parameter_satisfies(parameter, &ty)) =>
            {
                *value
            }
            expression => expression,
        }
    }
}

struct FunctionReturnAdapter<'a> {
    return_type: &'a JavaType,
}

impl JavaAstRewriter for FunctionReturnAdapter<'_> {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_statement(&mut self, statement: JavaStmt) -> JavaStmt {
        match statement {
            JavaStmt::Return(Some(expression)) => JavaStmt::Return(Some(
                FunctionContract::adapt_return(expression, self.return_type),
            )),
            statement => statement,
        }
    }
}

impl FunctionContract {
    fn resolve(
        &self,
        target: &JavaType,
        names: &JavaTypeNameResolver,
        source_abi: &JavaSourceAbi,
        type_variables: &BTreeSet<JavaIdentifier>,
    ) -> Option<ResolvedFunctionContract> {
        let target = names.source_signature(target)?;
        let signature = source_abi.inherited_method_signature(&target, &self.method)?;
        let parameter_types = signature
            .parameter_types
            .iter()
            .map(|ty| names.resolve_generic_type(ty))
            .collect::<Result<Vec<_>, _>>()
            .ok()?;
        let return_type = names.resolve_generic_type(&signature.return_type).ok()?;
        parameter_types
            .iter()
            .chain(std::iter::once(&return_type))
            .all(|ty| FunctionTargetContract::valid_in_scope(ty, type_variables))
            .then_some(ResolvedFunctionContract {
                parameter_types,
                return_type,
            })
    }

    fn adapt_expression(
        &self,
        target: &JavaType,
        expression: JavaExpr,
        names: &JavaTypeNameResolver,
        source_abi: &JavaSourceAbi,
        type_variables: &BTreeSet<JavaIdentifier>,
        parameter_names: &mut FunctionParameterNames,
    ) -> JavaExpr {
        let Some(contract) = self.resolve(target, names, source_abi, type_variables) else {
            return expression;
        };
        match expression {
            JavaExpr::Lambda { parameters, body } => {
                let body = FunctionParameterAdapter::new(
                    &parameters,
                    &contract.parameter_types,
                    names,
                    source_abi,
                )
                .rewrite_expression(*body);
                JavaExpr::Lambda {
                    parameters,
                    body: Box::new(Self::adapt_return(body, &contract.return_type)),
                }
            }
            JavaExpr::BlockLambda { parameters, body } => {
                let body = FunctionParameterAdapter::new(
                    &parameters,
                    &contract.parameter_types,
                    names,
                    source_abi,
                )
                .rewrite_statement(*body);
                JavaExpr::BlockLambda {
                    parameters,
                    body: Box::new(
                        FunctionReturnAdapter {
                            return_type: &contract.return_type,
                        }
                        .rewrite_statement(body),
                    ),
                }
            }
            JavaExpr::MethodReference { receiver, method }
                if Self::contains_type_variable(&contract.return_type) =>
            {
                let parameters = parameter_names.allocate(contract.parameter_types.len());
                let call = JavaExpr::Call {
                    receiver: Some(receiver),
                    owner: None,
                    type_arguments: Vec::new(),
                    method,
                    args: parameters.iter().cloned().map(JavaExpr::Name).collect(),
                };
                JavaExpr::Lambda {
                    parameters,
                    body: Box::new(Self::adapt_return(call, &contract.return_type)),
                }
            }
            expression => expression,
        }
    }

    fn adapt_return(expression: JavaExpr, return_type: &JavaType) -> JavaExpr {
        match expression {
            JavaExpr::Cast { ty, value }
                if FunctionTargetContract::compatible(&ty, return_type) =>
            {
                JavaExpr::Cast {
                    ty: return_type.clone(),
                    value,
                }
            }
            expression if Self::contains_type_variable(return_type) => JavaExpr::Cast {
                ty: return_type.clone(),
                value: Box::new(expression),
            },
            expression => expression,
        }
    }

    fn requires_explicit_target(
        &self,
        target: &JavaType,
        names: &JavaTypeNameResolver,
        source_abi: &JavaSourceAbi,
        type_variables: &BTreeSet<JavaIdentifier>,
    ) -> bool {
        self.resolve(target, names, source_abi, type_variables)
            .is_some_and(|contract| {
                matches!(contract.return_type, JavaType::Primitive(_))
                    || Self::contains_type_variable(&contract.return_type)
            })
    }

    fn contains_type_variable(ty: &JavaType) -> bool {
        match ty {
            JavaType::Variable(_) => true,
            JavaType::Array(element) => Self::contains_type_variable(element),
            JavaType::Class(class) => class.segments.iter().any(|segment| {
                segment.arguments.iter().any(|argument| match argument {
                    JavaTypeArgument::Exact(ty)
                    | JavaTypeArgument::Extends(ty)
                    | JavaTypeArgument::Super(ty) => Self::contains_type_variable(ty),
                    JavaTypeArgument::Any => false,
                })
            }),
            JavaType::Primitive(_) => false,
        }
    }

    fn specialize(
        &self,
        target: &JavaType,
        body: &mut JavaAnonymousClassBody,
        names: &JavaTypeNameResolver,
        source_abi: &JavaSourceAbi,
        type_variables: &BTreeSet<JavaIdentifier>,
    ) {
        let Some(contract) = self.resolve(target, names, source_abi, type_variables) else {
            return;
        };
        if body.methods.len() != 1 {
            return;
        }
        let method = &mut body.methods[0];
        if method.parameters.len() != contract.parameter_types.len() {
            return;
        }
        let return_type = contract.return_type;
        let previous_return_type = method.return_type.clone();
        for (parameter, ty) in method.parameters.iter_mut().zip(contract.parameter_types) {
            parameter.ty = ty;
        }
        method.return_type = Some(return_type.clone());
        if previous_return_type.as_ref() != Some(&return_type) {
            if let Some(body) = &mut method.body {
                ReturnTypeAdapter {
                    expected: return_type,
                }
                .rewrite_body(body);
            }
        }
    }
}

struct AnonymousIdentitySubstitution<'a> {
    identity: &'a JavaType,
}

impl JavaAstRewriter for AnonymousIdentitySubstitution<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        match expression {
            JavaExpr::Call {
                receiver: Some(receiver),
                owner: None,
                type_arguments,
                method,
                args,
            } if matches!(receiver.as_ref(), JavaExpr::QualifiedThis(owner) if AnonymousTypeIdentity::matches(self.identity, owner)) => {
                JavaExpr::Call {
                    receiver: None,
                    owner: None,
                    type_arguments,
                    method,
                    args,
                }
            }
            JavaExpr::Field { owner, name } if matches!(owner.as_ref(), JavaExpr::QualifiedThis(identity) if AnonymousTypeIdentity::matches(self.identity, identity)) => {
                JavaExpr::Name(name)
            }
            JavaExpr::MethodReference { receiver, method } if matches!(receiver.as_ref(), JavaExpr::QualifiedThis(identity) if AnonymousTypeIdentity::matches(self.identity, identity)) => {
                JavaExpr::MethodReference {
                    receiver: Box::new(JavaExpr::This),
                    method,
                }
            }
            JavaExpr::Call {
                receiver: None,
                owner: Some(owner),
                type_arguments,
                method,
                args,
            } if &owner == self.identity => JavaExpr::Call {
                receiver: None,
                owner: None,
                type_arguments,
                method,
                args,
            },
            JavaExpr::StaticField { owner, name } if &owner == self.identity => {
                JavaExpr::Name(name)
            }
            expression => expression,
        }
    }
}

struct ReturnTypeAdapter {
    expected: JavaType,
}

impl JavaAstRewriter for ReturnTypeAdapter {
    fn finish_statement(&mut self, statement: JavaStmt) -> JavaStmt {
        let JavaStmt::Return(Some(value)) = statement else {
            return statement;
        };
        if matches!(&value, JavaExpr::Cast { ty, .. } if ty == &self.expected) {
            return JavaStmt::Return(Some(value));
        }
        JavaStmt::Return(Some(JavaExpr::Cast {
            ty: self.expected.clone(),
            value: Box::new(value),
        }))
    }
}

struct ParameterSubstitution<'a> {
    values: &'a BTreeMap<JavaIdentifier, JavaExpr>,
}

impl JavaAstRewriter for ParameterSubstitution<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        match expression {
            JavaExpr::Name(name) => self
                .values
                .get(&name)
                .cloned()
                .unwrap_or(JavaExpr::Name(name)),
            expression => expression,
        }
    }
}

struct FunctionBinding<'a> {
    owner: &'a JavaType,
    receiver: Option<&'a JavaExpr>,
    parameters: ParameterSubstitution<'a>,
}

impl JavaAstRewriter for FunctionBinding<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        match self.parameters.finish_expression(expression) {
            JavaExpr::This => self.receiver.cloned().unwrap_or(JavaExpr::This),
            JavaExpr::QualifiedThis(owner) if &owner == self.owner => self
                .receiver
                .cloned()
                .unwrap_or(JavaExpr::QualifiedThis(owner)),
            expression => expression,
        }
    }
}

struct CaptureSubstitution<'a> {
    values: BTreeMap<JavaIdentifier, JavaExpr>,
    identity: Option<&'a JavaType>,
    value_types: &'a BTreeMap<JavaIdentifier, LexicalValueType>,
}

impl JavaAstRewriter for CaptureSubstitution<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        match expression {
            JavaExpr::Cast { ty, value }
                if self.capture_type(value.as_ref()).is_some_and(|captured| {
                    captured.authoritative && Self::same_erasure(&captured.ty, &ty)
                }) =>
            {
                *value
            }
            JavaExpr::Field { owner, name }
                if matches!(owner.as_ref(), JavaExpr::This)
                    || matches!(
                        (owner.as_ref(), self.identity),
                        (JavaExpr::QualifiedThis(owner), Some(identity)) if owner == identity
                    ) =>
            {
                self.values
                    .get(&name)
                    .cloned()
                    .unwrap_or(JavaExpr::Field { owner, name })
            }
            expression => expression,
        }
    }
}

impl CaptureSubstitution<'_> {
    fn capture_type(&self, expression: &JavaExpr) -> Option<&LexicalValueType> {
        match expression {
            JavaExpr::Name(name) if self.values.values().any(|captured| captured == expression) => {
                self.value_types.get(name)
            }
            JavaExpr::Cast { value, .. } => self.capture_type(value),
            _ => None,
        }
    }

    fn same_erasure(left: &JavaType, right: &JavaType) -> bool {
        match (left, right) {
            (JavaType::Array(left), JavaType::Array(right)) => Self::same_erasure(left, right),
            (JavaType::Class(left), JavaType::Class(right)) => left.name() == right.name(),
            (JavaType::Primitive(left), JavaType::Primitive(right)) => left == right,
            (JavaType::Variable(left), JavaType::Variable(right)) => left == right,
            _ => false,
        }
    }
}
