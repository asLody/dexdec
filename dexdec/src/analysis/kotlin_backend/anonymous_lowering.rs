use std::collections::{BTreeMap, BTreeSet};

use crate::language::kotlin::{
    KotlinAnonymousClassBody, KotlinAssignOp, KotlinAstRewriter, KotlinClassName, KotlinClassType,
    KotlinClassTypeSegment, KotlinConstructorTarget, KotlinExpr, KotlinIdentifier,
    KotlinMethodDeclaration, KotlinMethodDeclarationKind, KotlinModifier, KotlinNameScope,
    KotlinStmt, KotlinType, KotlinTypeArgument, KotlinTypeDeclaration,
};

use super::kotlin_model::KotlinSourceAbi;
use super::type_names::KotlinTypeNameResolver;

#[derive(Clone)]
pub(super) struct LoweredNestedType {
    pub identity: Option<KotlinType>,
    pub lexical_type_variables: BTreeSet<KotlinIdentifier>,
    pub is_anonymous: bool,
    pub is_function_object: bool,
    pub function_type: Option<KotlinType>,
    pub function_contract: Option<FunctionContract>,
    pub synthetic_final_fields: BTreeSet<KotlinIdentifier>,
    pub liveness: NestedTypeLiveness,
    pub declaration: KotlinTypeDeclaration,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct RecoveredFunction {
    pub owner: KotlinIdentifier,
    pub name: KotlinIdentifier,
    pub arity: usize,
}

#[derive(Clone, Default)]
pub(super) struct NestedTypeLiveness {
    removable: BTreeSet<KotlinIdentifier>,
    recovered_functions: BTreeSet<RecoveredFunction>,
    children: BTreeMap<KotlinIdentifier, Self>,
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
        removable: impl IntoIterator<Item = KotlinIdentifier>,
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

    pub(super) fn rename_owner(&mut self, from: &KotlinIdentifier, to: &KotlinIdentifier) {
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
        declaration: &mut KotlinTypeDeclaration,
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
    pub removable_types: BTreeSet<KotlinIdentifier>,
    pub recovered_functions: BTreeSet<RecoveredFunction>,
}

impl EnumConstantBodyRecovery {
    pub(super) fn apply(
        declaration: &mut KotlinTypeDeclaration,
        implementations: &[Option<KotlinType>],
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
        declaration: &mut KotlinTypeDeclaration,
        owner: &KotlinType,
        mut nested: Vec<LoweredNestedType>,
        names: &KotlinTypeNameResolver,
        source_abi: &KotlinSourceAbi,
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
                        KotlinType::Class(KotlinClassType::raw(KotlinClassName::simple(
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

    fn is_empty_synthetic_type(declaration: &KotlinTypeDeclaration) -> bool {
        declaration.enum_constants.is_empty()
            && declaration.fields.is_empty()
            && declaration.properties.is_empty()
            && declaration.methods.is_empty()
            && declaration.nested.is_empty()
    }

    fn construction_count(declaration: &mut KotlinTypeDeclaration, identity: &KotlinType) -> usize {
        let mut counter = AnonymousConstructionCounter { identity, count: 0 };
        Self::rewrite_tree(declaration, &mut counter);
        counter.count
    }

    fn construction_name_count(
        declaration: &mut KotlinTypeDeclaration,
        name: &KotlinIdentifier,
    ) -> usize {
        let mut counter = NestedConstructionCounter { name, count: 0 };
        Self::rewrite_tree(declaration, &mut counter);
        counter.count
    }

    fn bind_construction(
        declaration: &mut KotlinTypeDeclaration,
        owner: &KotlinType,
        lexical_type_variables: Option<&BTreeSet<KotlinIdentifier>>,
        candidate: &LoweredNestedType,
        names: &KotlinTypeNameResolver,
        source_abi: &KotlinSourceAbi,
        parameter_names: &mut FunctionParameterNames,
        recovered_functions: &mut BTreeSet<RecoveredFunction>,
    ) -> bool {
        let summaries = FunctionSummary::collect(declaration, owner);
        let mut owner_variables = lexical_type_variables.cloned().unwrap_or_else(|| {
            names
                .source_signature(owner)
                .into_iter()
                .flat_map(|owner| source_abi.lexical_type_variables(&owner.erased()))
                .map(KotlinIdentifier::from_dex)
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
                if fields_are_static || field.modifiers.contains(&KotlinModifier::Static) {
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
            let instance_member = method.kind == KotlinMethodDeclarationKind::Constructor
                || (method.kind == KotlinMethodDeclarationKind::Method
                    && !method.modifiers.contains(&KotlinModifier::Static));
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
                nested.modifiers.contains(&KotlinModifier::Static),
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

    fn nested_owner(owner: &KotlinType, name: &KotlinIdentifier, is_static: bool) -> KotlinType {
        let KotlinType::Class(owner) = owner else {
            return KotlinType::Class(KotlinClassType::raw(KotlinClassName::simple(name.clone())));
        };
        let mut nested = owner.clone();
        if is_static {
            for segment in &mut nested.segments {
                segment.arguments.clear();
            }
        }
        nested.segments.push(KotlinClassTypeSegment {
            name: name.clone(),
            arguments: Vec::new(),
        });
        KotlinType::Class(nested)
    }

    fn rewrite_tree(
        declaration: &mut KotlinTypeDeclaration,
        rewriter: &mut impl KotlinAstRewriter,
    ) {
        Self::rewrite_members(declaration, rewriter);
        for nested in &mut declaration.nested {
            Self::rewrite_tree(nested, rewriter);
        }
    }

    fn rewrite_members(
        declaration: &mut KotlinTypeDeclaration,
        rewriter: &mut impl KotlinAstRewriter,
    ) {
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
    fn apply(candidate: &mut LoweredNestedType, names: &KotlinTypeNameResolver) {
        if !candidate.is_function_object {
            return;
        }
        let declaration = &mut candidate.declaration;
        declaration.extends = declaration.extends.take().map(KotlinType::into_raw);
        declaration.implements = std::mem::take(&mut declaration.implements)
            .into_iter()
            .map(KotlinType::into_raw)
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
    identity: &'a KotlinType,
    count: usize,
}

struct NestedTypeReferenceBinding<'a> {
    identity: &'a KotlinType,
    lexical_type: &'a KotlinType,
}

impl KotlinAstRewriter for NestedTypeReferenceBinding<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match expression {
            KotlinExpr::New {
                enclosing,
                ty,
                target_type,
                args,
                anonymous_body,
            } if &ty == self.identity => KotlinExpr::New {
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

impl KotlinAstRewriter for AnonymousConstructionCounter<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if matches!(&expression, KotlinExpr::New { ty, .. } if AnonymousTypeIdentity::matches(self.identity, ty))
        {
            self.count += 1;
        }
        expression
    }
}

struct NestedConstructionCounter<'a> {
    name: &'a KotlinIdentifier,
    count: usize,
}

impl KotlinAstRewriter for NestedConstructionCounter<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if matches!(
            &expression,
            KotlinExpr::New {
                ty: KotlinType::Class(ty),
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
    fn matches(expected: &KotlinType, actual: &KotlinType) -> bool {
        match (expected, actual) {
            (KotlinType::Class(expected), KotlinType::Class(actual)) => {
                expected.name() == actual.name()
                    || Self::unqualified_matches(expected, actual)
                    || Self::unqualified_matches(actual, expected)
            }
            _ => expected == actual,
        }
    }

    fn unqualified_matches(qualified: &KotlinClassType, unqualified: &KotlinClassType) -> bool {
        let [actual] = unqualified.segments.as_slice() else {
            return false;
        };
        qualified
            .segments
            .last()
            .is_some_and(|expected| expected.name == actual.name)
    }
}

struct RecoveredAnonymousTypeBinding<'a> {
    identity: &'a KotlinType,
    replacement: &'a KotlinType,
}

impl RecoveredAnonymousTypeBinding<'_> {
    fn ty(&self, ty: KotlinType) -> KotlinType {
        if AnonymousTypeIdentity::matches(self.identity, &ty) {
            return self.replacement.clone();
        }
        match ty {
            KotlinType::Array(element) => {
                KotlinType::Array(Box::new(element.map_type(|element| self.ty(element))))
            }
            KotlinType::Class(mut class) => {
                for argument in class
                    .segments
                    .iter_mut()
                    .flat_map(|segment| &mut segment.arguments)
                {
                    *argument = match std::mem::replace(argument, KotlinTypeArgument::Any) {
                        KotlinTypeArgument::Any => KotlinTypeArgument::Any,
                        KotlinTypeArgument::Exact(value) => {
                            KotlinTypeArgument::Exact(self.ty(value))
                        }
                        KotlinTypeArgument::Extends(value) => {
                            KotlinTypeArgument::Extends(self.ty(value))
                        }
                        KotlinTypeArgument::Super(value) => {
                            KotlinTypeArgument::Super(self.ty(value))
                        }
                    };
                }
                KotlinType::Class(class)
            }
            KotlinType::Primitive(_) | KotlinType::Variable(_) => ty,
        }
    }
}

impl KotlinAstRewriter for RecoveredAnonymousTypeBinding<'_> {
    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        match statement {
            KotlinStmt::Variable {
                binding,
                ty,
                name,
                value,
            } => KotlinStmt::Variable {
                binding,
                ty: self.ty(ty),
                name,
                value,
            },
            KotlinStmt::ForEach {
                label,
                ty,
                variable,
                iterable,
                body,
            } => KotlinStmt::ForEach {
                label,
                ty: self.ty(ty),
                variable,
                iterable,
                body,
            },
            statement => statement,
        }
    }

    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match expression {
            KotlinExpr::Call {
                receiver,
                owner,
                type_arguments,
                method,
                args,
            } => KotlinExpr::Call {
                receiver,
                owner: owner.map(|owner| self.ty(owner)),
                type_arguments: type_arguments
                    .into_iter()
                    .map(|argument| self.ty(argument))
                    .collect(),
                method,
                args,
            },
            KotlinExpr::StaticField { owner, name } => KotlinExpr::StaticField {
                owner: self.ty(owner),
                name,
            },
            KotlinExpr::New {
                enclosing,
                ty,
                target_type,
                args,
                anonymous_body,
            } => KotlinExpr::New {
                enclosing,
                ty: self.ty(ty),
                target_type: target_type.map(|target| self.ty(target)),
                args,
                anonymous_body,
            },
            KotlinExpr::NewArray {
                element_type,
                dimensions,
                initializer,
            } => KotlinExpr::NewArray {
                element_type: self.ty(element_type),
                dimensions,
                initializer,
            },
            KotlinExpr::Cast { ty, value } => KotlinExpr::Cast {
                ty: self.ty(ty),
                value,
            },
            KotlinExpr::InstanceOf { value, ty } => KotlinExpr::InstanceOf {
                value,
                ty: self.ty(ty),
            },
            KotlinExpr::ClassLiteral(ty) => KotlinExpr::ClassLiteral(self.ty(ty)),
            expression => expression,
        }
    }
}

struct FunctionParameterNames {
    scope: KotlinNameScope,
}

impl FunctionParameterNames {
    fn new() -> Self {
        Self {
            scope: KotlinNameScope::default(),
        }
    }

    fn reserve_declaration(&mut self, declaration: &mut KotlinTypeDeclaration) {
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

    fn allocate(&mut self, arity: usize) -> Vec<KotlinIdentifier> {
        (0..arity)
            .map(|index| {
                let preferred = match (arity, index) {
                    (1, _) => "value".to_string(),
                    (2, 0) => "left".to_string(),
                    (2, _) => "right".to_string(),
                    (_, index) => format!("argument{}", index + 1),
                };
                self.scope.claim(KotlinIdentifier::from_dex(&preferred))
            })
            .collect()
    }
}

struct LexicalNameInventory<'a> {
    scope: &'a mut KotlinNameScope,
}

impl KotlinAstRewriter for LexicalNameInventory<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match &expression {
            KotlinExpr::Name(name) => {
                self.scope.reserve(name.clone());
            }
            KotlinExpr::Lambda { parameters, .. } => {
                for parameter in parameters {
                    self.scope.reserve(parameter.clone());
                }
            }
            _ => {}
        }
        expression
    }

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        match &statement {
            KotlinStmt::Variable { name, .. } => {
                self.scope.reserve(name.clone());
            }
            KotlinStmt::ForEach { variable, .. } => {
                self.scope.reserve(variable.clone());
            }
            KotlinStmt::Try { catches, .. } => {
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
    owner: KotlinType,
    names: &'a KotlinTypeNameResolver,
    source_abi: &'a KotlinSourceAbi,
    summaries: &'a [FunctionSummary],
    parameter_names: &'a mut FunctionParameterNames,
    type_variables: &'a BTreeSet<KotlinIdentifier>,
    recovered_functions: &'a mut BTreeSet<RecoveredFunction>,
    mutable_names: BTreeSet<KotlinIdentifier>,
    variable_targets: BTreeMap<KotlinIdentifier, KotlinType>,
    value_types: BTreeMap<KotlinIdentifier, LexicalValueType>,
    replaced: bool,
    conversion_open: bool,
    functional_type: Option<KotlinType>,
}

impl<'a> AnonymousConstructionBinder<'a> {
    fn new(
        candidate: &'a LoweredNestedType,
        owner: KotlinType,
        names: &'a KotlinTypeNameResolver,
        source_abi: &'a KotlinSourceAbi,
        summaries: &'a [FunctionSummary],
        parameter_names: &'a mut FunctionParameterNames,
        type_variables: &'a BTreeSet<KotlinIdentifier>,
        recovered_functions: &'a mut BTreeSet<RecoveredFunction>,
        mutable_names: BTreeSet<KotlinIdentifier>,
        variable_targets: BTreeMap<KotlinIdentifier, KotlinType>,
        value_types: BTreeMap<KotlinIdentifier, LexicalValueType>,
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

impl KotlinAstRewriter for AnonymousConstructionBinder<'_> {
    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        let statement = match statement {
            KotlinStmt::Variable {
                binding,
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
                return KotlinStmt::Variable {
                    binding,
                    ty: target.clone(),
                    name,
                    value: Some(Self::retarget_function(value, &target)),
                };
            }
            statement => statement,
        };
        let KotlinStmt::Variable {
            binding,
            ty,
            name,
            value:
                Some(KotlinExpr::New {
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
        KotlinStmt::Variable {
            binding,
            ty: variable_type,
            name,
            value: Some(KotlinExpr::New {
                enclosing,
                ty: allocation_type,
                target_type,
                args,
                anonymous_body,
            }),
        }
    }

    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if self.replaced {
            if self.conversion_open {
                let KotlinExpr::Cast { ty, value } = expression else {
                    self.conversion_open = false;
                    return expression;
                };
                let functional = self
                    .functional_type
                    .clone()
                    .expect("a recovered function has a functional type");
                let target = FunctionTargetContract::reconcile(&functional, &ty);
                let value = match *value {
                    KotlinExpr::Cast { ty, value } if ty == target => value,
                    value => Box::new(value),
                };
                return KotlinExpr::Cast { ty: target, value };
            }
            return expression;
        }
        let KotlinExpr::New {
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
            return KotlinExpr::New {
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
                KotlinExpr::This => KotlinExpr::QualifiedThis(self.owner.clone()),
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
            return KotlinExpr::New {
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
                explicit_target |= matches!(expression, KotlinExpr::BlockLambda { .. })
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
                    expression = KotlinExpr::Cast {
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
        KotlinExpr::New {
            enclosing,
            ty: base,
            target_type: None,
            args: instance.super_arguments,
            anonymous_body: Some(Box::new(instance.body)),
        }
    }
}

impl AnonymousConstructionBinder<'_> {
    fn retarget_function(expression: KotlinExpr, target: &KotlinType) -> KotlinExpr {
        match expression {
            KotlinExpr::Cast { ty, value } if FunctionTargetContract::compatible(&ty, target) => {
                KotlinExpr::Cast {
                    ty: target.clone(),
                    value,
                }
            }
            expression => expression,
        }
    }
}

struct FunctionVariableTargets<'a> {
    identity: &'a KotlinType,
    type_variables: &'a BTreeSet<KotlinIdentifier>,
    allocations: BTreeSet<KotlinIdentifier>,
    targets: BTreeMap<KotlinIdentifier, KotlinType>,
}

impl<'a> FunctionVariableTargets<'a> {
    fn analyze(
        root: &KotlinStmt,
        identity: &'a KotlinType,
        type_variables: &'a BTreeSet<KotlinIdentifier>,
    ) -> BTreeMap<KotlinIdentifier, KotlinType> {
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

    fn allocates_identity(&self, expression: &KotlinExpr) -> bool {
        matches!(
            FunctionExpression::without_casts(expression),
            KotlinExpr::New { ty, .. } if AnonymousTypeIdentity::matches(self.identity, ty)
        )
    }
}

impl KotlinAstRewriter for FunctionVariableTargets<'_> {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if let KotlinExpr::Cast { ty, value } = &expression {
            if FunctionTargetContract::well_formed(ty)
                && FunctionTargetContract::valid_in_scope(ty, self.type_variables)
            {
                if let KotlinExpr::Name(name) = FunctionExpression::without_casts(value) {
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

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        if let KotlinStmt::Variable {
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
        base: &KotlinType,
        body: &mut KotlinAnonymousClassBody,
        names: &KotlinTypeNameResolver,
        source_abi: &KotlinSourceAbi,
        type_variables: &BTreeSet<KotlinIdentifier>,
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
    owner: KotlinType,
    owner_name: KotlinIdentifier,
    name: KotlinIdentifier,
    parameters: Vec<KotlinIdentifier>,
    parameter_types: Vec<KotlinType>,
    expression: Option<KotlinExpr>,
    body: KotlinStmt,
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
    fn normalize(receiver: &KotlinExpr, owner: &KotlinType) -> KotlinExpr {
        match receiver {
            KotlinExpr::Cast { ty, value }
                if ty == owner
                    && matches!(value.as_ref(), KotlinExpr::QualifiedThis(qualified) if qualified == owner) =>
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

    fn collect(declaration: &KotlinTypeDeclaration, owner: &KotlinType) -> Vec<Self> {
        declaration
            .methods
            .iter()
            .filter(|method| {
                method.compiler_generated && method.kind == KotlinMethodDeclarationKind::Method
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
                    dispatch: if method.modifiers.contains(&KotlinModifier::Static) {
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
        expression: &KotlinExpr,
        recovered: &mut BTreeSet<RecoveredFunction>,
    ) -> Option<KotlinExpr> {
        let site = FunctionCallSite::analyze(expression);
        let implementation = self.expression.clone()?;
        let result = self.bind(site.call)?.expression(implementation);
        recovered.insert(self.key());
        Some(site.rebuild(result))
    }

    fn expand_body(
        &self,
        expression: &KotlinExpr,
        recovered: &mut BTreeSet<RecoveredFunction>,
    ) -> Option<KotlinStmt> {
        let site = FunctionCallSite::analyze(expression);
        let result = self.bind(site.call)?.statement(self.body.clone());
        recovered.insert(self.key());
        Some(site.rebuild_returns(result))
    }

    fn bind(&self, expression: &KotlinExpr) -> Option<FunctionCallBinding<'_>> {
        let KotlinExpr::Call {
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
    owner: &'a KotlinType,
    receiver: Option<KotlinExpr>,
    values: BTreeMap<KotlinIdentifier, KotlinExpr>,
}

impl FunctionCallBinding<'_> {
    fn expression(&self, expression: KotlinExpr) -> KotlinExpr {
        self.rewriter().rewrite_expression(expression)
    }

    fn statement(&self, statement: KotlinStmt) -> KotlinStmt {
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

    fn is_adapter_for(&self, expression: &KotlinExpr, function: &KotlinMethodDeclaration) -> bool {
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
        while let Some(KotlinExpr::Cast { value, .. }) = expression {
            expression = Some(value);
        }
        matches!(expression, Some(KotlinExpr::New { .. }))
    }
}

struct FunctionCallSite<'a> {
    call: &'a KotlinExpr,
    conversions: Vec<KotlinType>,
}

impl<'a> FunctionCallSite<'a> {
    fn analyze(mut expression: &'a KotlinExpr) -> Self {
        let mut conversions = Vec::new();
        while let KotlinExpr::Cast { ty, value } = expression {
            conversions.push(ty.clone());
            expression = value;
        }
        Self {
            call: expression,
            conversions,
        }
    }

    fn rebuild(self, mut expression: KotlinExpr) -> KotlinExpr {
        FunctionReturnConversion::convert(expression, &self.conversions)
    }

    fn rebuild_returns(self, statement: KotlinStmt) -> KotlinStmt {
        FunctionReturnConversion {
            conversions: &self.conversions,
        }
        .statement(statement)
    }
}

struct FunctionReturnConversion<'a> {
    conversions: &'a [KotlinType],
}

impl FunctionReturnConversion<'_> {
    fn convert(mut expression: KotlinExpr, conversions: &[KotlinType]) -> KotlinExpr {
        for ty in conversions.iter().rev() {
            expression = KotlinExpr::Cast {
                ty: ty.clone(),
                value: Box::new(expression),
            };
        }
        expression
    }

    fn statement(&self, statement: KotlinStmt) -> KotlinStmt {
        match statement {
            KotlinStmt::Block(statements) => KotlinStmt::Block(
                statements
                    .into_iter()
                    .map(|statement| self.statement(statement))
                    .collect(),
            ),
            KotlinStmt::Labeled { label, body } => KotlinStmt::Labeled {
                label,
                body: Box::new(self.statement(*body)),
            },
            KotlinStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => KotlinStmt::If {
                condition,
                then_stmt: Box::new(self.statement(*then_stmt)),
                else_stmt: else_stmt.map(|statement| Box::new(self.statement(*statement))),
            },
            KotlinStmt::While {
                label,
                condition,
                body,
            } => KotlinStmt::While {
                label,
                condition,
                body: Box::new(self.statement(*body)),
            },
            KotlinStmt::DoWhile {
                label,
                body,
                condition,
            } => KotlinStmt::DoWhile {
                label,
                body: Box::new(self.statement(*body)),
                condition,
            },
            KotlinStmt::For {
                label,
                init,
                condition,
                update,
                body,
            } => KotlinStmt::For {
                label,
                init,
                condition,
                update,
                body: Box::new(self.statement(*body)),
            },
            KotlinStmt::ForEach {
                label,
                ty,
                variable,
                iterable,
                body,
            } => KotlinStmt::ForEach {
                label,
                ty,
                variable,
                iterable,
                body: Box::new(self.statement(*body)),
            },
            KotlinStmt::Switch {
                label,
                selector,
                cases,
            } => KotlinStmt::Switch {
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
            KotlinStmt::Try {
                body,
                catches,
                finally,
            } => KotlinStmt::Try {
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
            KotlinStmt::Synchronized { lock, body } => KotlinStmt::Synchronized {
                lock,
                body: Box::new(self.statement(*body)),
            },
            KotlinStmt::Return(Some(expression)) => {
                KotlinStmt::Return(Some(Self::convert(expression, self.conversions)))
            }
            statement => statement,
        }
    }
}

struct FunctionArgument;

impl FunctionArgument {
    fn remove_transport_cast(mut argument: KotlinExpr, parameter: &KotlinType) -> KotlinExpr {
        while matches!(&argument, KotlinExpr::Cast { ty, .. } if ty == parameter) {
            let KotlinExpr::Cast { value, .. } = argument else {
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
        body: &KotlinAnonymousClassBody,
        summaries: &[FunctionSummary],
        parameter_names: &mut FunctionParameterNames,
        recovered: &mut BTreeSet<RecoveredFunction>,
    ) -> Option<KotlinExpr> {
        if !body.fields.is_empty() || !body.properties.is_empty() || !body.nested.is_empty() {
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
            .zip(parameters.iter().cloned().map(KotlinExpr::Name))
            .collect::<BTreeMap<_, _>>();
        let mut substitution = ParameterSubstitution { values: &values };
        if let Some(forwarding_call) = forwarding_call {
            if let Some(statement) = summaries
                .iter()
                .filter(|summary| summary.is_adapter_for(forwarding_call, method))
                .find_map(|summary| summary.expand_body(forwarding_call, recovered))
            {
                return Some(KotlinExpr::BlockLambda {
                    parameters,
                    body: Box::new(substitution.rewrite_statement(statement)),
                });
            }
            if let Some(reference) = Self::method_reference(forwarding_call, method) {
                return Some(reference);
            }
            return Some(KotlinExpr::Lambda {
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
            return Some(KotlinExpr::BlockLambda {
                parameters,
                body: Box::new(substitution.rewrite_statement(statement)),
            });
        }
        Some(KotlinExpr::Lambda {
            parameters,
            body: Box::new(substitution.rewrite_expression(expression)),
        })
    }

    pub(super) fn summary_expression(method: &KotlinMethodDeclaration) -> Option<KotlinExpr> {
        ReturnExpression::recover(&method.body.as_ref()?.root)
    }

    fn body_expression(method: &KotlinMethodDeclaration) -> Option<&KotlinExpr> {
        let root = &method.body.as_ref()?.root;
        match root {
            KotlinStmt::Return(Some(expression)) => Some(expression),
            KotlinStmt::Block(statements) => match statements.as_slice() {
                [KotlinStmt::Return(Some(expression))] => Some(expression),
                _ => None,
            },
            _ => None,
        }
    }

    fn forwards_parameters(args: &[KotlinExpr], method: &KotlinMethodDeclaration) -> bool {
        args.len() == method.parameters.len()
            && args
                .iter()
                .zip(&method.parameters)
                .all(|(argument, parameter)| {
                    Self::without_casts(argument) == &KotlinExpr::Name(parameter.name.clone())
                })
    }

    fn call_arguments(expression: &KotlinExpr) -> &[KotlinExpr] {
        match expression {
            KotlinExpr::Call { args, .. } => args,
            _ => &[],
        }
    }

    fn method_reference(
        expression: &KotlinExpr,
        method: &KotlinMethodDeclaration,
    ) -> Option<KotlinExpr> {
        let KotlinExpr::Call {
            receiver: Some(receiver),
            method: referenced_method,
            args,
            ..
        } = expression
        else {
            return None;
        };
        Self::forwards_parameters(args, method).then(|| KotlinExpr::MethodReference {
            receiver: receiver.clone(),
            method: referenced_method.clone(),
        })
    }

    pub(super) fn without_casts(mut expression: &KotlinExpr) -> &KotlinExpr {
        while let KotlinExpr::Cast { value, .. } = expression {
            expression = value;
        }
        expression
    }
}

struct VoidFunctionBody;

impl VoidFunctionBody {
    fn forwarded_call(root: &KotlinStmt) -> Option<&KotlinExpr> {
        let mut call = None;
        let mut pending = vec![root];
        while let Some(statement) = pending.pop() {
            match statement {
                KotlinStmt::Empty | KotlinStmt::Return(None) => {}
                KotlinStmt::Block(statements) => pending.extend(statements.iter().rev()),
                KotlinStmt::Expression(expression @ KotlinExpr::Call { .. }) if call.is_none() => {
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
    fn recover(statement: &KotlinStmt) -> Option<KotlinExpr> {
        Self::with_continuation(statement, None)
    }

    fn with_continuation(
        statement: &KotlinStmt,
        continuation: Option<KotlinExpr>,
    ) -> Option<KotlinExpr> {
        match statement {
            KotlinStmt::Return(Some(expression)) => Some(expression.clone()),
            KotlinStmt::Empty => continuation,
            KotlinStmt::Block(statements) => {
                statements
                    .iter()
                    .rev()
                    .try_fold(continuation, |continuation, statement| {
                        Self::with_continuation(statement, continuation).map(Some)
                    })?
            }
            KotlinStmt::Assign { target, op, value } if continuation.as_ref() == Some(value) => {
                Some(KotlinExpr::Assignment {
                    target: Box::new(target.clone()),
                    op: *op,
                    value: Box::new(value.clone()),
                })
            }
            KotlinStmt::If {
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
            KotlinStmt::Variable { .. }
            | KotlinStmt::Expression(_)
            | KotlinStmt::Assign { .. }
            | KotlinStmt::ConstructorInvocation { .. }
            | KotlinStmt::While { .. }
            | KotlinStmt::DoWhile { .. }
            | KotlinStmt::For { .. }
            | KotlinStmt::ForEach { .. }
            | KotlinStmt::Switch { .. }
            | KotlinStmt::Try { .. }
            | KotlinStmt::Synchronized { .. }
            | KotlinStmt::Break(_)
            | KotlinStmt::Continue(_)
            | KotlinStmt::Throw(_)
            | KotlinStmt::Return(None)
            | KotlinStmt::Labeled { .. } => None,
        }
    }

    fn select(condition: KotlinExpr, when_true: KotlinExpr, when_false: KotlinExpr) -> KotlinExpr {
        match (&when_true, &when_false) {
            (
                KotlinExpr::Literal(crate::language::kotlin::KotlinLiteral::Boolean(true)),
                KotlinExpr::Literal(crate::language::kotlin::KotlinLiteral::Boolean(false)),
            ) => condition,
            (
                KotlinExpr::Literal(crate::language::kotlin::KotlinLiteral::Boolean(false)),
                KotlinExpr::Literal(crate::language::kotlin::KotlinLiteral::Boolean(true)),
            ) => KotlinExpr::Unary {
                op: crate::language::kotlin::KotlinUnaryOp::LogicalNot,
                operand: Box::new(condition),
            },
            _ => KotlinExpr::Conditional {
                condition: Box::new(condition),
                when_true: Box::new(when_true),
                when_false: Box::new(when_false),
            },
        }
    }
}

struct FunctionTargetContract;

impl FunctionTargetContract {
    fn valid_in_scope(ty: &KotlinType, type_variables: &BTreeSet<KotlinIdentifier>) -> bool {
        match ty {
            KotlinType::Variable(variable) => type_variables.contains(variable),
            KotlinType::Array(element) => Self::valid_in_scope(element, type_variables),
            KotlinType::Class(class) => class.segments.iter().all(|segment| {
                segment.arguments.iter().all(|argument| match argument {
                    KotlinTypeArgument::Any => true,
                    KotlinTypeArgument::Exact(value)
                    | KotlinTypeArgument::Extends(value)
                    | KotlinTypeArgument::Super(value) => {
                        Self::valid_in_scope(value, type_variables)
                    }
                })
            }),
            KotlinType::Primitive(_) => true,
        }
    }

    fn reconcile(declared: &KotlinType, contextual: &KotlinType) -> KotlinType {
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

    fn well_formed(ty: &KotlinType) -> bool {
        match ty {
            KotlinType::Primitive(_) => false,
            KotlinType::Variable(_) => true,
            KotlinType::Array(_) => true,
            KotlinType::Class(class) => class.segments.iter().all(|segment| {
                segment.arguments.iter().all(|argument| match argument {
                    KotlinTypeArgument::Any => true,
                    KotlinTypeArgument::Exact(value)
                    | KotlinTypeArgument::Extends(value)
                    | KotlinTypeArgument::Super(value) => Self::well_formed(value),
                })
            }),
        }
    }

    fn compatible(left: &KotlinType, right: &KotlinType) -> bool {
        match (left, right) {
            (KotlinType::Variable(_), _) | (_, KotlinType::Variable(_)) => true,
            (KotlinType::Array(left), KotlinType::Array(right)) => Self::compatible(left, right),
            (KotlinType::Class(left), KotlinType::Class(right)) => {
                left.name() == right.name() && left.segments.len() == right.segments.len()
            }
            (KotlinType::Primitive(left), KotlinType::Primitive(right)) => left == right,
            _ => false,
        }
    }

    fn information(ty: &KotlinType) -> usize {
        match ty {
            KotlinType::Primitive(_) => 0,
            KotlinType::Variable(_) => 2,
            KotlinType::Array(element) => 1 + Self::information(element),
            KotlinType::Class(class) => {
                1 + class
                    .segments
                    .iter()
                    .flat_map(|segment| &segment.arguments)
                    .map(|argument| match argument {
                        KotlinTypeArgument::Any => 0,
                        KotlinTypeArgument::Exact(value) => 2 + Self::information(value),
                        KotlinTypeArgument::Extends(value) | KotlinTypeArgument::Super(value) => {
                            1 + Self::information(value)
                        }
                    })
                    .sum::<usize>()
            }
        }
    }

    fn has_type_arguments(ty: &KotlinType) -> bool {
        match ty {
            KotlinType::Class(class) => class
                .segments
                .iter()
                .any(|segment| !segment.arguments.is_empty()),
            KotlinType::Array(element) => Self::has_type_arguments(element),
            KotlinType::Primitive(_) | KotlinType::Variable(_) => false,
        }
    }
}

struct AnonymousInstance {
    base: KotlinType,
    super_arguments: Vec<KotlinExpr>,
    body: KotlinAnonymousClassBody,
}

impl AnonymousInstance {
    fn base_type(candidate: &LoweredNestedType) -> Option<KotlinType> {
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
        arguments: Vec<KotlinExpr>,
        _target: Option<&KotlinType>,
        mutable_names: &BTreeSet<KotlinIdentifier>,
        value_types: &BTreeMap<KotlinIdentifier, LexicalValueType>,
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
                method.kind == KotlinMethodDeclarationKind::Constructor
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
                KotlinStmt::Block(statements) => statements.as_slice(),
                statement => std::slice::from_ref(statement),
            };
            let mut super_invocations = 0usize;
            for statement in statements {
                match statement {
                    KotlinStmt::ConstructorInvocation {
                        target: KotlinConstructorTarget::Super,
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
                    KotlinStmt::Assign {
                        target: KotlinExpr::Field { owner, name: field },
                        op: KotlinAssignOp::Assign,
                        value: KotlinExpr::Name(parameter),
                    } if matches!(owner.as_ref(), KotlinExpr::This)
                        && candidate.synthetic_final_fields.contains(field) =>
                    {
                        let value = parameters.get(parameter)?.clone();
                        captures.insert(field.clone(), value);
                    }
                    KotlinStmt::Assign {
                        target: KotlinExpr::Field { owner, name: field },
                        op: KotlinAssignOp::Assign,
                        value,
                    } if matches!(owner.as_ref(), KotlinExpr::This)
                        && declaration.fields.iter().any(|declaration| {
                            &declaration.name == field
                                && !declaration.modifiers.contains(&KotlinModifier::Static)
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
                    KotlinStmt::Empty => {}
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
        let mut body = KotlinAnonymousClassBody {
            super_constructor_call: declaration.extends.is_some(),
            fields,
            properties: declaration.properties.clone(),
            methods: declaration
                .methods
                .iter()
                .filter(|method| method.kind != KotlinMethodDeclarationKind::Constructor)
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
    fn stable(value: &KotlinExpr, mutable_names: &BTreeSet<KotlinIdentifier>) -> bool {
        match value {
            KotlinExpr::Name(name) => !mutable_names.contains(name),
            KotlinExpr::This
            | KotlinExpr::QualifiedThis(_)
            | KotlinExpr::Literal(_)
            | KotlinExpr::ClassLiteral(_) => true,
            _ => false,
        }
    }
}

#[derive(Default)]
struct LexicalValueTypes {
    types: BTreeMap<KotlinIdentifier, LexicalValueType>,
    conflicts: BTreeSet<KotlinIdentifier>,
}

struct LexicalValueType {
    ty: KotlinType,
    authoritative: bool,
}

impl LexicalValueTypes {
    fn collect(method: &KotlinMethodDeclaration) -> BTreeMap<KotlinIdentifier, LexicalValueType> {
        let mut values = Self::default();
        for parameter in &method.parameters {
            values.record(parameter.name.clone(), parameter.ty.clone(), true);
        }
        if let Some(body) = &method.body {
            values.rewrite_statement(body.root.clone());
        }
        values.types
    }

    fn record(&mut self, name: KotlinIdentifier, ty: KotlinType, authoritative: bool) {
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

impl KotlinAstRewriter for LexicalValueTypes {
    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        match &statement {
            KotlinStmt::Variable { ty, name, .. } => self.record(name.clone(), ty.clone(), false),
            KotlinStmt::ForEach { ty, variable, .. } => {
                self.record(variable.clone(), ty.clone(), false);
            }
            _ => {}
        }
        statement
    }
}

#[derive(Default)]
struct MutableLocals {
    names: BTreeSet<KotlinIdentifier>,
}

impl MutableLocals {
    fn collect(root: &KotlinStmt) -> BTreeSet<KotlinIdentifier> {
        let mut collector = Self::default();
        collector.rewrite_statement(root.clone());
        collector.names
    }
}

impl KotlinAstRewriter for MutableLocals {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if let KotlinExpr::Update { target, .. } = &expression {
            if let KotlinExpr::Name(name) = target.as_ref() {
                self.names.insert(name.clone());
            }
        }
        expression
    }

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        if let KotlinStmt::Assign {
            target: KotlinExpr::Name(name),
            ..
        } = &statement
        {
            self.names.insert(name.clone());
        }
        statement
    }
}

struct ResolvedFunctionContract {
    parameter_types: Vec<KotlinType>,
    return_type: KotlinType,
}

struct FunctionParameterAdapter<'a> {
    parameters: BTreeMap<KotlinIdentifier, KotlinType>,
    names: &'a KotlinTypeNameResolver,
    source_abi: &'a KotlinSourceAbi,
}

impl<'a> FunctionParameterAdapter<'a> {
    fn new(
        parameters: &[KotlinIdentifier],
        types: &[KotlinType],
        names: &'a KotlinTypeNameResolver,
        source_abi: &'a KotlinSourceAbi,
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

    fn erasure(&self, ty: &KotlinType) -> Option<crate::ir::ArgType> {
        self.names.source_signature(ty).map(|ty| ty.erased())
    }

    fn parameter_satisfies(&self, parameter: &KotlinIdentifier, target: &KotlinType) -> bool {
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

impl KotlinAstRewriter for FunctionParameterAdapter<'_> {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match expression {
            KotlinExpr::Cast { ty, value }
                if matches!(value.as_ref(), KotlinExpr::Name(parameter)
                    if self.parameter_satisfies(parameter, &ty)) =>
            {
                *value
            }
            expression => expression,
        }
    }
}

struct FunctionReturnAdapter<'a> {
    return_type: &'a KotlinType,
}

impl KotlinAstRewriter for FunctionReturnAdapter<'_> {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        match statement {
            KotlinStmt::Return(Some(expression)) => KotlinStmt::Return(Some(
                FunctionContract::adapt_return(expression, self.return_type),
            )),
            statement => statement,
        }
    }
}

impl FunctionContract {
    fn resolve(
        &self,
        target: &KotlinType,
        names: &KotlinTypeNameResolver,
        source_abi: &KotlinSourceAbi,
        type_variables: &BTreeSet<KotlinIdentifier>,
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
        target: &KotlinType,
        expression: KotlinExpr,
        names: &KotlinTypeNameResolver,
        source_abi: &KotlinSourceAbi,
        type_variables: &BTreeSet<KotlinIdentifier>,
        parameter_names: &mut FunctionParameterNames,
    ) -> KotlinExpr {
        let Some(contract) = self.resolve(target, names, source_abi, type_variables) else {
            return expression;
        };
        match expression {
            KotlinExpr::Lambda { parameters, body } => {
                let body = FunctionParameterAdapter::new(
                    &parameters,
                    &contract.parameter_types,
                    names,
                    source_abi,
                )
                .rewrite_expression(*body);
                KotlinExpr::Lambda {
                    parameters,
                    body: Box::new(Self::adapt_return(body, &contract.return_type)),
                }
            }
            KotlinExpr::BlockLambda { parameters, body } => {
                let body = FunctionParameterAdapter::new(
                    &parameters,
                    &contract.parameter_types,
                    names,
                    source_abi,
                )
                .rewrite_statement(*body);
                KotlinExpr::BlockLambda {
                    parameters,
                    body: Box::new(
                        FunctionReturnAdapter {
                            return_type: &contract.return_type,
                        }
                        .rewrite_statement(body),
                    ),
                }
            }
            KotlinExpr::MethodReference { receiver, method }
                if Self::contains_type_variable(&contract.return_type) =>
            {
                let parameters = parameter_names.allocate(contract.parameter_types.len());
                let call = KotlinExpr::Call {
                    receiver: Some(receiver),
                    owner: None,
                    type_arguments: Vec::new(),
                    method,
                    args: parameters.iter().cloned().map(KotlinExpr::Name).collect(),
                };
                KotlinExpr::Lambda {
                    parameters,
                    body: Box::new(Self::adapt_return(call, &contract.return_type)),
                }
            }
            expression => expression,
        }
    }

    fn adapt_return(expression: KotlinExpr, return_type: &KotlinType) -> KotlinExpr {
        match expression {
            KotlinExpr::Cast { ty, value }
                if FunctionTargetContract::compatible(&ty, return_type) =>
            {
                KotlinExpr::Cast {
                    ty: return_type.clone(),
                    value,
                }
            }
            expression if Self::contains_type_variable(return_type) => KotlinExpr::Cast {
                ty: return_type.clone(),
                value: Box::new(expression),
            },
            expression => expression,
        }
    }

    fn requires_explicit_target(
        &self,
        target: &KotlinType,
        names: &KotlinTypeNameResolver,
        source_abi: &KotlinSourceAbi,
        type_variables: &BTreeSet<KotlinIdentifier>,
    ) -> bool {
        self.resolve(target, names, source_abi, type_variables)
            .is_some_and(|contract| {
                matches!(contract.return_type, KotlinType::Primitive(_))
                    || Self::contains_type_variable(&contract.return_type)
            })
    }

    fn contains_type_variable(ty: &KotlinType) -> bool {
        match ty {
            KotlinType::Variable(_) => true,
            KotlinType::Array(element) => Self::contains_type_variable(element),
            KotlinType::Class(class) => class.segments.iter().any(|segment| {
                segment.arguments.iter().any(|argument| match argument {
                    KotlinTypeArgument::Exact(ty)
                    | KotlinTypeArgument::Extends(ty)
                    | KotlinTypeArgument::Super(ty) => Self::contains_type_variable(ty),
                    KotlinTypeArgument::Any => false,
                })
            }),
            KotlinType::Primitive(_) => false,
        }
    }

    fn specialize(
        &self,
        target: &KotlinType,
        body: &mut KotlinAnonymousClassBody,
        names: &KotlinTypeNameResolver,
        source_abi: &KotlinSourceAbi,
        type_variables: &BTreeSet<KotlinIdentifier>,
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
    identity: &'a KotlinType,
}

impl KotlinAstRewriter for AnonymousIdentitySubstitution<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match expression {
            KotlinExpr::Call {
                receiver: Some(receiver),
                owner: None,
                type_arguments,
                method,
                args,
            } if matches!(receiver.as_ref(), KotlinExpr::QualifiedThis(owner) if AnonymousTypeIdentity::matches(self.identity, owner)) => {
                KotlinExpr::Call {
                    receiver: None,
                    owner: None,
                    type_arguments,
                    method,
                    args,
                }
            }
            KotlinExpr::Field { owner, name } if matches!(owner.as_ref(), KotlinExpr::QualifiedThis(identity) if AnonymousTypeIdentity::matches(self.identity, identity)) => {
                KotlinExpr::Name(name)
            }
            KotlinExpr::MethodReference { receiver, method } if matches!(receiver.as_ref(), KotlinExpr::QualifiedThis(identity) if AnonymousTypeIdentity::matches(self.identity, identity)) => {
                KotlinExpr::MethodReference {
                    receiver: Box::new(KotlinExpr::This),
                    method,
                }
            }
            KotlinExpr::Call {
                receiver: None,
                owner: Some(owner),
                type_arguments,
                method,
                args,
            } if &owner == self.identity => KotlinExpr::Call {
                receiver: None,
                owner: None,
                type_arguments,
                method,
                args,
            },
            KotlinExpr::StaticField { owner, name } if &owner == self.identity => {
                KotlinExpr::Name(name)
            }
            expression => expression,
        }
    }
}

struct ReturnTypeAdapter {
    expected: KotlinType,
}

impl KotlinAstRewriter for ReturnTypeAdapter {
    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        let KotlinStmt::Return(Some(value)) = statement else {
            return statement;
        };
        if matches!(&value, KotlinExpr::Cast { ty, .. } if ty == &self.expected) {
            return KotlinStmt::Return(Some(value));
        }
        KotlinStmt::Return(Some(KotlinExpr::Cast {
            ty: self.expected.clone(),
            value: Box::new(value),
        }))
    }
}

struct ParameterSubstitution<'a> {
    values: &'a BTreeMap<KotlinIdentifier, KotlinExpr>,
}

impl KotlinAstRewriter for ParameterSubstitution<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match expression {
            KotlinExpr::Name(name) => self
                .values
                .get(&name)
                .cloned()
                .unwrap_or(KotlinExpr::Name(name)),
            expression => expression,
        }
    }
}

struct FunctionBinding<'a> {
    owner: &'a KotlinType,
    receiver: Option<&'a KotlinExpr>,
    parameters: ParameterSubstitution<'a>,
}

impl KotlinAstRewriter for FunctionBinding<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match self.parameters.finish_expression(expression) {
            KotlinExpr::This => self.receiver.cloned().unwrap_or(KotlinExpr::This),
            KotlinExpr::QualifiedThis(owner) if &owner == self.owner => self
                .receiver
                .cloned()
                .unwrap_or(KotlinExpr::QualifiedThis(owner)),
            expression => expression,
        }
    }
}

struct CaptureSubstitution<'a> {
    values: BTreeMap<KotlinIdentifier, KotlinExpr>,
    identity: Option<&'a KotlinType>,
    value_types: &'a BTreeMap<KotlinIdentifier, LexicalValueType>,
}

impl KotlinAstRewriter for CaptureSubstitution<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match expression {
            KotlinExpr::Cast { ty, value }
                if self.capture_type(value.as_ref()).is_some_and(|captured| {
                    captured.authoritative && Self::same_erasure(&captured.ty, &ty)
                }) =>
            {
                *value
            }
            KotlinExpr::Field { owner, name }
                if matches!(owner.as_ref(), KotlinExpr::This)
                    || matches!(
                        (owner.as_ref(), self.identity),
                        (KotlinExpr::QualifiedThis(owner), Some(identity)) if owner == identity
                    ) =>
            {
                self.values
                    .get(&name)
                    .cloned()
                    .unwrap_or(KotlinExpr::Field { owner, name })
            }
            expression => expression,
        }
    }
}

impl CaptureSubstitution<'_> {
    fn capture_type(&self, expression: &KotlinExpr) -> Option<&LexicalValueType> {
        match expression {
            KotlinExpr::Name(name)
                if self.values.values().any(|captured| captured == expression) =>
            {
                self.value_types.get(name)
            }
            KotlinExpr::Cast { value, .. } => self.capture_type(value),
            _ => None,
        }
    }

    fn same_erasure(left: &KotlinType, right: &KotlinType) -> bool {
        match (left, right) {
            (KotlinType::Array(left), KotlinType::Array(right)) => Self::same_erasure(left, right),
            (KotlinType::Class(left), KotlinType::Class(right)) => left.name() == right.name(),
            (KotlinType::Primitive(left), KotlinType::Primitive(right)) => left == right,
            (KotlinType::Variable(left), KotlinType::Variable(right)) => left == right,
            _ => false,
        }
    }
}
