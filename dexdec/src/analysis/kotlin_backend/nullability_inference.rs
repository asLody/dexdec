use std::collections::{BTreeMap, BTreeSet};

use crate::language::kotlin::{
    KotlinAstRewriter, KotlinExpr, KotlinIdentifier, KotlinLiteral, KotlinMethodDeclarationKind,
    KotlinModifier, KotlinStmt, KotlinType, KotlinTypeDeclaration,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct MethodKey {
    name: KotlinIdentifier,
    arity: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ParameterId {
    method: usize,
    parameter: usize,
}

#[derive(Debug, Default)]
struct ParameterFacts {
    uses: usize,
    required: usize,
    dependencies: Vec<Vec<ParameterId>>,
}

/// Solves reference parameter nullability over one Kotlin declaration.
///
/// Constraints come from dereferences, explicit null observations, and calls
/// between methods in the declaration. Recursive call components are solved as
/// a graph fixed point, then checked backwards against every known caller.
pub(super) struct KotlinNullabilityInference;

impl KotlinNullabilityInference {
    pub(super) fn apply(declaration: &mut KotlinTypeDeclaration) {
        Self::apply_type(declaration);
        for nested in &mut declaration.nested {
            Self::apply(nested);
        }
    }

    fn apply_type(declaration: &mut KotlinTypeDeclaration) {
        Self::infer_field_contracts(declaration);
        Self::mark_stable_fields(declaration);
        let method_keys = declaration
            .methods
            .iter()
            .map(|method| {
                method.name.clone().map(|name| MethodKey {
                    name,
                    arity: method.parameters.len(),
                })
            })
            .collect::<Vec<_>>();
        let mut targets = BTreeMap::<MethodKey, Vec<usize>>::new();
        for (method, key) in method_keys.iter().enumerate() {
            if let Some(key) = key {
                targets.entry(key.clone()).or_default().push(method);
            }
        }

        let mut facts = declaration
            .methods
            .iter()
            .map(|method| {
                (0..method.parameters.len())
                    .map(|_| ParameterFacts::default())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut incoming = BTreeMap::<ParameterId, Vec<ParameterId>>::new();
        let mut unsafe_incoming = BTreeSet::new();

        for (method_index, method) in declaration.methods.iter().enumerate() {
            let Some(body) = &method.body else {
                continue;
            };
            let parameters = method
                .parameters
                .iter()
                .enumerate()
                .map(|(index, parameter)| (parameter.name.clone(), index))
                .collect();
            let mut collector = ConstraintCollector {
                owner: &declaration.name,
                method: method_index,
                parameters,
                targets: &targets,
                facts: &mut facts[method_index],
                incoming: &mut incoming,
                unsafe_incoming: &mut unsafe_incoming,
            };
            collector.rewrite_statement(body.root.clone());
        }

        let eligible = facts
            .iter()
            .enumerate()
            .flat_map(|(method, parameters)| {
                parameters
                    .iter()
                    .enumerate()
                    .filter_map(move |(parameter, fact)| {
                        (fact.uses != 0 && fact.uses == fact.required + fact.dependencies.len())
                            .then_some(ParameterId { method, parameter })
                    })
            })
            .collect::<BTreeSet<_>>();

        let mut non_null = eligible
            .iter()
            .copied()
            .filter(|id| facts[id.method][id.parameter].required != 0)
            .collect::<BTreeSet<_>>();
        loop {
            let before = non_null.len();
            for id in &eligible {
                let fact = &facts[id.method][id.parameter];
                let anchored = fact.required != 0
                    || fact
                        .dependencies
                        .iter()
                        .flatten()
                        .any(|target| non_null.contains(target));
                let dependencies_hold = fact
                    .dependencies
                    .iter()
                    .all(|targets| targets.iter().all(|target| eligible.contains(target)));
                if anchored && dependencies_hold {
                    non_null.insert(*id);
                }
            }
            if non_null.len() == before {
                break;
            }
        }

        loop {
            let before = non_null.len();
            let current = non_null.clone();
            non_null.retain(|id| {
                !unsafe_incoming.contains(id)
                    && incoming
                        .get(id)
                        .into_iter()
                        .flatten()
                        .all(|caller| current.contains(caller))
                    && facts[id.method][id.parameter]
                        .dependencies
                        .iter()
                        .all(|targets| targets.iter().all(|target| current.contains(target)))
            });
            if non_null.len() == before {
                break;
            }
        }

        for (method_index, method) in declaration.methods.iter_mut().enumerate() {
            let mut names = method
                .parameters
                .iter()
                .filter(|parameter| !parameter.nullable)
                .map(|parameter| parameter.name.clone())
                .collect::<BTreeSet<_>>();
            if method.modifiers.contains(&KotlinModifier::Private)
                || method.kind == KotlinMethodDeclarationKind::Constructor
            {
                names.extend(
                    non_null
                        .iter()
                        .filter(|id| id.method == method_index)
                        .filter_map(|id| {
                            let parameter = method.parameters.get_mut(id.parameter)?;
                            if !matches!(parameter.ty, KotlinType::Class(_) | KotlinType::Array(_))
                            {
                                return None;
                            }
                            parameter.nullable = false;
                            Some(parameter.name.clone())
                        }),
                );
            }
            if names.is_empty() {
                continue;
            }
            if let Some(body) = &mut method.body {
                let mut shadows = ParameterShadowCollector {
                    parameters: &names,
                    shadowed: BTreeSet::new(),
                };
                shadows.rewrite_statement(body.root.clone());
                names.retain(|name| !shadows.shadowed.contains(name));
                let mut marker = KnownNonNullParameterMarker { names: &names };
                body.root =
                    marker.rewrite_statement(std::mem::replace(&mut body.root, KotlinStmt::Empty));
            }
        }
    }

    fn infer_field_contracts(declaration: &mut KotlinTypeDeclaration) {
        for field in &mut declaration.fields {
            if !matches!(field.ty, KotlinType::Class(_) | KotlinType::Array(_)) {
                field.nullable = false;
                continue;
            }
            if !field.nullable {
                continue;
            }
            field.nullable = !(field.modifiers.contains(&KotlinModifier::Final)
                && field
                    .initializer
                    .as_ref()
                    .is_some_and(Self::stable_non_null_value));
        }
    }

    fn mark_stable_fields(declaration: &mut KotlinTypeDeclaration) {
        // A property promoted into the primary constructor is still a property,
        // and reads of it are still known not to be null.
        let names =
            declaration
                .fields
                .iter()
                .chain(declaration.primary_parameters.iter().filter_map(
                    |parameter| match parameter {
                        crate::language::kotlin::KotlinPrimaryParameter::Property(property) => {
                            Some(property)
                        }
                        crate::language::kotlin::KotlinPrimaryParameter::Value(_) => None,
                    },
                ))
                .filter(|field| !field.nullable)
                .map(|field| field.name.clone())
                .collect::<BTreeSet<_>>();
        if names.is_empty() {
            return;
        }
        let owner = declaration.name.clone();
        let mut marker = KnownNonNullFieldMarker {
            owner: &owner,
            names: &names,
        };
        for field in &mut declaration.fields {
            if let Some(initializer) = field.initializer.take() {
                field.initializer = Some(marker.rewrite_expression(initializer));
            }
        }
        for method in &mut declaration.methods {
            if let Some(body) = &mut method.body {
                body.root =
                    marker.rewrite_statement(std::mem::replace(&mut body.root, KotlinStmt::Empty));
            }
        }
        for property in &mut declaration.properties {
            if let Some(body) = &mut property.getter {
                body.root =
                    marker.rewrite_statement(std::mem::replace(&mut body.root, KotlinStmt::Empty));
            }
        }
    }

    fn stable_non_null_value(expression: &KotlinExpr) -> bool {
        match expression {
            KotlinExpr::This
            | KotlinExpr::QualifiedThis(_)
            | KotlinExpr::Super
            | KotlinExpr::ClassLiteral(_)
            | KotlinExpr::Lambda { .. }
            | KotlinExpr::BlockLambda { .. }
            | KotlinExpr::New { .. }
            | KotlinExpr::NewArray { .. } => true,
            KotlinExpr::Literal(KotlinLiteral::Null) => false,
            KotlinExpr::Literal(_) => true,
            KotlinExpr::Conditional {
                when_true,
                when_false,
                ..
            } => Self::stable_non_null_value(when_true) && Self::stable_non_null_value(when_false),
            KotlinExpr::SmartCast(value) | KotlinExpr::NonNullAssertion(value) => {
                Self::stable_non_null_value(value)
            }
            _ => false,
        }
    }
}

struct ParameterShadowCollector<'a> {
    parameters: &'a BTreeSet<KotlinIdentifier>,
    shadowed: BTreeSet<KotlinIdentifier>,
}

impl KotlinAstRewriter for ParameterShadowCollector<'_> {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_anonymous_body(
        &mut self,
        _body: &mut crate::language::kotlin::KotlinAnonymousClassBody,
    ) {
    }

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        if let KotlinStmt::Variable { name, .. } = &statement {
            if self.parameters.contains(name) {
                self.shadowed.insert(name.clone());
            }
        }
        statement
    }
}

struct KnownNonNullFieldMarker<'a> {
    owner: &'a KotlinIdentifier,
    names: &'a BTreeSet<KotlinIdentifier>,
}

impl KotlinAstRewriter for KnownNonNullFieldMarker<'_> {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_anonymous_body(
        &mut self,
        _body: &mut crate::language::kotlin::KotlinAnonymousClassBody,
    ) {
    }

    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if let KotlinExpr::NonNullAssertion(value) = expression {
            return match *value {
                value @ KotlinExpr::SmartCast(_) => value,
                value => KotlinExpr::NonNullAssertion(Box::new(value)),
            };
        }
        let stable = match &expression {
            KotlinExpr::Field { owner, name } => {
                self.names.contains(name)
                    && matches!(
                        owner.as_ref(),
                        KotlinExpr::This | KotlinExpr::QualifiedThis(_)
                    )
            }
            KotlinExpr::StaticField { owner, name } => {
                self.names.contains(name)
                    && matches!(
                        owner,
                        KotlinType::Class(class)
                            if class
                                .segments
                                .last()
                                .is_some_and(|segment| &segment.name == self.owner)
                    )
            }
            _ => false,
        };
        if stable {
            KotlinExpr::SmartCast(Box::new(expression))
        } else {
            expression
        }
    }
}

struct ConstraintCollector<'a> {
    owner: &'a KotlinIdentifier,
    method: usize,
    parameters: BTreeMap<KotlinIdentifier, usize>,
    targets: &'a BTreeMap<MethodKey, Vec<usize>>,
    facts: &'a mut [ParameterFacts],
    incoming: &'a mut BTreeMap<ParameterId, Vec<ParameterId>>,
    unsafe_incoming: &'a mut BTreeSet<ParameterId>,
}

impl KotlinAstRewriter for ConstraintCollector<'_> {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_anonymous_body(
        &mut self,
        _body: &mut crate::language::kotlin::KotlinAnonymousClassBody,
    ) {
    }

    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if let KotlinExpr::Name(name) = &expression {
            if let Some(parameter) = self.parameters.get(name) {
                self.facts[*parameter].uses += 1;
            }
        }
        if let Some(receiver) = Self::receiver(&expression) {
            if let Some(parameter) =
                Self::direct_name(receiver).and_then(|name| self.parameters.get(name))
            {
                self.facts[*parameter].required += 1;
            }
        }
        if let KotlinExpr::Call {
            receiver,
            owner,
            method,
            args,
            ..
        } = &expression
        {
            let key = MethodKey {
                name: method.clone(),
                arity: args.len(),
            };
            if Self::is_local_call(self.owner, owner.as_ref(), receiver.as_deref()) {
                let Some(methods) = self.targets.get(&key) else {
                    return expression;
                };
                for (index, argument) in args.iter().enumerate() {
                    let targets = methods
                        .iter()
                        .map(|method| ParameterId {
                            method: *method,
                            parameter: index,
                        })
                        .collect::<Vec<_>>();
                    if targets.is_empty() || Self::is_proven_non_null(argument) {
                        continue;
                    }
                    if let Some(parameter) =
                        Self::direct_name(argument).and_then(|name| self.parameters.get(name))
                    {
                        let caller = ParameterId {
                            method: self.method,
                            parameter: *parameter,
                        };
                        self.facts[*parameter].dependencies.push(targets.clone());
                        for target in targets {
                            self.incoming.entry(target).or_default().push(caller);
                        }
                    } else {
                        self.unsafe_incoming.extend(targets);
                    }
                }
            }
        }
        expression
    }
}

impl ConstraintCollector<'_> {
    fn receiver(expression: &KotlinExpr) -> Option<&KotlinExpr> {
        match expression {
            KotlinExpr::Field { owner, .. } => Some(owner),
            KotlinExpr::ArrayAccess { array, .. } => Some(array),
            KotlinExpr::Call {
                receiver: Some(receiver),
                ..
            }
            | KotlinExpr::MethodReference { receiver, .. } => Some(receiver),
            _ => None,
        }
    }

    fn direct_name(expression: &KotlinExpr) -> Option<&KotlinIdentifier> {
        match expression {
            KotlinExpr::Name(name) => Some(name),
            KotlinExpr::SmartCast(value) | KotlinExpr::NonNullAssertion(value) => {
                Self::direct_name(value)
            }
            _ => None,
        }
    }

    fn is_proven_non_null(expression: &KotlinExpr) -> bool {
        match expression {
            KotlinExpr::This
            | KotlinExpr::QualifiedThis(_)
            | KotlinExpr::Super
            | KotlinExpr::ClassLiteral(_)
            | KotlinExpr::Lambda { .. }
            | KotlinExpr::BlockLambda { .. }
            | KotlinExpr::New { .. }
            | KotlinExpr::NewArray { .. }
            | KotlinExpr::NonNullAssertion(_)
            | KotlinExpr::Literal(crate::language::kotlin::KotlinLiteral::String(_)) => true,
            // A smart cast is stable only when it refers to a local value.
            // Kotlin does not preserve smart casts for mutable or open fields.
            KotlinExpr::SmartCast(value) => Self::direct_name(value).is_some(),
            _ => false,
        }
    }

    fn is_local_call(
        owner: &KotlinIdentifier,
        target: Option<&KotlinType>,
        receiver: Option<&KotlinExpr>,
    ) -> bool {
        if let Some(target) = target {
            return matches!(
                target,
                KotlinType::Class(class)
                    if class.segments.last().is_some_and(|segment| &segment.name == owner)
            );
        }
        match receiver {
            None | Some(KotlinExpr::This) => true,
            Some(KotlinExpr::QualifiedThis(KotlinType::Class(target))) => target
                .segments
                .last()
                .is_some_and(|segment| &segment.name == owner),
            _ => false,
        }
    }
}

struct KnownNonNullParameterMarker<'a> {
    names: &'a BTreeSet<KotlinIdentifier>,
}

impl KotlinAstRewriter for KnownNonNullParameterMarker<'_> {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_anonymous_body(
        &mut self,
        _body: &mut crate::language::kotlin::KotlinAnonymousClassBody,
    ) {
    }

    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match expression {
            KotlinExpr::Name(name) if self.names.contains(&name) => {
                KotlinExpr::SmartCast(Box::new(KotlinExpr::Name(name)))
            }
            KotlinExpr::SmartCast(value) => match *value {
                KotlinExpr::SmartCast(value) => KotlinExpr::SmartCast(value),
                value => KotlinExpr::SmartCast(Box::new(value)),
            },
            KotlinExpr::NonNullAssertion(value) => match *value {
                value @ KotlinExpr::SmartCast(_) => value,
                value => KotlinExpr::NonNullAssertion(Box::new(value)),
            },
            expression => expression,
        }
    }
}
