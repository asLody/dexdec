use std::collections::{BTreeMap, BTreeSet};

use crate::language::kotlin::{
    KotlinAnonymousClassBody, KotlinAstRewriter, KotlinClassName, KotlinClassType, KotlinExpr,
    KotlinIdentifier, KotlinMethodDeclaration, KotlinMethodDeclarationKind, KotlinModifier,
    KotlinStmt, KotlinType, KotlinTypeDeclaration,
};

use super::anonymous_lowering::{FunctionExpression, RecoveredFunction};

/// Eliminates compiler-generated member bridges after their source expression
/// can be substituted at every call site in the compilation unit.
pub(super) struct SyntheticMemberRecovery;

impl SyntheticMemberRecovery {
    pub(super) fn apply(
        declaration: &mut KotlinTypeDeclaration,
        recovered_functions: &BTreeSet<RecoveredFunction>,
    ) {
        SyntheticFunctionRecovery::apply(declaration);
        SuperBridgeRecovery::apply(declaration);
        Self::remove_recovered_functions(declaration, recovered_functions);
        let contracts = MethodContractCatalog::collect(declaration);
        let mut candidates = BTreeMap::new();
        let mut collisions = BTreeSet::new();
        Self::collect_root(declaration, &contracts, &mut candidates, &mut collisions);
        for collision in collisions {
            candidates.remove(&collision);
        }
        if candidates.is_empty() {
            return;
        }

        let mut references = AccessorReferences {
            candidates: &candidates,
            counts: BTreeMap::new(),
        };
        Self::rewrite(declaration, &mut references);
        let mut inliner = AccessorInliner {
            candidates: &candidates,
            rewritten: BTreeMap::new(),
        };
        Self::rewrite(declaration, &mut inliner);
        let complete = references
            .counts
            .into_iter()
            .filter_map(|(key, references)| {
                (references != 0 && inliner.rewritten.get(&key) == Some(&references)).then_some(key)
            })
            .collect();
        Self::remove_root(declaration, &complete);
    }

    pub(super) fn remove_recovered_functions(
        declaration: &mut KotlinTypeDeclaration,
        recovered: &BTreeSet<RecoveredFunction>,
    ) {
        let candidates = recovered
            .iter()
            .filter(|function| function.owner == declaration.name)
            .map(|function| MethodKey {
                name: function.name.clone(),
                arity: function.arity,
            })
            .collect::<BTreeSet<_>>();
        if !candidates.is_empty() {
            let mut references = MethodReferences::new(&candidates);
            Self::rewrite(declaration, &mut references);
            SyntheticFunctionRecovery::retain(&mut declaration.methods, &candidates, &references);
        }
        for nested in &mut declaration.nested {
            Self::remove_recovered_functions(nested, recovered);
        }
    }

    fn collect_root(
        declaration: &KotlinTypeDeclaration,
        contracts: &MethodContractCatalog,
        candidates: &mut BTreeMap<AccessorKey, Accessor>,
        collisions: &mut BTreeSet<AccessorKey>,
    ) {
        Self::collect_type(
            declaration,
            vec![declaration.name.clone()],
            contracts,
            candidates,
            collisions,
        );
        for nested in &declaration.nested {
            Self::collect_nested(nested, Vec::new(), contracts, candidates, collisions);
        }
    }

    fn collect_nested(
        declaration: &KotlinTypeDeclaration,
        mut parent_path: Vec<KotlinIdentifier>,
        contracts: &MethodContractCatalog,
        candidates: &mut BTreeMap<AccessorKey, Accessor>,
        collisions: &mut BTreeSet<AccessorKey>,
    ) {
        parent_path.push(declaration.name.clone());
        Self::collect_type(
            declaration,
            parent_path.clone(),
            contracts,
            candidates,
            collisions,
        );
        for nested in &declaration.nested {
            Self::collect_nested(
                nested,
                parent_path.clone(),
                contracts,
                candidates,
                collisions,
            );
        }
    }

    fn collect_type(
        declaration: &KotlinTypeDeclaration,
        owner_path: Vec<KotlinIdentifier>,
        contracts: &MethodContractCatalog,
        candidates: &mut BTreeMap<AccessorKey, Accessor>,
        collisions: &mut BTreeSet<AccessorKey>,
    ) {
        let owner = KotlinType::Class(KotlinClassType::raw(KotlinClassName::from_identifiers(
            owner_path,
        )));
        for method in &declaration.methods {
            let Some(accessor) = Accessor::analyze(owner.clone(), method, contracts) else {
                continue;
            };
            let key = accessor.key.clone();
            if candidates.insert(key.clone(), accessor).is_some() {
                collisions.insert(key);
            }
        }
    }

    fn rewrite(declaration: &mut KotlinTypeDeclaration, rewriter: &mut impl KotlinAstRewriter) {
        rewriter.rewrite_type_declaration(declaration);
    }

    fn remove_root(declaration: &mut KotlinTypeDeclaration, rewritten: &BTreeSet<AccessorKey>) {
        Self::remove_type(declaration, vec![declaration.name.clone()], rewritten);
        for nested in &mut declaration.nested {
            Self::remove_nested(nested, Vec::new(), rewritten);
        }
    }

    fn remove_nested(
        declaration: &mut KotlinTypeDeclaration,
        mut parent_path: Vec<KotlinIdentifier>,
        rewritten: &BTreeSet<AccessorKey>,
    ) {
        parent_path.push(declaration.name.clone());
        Self::remove_type(declaration, parent_path.clone(), rewritten);
        for nested in &mut declaration.nested {
            Self::remove_nested(nested, parent_path.clone(), rewritten);
        }
    }

    fn remove_type(
        declaration: &mut KotlinTypeDeclaration,
        owner_path: Vec<KotlinIdentifier>,
        rewritten: &BTreeSet<AccessorKey>,
    ) {
        let owner = KotlinType::Class(KotlinClassType::raw(KotlinClassName::from_identifiers(
            owner_path,
        )));
        declaration.methods.retain(|method| {
            let Some(name) = &method.name else {
                return true;
            };
            !rewritten.contains(&AccessorKey::new(
                owner.clone(),
                name.clone(),
                method.parameters.len(),
            ))
        });
    }
}

struct SuperBridgeRecovery;

impl SuperBridgeRecovery {
    fn apply(declaration: &mut KotlinTypeDeclaration) {
        let mut candidates = BTreeSet::new();
        Self::collect_type(declaration, vec![declaration.name.clone()], &mut candidates);
        for nested in &declaration.nested {
            Self::collect_nested(nested, Vec::new(), &mut candidates);
        }
        if candidates.is_empty() {
            return;
        }
        let mut calls = SuperBridgeCalls {
            candidates: &candidates,
        };
        SyntheticMemberRecovery::rewrite(declaration, &mut calls);
        Self::convert_type(declaration, vec![declaration.name.clone()], &candidates);
        for nested in &mut declaration.nested {
            Self::convert_nested(nested, Vec::new(), &candidates);
        }
    }

    fn collect_nested(
        declaration: &KotlinTypeDeclaration,
        mut parent_path: Vec<KotlinIdentifier>,
        candidates: &mut BTreeSet<AccessorKey>,
    ) {
        parent_path.push(declaration.name.clone());
        Self::collect_type(declaration, parent_path.clone(), candidates);
        for nested in &declaration.nested {
            Self::collect_nested(nested, parent_path.clone(), candidates);
        }
    }

    fn collect_type(
        declaration: &KotlinTypeDeclaration,
        owner_path: Vec<KotlinIdentifier>,
        candidates: &mut BTreeSet<AccessorKey>,
    ) {
        let owner = KotlinType::Class(KotlinClassType::raw(KotlinClassName::from_identifiers(
            owner_path,
        )));
        for method in &declaration.methods {
            let Some(name) = method.name.clone() else {
                continue;
            };
            if !Self::is_bridge(&owner, method)
                || declaration.methods.iter().any(|other| {
                    other.name.as_ref() == Some(&name)
                        && other.parameters.len() + 1 == method.parameters.len()
                })
            {
                continue;
            }
            candidates.insert(AccessorKey::new(
                owner.clone(),
                name,
                method.parameters.len(),
            ));
        }
    }

    fn is_bridge(owner: &KotlinType, method: &KotlinMethodDeclaration) -> bool {
        if !method.compiler_generated
            || method.kind != KotlinMethodDeclarationKind::Method
            || !method.modifiers.contains(&KotlinModifier::Static)
        {
            return false;
        }
        let Some(receiver) = method.parameters.first() else {
            return false;
        };
        if receiver.ty.clone().into_raw() != owner.clone().into_raw() {
            return false;
        }
        let Some(expression) = Self::bridge_expression(method) else {
            return false;
        };
        let KotlinExpr::Call {
            receiver: Some(target),
            ..
        } = FunctionExpression::without_casts(&expression)
        else {
            return false;
        };
        if !matches!(target.as_ref(), KotlinExpr::Super) {
            return false;
        }
        let parameters = method
            .parameters
            .iter()
            .skip(1)
            .map(|parameter| parameter.name.clone())
            .collect::<BTreeSet<_>>();
        ExpressionParameters::used_once_with(&expression, &parameters, true)
    }

    fn bridge_expression(method: &KotlinMethodDeclaration) -> Option<KotlinExpr> {
        FunctionExpression::summary_expression(method).or_else(|| {
            let body = &method.body.as_ref()?.root;
            match body {
                KotlinStmt::Expression(expression) => Some(expression.clone()),
                KotlinStmt::Block(statements) => match statements.as_slice() {
                    [KotlinStmt::Expression(expression)] => Some(expression.clone()),
                    _ => None,
                },
                _ => None,
            }
        })
    }

    fn convert_nested(
        declaration: &mut KotlinTypeDeclaration,
        mut parent_path: Vec<KotlinIdentifier>,
        candidates: &BTreeSet<AccessorKey>,
    ) {
        parent_path.push(declaration.name.clone());
        Self::convert_type(declaration, parent_path.clone(), candidates);
        for nested in &mut declaration.nested {
            Self::convert_nested(nested, parent_path.clone(), candidates);
        }
    }

    fn convert_type(
        declaration: &mut KotlinTypeDeclaration,
        owner_path: Vec<KotlinIdentifier>,
        candidates: &BTreeSet<AccessorKey>,
    ) {
        let owner = KotlinType::Class(KotlinClassType::raw(KotlinClassName::from_identifiers(
            owner_path,
        )));
        for method in &mut declaration.methods {
            let Some(name) = method.name.clone() else {
                continue;
            };
            let key = AccessorKey::new(owner.clone(), name, method.parameters.len());
            if !candidates.contains(&key) {
                continue;
            }
            method
                .modifiers
                .retain(|modifier| *modifier != KotlinModifier::Static);
            method.parameters.remove(0);
        }
    }
}

struct SuperBridgeCalls<'a> {
    candidates: &'a BTreeSet<AccessorKey>,
}

impl KotlinAstRewriter for SuperBridgeCalls<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        let KotlinExpr::Call {
            receiver: None,
            owner: Some(owner),
            type_arguments,
            method,
            mut args,
        } = expression
        else {
            return expression;
        };
        let key = AccessorKey::new(owner.clone(), method.clone(), args.len());
        if !self.candidates.contains(&key) || args.is_empty() {
            return KotlinExpr::Call {
                receiver: None,
                owner: Some(owner),
                type_arguments,
                method,
                args,
            };
        }
        let receiver = args.remove(0);
        KotlinExpr::Call {
            receiver: Some(Box::new(receiver)),
            owner: None,
            type_arguments,
            method,
            args,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct MethodKey {
    name: KotlinIdentifier,
    arity: usize,
}

impl MethodKey {
    fn of(method: &KotlinMethodDeclaration) -> Option<Self> {
        Some(Self {
            name: method.name.clone()?,
            arity: method.parameters.len(),
        })
    }
}

/// Removes expression-bodied compiler artifacts after lambda recovery has
/// consumed their last reference. Anonymous classes are lexical type scopes,
/// so their method reachability can be decided without whole-program guesses.
struct SyntheticFunctionRecovery;

impl SyntheticFunctionRecovery {
    fn apply(declaration: &mut KotlinTypeDeclaration) {
        let mut recovery = Self;
        SyntheticMemberRecovery::rewrite(declaration, &mut recovery);
    }

    fn recover_type(declaration: &mut KotlinTypeDeclaration) {
        let candidates = Self::candidates(&declaration.methods);
        if candidates.is_empty() {
            return;
        }
        let mut references = MethodReferences::new(&candidates);
        SyntheticMemberRecovery::rewrite(declaration, &mut references);
        Self::retain(&mut declaration.methods, &candidates, &references);
    }

    fn recover(body: &mut KotlinAnonymousClassBody) {
        let candidates = Self::candidates(&body.methods);
        if candidates.is_empty() {
            return;
        }
        let mut references = MethodReferences::new(&candidates);
        for field in &mut body.fields {
            field.initializer = field
                .initializer
                .take()
                .map(|value| references.rewrite_expression(value));
        }
        for method in &mut body.methods {
            if let Some(body) = &mut method.body {
                references.rewrite_body(body);
            }
        }
        for nested in &mut body.nested {
            SyntheticMemberRecovery::rewrite(nested, &mut references);
        }
        Self::retain(&mut body.methods, &candidates, &references);
    }

    fn candidates(methods: &[KotlinMethodDeclaration]) -> BTreeSet<MethodKey> {
        methods
            .iter()
            .filter(|method| {
                method.compiler_generated
                    && method.kind == KotlinMethodDeclarationKind::Method
                    // The current compilation unit is a closed world only for
                    // private members. Package-visible synthetic helpers can
                    // be called from another generated class (for example by
                    // bytecode desugaring) and must survive local liveness.
                    && method.modifiers.contains(&KotlinModifier::Private)
                    && FunctionExpression::summary_expression(method).is_some()
            })
            .filter_map(MethodKey::of)
            .collect()
    }

    fn retain(
        methods: &mut Vec<KotlinMethodDeclaration>,
        candidates: &BTreeSet<MethodKey>,
        references: &MethodReferences<'_>,
    ) {
        methods.retain(|method| {
            let Some(key) = MethodKey::of(method) else {
                return true;
            };
            !candidates.contains(&key)
                || references.methods.contains(&key)
                || references.names.contains(&key.name)
        });
    }
}

impl KotlinAstRewriter for SyntheticFunctionRecovery {
    fn finish_anonymous_body(&mut self, body: &mut KotlinAnonymousClassBody) {
        Self::recover(body);
    }

    fn finish_type_declaration(&mut self, declaration: &mut KotlinTypeDeclaration) {
        Self::recover_type(declaration);
    }
}

struct MethodReferences<'a> {
    candidates: &'a BTreeSet<MethodKey>,
    methods: BTreeSet<MethodKey>,
    names: BTreeSet<KotlinIdentifier>,
}

impl<'a> MethodReferences<'a> {
    fn new(candidates: &'a BTreeSet<MethodKey>) -> Self {
        Self {
            candidates,
            methods: BTreeSet::new(),
            names: BTreeSet::new(),
        }
    }
}

impl KotlinAstRewriter for MethodReferences<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match &expression {
            KotlinExpr::Call { method, args, .. } => {
                let key = MethodKey {
                    name: method.clone(),
                    arity: args.len(),
                };
                if self.candidates.contains(&key) {
                    self.methods.insert(key);
                }
            }
            KotlinExpr::MethodReference { method, .. } => {
                if self
                    .candidates
                    .iter()
                    .any(|candidate| candidate.name == *method)
                {
                    self.names.insert(method.clone());
                }
            }
            _ => {}
        }
        expression
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct AccessorKey {
    owner: String,
    method: KotlinIdentifier,
    arity: usize,
}

impl AccessorKey {
    fn new(owner: KotlinType, method: KotlinIdentifier, arity: usize) -> Self {
        Self {
            owner: owner.to_string(),
            method,
            arity,
        }
    }
}

#[derive(Default)]
struct MethodContractCatalog {
    methods: BTreeMap<AccessorKey, MethodContract>,
    collisions: BTreeSet<AccessorKey>,
}

struct MethodContract {
    parameters: Vec<KotlinType>,
    inference_variables: BTreeSet<KotlinIdentifier>,
}

impl MethodContract {
    fn parameter_requires_inference(&self, ty: &KotlinType) -> bool {
        let mut pending = vec![ty];
        while let Some(ty) = pending.pop() {
            match ty {
                KotlinType::Variable(variable) => {
                    if self.inference_variables.contains(variable) {
                        return true;
                    }
                }
                KotlinType::Array(element) => pending.push(element),
                KotlinType::Class(class) => {
                    pending.extend(class.segments.iter().flat_map(|segment| {
                        segment
                            .arguments
                            .iter()
                            .filter_map(|argument| match argument {
                                crate::language::kotlin::KotlinTypeArgument::Any => None,
                                crate::language::kotlin::KotlinTypeArgument::Exact(ty)
                                | crate::language::kotlin::KotlinTypeArgument::Extends(ty)
                                | crate::language::kotlin::KotlinTypeArgument::Super(ty) => {
                                    Some(ty)
                                }
                            })
                    }));
                }
                KotlinType::Primitive(_) => {}
            }
        }
        false
    }
}

impl MethodContractCatalog {
    fn collect(declaration: &KotlinTypeDeclaration) -> Self {
        let mut catalog = Self::default();
        catalog.collect_type(declaration, vec![declaration.name.clone()]);
        for nested in &declaration.nested {
            catalog.collect_nested(nested, Vec::new());
        }
        for collision in &catalog.collisions {
            catalog.methods.remove(collision);
        }
        catalog
    }

    fn collect_nested(
        &mut self,
        declaration: &KotlinTypeDeclaration,
        mut parent_path: Vec<KotlinIdentifier>,
    ) {
        parent_path.push(declaration.name.clone());
        self.collect_type(declaration, parent_path.clone());
        for nested in &declaration.nested {
            self.collect_nested(nested, parent_path.clone());
        }
    }

    fn collect_type(
        &mut self,
        declaration: &KotlinTypeDeclaration,
        owner_path: Vec<KotlinIdentifier>,
    ) {
        let owner = KotlinType::Class(KotlinClassType::raw(KotlinClassName::from_identifiers(
            owner_path,
        )));
        for method in &declaration.methods {
            let Some(name) = method.name.clone() else {
                continue;
            };
            let key = AccessorKey::new(owner.clone(), name, method.parameters.len());
            let contract = MethodContract {
                parameters: method
                    .parameters
                    .iter()
                    .map(|parameter| parameter.ty.clone())
                    .collect(),
                inference_variables: method
                    .type_parameters
                    .iter()
                    .map(|parameter| parameter.name.clone())
                    .collect(),
            };
            if self.methods.insert(key.clone(), contract).is_some() {
                self.collisions.insert(key);
            }
        }
    }

    fn argument_conversions(
        &self,
        lexical_owner: &KotlinType,
        expression: &KotlinExpr,
        accessor_parameters: &[AccessorParameter],
    ) -> BTreeMap<KotlinIdentifier, KotlinType> {
        let KotlinExpr::Call {
            receiver,
            owner,
            method,
            args,
            ..
        } = expression
        else {
            return BTreeMap::new();
        };
        let target_owner = owner
            .as_ref()
            .or_else(|| receiver.as_ref().map(|_| lexical_owner));
        let Some(target_owner) = target_owner else {
            return BTreeMap::new();
        };
        let key = AccessorKey::new(target_owner.clone(), method.clone(), args.len());
        let Some(contract) = self.methods.get(&key) else {
            return BTreeMap::new();
        };
        args.iter()
            .zip(&contract.parameters)
            .filter_map(|(argument, target)| {
                // An explicit conversion in the recovered accessor body is
                // already the complete adaptation for this call. Inferring a
                // second conversion from the callee declaration can leak the
                // callee's inference variables into the accessor caller.
                let KotlinExpr::Name(name) = argument else {
                    return None;
                };
                if contract.parameter_requires_inference(target) {
                    return None;
                }
                let parameter = accessor_parameters
                    .iter()
                    .find(|parameter| parameter.name == *name)?;
                (parameter.ty != *target).then(|| (name.clone(), target.clone()))
            })
            .collect()
    }
}

struct Accessor {
    key: AccessorKey,
    parameters: Vec<AccessorParameter>,
    conversions: BTreeMap<KotlinIdentifier, KotlinType>,
    expression: KotlinExpr,
}

struct AccessorParameter {
    name: KotlinIdentifier,
    ty: KotlinType,
}

impl Accessor {
    fn analyze(
        owner: KotlinType,
        method: &KotlinMethodDeclaration,
        contracts: &MethodContractCatalog,
    ) -> Option<Self> {
        if !method.compiler_generated
            || method.kind != KotlinMethodDeclarationKind::Method
            || !method.modifiers.contains(&KotlinModifier::Static)
            || method.modifiers.iter().any(|modifier| {
                matches!(
                    modifier,
                    KotlinModifier::Public | KotlinModifier::Private | KotlinModifier::Protected
                )
            })
        {
            return None;
        }
        let name = method.name.clone()?;
        let expression = FunctionExpression::summary_expression(method)?;
        let parameters = method
            .parameters
            .iter()
            .map(|parameter| AccessorParameter {
                name: parameter.name.clone(),
                ty: parameter.ty.clone(),
            })
            .collect::<Vec<_>>();
        if !LexicalMemberAccess::matches(&owner, method, &expression) {
            return None;
        }
        let allowed = parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect::<BTreeSet<_>>();
        if !ExpressionParameters::used_once(&expression, &allowed) {
            return None;
        }
        let mut conversions = match &expression {
            KotlinExpr::Assignment { value, .. } => {
                match FunctionExpression::without_casts(value.as_ref()) {
                    KotlinExpr::Name(name) => BTreeMap::from([(
                        name.clone(),
                        parameters
                            .iter()
                            .find(|parameter| &parameter.name == name)?
                            .ty
                            .clone(),
                    )]),
                    _ => BTreeMap::new(),
                }
            }
            _ => BTreeMap::new(),
        };
        conversions.extend(contracts.argument_conversions(&owner, &expression, &parameters));
        Some(Self {
            key: AccessorKey::new(owner, name, parameters.len()),
            parameters,
            conversions,
            expression,
        })
    }
}

struct LexicalMemberAccess;

impl LexicalMemberAccess {
    fn matches(
        owner: &KotlinType,
        method: &KotlinMethodDeclaration,
        expression: &KotlinExpr,
    ) -> bool {
        let owner_name = owner.to_string();
        let expression = Self::without_cast(expression);
        let receiver_parameter = method
            .parameters
            .first()
            .filter(|parameter| parameter.ty.clone().into_raw().to_string() == owner_name);
        match expression {
            KotlinExpr::Assignment { target, .. } => Self::matches(owner, method, target),
            KotlinExpr::Field { owner: receiver, .. } => receiver_parameter.is_some_and(
                |parameter| matches!(receiver.as_ref(), KotlinExpr::Name(name) if name == &parameter.name),
            ),
            KotlinExpr::StaticField { owner, .. } => owner.to_string() == owner_name,
            KotlinExpr::Call {
                receiver: Some(receiver),
                ..
            } => receiver_parameter.is_some_and(
                |parameter| matches!(receiver.as_ref(), KotlinExpr::Name(name) if name == &parameter.name),
            ),
            KotlinExpr::Call {
                receiver: None,
                owner: Some(target),
                ..
            } => target.to_string() == owner_name,
            _ => false,
        }
    }

    fn without_cast(mut expression: &KotlinExpr) -> &KotlinExpr {
        while let KotlinExpr::Cast { value, .. } = expression {
            expression = value;
        }
        expression
    }
}

struct AccessorInliner<'a> {
    candidates: &'a BTreeMap<AccessorKey, Accessor>,
    rewritten: BTreeMap<AccessorKey, usize>,
}

impl KotlinAstRewriter for AccessorInliner<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        let KotlinExpr::Call {
            receiver: None,
            owner: Some(owner),
            type_arguments,
            method,
            args,
        } = expression
        else {
            return expression;
        };
        let key = AccessorKey::new(owner.clone(), method.clone(), args.len());
        let Some(accessor) = self.candidates.get(&key) else {
            return KotlinExpr::Call {
                receiver: None,
                owner: Some(owner),
                type_arguments,
                method,
                args,
            };
        };
        let values = accessor
            .parameters
            .iter()
            .zip(args)
            .map(|(parameter, value)| {
                let conversion = accessor.conversions.get(&parameter.name).filter(|target| {
                    !matches!(
                        &value,
                        KotlinExpr::Literal(crate::language::kotlin::KotlinLiteral::Null)
                    ) && !matches!(target, KotlinType::Primitive(_))
                });
                let value = match conversion {
                    Some(target) => KotlinExpr::Cast {
                        ty: target.clone(),
                        value: Box::new(value),
                    },
                    None => value,
                };
                (parameter.name.clone(), value)
            })
            .collect::<BTreeMap<_, _>>();
        let mut substitution = ParameterSubstitution { values };
        *self.rewritten.entry(key).or_default() += 1;
        substitution.rewrite_expression(accessor.expression.clone())
    }
}

struct AccessorReferences<'a> {
    candidates: &'a BTreeMap<AccessorKey, Accessor>,
    counts: BTreeMap<AccessorKey, usize>,
}

impl KotlinAstRewriter for AccessorReferences<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if let KotlinExpr::Call {
            receiver: None,
            owner: Some(owner),
            method,
            args,
            ..
        } = &expression
        {
            let key = AccessorKey::new(owner.clone(), method.clone(), args.len());
            if self.candidates.contains_key(&key) {
                *self.counts.entry(key).or_default() += 1;
            }
        }
        expression
    }
}

struct ParameterSubstitution {
    values: BTreeMap<KotlinIdentifier, KotlinExpr>,
}

impl KotlinAstRewriter for ParameterSubstitution {
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

struct ExpressionParameters;

impl ExpressionParameters {
    fn used_once(expression: &KotlinExpr, parameters: &BTreeSet<KotlinIdentifier>) -> bool {
        Self::used_once_with(expression, parameters, false)
    }

    fn used_once_with(
        expression: &KotlinExpr,
        parameters: &BTreeSet<KotlinIdentifier>,
        allow_super: bool,
    ) -> bool {
        let mut uses = parameters
            .iter()
            .cloned()
            .map(|parameter| (parameter, 0usize))
            .collect::<BTreeMap<_, _>>();
        let mut pending = vec![expression];
        while let Some(expression) = pending.pop() {
            match expression {
                KotlinExpr::Name(name) => {
                    let Some(count) = uses.get_mut(name) else {
                        return false;
                    };
                    *count += 1;
                }
                KotlinExpr::Super if allow_super => {}
                KotlinExpr::This | KotlinExpr::QualifiedThis(_) | KotlinExpr::Super => {
                    return false
                }
                KotlinExpr::Literal(_)
                | KotlinExpr::ClassLiteral(_)
                | KotlinExpr::ObjectReference(_)
                | KotlinExpr::StaticField { .. } => {}
                KotlinExpr::SmartCast(value)
                | KotlinExpr::NonNullAssertion(value)
                | KotlinExpr::JvmIntrinsic {
                    expression: value, ..
                } => pending.push(value),
                KotlinExpr::Field { owner, .. } => pending.push(owner),
                KotlinExpr::ArrayAccess { array, index } => {
                    pending.push(index);
                    pending.push(array);
                }
                KotlinExpr::Call { receiver, args, .. } => {
                    pending.extend(args.iter().rev());
                    pending.extend(receiver.iter().map(|value| value.as_ref()));
                }
                KotlinExpr::MethodReference { receiver, .. } => pending.push(receiver),
                KotlinExpr::Lambda { body, .. } => pending.push(body),
                KotlinExpr::BlockLambda { .. } => return false,
                KotlinExpr::New {
                    enclosing, args, ..
                } => {
                    pending.extend(args.iter().rev());
                    pending.extend(enclosing.iter().map(|value| value.as_ref()));
                }
                KotlinExpr::NewArray {
                    dimensions,
                    initializer,
                    ..
                } => {
                    pending.extend(initializer.iter().rev());
                    pending.extend(dimensions.iter().rev());
                }
                KotlinExpr::Unary { operand, .. }
                | KotlinExpr::Cast { value: operand, .. }
                | KotlinExpr::InstanceOf { value: operand, .. } => pending.push(operand),
                KotlinExpr::Update { target, .. } => pending.push(target),
                KotlinExpr::Binary { left, right, .. } => {
                    pending.push(right);
                    pending.push(left);
                }
                KotlinExpr::Conditional {
                    condition,
                    when_true,
                    when_false,
                } => {
                    pending.push(when_false);
                    pending.push(when_true);
                    pending.push(condition);
                }
                KotlinExpr::Assignment { target, value, .. } => {
                    pending.push(value);
                    pending.push(target);
                }
            }
        }
        uses.into_values().all(|count| count == 1)
    }
}
