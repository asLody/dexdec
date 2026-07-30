//! Lexically minimal placement of Kotlin local declarations.

use std::collections::BTreeMap;

use super::{
    KotlinAssignOp, KotlinAstTransform, KotlinExpr, KotlinIdentifier, KotlinMethodBody, KotlinStmt,
    KotlinType,
};

#[derive(Debug, Default)]
pub struct LexicalDeclarationPlacement;

impl KotlinAstTransform for LexicalDeclarationPlacement {
    type Error = super::KotlinStructuralError;

    fn apply(&mut self, body: &mut KotlinMethodBody) -> Result<bool, Self::Error> {
        let inventory = DeclarationInventory::extract(&mut body.root);
        if inventory.is_empty() {
            return Ok(false);
        }
        let analysis = LexicalReferenceAnalysis::analyze(&body.root);
        DeclarationRewriter::new(DeclarationPlan::build(inventory, &analysis))
            .apply(&mut body.root);
        Ok(true)
    }
}

#[derive(Debug, Default)]
struct DeclarationInventory(BTreeMap<KotlinIdentifier, KotlinType>);

impl DeclarationInventory {
    fn extract(root: &mut KotlinStmt) -> Self {
        let KotlinStmt::Block(statements) = root else {
            return Self::default();
        };
        let mut inventory = BTreeMap::new();
        statements.retain(|statement| match statement {
            KotlinStmt::Variable {
                ty,
                name,
                value: None,
                ..
            } => {
                inventory.insert(name.clone(), ty.clone());
                false
            }
            _ => true,
        });
        Self(inventory)
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ScopeId(usize);

#[derive(Debug, Clone, Copy)]
struct ReferenceSite {
    scope: ScopeId,
    statement: usize,
    event: usize,
}

#[derive(Debug)]
struct LexicalScope {
    parent: Option<ScopeId>,
    owner_statement: Option<usize>,
    depth: usize,
}

#[derive(Debug)]
struct LexicalReferenceAnalysis {
    scopes: Vec<LexicalScope>,
    references: BTreeMap<KotlinIdentifier, Vec<ReferenceSite>>,
    next_event: usize,
}

impl LexicalReferenceAnalysis {
    fn analyze(root: &KotlinStmt) -> Self {
        let mut analysis = Self {
            scopes: vec![LexicalScope {
                parent: None,
                owner_statement: None,
                depth: 0,
            }],
            references: BTreeMap::new(),
            next_event: 0,
        };
        if let KotlinStmt::Block(statements) = root {
            analysis.block(statements, ScopeId(0));
        }
        analysis
    }

    fn block(&mut self, statements: &[KotlinStmt], scope: ScopeId) {
        for (index, statement) in statements.iter().enumerate() {
            self.statement(statement, scope, index);
        }
    }

    fn statement(&mut self, statement: &KotlinStmt, scope: ScopeId, index: usize) {
        let site = self.site(scope, index);
        match statement {
            KotlinStmt::Empty | KotlinStmt::Break(_) | KotlinStmt::Continue(_) => {}
            KotlinStmt::Block(statements) => self.child_block(statements, scope, index),
            KotlinStmt::Labeled { body, .. } => self.body(body, scope, index),
            KotlinStmt::Variable { value, .. } => self.optional_expression(value.as_ref(), site),
            KotlinStmt::Expression(expression) | KotlinStmt::Throw(expression) => {
                self.expression(expression, site);
            }
            KotlinStmt::ConstructorInvocation { args, .. } => self.expressions(args, site),
            KotlinStmt::Assign { target, op, value } => {
                self.assignment(target, *op, value, site);
            }
            KotlinStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => {
                self.expression(condition, site);
                self.body(then_stmt, scope, index);
                if let Some(else_stmt) = else_stmt {
                    self.body(else_stmt, scope, index);
                }
            }
            KotlinStmt::While {
                condition, body, ..
            } => {
                self.expression(condition, site);
                self.body(body, scope, index);
            }
            KotlinStmt::DoWhile {
                body, condition, ..
            } => {
                self.body(body, scope, index);
                self.expression(condition, site);
            }
            KotlinStmt::For {
                init,
                condition,
                update,
                body,
                ..
            } => {
                for initializer in init {
                    self.inline_statement(initializer, site);
                }
                self.optional_expression(condition.as_ref(), site);
                self.expressions(update, site);
                self.body(body, scope, index);
            }
            KotlinStmt::ForEach { iterable, body, .. } => {
                self.expression(iterable, site);
                self.body(body, scope, index);
            }
            KotlinStmt::Switch {
                selector, cases, ..
            } => {
                self.expression(selector, site);
                for case in cases {
                    self.expressions(&case.labels, site);
                    let child = self.new_scope(scope, index);
                    self.block(&case.body, child);
                }
            }
            KotlinStmt::Try {
                body,
                catches,
                finally,
            } => {
                self.body(body, scope, index);
                for catch in catches {
                    self.body(&catch.body, scope, index);
                }
                if let Some(finally) = finally {
                    self.body(finally, scope, index);
                }
            }
            KotlinStmt::Synchronized { lock, body } => {
                self.expression(lock, site);
                self.body(body, scope, index);
            }
            KotlinStmt::Return(value) => self.optional_expression(value.as_ref(), site),
        }
    }

    fn body(&mut self, body: &KotlinStmt, parent: ScopeId, owner: usize) {
        match body {
            KotlinStmt::Block(statements) => self.child_block(statements, parent, owner),
            statement => self.statement(statement, parent, owner),
        }
    }

    fn child_block(&mut self, statements: &[KotlinStmt], parent: ScopeId, owner: usize) {
        let child = self.new_scope(parent, owner);
        self.block(statements, child);
    }

    fn new_scope(&mut self, parent: ScopeId, owner_statement: usize) -> ScopeId {
        let id = ScopeId(self.scopes.len());
        self.scopes.push(LexicalScope {
            parent: Some(parent),
            owner_statement: Some(owner_statement),
            depth: self.scopes[parent.0].depth + 1,
        });
        id
    }

    fn inline_statement(&mut self, statement: &KotlinStmt, site: ReferenceSite) {
        match statement {
            KotlinStmt::Variable { value, .. } => self.optional_expression(value.as_ref(), site),
            KotlinStmt::Assign { target, op, value } => self.assignment(target, *op, value, site),
            KotlinStmt::Expression(expression) => self.expression(expression, site),
            _ => {}
        }
    }

    fn assignment(
        &mut self,
        target: &KotlinExpr,
        op: KotlinAssignOp,
        value: &KotlinExpr,
        site: ReferenceSite,
    ) {
        match target {
            KotlinExpr::Name(name) => {
                self.reference(name, site);
                if op != KotlinAssignOp::Assign {
                    self.reference(name, site);
                }
            }
            target => self.expression(target, site),
        }
        self.expression(value, site);
    }

    fn optional_expression(&mut self, expression: Option<&KotlinExpr>, site: ReferenceSite) {
        if let Some(expression) = expression {
            self.expression(expression, site);
        }
    }

    fn expressions(&mut self, expressions: &[KotlinExpr], site: ReferenceSite) {
        for expression in expressions {
            self.expression(expression, site);
        }
    }

    fn expression(&mut self, root: &KotlinExpr, site: ReferenceSite) {
        let mut pending = vec![root];
        while let Some(expression) = pending.pop() {
            match expression {
                KotlinExpr::This
                | KotlinExpr::QualifiedThis(_)
                | KotlinExpr::Super
                | KotlinExpr::Literal(_)
                | KotlinExpr::ClassLiteral(_)
                | KotlinExpr::ObjectReference(_)
                | KotlinExpr::StaticField { .. } => {}
                KotlinExpr::Name(name) => self.reference(name, site),
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
                KotlinExpr::BlockLambda { body, .. } => {
                    self.statement(body, site.scope, site.statement);
                }
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
    }

    fn reference(&mut self, name: &KotlinIdentifier, site: ReferenceSite) {
        self.references.entry(name.clone()).or_default().push(site);
    }

    fn site(&mut self, scope: ScopeId, statement: usize) -> ReferenceSite {
        let site = ReferenceSite {
            scope,
            statement,
            event: self.next_event,
        };
        self.next_event += 1;
        site
    }

    fn common_scope(&self, references: &[ReferenceSite]) -> ScopeId {
        references
            .iter()
            .skip(1)
            .fold(references[0].scope, |scope, reference| {
                self.scope_lca(scope, reference.scope)
            })
    }

    fn scope_lca(&self, mut left: ScopeId, mut right: ScopeId) -> ScopeId {
        while self.scopes[left.0].depth > self.scopes[right.0].depth {
            left = self.scopes[left.0].parent.unwrap_or(ScopeId(0));
        }
        while self.scopes[right.0].depth > self.scopes[left.0].depth {
            right = self.scopes[right.0].parent.unwrap_or(ScopeId(0));
        }
        while left != right {
            left = self.scopes[left.0].parent.unwrap_or(ScopeId(0));
            right = self.scopes[right.0].parent.unwrap_or(ScopeId(0));
        }
        left
    }

    fn insertion_index(&self, scope: ScopeId, reference: ReferenceSite) -> usize {
        if reference.scope == scope {
            return reference.statement;
        }
        let mut current = reference.scope;
        loop {
            let lexical = &self.scopes[current.0];
            if lexical.parent == Some(scope) {
                return lexical.owner_statement.unwrap_or(reference.statement);
            }
            current = lexical.parent.unwrap_or(scope);
            if current == scope {
                return reference.statement;
            }
        }
    }
}

#[derive(Debug)]
struct DeclarationPlacement {
    name: KotlinIdentifier,
    ty: KotlinType,
    statement: usize,
    order: usize,
    for_inline: bool,
}

#[derive(Debug, Default)]
struct DeclarationPlan {
    scopes: BTreeMap<ScopeId, Vec<DeclarationPlacement>>,
}

impl DeclarationPlan {
    fn build(inventory: DeclarationInventory, analysis: &LexicalReferenceAnalysis) -> Self {
        let mut plan = Self::default();
        for (name, ty) in inventory.0 {
            let Some(references) = analysis
                .references
                .get(&name)
                .filter(|refs| !refs.is_empty())
            else {
                continue;
            };
            let scope = analysis.common_scope(references);
            let statement = references
                .iter()
                .map(|reference| analysis.insertion_index(scope, *reference))
                .min()
                .unwrap_or(0);
            let order = references
                .iter()
                .map(|reference| reference.event)
                .min()
                .unwrap_or(0);
            let for_inline = references
                .iter()
                .all(|reference| analysis.insertion_index(scope, *reference) == statement);
            plan.scopes
                .entry(scope)
                .or_default()
                .push(DeclarationPlacement {
                    name,
                    ty,
                    statement,
                    order,
                    for_inline,
                });
        }
        plan
    }
}

struct DeclarationRewriter {
    plan: DeclarationPlan,
    next_scope: usize,
}

impl DeclarationRewriter {
    fn new(plan: DeclarationPlan) -> Self {
        Self {
            plan,
            next_scope: 1,
        }
    }

    fn apply(&mut self, root: &mut KotlinStmt) {
        if let KotlinStmt::Block(statements) = root {
            self.block(statements, ScopeId(0));
        }
    }

    fn block(&mut self, statements: &mut Vec<KotlinStmt>, scope: ScopeId) {
        for statement in statements.iter_mut() {
            self.statement(statement);
        }
        let mut placements = self.plan.scopes.remove(&scope).unwrap_or_default();
        placements.sort_by(|left, right| {
            right
                .statement
                .cmp(&left.statement)
                .then_with(|| left.order.cmp(&right.order))
        });
        while let Some(index) = placements.first().map(|placement| placement.statement) {
            let count = placements
                .iter()
                .take_while(|placement| placement.statement == index)
                .count();
            let group = placements.drain(..count).collect();
            Self::place(statements, index.min(statements.len()), group);
        }
    }

    fn statement(&mut self, statement: &mut KotlinStmt) {
        match statement {
            KotlinStmt::Block(statements) => {
                let scope = self.child_scope();
                self.block(statements, scope);
            }
            KotlinStmt::Labeled { body, .. }
            | KotlinStmt::While { body, .. }
            | KotlinStmt::DoWhile { body, .. }
            | KotlinStmt::For { body, .. }
            | KotlinStmt::ForEach { body, .. }
            | KotlinStmt::Synchronized { body, .. } => self.body(body),
            KotlinStmt::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                self.body(then_stmt);
                if let Some(else_stmt) = else_stmt {
                    self.body(else_stmt);
                }
            }
            KotlinStmt::Switch { cases, .. } => {
                for case in cases {
                    let scope = self.child_scope();
                    self.block(&mut case.body, scope);
                }
            }
            KotlinStmt::Try {
                body,
                catches,
                finally,
            } => {
                self.body(body);
                for catch in catches {
                    self.body(&mut catch.body);
                }
                if let Some(finally) = finally {
                    self.body(finally);
                }
            }
            KotlinStmt::Empty
            | KotlinStmt::Variable { .. }
            | KotlinStmt::Expression(_)
            | KotlinStmt::ConstructorInvocation { .. }
            | KotlinStmt::Assign { .. }
            | KotlinStmt::Return(_)
            | KotlinStmt::Throw(_)
            | KotlinStmt::Break(_)
            | KotlinStmt::Continue(_) => {}
        }
    }

    fn body(&mut self, body: &mut KotlinStmt) {
        if let KotlinStmt::Block(statements) = body {
            let scope = self.child_scope();
            self.block(statements, scope);
        } else {
            self.statement(body);
        }
    }

    fn child_scope(&mut self) -> ScopeId {
        let scope = ScopeId(self.next_scope);
        self.next_scope += 1;
        scope
    }

    fn place(
        statements: &mut Vec<KotlinStmt>,
        index: usize,
        placements: Vec<DeclarationPlacement>,
    ) {
        let direct_inline = statements.get(index).and_then(|statement| {
            placements
                .iter()
                .position(|placement| Self::can_inline(statement, &placement.name))
        });
        let for_inline = direct_inline
            .is_none()
            .then(|| {
                statements.get(index).and_then(|statement| {
                    placements.iter().position(|placement| {
                        placement.for_inline && Self::can_inline_for(statement, &placement.name)
                    })
                })
            })
            .flatten();
        let mut declarations = Vec::new();
        for (placement_index, placement) in placements.into_iter().enumerate() {
            if Some(placement_index) == direct_inline {
                let value = match std::mem::replace(&mut statements[index], KotlinStmt::Empty) {
                    KotlinStmt::Assign { value, .. } => value,
                    statement => {
                        statements[index] = statement;
                        continue;
                    }
                };
                statements[index] = KotlinStmt::Variable {
                    binding: Default::default(),
                    ty: placement.ty,
                    name: placement.name,
                    value: Some(value),
                };
            } else if Some(placement_index) == for_inline {
                if let KotlinStmt::For { init, .. } = &mut statements[index] {
                    let value = match std::mem::replace(&mut init[0], KotlinStmt::Empty) {
                        KotlinStmt::Assign { value, .. } => value,
                        initializer => {
                            init[0] = initializer;
                            continue;
                        }
                    };
                    init[0] = KotlinStmt::Variable {
                        binding: Default::default(),
                        ty: placement.ty,
                        name: placement.name,
                        value: Some(value),
                    };
                }
            } else {
                declarations.push(KotlinStmt::Variable {
                    binding: Default::default(),
                    ty: placement.ty,
                    name: placement.name,
                    value: None,
                });
            }
        }
        statements.splice(index..index, declarations);
    }

    fn can_inline(statement: &KotlinStmt, name: &KotlinIdentifier) -> bool {
        let KotlinStmt::Assign {
            target: KotlinExpr::Name(target),
            op: KotlinAssignOp::Assign,
            value,
        } = statement
        else {
            return false;
        };
        target == name && !ExpressionNames::contains(value, name)
    }

    fn can_inline_for(statement: &KotlinStmt, name: &KotlinIdentifier) -> bool {
        let KotlinStmt::For { init, .. } = statement else {
            return false;
        };
        matches!(init.as_slice(), [initializer] if Self::can_inline(initializer, name))
    }
}

struct ExpressionNames;

impl ExpressionNames {
    fn contains(root: &KotlinExpr, expected: &KotlinIdentifier) -> bool {
        let mut pending = vec![root];
        while let Some(expression) = pending.pop() {
            match expression {
                KotlinExpr::Name(name) if name == expected => return true,
                KotlinExpr::This
                | KotlinExpr::QualifiedThis(_)
                | KotlinExpr::Super
                | KotlinExpr::Name(_)
                | KotlinExpr::Literal(_)
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
                KotlinExpr::BlockLambda { .. } => return true,
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
        false
    }
}
