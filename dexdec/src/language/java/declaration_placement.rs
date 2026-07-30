//! Lexically minimal placement of Java local declarations.

use std::collections::BTreeMap;

use super::{
    JavaAssignOp, JavaAstTransform, JavaExpr, JavaIdentifier, JavaMethodBody, JavaStmt, JavaType,
};

#[derive(Debug, Default)]
pub struct LexicalDeclarationPlacement;

impl JavaAstTransform for LexicalDeclarationPlacement {
    type Error = super::JavaStructuralError;

    fn apply(&mut self, body: &mut JavaMethodBody) -> Result<bool, Self::Error> {
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
struct DeclarationInventory(BTreeMap<JavaIdentifier, JavaType>);

impl DeclarationInventory {
    fn extract(root: &mut JavaStmt) -> Self {
        let JavaStmt::Block(statements) = root else {
            return Self::default();
        };
        let mut inventory = BTreeMap::new();
        statements.retain(|statement| match statement {
            JavaStmt::Variable {
                ty,
                name,
                value: None,
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
    references: BTreeMap<JavaIdentifier, Vec<ReferenceSite>>,
    next_event: usize,
}

impl LexicalReferenceAnalysis {
    fn analyze(root: &JavaStmt) -> Self {
        let mut analysis = Self {
            scopes: vec![LexicalScope {
                parent: None,
                owner_statement: None,
                depth: 0,
            }],
            references: BTreeMap::new(),
            next_event: 0,
        };
        if let JavaStmt::Block(statements) = root {
            analysis.block(statements, ScopeId(0));
        }
        analysis
    }

    fn block(&mut self, statements: &[JavaStmt], scope: ScopeId) {
        for (index, statement) in statements.iter().enumerate() {
            self.statement(statement, scope, index);
        }
    }

    fn statement(&mut self, statement: &JavaStmt, scope: ScopeId, index: usize) {
        let site = self.site(scope, index);
        match statement {
            JavaStmt::Empty | JavaStmt::Break(_) | JavaStmt::Continue(_) => {}
            JavaStmt::Block(statements) => self.child_block(statements, scope, index),
            JavaStmt::Labeled { body, .. } => self.body(body, scope, index),
            JavaStmt::Variable { value, .. } => self.optional_expression(value.as_ref(), site),
            JavaStmt::Expression(expression) | JavaStmt::Throw(expression) => {
                self.expression(expression, site);
            }
            JavaStmt::ConstructorInvocation { args, .. } => self.expressions(args, site),
            JavaStmt::Assign { target, op, value } => {
                self.assignment(target, *op, value, site);
            }
            JavaStmt::If {
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
            JavaStmt::While {
                condition, body, ..
            } => {
                self.expression(condition, site);
                self.body(body, scope, index);
            }
            JavaStmt::DoWhile {
                body, condition, ..
            } => {
                self.body(body, scope, index);
                self.expression(condition, site);
            }
            JavaStmt::For {
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
            JavaStmt::ForEach { iterable, body, .. } => {
                self.expression(iterable, site);
                self.body(body, scope, index);
            }
            JavaStmt::Switch {
                selector, cases, ..
            } => {
                self.expression(selector, site);
                for case in cases {
                    self.expressions(&case.labels, site);
                    let child = self.new_scope(scope, index);
                    self.block(&case.body, child);
                }
            }
            JavaStmt::Try {
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
            JavaStmt::Synchronized { lock, body } => {
                self.expression(lock, site);
                self.body(body, scope, index);
            }
            JavaStmt::Return(value) => self.optional_expression(value.as_ref(), site),
        }
    }

    fn body(&mut self, body: &JavaStmt, parent: ScopeId, owner: usize) {
        match body {
            JavaStmt::Block(statements) => self.child_block(statements, parent, owner),
            statement => self.statement(statement, parent, owner),
        }
    }

    fn child_block(&mut self, statements: &[JavaStmt], parent: ScopeId, owner: usize) {
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

    fn inline_statement(&mut self, statement: &JavaStmt, site: ReferenceSite) {
        match statement {
            JavaStmt::Variable { value, .. } => self.optional_expression(value.as_ref(), site),
            JavaStmt::Assign { target, op, value } => self.assignment(target, *op, value, site),
            JavaStmt::Expression(expression) => self.expression(expression, site),
            _ => {}
        }
    }

    fn assignment(
        &mut self,
        target: &JavaExpr,
        op: JavaAssignOp,
        value: &JavaExpr,
        site: ReferenceSite,
    ) {
        match target {
            JavaExpr::Name(name) => {
                self.reference(name, site);
                if op != JavaAssignOp::Assign {
                    self.reference(name, site);
                }
            }
            target => self.expression(target, site),
        }
        self.expression(value, site);
    }

    fn optional_expression(&mut self, expression: Option<&JavaExpr>, site: ReferenceSite) {
        if let Some(expression) = expression {
            self.expression(expression, site);
        }
    }

    fn expressions(&mut self, expressions: &[JavaExpr], site: ReferenceSite) {
        for expression in expressions {
            self.expression(expression, site);
        }
    }

    fn expression(&mut self, root: &JavaExpr, site: ReferenceSite) {
        let mut pending = vec![root];
        while let Some(expression) = pending.pop() {
            match expression {
                JavaExpr::This
                | JavaExpr::QualifiedThis(_)
                | JavaExpr::Super
                | JavaExpr::Literal(_)
                | JavaExpr::ClassLiteral(_)
                | JavaExpr::StaticField { .. } => {}
                JavaExpr::Name(name) => self.reference(name, site),
                JavaExpr::Field { owner, .. } => pending.push(owner),
                JavaExpr::ArrayAccess { array, index } => {
                    pending.push(index);
                    pending.push(array);
                }
                JavaExpr::Call { receiver, args, .. } => {
                    pending.extend(args.iter().rev());
                    pending.extend(receiver.iter().map(|value| value.as_ref()));
                }
                JavaExpr::MethodReference { receiver, .. } => pending.push(receiver),
                JavaExpr::Lambda { body, .. } => pending.push(body),
                JavaExpr::BlockLambda { body, .. } => {
                    self.statement(body, site.scope, site.statement);
                }
                JavaExpr::New {
                    enclosing, args, ..
                } => {
                    pending.extend(args.iter().rev());
                    pending.extend(enclosing.iter().map(|value| value.as_ref()));
                }
                JavaExpr::NewArray {
                    dimensions,
                    initializer,
                    ..
                } => {
                    pending.extend(initializer.iter().rev());
                    pending.extend(dimensions.iter().rev());
                }
                JavaExpr::Unary { operand, .. }
                | JavaExpr::Cast { value: operand, .. }
                | JavaExpr::InstanceOf { value: operand, .. } => pending.push(operand),
                JavaExpr::Update { target, .. } => pending.push(target),
                JavaExpr::Binary { left, right, .. } => {
                    pending.push(right);
                    pending.push(left);
                }
                JavaExpr::Conditional {
                    condition,
                    when_true,
                    when_false,
                } => {
                    pending.push(when_false);
                    pending.push(when_true);
                    pending.push(condition);
                }
                JavaExpr::Assignment { target, value, .. } => {
                    pending.push(value);
                    pending.push(target);
                }
            }
        }
    }

    fn reference(&mut self, name: &JavaIdentifier, site: ReferenceSite) {
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
    name: JavaIdentifier,
    ty: JavaType,
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

    fn apply(&mut self, root: &mut JavaStmt) {
        if let JavaStmt::Block(statements) = root {
            self.block(statements, ScopeId(0));
        }
    }

    fn block(&mut self, statements: &mut Vec<JavaStmt>, scope: ScopeId) {
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

    fn statement(&mut self, statement: &mut JavaStmt) {
        match statement {
            JavaStmt::Block(statements) => {
                let scope = self.child_scope();
                self.block(statements, scope);
            }
            JavaStmt::Labeled { body, .. }
            | JavaStmt::While { body, .. }
            | JavaStmt::DoWhile { body, .. }
            | JavaStmt::For { body, .. }
            | JavaStmt::ForEach { body, .. }
            | JavaStmt::Synchronized { body, .. } => self.body(body),
            JavaStmt::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                self.body(then_stmt);
                if let Some(else_stmt) = else_stmt {
                    self.body(else_stmt);
                }
            }
            JavaStmt::Switch { cases, .. } => {
                for case in cases {
                    let scope = self.child_scope();
                    self.block(&mut case.body, scope);
                }
            }
            JavaStmt::Try {
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

    fn body(&mut self, body: &mut JavaStmt) {
        if let JavaStmt::Block(statements) = body {
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

    fn place(statements: &mut Vec<JavaStmt>, index: usize, placements: Vec<DeclarationPlacement>) {
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
                let value = match std::mem::replace(&mut statements[index], JavaStmt::Empty) {
                    JavaStmt::Assign { value, .. } => value,
                    statement => {
                        statements[index] = statement;
                        continue;
                    }
                };
                statements[index] = JavaStmt::Variable {
                    ty: placement.ty,
                    name: placement.name,
                    value: Some(value),
                };
            } else if Some(placement_index) == for_inline {
                if let JavaStmt::For { init, .. } = &mut statements[index] {
                    let value = match std::mem::replace(&mut init[0], JavaStmt::Empty) {
                        JavaStmt::Assign { value, .. } => value,
                        initializer => {
                            init[0] = initializer;
                            continue;
                        }
                    };
                    init[0] = JavaStmt::Variable {
                        ty: placement.ty,
                        name: placement.name,
                        value: Some(value),
                    };
                }
            } else {
                declarations.push(JavaStmt::Variable {
                    ty: placement.ty,
                    name: placement.name,
                    value: None,
                });
            }
        }
        statements.splice(index..index, declarations);
    }

    fn can_inline(statement: &JavaStmt, name: &JavaIdentifier) -> bool {
        let JavaStmt::Assign {
            target: JavaExpr::Name(target),
            op: JavaAssignOp::Assign,
            value,
        } = statement
        else {
            return false;
        };
        target == name && !ExpressionNames::contains(value, name)
    }

    fn can_inline_for(statement: &JavaStmt, name: &JavaIdentifier) -> bool {
        let JavaStmt::For { init, .. } = statement else {
            return false;
        };
        matches!(init.as_slice(), [initializer] if Self::can_inline(initializer, name))
    }
}

struct ExpressionNames;

impl ExpressionNames {
    fn contains(root: &JavaExpr, expected: &JavaIdentifier) -> bool {
        let mut pending = vec![root];
        while let Some(expression) = pending.pop() {
            match expression {
                JavaExpr::Name(name) if name == expected => return true,
                JavaExpr::This
                | JavaExpr::QualifiedThis(_)
                | JavaExpr::Super
                | JavaExpr::Name(_)
                | JavaExpr::Literal(_)
                | JavaExpr::ClassLiteral(_)
                | JavaExpr::StaticField { .. } => {}
                JavaExpr::Field { owner, .. } => pending.push(owner),
                JavaExpr::ArrayAccess { array, index } => {
                    pending.push(index);
                    pending.push(array);
                }
                JavaExpr::Call { receiver, args, .. } => {
                    pending.extend(args.iter().rev());
                    pending.extend(receiver.iter().map(|value| value.as_ref()));
                }
                JavaExpr::MethodReference { receiver, .. } => pending.push(receiver),
                JavaExpr::Lambda { body, .. } => pending.push(body),
                JavaExpr::BlockLambda { .. } => return true,
                JavaExpr::New {
                    enclosing, args, ..
                } => {
                    pending.extend(args.iter().rev());
                    pending.extend(enclosing.iter().map(|value| value.as_ref()));
                }
                JavaExpr::NewArray {
                    dimensions,
                    initializer,
                    ..
                } => {
                    pending.extend(initializer.iter().rev());
                    pending.extend(dimensions.iter().rev());
                }
                JavaExpr::Unary { operand, .. }
                | JavaExpr::Cast { value: operand, .. }
                | JavaExpr::InstanceOf { value: operand, .. } => pending.push(operand),
                JavaExpr::Update { target, .. } => pending.push(target),
                JavaExpr::Binary { left, right, .. } => {
                    pending.push(right);
                    pending.push(left);
                }
                JavaExpr::Conditional {
                    condition,
                    when_true,
                    when_false,
                } => {
                    pending.push(when_false);
                    pending.push(when_true);
                    pending.push(condition);
                }
                JavaExpr::Assignment { target, value, .. } => {
                    pending.push(value);
                    pending.push(target);
                }
            }
        }
        false
    }
}
