use std::collections::{BTreeMap, BTreeSet};

use super::{
    JavaAssignOp, JavaAstRewriter, JavaAstTransform, JavaBinaryOp, JavaExpr, JavaIdentifier,
    JavaLiteral, JavaMethodBody, JavaPrimitiveType, JavaStmt, JavaType,
};

#[derive(Debug, Default)]
pub struct DefiniteAssignment;

impl JavaAstTransform for DefiniteAssignment {
    type Error = super::JavaStructuralError;

    fn apply(&mut self, body: &mut JavaMethodBody) -> Result<bool, Self::Error> {
        let declarations = Declarations::collect(&body.root);
        if declarations.is_empty() {
            return Ok(false);
        }

        let mut analysis = AssignmentAnalysis::new(declarations);
        analysis.analyze(&body.root);
        let mut changed = analysis.initialize(&mut body.root);
        let mut known = KnownValues::default();
        changed |= known.rewrite(&mut body.root).changed;
        Ok(changed)
    }
}

#[derive(Default)]
struct KnownValues {
    values: BTreeMap<JavaIdentifier, JavaLiteral>,
}

#[derive(Default)]
struct RewriteResult {
    changed: bool,
    completes: bool,
}

impl KnownValues {
    fn rewrite(&mut self, statement: &mut JavaStmt) -> RewriteResult {
        match statement {
            JavaStmt::Empty => Self::complete(false),
            JavaStmt::Block(statements) => self.sequence(statements),
            JavaStmt::Variable { name, value, .. } => {
                self.values.remove(name);
                if let Some(value) = value {
                    self.invalidate(value);
                    if let JavaExpr::Literal(literal) = value {
                        self.values.insert(name.clone(), literal.clone());
                    }
                }
                Self::complete(false)
            }
            JavaStmt::Assign { target, op, value } => {
                self.invalidate(value);
                self.invalidate(target);
                let JavaExpr::Name(name) = target else {
                    return Self::complete(false);
                };
                let literal = match (op, value) {
                    (JavaAssignOp::Assign, JavaExpr::Literal(literal)) => Some(literal.clone()),
                    _ => None,
                };
                if literal
                    .as_ref()
                    .is_some_and(|literal| self.values.get(name) == Some(literal))
                {
                    *statement = JavaStmt::Empty;
                    return Self::complete(true);
                }
                self.values.remove(name);
                if let Some(literal) = literal {
                    self.values.insert(name.clone(), literal);
                }
                Self::complete(false)
            }
            JavaStmt::Expression(expression) => {
                self.invalidate(expression);
                Self::complete(false)
            }
            JavaStmt::ConstructorInvocation { args, .. } => {
                for argument in args {
                    self.invalidate(argument);
                }
                Self::complete(false)
            }
            JavaStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => {
                self.invalidate(condition);
                let incoming = self.values.clone();
                let when_true = self.branch(then_stmt, &incoming);
                let when_false = else_stmt
                    .as_deref_mut()
                    .map(|statement| self.branch(statement, &incoming))
                    .unwrap_or_else(|| (Self::complete(false), incoming.clone()));
                self.values = Self::join(
                    (when_true.0.completes, when_true.1),
                    (when_false.0.completes, when_false.1),
                );
                RewriteResult {
                    changed: when_true.0.changed || when_false.0.changed,
                    completes: when_true.0.completes || when_false.0.completes,
                }
            }
            JavaStmt::Try {
                body,
                catches,
                finally,
            } => {
                let incoming = self.values.clone();
                let body_result = self.branch(body, &incoming).0;
                let mut changed = body_result.changed;
                let mut completes = body_result.completes;
                for catch in catches {
                    let result = self.branch(&mut catch.body, &incoming).0;
                    changed |= result.changed;
                    completes |= result.completes;
                }
                if let Some(finally) = finally {
                    let result = self.branch(finally, &incoming).0;
                    changed |= result.changed;
                    completes &= result.completes;
                }
                self.values.clear();
                RewriteResult { changed, completes }
            }
            JavaStmt::Synchronized { lock, body } => {
                self.invalidate(lock);
                self.rewrite(body)
            }
            JavaStmt::Labeled { body, .. } => {
                let result = self.rewrite(body);
                self.values.clear();
                result
            }
            JavaStmt::While {
                condition, body, ..
            } => {
                self.invalidate(condition);
                let incoming = self.values.clone();
                let result = self.branch(body, &incoming).0;
                self.values.clear();
                RewriteResult {
                    changed: result.changed,
                    completes: true,
                }
            }
            JavaStmt::DoWhile {
                body, condition, ..
            } => {
                let incoming = self.values.clone();
                let result = self.branch(body, &incoming).0;
                self.invalidate(condition);
                self.values.clear();
                RewriteResult {
                    changed: result.changed,
                    completes: true,
                }
            }
            JavaStmt::For {
                init,
                condition,
                update,
                body,
                ..
            } => {
                let mut result = self.sequence(init);
                if let Some(condition) = condition {
                    self.invalidate(condition);
                }
                let incoming = self.values.clone();
                let body_result = self.branch(body, &incoming).0;
                result.changed |= body_result.changed;
                for expression in update {
                    self.invalidate(expression);
                }
                self.values.clear();
                result.completes = true;
                result
            }
            JavaStmt::ForEach { iterable, body, .. } => {
                self.invalidate(iterable);
                let incoming = self.values.clone();
                let result = self.branch(body, &incoming).0;
                self.values.clear();
                RewriteResult {
                    changed: result.changed,
                    completes: true,
                }
            }
            JavaStmt::Switch {
                selector, cases, ..
            } => {
                self.invalidate(selector);
                let incoming = self.values.clone();
                let mut changed = false;
                for case in cases {
                    let mut branch = Self {
                        values: incoming.clone(),
                    };
                    changed |= branch.sequence(&mut case.body).changed;
                }
                self.values.clear();
                RewriteResult {
                    changed,
                    completes: true,
                }
            }
            JavaStmt::Return(value) => {
                if let Some(value) = value {
                    self.invalidate(value);
                }
                Self::terminal()
            }
            JavaStmt::Throw(value) => {
                self.invalidate(value);
                Self::terminal()
            }
            JavaStmt::Break(_) | JavaStmt::Continue(_) => Self::terminal(),
        }
    }

    fn sequence(&mut self, statements: &mut Vec<JavaStmt>) -> RewriteResult {
        let mut result = Self::complete(false);
        for statement in statements.iter_mut() {
            if !result.completes {
                break;
            }
            let next = self.rewrite(statement);
            result.changed |= next.changed;
            result.completes = next.completes;
        }
        if result.changed {
            statements.retain(|statement| !matches!(statement, JavaStmt::Empty));
        }
        result
    }

    fn branch(
        &self,
        statement: &mut JavaStmt,
        incoming: &BTreeMap<JavaIdentifier, JavaLiteral>,
    ) -> (RewriteResult, BTreeMap<JavaIdentifier, JavaLiteral>) {
        let mut branch = Self {
            values: incoming.clone(),
        };
        let result = branch.rewrite(statement);
        (result, branch.values)
    }

    fn join(
        left: (bool, BTreeMap<JavaIdentifier, JavaLiteral>),
        right: (bool, BTreeMap<JavaIdentifier, JavaLiteral>),
    ) -> BTreeMap<JavaIdentifier, JavaLiteral> {
        match (left.0, right.0) {
            (true, false) => left.1,
            (false, true) => right.1,
            (false, false) => BTreeMap::new(),
            (true, true) => {
                let mut joined = left.1;
                joined.retain(|name, value| right.1.get(name) == Some(value));
                joined
            }
        }
    }

    fn invalidate(&mut self, expression: &JavaExpr) {
        let mut writes = ExpressionWrites::default();
        writes.rewrite_expression(expression.clone());
        for name in writes.names {
            self.values.remove(&name);
        }
    }

    fn complete(changed: bool) -> RewriteResult {
        RewriteResult {
            changed,
            completes: true,
        }
    }

    fn terminal() -> RewriteResult {
        RewriteResult {
            changed: false,
            completes: false,
        }
    }
}

#[derive(Default)]
struct ExpressionWrites {
    names: BTreeSet<JavaIdentifier>,
}

impl JavaAstRewriter for ExpressionWrites {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        match &expression {
            JavaExpr::Assignment { target, .. } | JavaExpr::Update { target, .. } => {
                if let JavaExpr::Name(name) = target.as_ref() {
                    self.names.insert(name.clone());
                }
            }
            _ => {}
        }
        expression
    }
}

#[derive(Debug, Default)]
struct Declarations(BTreeMap<JavaIdentifier, JavaType>);

impl Declarations {
    fn collect(root: &JavaStmt) -> Self {
        let mut declarations = Self::default();
        let mut pending = vec![root];
        while let Some(statement) = pending.pop() {
            match statement {
                JavaStmt::Variable {
                    ty,
                    name,
                    value: None,
                } => {
                    declarations.0.insert(name.clone(), ty.clone());
                }
                JavaStmt::Block(children) => pending.extend(children),
                JavaStmt::Labeled { body, .. }
                | JavaStmt::While { body, .. }
                | JavaStmt::DoWhile { body, .. }
                | JavaStmt::For { body, .. }
                | JavaStmt::ForEach { body, .. }
                | JavaStmt::Synchronized { body, .. } => pending.push(body),
                JavaStmt::If {
                    then_stmt,
                    else_stmt,
                    ..
                } => {
                    pending.push(then_stmt);
                    if let Some(else_stmt) = else_stmt {
                        pending.push(else_stmt);
                    }
                }
                JavaStmt::Switch { cases, .. } => {
                    pending.extend(cases.iter().flat_map(|case| case.body.iter()));
                }
                JavaStmt::Try {
                    body,
                    catches,
                    finally,
                } => {
                    pending.push(body);
                    pending.extend(catches.iter().map(|catch| &catch.body));
                    if let Some(finally) = finally {
                        pending.push(finally);
                    }
                }
                JavaStmt::Empty
                | JavaStmt::Expression(_)
                | JavaStmt::ConstructorInvocation { .. }
                | JavaStmt::Assign { .. }
                | JavaStmt::Return(_)
                | JavaStmt::Throw(_)
                | JavaStmt::Break(_)
                | JavaStmt::Continue(_)
                | JavaStmt::Variable { .. } => {}
            }
        }
        declarations
    }

    fn is_candidate(&self, name: &JavaIdentifier) -> bool {
        self.0.contains_key(name)
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

#[derive(Debug, Clone)]
struct Flow {
    assigned: BTreeSet<JavaIdentifier>,
    completes: bool,
}

impl Default for Flow {
    fn default() -> Self {
        Self {
            assigned: BTreeSet::new(),
            completes: true,
        }
    }
}

impl Flow {
    fn normal_join(flows: impl IntoIterator<Item = Self>) -> Self {
        let mut normal = flows.into_iter().filter(|flow| flow.completes);
        let Some(mut joined) = normal.next() else {
            return Self {
                assigned: BTreeSet::new(),
                completes: false,
            };
        };
        for flow in normal {
            joined.assigned.retain(|name| flow.assigned.contains(name));
        }
        joined
    }
}

#[derive(Debug)]
struct AssignmentAnalysis {
    declarations: Declarations,
    required: BTreeSet<JavaIdentifier>,
}

impl AssignmentAnalysis {
    fn new(declarations: Declarations) -> Self {
        Self {
            declarations,
            required: BTreeSet::new(),
        }
    }

    fn analyze(&mut self, root: &JavaStmt) {
        self.statement(root, Flow::default());
    }

    fn statement(&mut self, statement: &JavaStmt, mut flow: Flow) -> Flow {
        match statement {
            JavaStmt::Empty => flow,
            JavaStmt::Block(statements) => self.sequence(statements, flow),
            JavaStmt::Labeled { body, .. } => {
                let body_flow = self.statement(body, flow.clone());
                Flow::normal_join([flow, body_flow])
            }
            JavaStmt::Variable { name, value, .. } => {
                flow.assigned.remove(name);
                if let Some(value) = value {
                    self.expression(value, &mut flow.assigned);
                    flow.assigned.insert(name.clone());
                }
                flow
            }
            JavaStmt::Expression(expression) => {
                self.expression(expression, &mut flow.assigned);
                flow
            }
            JavaStmt::ConstructorInvocation { args, .. } => {
                self.expressions(args, &mut flow.assigned);
                flow
            }
            JavaStmt::Assign { target, op, value } => {
                self.assignment(target, *op, value, &mut flow.assigned);
                flow
            }
            JavaStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => {
                self.expression(condition, &mut flow.assigned);
                let when_true = self.statement(then_stmt, flow.clone());
                let when_false = else_stmt
                    .as_deref()
                    .map(|statement| self.statement(statement, flow.clone()))
                    .unwrap_or(flow);
                Flow::normal_join([when_true, when_false])
            }
            JavaStmt::While {
                condition, body, ..
            } => {
                self.expression(condition, &mut flow.assigned);
                self.statement(body, flow.clone());
                flow
            }
            JavaStmt::DoWhile {
                body, condition, ..
            } => {
                let body_flow = self.statement(body, flow.clone());
                let mut condition_flow = if body_flow.completes {
                    body_flow
                } else {
                    flow.clone()
                };
                self.expression(condition, &mut condition_flow.assigned);
                Flow::normal_join([flow, condition_flow])
            }
            JavaStmt::For {
                init,
                condition,
                update,
                body,
                ..
            } => {
                flow = self.sequence(init, flow);
                if !flow.completes {
                    return flow;
                }
                if let Some(condition) = condition {
                    self.expression(condition, &mut flow.assigned);
                }
                let mut iteration = self.statement(body, flow.clone());
                if !iteration.completes {
                    iteration = flow.clone();
                }
                self.expressions(update, &mut iteration.assigned);
                Flow::normal_join([flow, iteration])
            }
            JavaStmt::ForEach {
                variable,
                iterable,
                body,
                ..
            } => {
                self.expression(iterable, &mut flow.assigned);
                let mut iteration = flow.clone();
                iteration.assigned.insert(variable.clone());
                self.statement(body, iteration);
                flow
            }
            JavaStmt::Switch {
                selector, cases, ..
            } => {
                self.expression(selector, &mut flow.assigned);
                let branches = std::iter::once(flow.clone()).chain(
                    cases
                        .iter()
                        .map(|case| self.sequence(&case.body, flow.clone())),
                );
                Flow::normal_join(branches)
            }
            JavaStmt::Try {
                body,
                catches,
                finally,
            } => {
                let body_flow = self.statement(body, flow.clone());
                let branches = std::iter::once(body_flow).chain(catches.iter().map(|catch| {
                    let mut catch_flow = flow.clone();
                    catch_flow.assigned.insert(catch.variable.clone());
                    self.statement(&catch.body, catch_flow)
                }));
                let joined = Flow::normal_join(branches);
                let Some(finally) = finally else {
                    return joined;
                };
                // A finally block is also reached by exceptional edges from
                // any point in the protected body or a handler.
                self.statement(finally, flow.clone());
                let joined_completes = joined.completes;
                let finally_flow = self.statement(finally, joined);
                if joined_completes && finally_flow.completes {
                    finally_flow
                } else {
                    Flow {
                        assigned: BTreeSet::new(),
                        completes: false,
                    }
                }
            }
            JavaStmt::Synchronized { lock, body } => {
                self.expression(lock, &mut flow.assigned);
                self.statement(body, flow)
            }
            JavaStmt::Return(value) => {
                if let Some(value) = value {
                    self.expression(value, &mut flow.assigned);
                }
                flow.completes = false;
                flow
            }
            JavaStmt::Throw(value) => {
                self.expression(value, &mut flow.assigned);
                flow.completes = false;
                flow
            }
            JavaStmt::Break(_) | JavaStmt::Continue(_) => {
                flow.completes = false;
                flow
            }
        }
    }

    fn sequence(&mut self, statements: &[JavaStmt], mut flow: Flow) -> Flow {
        for statement in statements {
            if !flow.completes {
                break;
            }
            flow = self.statement(statement, flow);
        }
        flow
    }

    fn expressions(&mut self, expressions: &[JavaExpr], assigned: &mut BTreeSet<JavaIdentifier>) {
        for expression in expressions {
            self.expression(expression, assigned);
        }
    }

    fn expression(&mut self, expression: &JavaExpr, assigned: &mut BTreeSet<JavaIdentifier>) {
        match expression {
            JavaExpr::This
            | JavaExpr::QualifiedThis(_)
            | JavaExpr::Super
            | JavaExpr::Literal(_)
            | JavaExpr::ClassLiteral(_)
            | JavaExpr::StaticField { .. } => {}
            JavaExpr::Name(name) => self.read(name, assigned),
            JavaExpr::Field { owner, .. } => self.expression(owner, assigned),
            JavaExpr::ArrayAccess { array, index } => {
                self.expression(array, assigned);
                self.expression(index, assigned);
            }
            JavaExpr::Call { receiver, args, .. } => {
                if let Some(receiver) = receiver {
                    self.expression(receiver, assigned);
                }
                self.expressions(args, assigned);
            }
            JavaExpr::MethodReference { receiver, .. } => {
                self.expression(receiver, assigned);
            }
            JavaExpr::Lambda { body, .. } => {
                let mut lambda_assigned = assigned.clone();
                self.expression(body, &mut lambda_assigned);
            }
            JavaExpr::BlockLambda { body, .. } => {
                self.statement(
                    body,
                    Flow {
                        assigned: assigned.clone(),
                        completes: true,
                    },
                );
            }
            JavaExpr::New {
                enclosing, args, ..
            } => {
                if let Some(enclosing) = enclosing {
                    self.expression(enclosing, assigned);
                }
                self.expressions(args, assigned);
            }
            JavaExpr::NewArray {
                dimensions,
                initializer,
                ..
            } => {
                self.expressions(dimensions, assigned);
                self.expressions(initializer, assigned);
            }
            JavaExpr::Unary { operand, .. }
            | JavaExpr::Cast { value: operand, .. }
            | JavaExpr::InstanceOf { value: operand, .. } => self.expression(operand, assigned),
            JavaExpr::Update { target, .. } => {
                match target.as_ref() {
                    JavaExpr::Name(name) => self.read(name, assigned),
                    target => self.expression(target, assigned),
                }
                if let JavaExpr::Name(name) = target.as_ref() {
                    assigned.insert(name.clone());
                }
            }
            JavaExpr::Binary { left, op, right } => {
                self.expression(left, assigned);
                if matches!(op, JavaBinaryOp::LogicalAnd | JavaBinaryOp::LogicalOr) {
                    let skipped = assigned.clone();
                    self.expression(right, assigned);
                    assigned.retain(|name| skipped.contains(name));
                } else {
                    self.expression(right, assigned);
                }
            }
            JavaExpr::Conditional {
                condition,
                when_true,
                when_false,
            } => {
                self.expression(condition, assigned);
                let mut true_state = assigned.clone();
                self.expression(when_true, &mut true_state);
                let mut false_state = assigned.clone();
                self.expression(when_false, &mut false_state);
                true_state.retain(|name| false_state.contains(name));
                *assigned = true_state;
            }
            JavaExpr::Assignment { target, op, value } => {
                self.assignment(target, *op, value, assigned);
            }
        }
    }

    fn assignment(
        &mut self,
        target: &JavaExpr,
        op: JavaAssignOp,
        value: &JavaExpr,
        assigned: &mut BTreeSet<JavaIdentifier>,
    ) {
        match target {
            JavaExpr::Name(name) => {
                if op != JavaAssignOp::Assign {
                    self.read(name, assigned);
                }
            }
            target => self.expression(target, assigned),
        }
        self.expression(value, assigned);
        if let JavaExpr::Name(name) = target {
            assigned.insert(name.clone());
        }
    }

    fn read(&mut self, name: &JavaIdentifier, assigned: &BTreeSet<JavaIdentifier>) {
        if self.declarations.is_candidate(name) && !assigned.contains(name) {
            self.required.insert(name.clone());
        }
    }

    fn initialize(&self, root: &mut JavaStmt) -> bool {
        let mut changed = false;
        Self::initialize_statement(root, &self.required, &mut changed);
        changed
    }

    fn initialize_statement(
        statement: &mut JavaStmt,
        required: &BTreeSet<JavaIdentifier>,
        changed: &mut bool,
    ) {
        match statement {
            JavaStmt::Variable {
                ty,
                name,
                value: value @ None,
            } if required.contains(name) => {
                *value = Some(Self::default_value(ty));
                *changed = true;
            }
            JavaStmt::Block(children) => {
                for child in children {
                    Self::initialize_statement(child, required, changed);
                }
            }
            JavaStmt::Labeled { body, .. }
            | JavaStmt::While { body, .. }
            | JavaStmt::DoWhile { body, .. }
            | JavaStmt::For { body, .. }
            | JavaStmt::ForEach { body, .. }
            | JavaStmt::Synchronized { body, .. } => {
                Self::initialize_statement(body, required, changed);
            }
            JavaStmt::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                Self::initialize_statement(then_stmt, required, changed);
                if let Some(else_stmt) = else_stmt {
                    Self::initialize_statement(else_stmt, required, changed);
                }
            }
            JavaStmt::Switch { cases, .. } => {
                for case in cases {
                    for child in &mut case.body {
                        Self::initialize_statement(child, required, changed);
                    }
                }
            }
            JavaStmt::Try {
                body,
                catches,
                finally,
            } => {
                Self::initialize_statement(body, required, changed);
                for catch in catches {
                    Self::initialize_statement(&mut catch.body, required, changed);
                }
                if let Some(finally) = finally {
                    Self::initialize_statement(finally, required, changed);
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

    fn default_value(ty: &JavaType) -> JavaExpr {
        let literal = match ty {
            JavaType::Primitive(JavaPrimitiveType::Boolean) => JavaLiteral::Boolean(false),
            JavaType::Primitive(JavaPrimitiveType::Long) => JavaLiteral::Long(0),
            JavaType::Primitive(JavaPrimitiveType::Float) => JavaLiteral::Float(0.0),
            JavaType::Primitive(JavaPrimitiveType::Double) => JavaLiteral::Double(0.0),
            JavaType::Primitive(JavaPrimitiveType::Char) => JavaLiteral::Character(0),
            JavaType::Primitive(
                JavaPrimitiveType::Byte | JavaPrimitiveType::Short | JavaPrimitiveType::Int,
            ) => JavaLiteral::Integer(0),
            JavaType::Primitive(JavaPrimitiveType::Void)
            | JavaType::Class(_)
            | JavaType::Variable(_)
            | JavaType::Array(_) => JavaLiteral::Null,
        };
        JavaExpr::Literal(literal)
    }
}
