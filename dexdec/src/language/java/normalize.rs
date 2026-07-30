use super::{
    JavaAstRewriter, JavaBinaryOp, JavaCatch, JavaExpr, JavaIdentifier, JavaLiteral,
    JavaMethodBody, JavaPrimitiveType, JavaStmt, JavaSwitchCase, JavaType,
};

pub trait JavaAstTransform {
    type Error;

    fn apply(&mut self, body: &mut JavaMethodBody) -> Result<bool, Self::Error>;
}

#[derive(Debug, Default)]
pub struct JavaAstNormalizer;

#[derive(Debug, Clone)]
pub struct JavaMethodCompletion {
    return_type: JavaType,
}

impl JavaMethodCompletion {
    pub fn new(return_type: JavaType) -> Self {
        Self { return_type }
    }

    fn default_value(&self) -> Option<JavaExpr> {
        let literal = match self.return_type {
            JavaType::Primitive(JavaPrimitiveType::Void) => return None,
            JavaType::Primitive(JavaPrimitiveType::Boolean) => JavaLiteral::Boolean(false),
            JavaType::Primitive(JavaPrimitiveType::Long) => JavaLiteral::Long(0),
            JavaType::Primitive(JavaPrimitiveType::Float) => JavaLiteral::Float(0.0),
            JavaType::Primitive(JavaPrimitiveType::Double) => JavaLiteral::Double(0.0),
            JavaType::Primitive(JavaPrimitiveType::Char) => JavaLiteral::Character(0),
            JavaType::Primitive(
                JavaPrimitiveType::Byte | JavaPrimitiveType::Short | JavaPrimitiveType::Int,
            ) => JavaLiteral::Integer(0),
            JavaType::Class(_) | JavaType::Variable(_) | JavaType::Array(_) => JavaLiteral::Null,
        };
        Some(JavaExpr::Literal(literal))
    }
}

impl JavaAstTransform for JavaMethodCompletion {
    type Error = std::convert::Infallible;

    fn apply(&mut self, body: &mut JavaMethodBody) -> Result<bool, Self::Error> {
        if !TerminalBranchLinearizer::can_complete_normally(&body.root) {
            return Ok(false);
        }
        let Some(value) = self.default_value() else {
            return Ok(false);
        };
        let terminal = JavaStmt::Return(Some(value));
        match &mut body.root {
            JavaStmt::Block(statements) => statements.push(terminal),
            JavaStmt::Empty => body.root = JavaStmt::Block(vec![terminal]),
            root => {
                let preceding = std::mem::replace(root, JavaStmt::Empty);
                body.root = JavaStmt::Block(vec![preceding, terminal]);
            }
        }
        Ok(true)
    }
}

/// Re-expresses DEX `return-void` exits from a class initializer as structured
/// Java control flow. Java forbids explicit returns in initializer blocks.
#[derive(Debug, Default)]
pub struct JavaInitializerExitLowering;

impl JavaAstTransform for JavaInitializerExitLowering {
    type Error = super::JavaStructuralError;

    fn apply(&mut self, body: &mut JavaMethodBody) -> Result<bool, Self::Error> {
        let JavaStmt::Block(statements) = &mut body.root else {
            return Ok(false);
        };
        let mut changed = TerminalBranchLinearizer::apply_required_void_exit(statements);
        if changed {
            if let Some(last) = statements.last_mut() {
                changed |= JavaAstNormalizer::strip_terminal_void_return(last);
            }
            if matches!(statements.last(), Some(JavaStmt::Empty)) {
                statements.pop();
            }
        }
        Ok(changed)
    }
}

impl JavaAstNormalizer {
    fn normalize(root: JavaStmt) -> Result<(JavaStmt, bool), super::JavaStructuralError> {
        let mut pending = vec![SyntaxTask::Visit(root)];
        let mut results = Vec::new();
        let mut changed = false;
        while let Some(task) = pending.pop() {
            match task {
                SyntaxTask::Visit(statement) => match statement {
                    JavaStmt::Block(children) => {
                        let count = children.len();
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::Block(count)));
                        pending.extend(children.into_iter().rev().map(SyntaxTask::Visit));
                    }
                    JavaStmt::Labeled { label, body } => {
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::Labeled(label)));
                        pending.push(SyntaxTask::Visit(*body));
                    }
                    JavaStmt::If {
                        condition,
                        then_stmt,
                        else_stmt,
                    } => {
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::If {
                            condition,
                            has_else: else_stmt.is_some(),
                        }));
                        if let Some(else_stmt) = else_stmt {
                            pending.push(SyntaxTask::Visit(*else_stmt));
                        }
                        pending.push(SyntaxTask::Visit(*then_stmt));
                    }
                    JavaStmt::While {
                        label,
                        condition,
                        body,
                    } => {
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::While { label, condition }));
                        pending.push(SyntaxTask::Visit(*body));
                    }
                    JavaStmt::DoWhile {
                        label,
                        body,
                        condition,
                    } => {
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::DoWhile {
                            label,
                            condition,
                        }));
                        pending.push(SyntaxTask::Visit(*body));
                    }
                    JavaStmt::For {
                        label,
                        init,
                        condition,
                        update,
                        body,
                    } => {
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::For {
                            label,
                            init,
                            condition,
                            update,
                        }));
                        pending.push(SyntaxTask::Visit(*body));
                    }
                    JavaStmt::ForEach {
                        label,
                        ty,
                        variable,
                        iterable,
                        body,
                    } => {
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::ForEach {
                            label,
                            ty,
                            variable,
                            iterable,
                        }));
                        pending.push(SyntaxTask::Visit(*body));
                    }
                    JavaStmt::Switch {
                        label,
                        selector,
                        mut cases,
                    } => {
                        let bodies = cases
                            .iter_mut()
                            .map(|case| JavaStmt::Block(std::mem::take(&mut case.body)))
                            .collect::<Vec<_>>();
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::Switch {
                            label,
                            selector,
                            cases,
                        }));
                        pending.extend(bodies.into_iter().rev().map(SyntaxTask::Visit));
                    }
                    JavaStmt::Try {
                        body,
                        mut catches,
                        finally,
                    } => {
                        let has_finally = finally.is_some();
                        let mut bodies =
                            Vec::with_capacity(1 + catches.len() + usize::from(has_finally));
                        bodies.push(*body);
                        bodies.extend(
                            catches
                                .iter_mut()
                                .map(|catch| std::mem::replace(&mut catch.body, JavaStmt::Empty)),
                        );
                        if let Some(finally) = finally {
                            bodies.push(*finally);
                        }
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::Try {
                            catches,
                            has_finally,
                        }));
                        pending.extend(bodies.into_iter().rev().map(SyntaxTask::Visit));
                    }
                    JavaStmt::Synchronized { lock, body } => {
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::Synchronized(lock)));
                        pending.push(SyntaxTask::Visit(*body));
                    }
                    leaf => results.push(leaf),
                },
                SyntaxTask::Rebuild(frame) => {
                    let count = frame.child_count();
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(super::JavaStructuralError::MalformedWorkStack)?;
                    let children = results.drain(start..).collect();
                    let (statement, local_change) = frame.rebuild(children)?;
                    changed |= local_change;
                    results.push(statement);
                }
            }
        }
        let [root] = results.as_slice() else {
            return Err(super::JavaStructuralError::MalformedWorkStack);
        };
        Ok((root.clone(), changed))
    }

    fn flatten(children: Vec<JavaStmt>) -> (Vec<JavaStmt>, bool) {
        let mut flattened = Vec::with_capacity(children.len());
        let mut changed = false;
        for child in children {
            match child {
                JavaStmt::Block(children) => {
                    flattened.extend(children);
                    changed = true;
                }
                JavaStmt::Empty => changed = true,
                child => flattened.push(child),
            }
        }
        changed |= TerminalBranchLinearizer::apply(&mut flattened);
        (flattened, changed)
    }

    fn protection(
        body: JavaStmt,
        catches: Vec<JavaCatch>,
        finally: Option<Box<JavaStmt>>,
    ) -> (JavaStmt, bool) {
        let empty_body = match &body {
            JavaStmt::Empty => true,
            JavaStmt::Block(statements) => statements.is_empty(),
            _ => false,
        };
        if empty_body && finally.is_none() {
            return (JavaStmt::Empty, true);
        }
        match (catches.is_empty() && finally.is_some(), body) {
            (
                true,
                JavaStmt::Try {
                    body,
                    catches,
                    finally: None,
                },
            ) => (
                JavaStmt::Try {
                    body,
                    catches,
                    finally,
                },
                true,
            ),
            (_, body) => (
                JavaStmt::Try {
                    body: Box::new(body),
                    catches,
                    finally,
                },
                false,
            ),
        }
    }

    fn synchronized(lock: JavaExpr, body: JavaStmt) -> (JavaStmt, bool) {
        let JavaStmt::Block(mut statements) = body else {
            return (
                JavaStmt::Synchronized {
                    lock,
                    body: Box::new(body),
                },
                false,
            );
        };
        let Some(JavaStmt::Synchronized {
            lock: inner_lock,
            body: inner_body,
        }) = statements.first()
        else {
            return (
                JavaStmt::Synchronized {
                    lock,
                    body: Box::new(JavaStmt::Block(statements)),
                },
                false,
            );
        };
        if inner_lock != &lock || !matches!(lock, JavaExpr::Name(_)) {
            return (
                JavaStmt::Synchronized {
                    lock,
                    body: Box::new(JavaStmt::Block(statements)),
                },
                false,
            );
        }
        let inner = match inner_body.as_ref() {
            JavaStmt::Block(inner) => inner.clone(),
            JavaStmt::Empty => Vec::new(),
            statement => vec![statement.clone()],
        };
        statements.splice(0..1, inner);
        (
            JavaStmt::Synchronized {
                lock,
                body: Box::new(JavaStmt::Block(statements)),
            },
            true,
        )
    }

    fn foreach(
        label: Option<JavaIdentifier>,
        ty: JavaType,
        variable: JavaIdentifier,
        iterable: JavaExpr,
        body: JavaStmt,
    ) -> (JavaStmt, bool) {
        let JavaStmt::Block(mut statements) = body else {
            return (
                JavaStmt::ForEach {
                    label,
                    ty,
                    variable,
                    iterable,
                    body: Box::new(body),
                },
                false,
            );
        };
        let Some(JavaStmt::Variable {
            ty: target_type,
            name: target,
            value:
                Some(JavaExpr::Cast {
                    ty: cast_type,
                    value,
                }),
        }) = statements.first()
        else {
            return (
                JavaStmt::ForEach {
                    label,
                    ty,
                    variable,
                    iterable,
                    body: Box::new(JavaStmt::Block(statements)),
                },
                false,
            );
        };
        if target_type != cast_type
            || !matches!(value.as_ref(), JavaExpr::Name(source) if source == &variable)
        {
            return (
                JavaStmt::ForEach {
                    label,
                    ty,
                    variable,
                    iterable,
                    body: Box::new(JavaStmt::Block(statements)),
                },
                false,
            );
        }
        let mut uses = NameUseCounter {
            target: &variable,
            count: 0,
        };
        for statement in statements.iter().skip(1).cloned() {
            uses.rewrite_statement(statement);
        }
        if uses.count != 0 {
            return (
                JavaStmt::ForEach {
                    label,
                    ty,
                    variable,
                    iterable,
                    body: Box::new(JavaStmt::Block(statements)),
                },
                false,
            );
        }
        let target_type = target_type.clone();
        let target = target.clone();
        statements.remove(0);
        (
            JavaStmt::ForEach {
                label,
                ty: target_type,
                variable: target,
                iterable,
                body: Box::new(JavaStmt::Block(statements)),
            },
            true,
        )
    }

    fn conditional(
        condition: JavaExpr,
        then_stmt: JavaStmt,
        else_stmt: Option<JavaStmt>,
    ) -> (JavaStmt, bool) {
        if let Some(else_stmt) = else_stmt {
            let then_empty = Self::is_empty(&then_stmt);
            let else_empty = Self::is_empty(&else_stmt);
            if then_empty && !else_empty {
                return (
                    JavaStmt::If {
                        condition: condition.negated(),
                        then_stmt: Box::new(else_stmt),
                        else_stmt: None,
                    },
                    true,
                );
            }
            if !then_empty && else_empty {
                return (
                    JavaStmt::If {
                        condition,
                        then_stmt: Box::new(then_stmt),
                        else_stmt: None,
                    },
                    true,
                );
            }
            return (
                JavaStmt::If {
                    condition,
                    then_stmt: Box::new(then_stmt),
                    else_stmt: Some(Box::new(else_stmt)),
                },
                false,
            );
        }
        let nested = match &then_stmt {
            JavaStmt::If {
                condition,
                then_stmt,
                else_stmt: None,
            } => Some((condition.clone(), then_stmt.as_ref().clone())),
            JavaStmt::Block(statements) => match statements.as_slice() {
                [JavaStmt::If {
                    condition,
                    then_stmt,
                    else_stmt: None,
                }] => Some((condition.clone(), then_stmt.as_ref().clone())),
                _ => None,
            },
            _ => None,
        };
        if let Some((nested_condition, nested_body)) = nested {
            return (
                JavaStmt::If {
                    condition: JavaExpr::Binary {
                        left: Box::new(condition),
                        op: JavaBinaryOp::LogicalAnd,
                        right: Box::new(nested_condition),
                    },
                    then_stmt: Box::new(nested_body),
                    else_stmt: None,
                },
                true,
            );
        }
        (
            JavaStmt::If {
                condition,
                then_stmt: Box::new(then_stmt),
                else_stmt: None,
            },
            false,
        )
    }

    fn is_empty(statement: &JavaStmt) -> bool {
        matches!(statement, JavaStmt::Empty)
            || matches!(statement, JavaStmt::Block(statements) if statements.is_empty())
    }

    fn strip_terminal_void_return(statement: &mut JavaStmt) -> bool {
        match statement {
            JavaStmt::Return(None) => {
                *statement = JavaStmt::Empty;
                true
            }
            JavaStmt::Block(statements) => {
                let changed = statements
                    .last_mut()
                    .is_some_and(Self::strip_terminal_void_return);
                if matches!(statements.last(), Some(JavaStmt::Empty)) {
                    statements.pop();
                }
                changed
            }
            JavaStmt::Synchronized { body, .. } => Self::strip_terminal_void_return(body),
            _ => false,
        }
    }
}

struct TerminalBranchLinearizer;

impl TerminalBranchLinearizer {
    const NESTING_PENALTY: usize = 12;

    fn apply(statements: &mut Vec<JavaStmt>) -> bool {
        let mut changed = false;
        let mut index = 0usize;
        while index + 1 < statements.len() {
            let Some(candidate) = Self::candidate(statements, index) else {
                index += 1;
                continue;
            };
            Self::linearize(statements, index, candidate);
            changed = true;
            index += 1;
        }
        changed
    }

    fn apply_required_void_exit(statements: &mut Vec<JavaStmt>) -> bool {
        let mut changed = false;
        let mut index = 0usize;
        while index + 1 < statements.len() {
            let Some(candidate) = Self::required_void_exit_candidate(statements, index) else {
                index += 1;
                continue;
            };
            Self::linearize(statements, index, candidate);
            changed = true;
            index += 1;
        }
        changed
    }

    fn linearize(statements: &mut Vec<JavaStmt>, index: usize, candidate: TerminalBranchCandidate) {
        let tail = statements.split_off(index + 1);
        let Some(JavaStmt::If {
            condition,
            then_stmt,
            else_stmt: None,
        }) = statements.pop()
        else {
            unreachable!("terminal branch candidate changed during linearization");
        };
        statements.push(JavaStmt::If {
            condition: condition.negated(),
            then_stmt: Box::new(JavaStmt::Block(tail.clone())),
            else_stmt: None,
        });
        match *then_stmt {
            JavaStmt::Block(body) => statements.extend(body),
            JavaStmt::Empty => {}
            statement => statements.push(statement),
        }
        if candidate.duplicates_tail {
            statements.extend(tail);
        }
    }

    fn candidate(statements: &[JavaStmt], index: usize) -> Option<TerminalBranchCandidate> {
        let JavaStmt::If {
            condition,
            then_stmt,
            else_stmt: None,
        } = statements.get(index)?
        else {
            return None;
        };
        let tail = &statements[index + 1..];
        if Self::sequence_can_complete_normally(tail) {
            return None;
        }
        let then_depth = Self::nesting_depth(then_stmt);
        let tail_depth = tail
            .iter()
            .map(Self::nesting_depth)
            .max()
            .unwrap_or_default();
        let original_depth = (then_depth + 1).max(tail_depth);
        let linearized_depth = then_depth.max(tail_depth + 1);
        let lowers_nesting = linearized_depth < original_depth;
        let lowers_condition_cost = linearized_depth == original_depth
            && condition.clone().negated().cost() < condition.cost();
        if !lowers_nesting && !lowers_condition_cost {
            return None;
        }
        let duplicates_tail = Self::can_complete_normally(then_stmt);
        if duplicates_tail {
            let depth_reduction = original_depth.saturating_sub(linearized_depth);
            let duplication_budget = depth_reduction.saturating_mul(Self::NESTING_PENALTY);
            if Self::sequence_cost(tail) > duplication_budget {
                return None;
            }
        }
        Some(TerminalBranchCandidate { duplicates_tail })
    }

    fn required_void_exit_candidate(
        statements: &[JavaStmt],
        index: usize,
    ) -> Option<TerminalBranchCandidate> {
        let JavaStmt::If {
            then_stmt,
            else_stmt: None,
            ..
        } = statements.get(index)?
        else {
            return None;
        };
        let tail = &statements[index + 1..];
        (!tail.is_empty()
            && !Self::sequence_can_complete_normally(tail)
            && Self::terminates_with_void_return(then_stmt))
        .then(|| TerminalBranchCandidate {
            duplicates_tail: Self::can_complete_normally(then_stmt),
        })
    }

    fn terminates_with_void_return(statement: &JavaStmt) -> bool {
        match statement {
            JavaStmt::Return(None) => true,
            JavaStmt::Block(statements) => statements
                .last()
                .is_some_and(Self::terminates_with_void_return),
            JavaStmt::Synchronized { body, .. } => Self::terminates_with_void_return(body),
            JavaStmt::If {
                then_stmt,
                else_stmt: Some(else_stmt),
                ..
            } => {
                Self::terminates_with_void_return(then_stmt)
                    && Self::terminates_with_void_return(else_stmt)
            }
            _ => false,
        }
    }

    fn sequence_can_complete_normally(statements: &[JavaStmt]) -> bool {
        statements.iter().all(Self::can_complete_normally)
    }

    fn can_complete_normally(statement: &JavaStmt) -> bool {
        match statement {
            JavaStmt::Return(_)
            | JavaStmt::Throw(_)
            | JavaStmt::Break(_)
            | JavaStmt::Continue(_) => false,
            JavaStmt::Block(statements) => Self::sequence_can_complete_normally(statements),
            JavaStmt::If {
                then_stmt,
                else_stmt: Some(else_stmt),
                ..
            } => Self::can_complete_normally(then_stmt) || Self::can_complete_normally(else_stmt),
            JavaStmt::Synchronized { body, .. } => Self::can_complete_normally(body),
            JavaStmt::While {
                label,
                condition,
                body,
            } => {
                !Self::is_true(condition)
                    || Self::contains_exiting_break(body, label.as_ref(), true)
            }
            JavaStmt::DoWhile {
                label,
                body,
                condition,
            } => {
                Self::contains_exiting_break(body, label.as_ref(), true)
                    || (Self::can_complete_normally(body) && !Self::is_true(condition))
            }
            JavaStmt::For {
                label,
                condition,
                body,
                ..
            } => {
                condition
                    .as_ref()
                    .is_some_and(|condition| !Self::is_true(condition))
                    || Self::contains_exiting_break(body, label.as_ref(), true)
            }
            JavaStmt::Switch { label, cases, .. } => {
                Self::switch_can_complete_normally(label.as_ref(), cases)
            }
            JavaStmt::Try {
                body,
                catches,
                finally,
            } => {
                let protected_completes = Self::can_complete_normally(body)
                    || catches
                        .iter()
                        .any(|catch| Self::can_complete_normally(&catch.body));
                let finally_completes = finally.as_deref().is_none_or(Self::can_complete_normally);
                protected_completes && finally_completes
            }
            JavaStmt::Empty
            | JavaStmt::Variable { .. }
            | JavaStmt::Expression(_)
            | JavaStmt::ConstructorInvocation { .. }
            | JavaStmt::Assign { .. }
            | JavaStmt::If {
                else_stmt: None, ..
            }
            | JavaStmt::Labeled { .. }
            | JavaStmt::ForEach { .. } => true,
        }
    }

    fn is_true(expression: &JavaExpr) -> bool {
        matches!(
            expression,
            JavaExpr::Literal(super::JavaLiteral::Boolean(true))
        )
    }

    fn switch_can_complete_normally(
        label: Option<&JavaIdentifier>,
        cases: &[JavaSwitchCase],
    ) -> bool {
        if cases.is_empty() || !cases.iter().any(|case| case.is_default) {
            return true;
        }
        if cases
            .last()
            .is_some_and(|case| Self::sequence_can_complete_normally(&case.body))
        {
            return true;
        }
        cases.iter().any(|case| {
            case.body
                .iter()
                .any(|statement| Self::contains_exiting_break(statement, label, true))
        })
    }

    fn contains_exiting_break(
        root: &JavaStmt,
        target_label: Option<&JavaIdentifier>,
        direct: bool,
    ) -> bool {
        let mut pending = vec![(root, direct)];
        while let Some((statement, direct)) = pending.pop() {
            match statement {
                JavaStmt::Break(None) if direct => return true,
                JavaStmt::Break(Some(label)) if target_label == Some(label) => return true,
                JavaStmt::Block(statements) => {
                    pending.extend(statements.iter().map(|statement| (statement, direct)));
                }
                JavaStmt::If {
                    then_stmt,
                    else_stmt,
                    ..
                } => {
                    pending.push((then_stmt, direct));
                    pending.extend(else_stmt.as_deref().map(|statement| (statement, direct)));
                }
                JavaStmt::Labeled { body, .. } | JavaStmt::Synchronized { body, .. } => {
                    pending.push((body, direct));
                }
                JavaStmt::Try {
                    body,
                    catches,
                    finally,
                } => {
                    pending.push((body, direct));
                    pending.extend(catches.iter().map(|catch| (&catch.body, direct)));
                    pending.extend(finally.as_deref().map(|statement| (statement, direct)));
                }
                JavaStmt::While { body, .. }
                | JavaStmt::DoWhile { body, .. }
                | JavaStmt::For { body, .. }
                | JavaStmt::ForEach { body, .. } => {
                    if target_label.is_some() {
                        pending.push((body, false));
                    }
                }
                JavaStmt::Switch { cases, .. } => {
                    if target_label.is_some() {
                        pending.extend(
                            cases
                                .iter()
                                .flat_map(|case| &case.body)
                                .map(|statement| (statement, false)),
                        );
                    }
                }
                JavaStmt::Empty
                | JavaStmt::Variable { .. }
                | JavaStmt::Expression(_)
                | JavaStmt::ConstructorInvocation { .. }
                | JavaStmt::Assign { .. }
                | JavaStmt::Return(_)
                | JavaStmt::Throw(_)
                | JavaStmt::Break(None)
                | JavaStmt::Break(Some(_))
                | JavaStmt::Continue(_) => {}
            }
        }
        false
    }

    fn nesting_depth(statement: &JavaStmt) -> usize {
        match statement {
            JavaStmt::Block(statements) => statements
                .iter()
                .map(Self::nesting_depth)
                .max()
                .unwrap_or_default(),
            JavaStmt::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                1 + Self::nesting_depth(then_stmt).max(
                    else_stmt
                        .as_deref()
                        .map(Self::nesting_depth)
                        .unwrap_or_default(),
                )
            }
            JavaStmt::Labeled { body, .. }
            | JavaStmt::While { body, .. }
            | JavaStmt::DoWhile { body, .. }
            | JavaStmt::For { body, .. }
            | JavaStmt::ForEach { body, .. }
            | JavaStmt::Synchronized { body, .. } => 1 + Self::nesting_depth(body),
            JavaStmt::Switch { cases, .. } => {
                1 + cases
                    .iter()
                    .flat_map(|case| &case.body)
                    .map(Self::nesting_depth)
                    .max()
                    .unwrap_or_default()
            }
            JavaStmt::Try {
                body,
                catches,
                finally,
            } => {
                let branches = std::iter::once(body.as_ref())
                    .chain(catches.iter().map(|catch| &catch.body))
                    .chain(finally.as_deref());
                1 + branches.map(Self::nesting_depth).max().unwrap_or_default()
            }
            JavaStmt::Empty
            | JavaStmt::Variable { .. }
            | JavaStmt::Expression(_)
            | JavaStmt::ConstructorInvocation { .. }
            | JavaStmt::Assign { .. }
            | JavaStmt::Return(_)
            | JavaStmt::Throw(_)
            | JavaStmt::Break(_)
            | JavaStmt::Continue(_) => 0,
        }
    }

    fn sequence_cost(statements: &[JavaStmt]) -> usize {
        statements.iter().map(Self::statement_cost).sum()
    }

    fn statement_cost(statement: &JavaStmt) -> usize {
        match statement {
            JavaStmt::Empty => 0,
            JavaStmt::Variable { value, .. } => {
                1 + value.as_ref().map(JavaExpr::cost).unwrap_or_default()
            }
            JavaStmt::Expression(expression) | JavaStmt::Throw(expression) => 1 + expression.cost(),
            JavaStmt::ConstructorInvocation { args, .. } => {
                1 + args.iter().map(JavaExpr::cost).sum::<usize>()
            }
            JavaStmt::Assign { target, value, .. } => 1 + target.cost() + value.cost(),
            JavaStmt::Return(value) => 1 + value.as_ref().map(JavaExpr::cost).unwrap_or_default(),
            JavaStmt::Break(_) | JavaStmt::Continue(_) => 1,
            JavaStmt::Block(statements) => Self::sequence_cost(statements),
            JavaStmt::Labeled { body, .. }
            | JavaStmt::While { body, .. }
            | JavaStmt::DoWhile { body, .. }
            | JavaStmt::ForEach { body, .. }
            | JavaStmt::Synchronized { body, .. } => 1 + Self::statement_cost(body),
            JavaStmt::For {
                init,
                condition,
                update,
                body,
                ..
            } => {
                1 + Self::sequence_cost(init)
                    + condition.as_ref().map(JavaExpr::cost).unwrap_or_default()
                    + update.iter().map(JavaExpr::cost).sum::<usize>()
                    + Self::statement_cost(body)
            }
            JavaStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => {
                1 + condition.cost()
                    + Self::statement_cost(then_stmt)
                    + else_stmt
                        .as_deref()
                        .map(Self::statement_cost)
                        .unwrap_or_default()
            }
            JavaStmt::Switch {
                selector, cases, ..
            } => {
                1 + selector.cost()
                    + cases
                        .iter()
                        .map(|case| Self::sequence_cost(&case.body))
                        .sum::<usize>()
            }
            JavaStmt::Try {
                body,
                catches,
                finally,
            } => {
                1 + Self::statement_cost(body)
                    + catches
                        .iter()
                        .map(|catch| Self::statement_cost(&catch.body))
                        .sum::<usize>()
                    + finally
                        .as_deref()
                        .map(Self::statement_cost)
                        .unwrap_or_default()
            }
        }
    }
}

struct TerminalBranchCandidate {
    duplicates_tail: bool,
}

impl JavaAstTransform for JavaAstNormalizer {
    type Error = super::JavaStructuralError;

    fn apply(&mut self, body: &mut JavaMethodBody) -> Result<bool, Self::Error> {
        let (mut root, mut changed) =
            Self::normalize(std::mem::replace(&mut body.root, JavaStmt::Empty))?;
        if let JavaStmt::Block(statements) = &mut root {
            if let Some(last) = statements.last_mut() {
                changed |= Self::strip_terminal_void_return(last);
            }
            if matches!(statements.last(), Some(JavaStmt::Empty)) {
                statements.pop();
            }
        }
        body.root = root;
        Ok(changed)
    }
}

enum SyntaxTask {
    Visit(JavaStmt),
    Rebuild(SyntaxFrame),
}

enum SyntaxFrame {
    Block(usize),
    Labeled(JavaIdentifier),
    If {
        condition: JavaExpr,
        has_else: bool,
    },
    While {
        label: Option<JavaIdentifier>,
        condition: JavaExpr,
    },
    DoWhile {
        label: Option<JavaIdentifier>,
        condition: JavaExpr,
    },
    For {
        label: Option<JavaIdentifier>,
        init: Vec<JavaStmt>,
        condition: Option<JavaExpr>,
        update: Vec<JavaExpr>,
    },
    ForEach {
        label: Option<JavaIdentifier>,
        ty: JavaType,
        variable: JavaIdentifier,
        iterable: JavaExpr,
    },
    Switch {
        label: Option<JavaIdentifier>,
        selector: JavaExpr,
        cases: Vec<JavaSwitchCase>,
    },
    Try {
        catches: Vec<JavaCatch>,
        has_finally: bool,
    },
    Synchronized(JavaExpr),
}

impl SyntaxFrame {
    fn child_count(&self) -> usize {
        match self {
            Self::Block(count) => *count,
            Self::Labeled(_) => 1,
            Self::If { has_else, .. } => 1 + usize::from(*has_else),
            Self::While { .. }
            | Self::DoWhile { .. }
            | Self::For { .. }
            | Self::ForEach { .. }
            | Self::Synchronized(_) => 1,
            Self::Switch { cases, .. } => cases.len(),
            Self::Try {
                catches,
                has_finally,
            } => 1 + catches.len() + usize::from(*has_finally),
        }
    }

    fn rebuild(
        self,
        children: Vec<JavaStmt>,
    ) -> Result<(JavaStmt, bool), super::JavaStructuralError> {
        let expected = self.child_count();
        if children.len() != expected {
            return Err(super::JavaStructuralError::ChildArity {
                expected,
                actual: children.len(),
            });
        }
        let mut children = children.into_iter();
        let statement = match self {
            Self::Block(_) => {
                let (children, changed) = JavaAstNormalizer::flatten(children.collect());
                return Ok((JavaStmt::Block(children), changed));
            }
            Self::Labeled(label) => JavaStmt::Labeled {
                label,
                body: Box::new(Self::child(&mut children)?),
            },
            Self::If {
                condition,
                has_else,
            } => {
                let then_stmt = Self::child(&mut children)?;
                let else_stmt = if has_else {
                    Some(Self::child(&mut children)?)
                } else {
                    None
                };
                return Ok(JavaAstNormalizer::conditional(
                    condition, then_stmt, else_stmt,
                ));
            }
            Self::While { label, condition } => JavaStmt::While {
                label,
                condition,
                body: Box::new(Self::child(&mut children)?),
            },
            Self::DoWhile { label, condition } => JavaStmt::DoWhile {
                label,
                body: Box::new(Self::child(&mut children)?),
                condition,
            },
            Self::For {
                label,
                init,
                condition,
                update,
            } => JavaStmt::For {
                label,
                init,
                condition,
                update,
                body: Box::new(Self::child(&mut children)?),
            },
            Self::ForEach {
                label,
                ty,
                variable,
                iterable,
            } => {
                return Ok(JavaAstNormalizer::foreach(
                    label,
                    ty,
                    variable,
                    iterable,
                    Self::child(&mut children)?,
                ));
            }
            Self::Switch {
                label,
                selector,
                mut cases,
            } => {
                for case in &mut cases {
                    case.body = match Self::child(&mut children)? {
                        JavaStmt::Block(body) => body,
                        JavaStmt::Empty => Vec::new(),
                        statement => vec![statement],
                    };
                }
                JavaStmt::Switch {
                    label,
                    selector,
                    cases,
                }
            }
            Self::Try {
                mut catches,
                has_finally,
            } => {
                let body = Self::child(&mut children)?;
                for catch in &mut catches {
                    catch.body = Self::child(&mut children)?;
                }
                let finally = if has_finally {
                    Some(Box::new(Self::child(&mut children)?))
                } else {
                    None
                };
                return Ok(JavaAstNormalizer::protection(body, catches, finally));
            }
            Self::Synchronized(lock) => {
                return Ok(JavaAstNormalizer::synchronized(
                    lock,
                    Self::child(&mut children)?,
                ));
            }
        };
        Ok((statement, false))
    }

    fn child(
        children: &mut impl Iterator<Item = JavaStmt>,
    ) -> Result<JavaStmt, super::JavaStructuralError> {
        children
            .next()
            .ok_or(super::JavaStructuralError::MalformedWorkStack)
    }
}

struct NameUseCounter<'a> {
    target: &'a JavaIdentifier,
    count: usize,
}

impl JavaAstRewriter for NameUseCounter<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        if matches!(&expression, JavaExpr::Name(name) if name == self.target) {
            self.count += 1;
        }
        expression
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_completion_appends_default_return_after_semantic_no_return_call() {
        let call = JavaStmt::Expression(JavaExpr::Name(JavaIdentifier::from_dex("neverReturns")));
        let mut body = JavaMethodBody {
            root: JavaStmt::Block(vec![call.clone()]),
        };

        assert!(
            JavaMethodCompletion::new(JavaType::Variable(JavaIdentifier::from_dex("T")))
                .apply(&mut body)
                .unwrap()
        );
        assert_eq!(
            body.root,
            JavaStmt::Block(vec![
                call,
                JavaStmt::Return(Some(JavaExpr::Literal(JavaLiteral::Null))),
            ])
        );
    }
}
