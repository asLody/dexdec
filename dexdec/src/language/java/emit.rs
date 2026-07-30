use std::fmt::Write;

use super::ast::{
    JavaAssignOp, JavaBinaryOp, JavaCatch, JavaConstructorTarget, JavaExpr, JavaIdentifier,
    JavaMethodBody, JavaStmt, JavaSwitchCase, JavaType, JavaUnaryOp,
};
use super::literals::JavaLiterals;
use super::unit::{
    JavaAnnotation, JavaAnnotationValue, JavaAnonymousClassBody, JavaCompilationUnit,
    JavaFieldDeclaration, JavaMethodDeclaration, JavaMethodDeclarationKind, JavaModifier,
    JavaTypeDeclaration,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JavaPrintError {
    MalformedExpression,
    MalformedDeclaration,
    InvalidInlineStatement,
    Formatting,
}

impl std::fmt::Display for JavaPrintError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedExpression => formatter.write_str("malformed Java expression tree"),
            Self::MalformedDeclaration => formatter.write_str("malformed Java declaration tree"),
            Self::InvalidInlineStatement => {
                formatter.write_str("for initializer is not an inline Java statement")
            }
            Self::Formatting => formatter.write_str("failed to format Java source"),
        }
    }
}

impl std::error::Error for JavaPrintError {}

impl From<std::fmt::Error> for JavaPrintError {
    fn from(_: std::fmt::Error) -> Self {
        Self::Formatting
    }
}

#[derive(Debug, Clone)]
pub struct JavaPrinter {
    indent: String,
}

impl Default for JavaPrinter {
    fn default() -> Self {
        Self {
            indent: "    ".to_string(),
        }
    }
}

impl JavaPrinter {
    pub fn new(indent: impl Into<String>) -> Self {
        Self {
            indent: indent.into(),
        }
    }

    pub fn print_method_body(&self, body: &JavaMethodBody) -> Result<String, JavaPrintError> {
        let mut output = String::new();
        self.render(&mut output, vec![PrintTask::Statement(&body.root, 0)])?;
        Ok(output)
    }

    pub fn print_method_body_at(
        &self,
        body: &JavaMethodBody,
        depth: usize,
    ) -> Result<String, JavaPrintError> {
        let mut output = String::new();
        let tasks = match &body.root {
            JavaStmt::Block(statements) => statements
                .iter()
                .rev()
                .map(|statement| PrintTask::Statement(statement, depth))
                .collect(),
            statement => vec![PrintTask::Statement(statement, depth)],
        };
        self.render(&mut output, tasks)?;
        Ok(output)
    }

    pub fn print_compilation_unit(
        &self,
        unit: &JavaCompilationUnit,
    ) -> Result<String, JavaPrintError> {
        let mut output = String::new();
        if let Some(package) = &unit.package {
            writeln!(output, "package {package};\n")?;
        }
        if !unit.imports.is_empty() {
            for import in &unit.imports {
                writeln!(output, "import {import};")?;
            }
            writeln!(output)?;
        }
        self.print_type_tree(&mut output, &unit.declaration)?;
        Ok(output)
    }

    pub fn print_method_declaration(
        &self,
        declaration: &JavaMethodDeclaration,
        depth: usize,
    ) -> Result<String, JavaPrintError> {
        let mut output = String::new();
        self.print_method_into(&mut output, declaration, depth)?;
        Ok(output)
    }

    fn print_type_tree(
        &self,
        output: &mut String,
        root: &JavaTypeDeclaration,
    ) -> Result<(), JavaPrintError> {
        self.print_type_subtree(output, root, 0)
    }

    fn print_anonymous_body(
        &self,
        body: &JavaAnonymousClassBody,
        depth: usize,
    ) -> Result<String, JavaPrintError> {
        let mut output = String::from("{\n");
        let mut wrote_member = false;
        for field in &body.fields {
            if wrote_member {
                writeln!(output)?;
            }
            self.print_field_into(&mut output, field, depth + 1)?;
            wrote_member = true;
        }
        for method in &body.methods {
            if wrote_member {
                writeln!(output)?;
            }
            self.print_method_into(&mut output, method, depth + 1)?;
            wrote_member = true;
        }
        for declaration in &body.nested {
            if wrote_member {
                writeln!(output)?;
            }
            self.print_type_subtree(&mut output, declaration, depth + 1)?;
            wrote_member = true;
        }
        self.indent(&mut output, depth);
        output.push('}');
        Ok(output)
    }

    fn print_type_subtree(
        &self,
        output: &mut String,
        root: &JavaTypeDeclaration,
        root_depth: usize,
    ) -> Result<(), JavaPrintError> {
        let mut pending = vec![TypePrintTask::Declaration {
            declaration: root,
            depth: root_depth,
            leading_blank: false,
        }];
        while let Some(task) = pending.pop() {
            match task {
                TypePrintTask::Declaration {
                    declaration,
                    depth,
                    leading_blank,
                } => {
                    if leading_blank {
                        writeln!(output)?;
                    }
                    let has_members =
                        self.print_type_declaration_into(output, declaration, depth)?;
                    pending.push(TypePrintTask::End { depth });
                    pending.extend(declaration.nested.iter().enumerate().rev().map(
                        |(index, nested)| TypePrintTask::Declaration {
                            declaration: nested,
                            depth: depth + 1,
                            leading_blank: has_members || index != 0,
                        },
                    ));
                }
                TypePrintTask::End { depth } => {
                    self.indent(output, depth);
                    writeln!(output, "}}")?;
                }
            }
        }
        Ok(())
    }

    fn print_type_declaration_into(
        &self,
        output: &mut String,
        declaration: &JavaTypeDeclaration,
        depth: usize,
    ) -> Result<bool, JavaPrintError> {
        self.annotations(output, &declaration.annotations, depth)?;
        self.indent(output, depth);
        self.modifiers(output, &declaration.modifiers)?;
        write!(
            output,
            "{} {}{}",
            declaration.kind.token(),
            declaration.name,
            Self::type_parameters(&declaration.type_parameters)
        )?;
        if let Some(extends) = &declaration.extends {
            write!(output, " extends {extends}")?;
        }
        if !declaration.implements.is_empty() {
            let relation = if declaration.kind.is_interface() {
                "extends"
            } else {
                "implements"
            };
            write!(
                output,
                " {relation} {}",
                declaration
                    .implements
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        }
        writeln!(output, " {{")?;

        let mut wrote_member = false;
        for (index, constant) in declaration.enum_constants.iter().enumerate() {
            if index != 0 {
                writeln!(output, ",")?;
            }
            self.annotations(output, &constant.annotations, depth + 1)?;
            self.indent(output, depth + 1);
            write!(output, "{}", constant.name)?;
            if !constant.arguments.is_empty() {
                write!(
                    output,
                    "({})",
                    constant
                        .arguments
                        .iter()
                        .map(|argument| self.target_typed_expression_at(argument, depth + 1))
                        .collect::<Result<Vec<_>, _>>()?
                        .join(", ")
                )?;
            }
            if let Some(body) = &constant.body {
                write!(output, " {}", self.print_anonymous_body(body, depth + 1)?)?;
            }
        }
        if !declaration.enum_constants.is_empty() {
            writeln!(output, ";")?;
            wrote_member = true;
        }
        for field in &declaration.fields {
            if wrote_member {
                writeln!(output)?;
            }
            self.print_field_into(output, field, depth + 1)?;
            wrote_member = true;
        }
        for method in &declaration.methods {
            if wrote_member {
                writeln!(output)?;
            }
            self.print_method_into(output, method, depth + 1)?;
            wrote_member = true;
        }
        Ok(wrote_member)
    }

    fn print_field_into(
        &self,
        output: &mut String,
        field: &JavaFieldDeclaration,
        depth: usize,
    ) -> Result<(), JavaPrintError> {
        self.annotations(output, &field.annotations, depth)?;
        self.indent(output, depth);
        self.modifiers(output, &field.modifiers)?;
        write!(output, "{} {}", field.ty, field.name)?;
        if let Some(initializer) = &field.initializer {
            write!(
                output,
                " = {}",
                self.target_typed_expression_at(initializer, depth)?
            )?;
        }
        writeln!(output, ";")?;
        Ok(())
    }

    fn print_method_into(
        &self,
        output: &mut String,
        method: &JavaMethodDeclaration,
        depth: usize,
    ) -> Result<(), JavaPrintError> {
        self.annotations(output, &method.annotations, depth)?;
        self.indent(output, depth);
        if method.kind == JavaMethodDeclarationKind::ClassInitializer {
            write!(output, "static")?;
        } else {
            self.modifiers(output, &method.modifiers)?;
            let parameters = method
                .parameters
                .iter()
                .map(|parameter| {
                    let annotations = parameter
                        .annotations
                        .iter()
                        .map(|annotation| self.annotation(annotation))
                        .collect::<Result<Vec<_>, _>>()?;
                    let prefix = if annotations.is_empty() {
                        String::new()
                    } else {
                        format!("{} ", annotations.join(" "))
                    };
                    let ty = if parameter.varargs {
                        match &parameter.ty {
                            JavaType::Array(element) => format!("{element}..."),
                            ty => ty.to_string(),
                        }
                    } else {
                        parameter.ty.to_string()
                    };
                    Ok(format!("{prefix}{ty} {}", parameter.name))
                })
                .collect::<Result<Vec<_>, JavaPrintError>>()?
                .join(", ");
            match method.kind {
                JavaMethodDeclarationKind::Method => {
                    let return_type = method
                        .return_type
                        .as_ref()
                        .ok_or(JavaPrintError::MalformedDeclaration)?;
                    let name = method
                        .name
                        .as_ref()
                        .ok_or(JavaPrintError::MalformedDeclaration)?;
                    write!(
                        output,
                        "{}{} {name}({parameters})",
                        Self::type_parameters_prefix(&method.type_parameters),
                        return_type,
                    )?;
                }
                JavaMethodDeclarationKind::Constructor => {
                    let name = method
                        .name
                        .as_ref()
                        .ok_or(JavaPrintError::MalformedDeclaration)?;
                    write!(
                        output,
                        "{}{name}({parameters})",
                        Self::type_parameters_prefix(&method.type_parameters)
                    )?;
                }
                JavaMethodDeclarationKind::ClassInitializer => {
                    return Err(JavaPrintError::MalformedDeclaration);
                }
            }
            if !method.throws.is_empty() {
                write!(
                    output,
                    " throws {}",
                    method
                        .throws
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                )?;
            }
        }
        let Some(body) = &method.body else {
            writeln!(output, ";")?;
            return Ok(());
        };
        writeln!(output, " {{")?;
        output.push_str(&self.print_method_body_at(body, depth + 1)?);
        self.indent(output, depth);
        writeln!(output, "}}")?;
        Ok(())
    }

    fn annotations(
        &self,
        output: &mut String,
        annotations: &[JavaAnnotation],
        depth: usize,
    ) -> Result<(), JavaPrintError> {
        for annotation in annotations {
            self.indent(output, depth);
            writeln!(output, "{}", self.annotation(annotation)?)?;
        }
        Ok(())
    }

    fn annotation(&self, annotation: &JavaAnnotation) -> Result<String, JavaPrintError> {
        let mut output = format!("@{}", annotation.ty);
        if annotation.elements.is_empty() {
            return Ok(output);
        }
        let implicit_value =
            annotation.elements.len() == 1 && annotation.elements[0].name.as_str() == "value";
        let elements = annotation
            .elements
            .iter()
            .map(|element| {
                let value = self.annotation_value(&element.value)?;
                Ok(if implicit_value {
                    value
                } else {
                    format!("{} = {value}", element.name)
                })
            })
            .collect::<Result<Vec<_>, JavaPrintError>>()?;
        write!(output, "({})", elements.join(", "))?;
        Ok(output)
    }

    fn annotation_value(&self, value: &JavaAnnotationValue) -> Result<String, JavaPrintError> {
        match value {
            JavaAnnotationValue::Expression(expression) => {
                self.target_typed_expression_at(expression, 0)
            }
            JavaAnnotationValue::Annotation(annotation) => self.annotation(annotation),
            JavaAnnotationValue::Array(values) => Ok(format!(
                "{{{}}}",
                values
                    .iter()
                    .map(|value| self.annotation_value(value))
                    .collect::<Result<Vec<_>, _>>()?
                    .join(", ")
            )),
        }
    }

    fn modifiers(
        &self,
        output: &mut String,
        modifiers: &[JavaModifier],
    ) -> Result<(), JavaPrintError> {
        for modifier in modifiers {
            write!(output, "{} ", modifier.token())?;
        }
        Ok(())
    }

    fn type_parameters(parameters: &[super::JavaTypeParameter]) -> String {
        if parameters.is_empty() {
            return String::new();
        }
        format!(
            "<{}>",
            parameters
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    fn type_parameters_prefix(parameters: &[super::JavaTypeParameter]) -> String {
        let parameters = Self::type_parameters(parameters);
        (!parameters.is_empty())
            .then(|| format!("{parameters} "))
            .unwrap_or_default()
    }

    fn render<'a>(
        &self,
        output: &mut String,
        mut pending: Vec<PrintTask<'a>>,
    ) -> Result<(), JavaPrintError> {
        while let Some(task) = pending.pop() {
            match task {
                PrintTask::Statement(statement, depth) => {
                    self.schedule_statement(output, statement, depth, &mut pending)?
                }
                PrintTask::ControlBody(body, depth) => {
                    if matches!(body, JavaStmt::Block(_)) {
                        pending.push(PrintTask::Statement(body, depth));
                    } else {
                        writeln!(output, "{{")?;
                        pending.push(PrintTask::CloseBrace(depth));
                        pending.push(PrintTask::Statement(body, depth + 1));
                    }
                }
                PrintTask::CloseBrace(depth) => {
                    self.indent(output, depth);
                    writeln!(output, "}}")?;
                }
                PrintTask::Else(body, depth) => {
                    Self::continue_clause(output, "else ")?;
                    pending.push(PrintTask::ControlBody(body, depth));
                }
                PrintTask::DoWhileTail(condition, depth) => {
                    Self::continue_clause(output, "")?;
                    writeln!(output, "while ({});", self.expression_at(condition, depth)?)?;
                }
                PrintTask::Catch(catch, depth) => {
                    let types = catch
                        .types
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(" | ");
                    Self::continue_clause(output, &format!("catch ({types} {}) ", catch.variable))?;
                    pending.push(PrintTask::ControlBody(&catch.body, depth));
                }
                PrintTask::Finally(body, depth) => {
                    Self::continue_clause(output, "finally ")?;
                    pending.push(PrintTask::ControlBody(body, depth));
                }
                PrintTask::SwitchCase(case, depth) => {
                    for label in &case.labels {
                        self.indent(output, depth);
                        writeln!(output, "case {}:", self.expression_at(label, depth)?)?;
                    }
                    if case.is_default {
                        self.indent(output, depth);
                        writeln!(output, "default:")?;
                    }
                    pending.extend(
                        case.body
                            .iter()
                            .rev()
                            .map(|statement| PrintTask::Statement(statement, depth + 1)),
                    );
                }
            }
        }
        Ok(())
    }

    fn continue_clause(output: &mut String, clause: &str) -> Result<(), JavaPrintError> {
        if output.ends_with('\n') {
            output.pop();
        }
        write!(output, " {clause}")?;
        Ok(())
    }

    fn schedule_statement<'a>(
        &self,
        output: &mut String,
        statement: &'a JavaStmt,
        depth: usize,
        pending: &mut Vec<PrintTask<'a>>,
    ) -> Result<(), JavaPrintError> {
        match statement {
            JavaStmt::Empty => {}
            JavaStmt::Block(statements) => {
                writeln!(output, "{{")?;
                pending.push(PrintTask::CloseBrace(depth));
                pending.extend(
                    statements
                        .iter()
                        .rev()
                        .map(|statement| PrintTask::Statement(statement, depth + 1)),
                );
            }
            JavaStmt::Labeled { label, body } => {
                self.indent(output, depth);
                write!(output, "{label}: ")?;
                match body.as_ref() {
                    JavaStmt::Block(statements) => {
                        writeln!(output, "{{")?;
                        pending.push(PrintTask::CloseBrace(depth));
                        pending.extend(
                            statements
                                .iter()
                                .rev()
                                .map(|statement| PrintTask::Statement(statement, depth + 1)),
                        );
                    }
                    statement => {
                        writeln!(output)?;
                        pending.push(PrintTask::Statement(statement, depth + 1));
                    }
                }
            }
            JavaStmt::Variable { ty, name, value } => {
                self.indent(output, depth);
                write!(output, "{ty} {name}")?;
                if let Some(value) = value {
                    write!(
                        output,
                        " = {}",
                        self.target_typed_expression_at(value, depth)?
                    )?;
                }
                writeln!(output, ";")?;
            }
            JavaStmt::Expression(expression) => {
                self.indent(output, depth);
                writeln!(output, "{};", self.expression_at(expression, depth)?)?;
            }
            JavaStmt::ConstructorInvocation { target, args } => {
                self.indent(output, depth);
                let target = match target {
                    JavaConstructorTarget::This => "this",
                    JavaConstructorTarget::Super => "super",
                };
                writeln!(
                    output,
                    "{}({});",
                    target,
                    args.iter()
                        .map(|argument| self.target_typed_expression_at(argument, depth))
                        .collect::<Result<Vec<_>, _>>()?
                        .join(", ")
                )?;
            }
            JavaStmt::Assign { target, op, value } => {
                self.indent(output, depth);
                writeln!(
                    output,
                    "{} {} {};",
                    self.expression_at(target, depth)?,
                    op.token(),
                    self.target_typed_expression_at(value, depth)?
                )?;
            }
            JavaStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => {
                self.indent(output, depth);
                write!(output, "if ({}) ", self.expression_at(condition, depth)?)?;
                if let Some(else_stmt) = else_stmt {
                    pending.push(PrintTask::Else(else_stmt, depth));
                }
                pending.push(PrintTask::ControlBody(then_stmt, depth));
            }
            JavaStmt::While {
                label,
                condition,
                body,
            } => {
                self.label(output, label, depth)?;
                self.indent(output, depth);
                write!(output, "while ({}) ", self.expression_at(condition, depth)?)?;
                pending.push(PrintTask::ControlBody(body, depth));
            }
            JavaStmt::DoWhile {
                label,
                body,
                condition,
            } => {
                self.label(output, label, depth)?;
                self.indent(output, depth);
                write!(output, "do ")?;
                pending.push(PrintTask::DoWhileTail(condition, depth));
                pending.push(PrintTask::ControlBody(body, depth));
            }
            JavaStmt::For {
                label,
                init,
                condition,
                update,
                body,
            } => {
                self.label(output, label, depth)?;
                self.indent(output, depth);
                let init = init
                    .iter()
                    .map(|statement| self.inline_statement(statement, depth))
                    .collect::<Result<Vec<_>, _>>()?
                    .join(", ");
                let condition = condition
                    .as_ref()
                    .map(|condition| self.expression_at(condition, depth))
                    .transpose()?
                    .unwrap_or_default();
                let update = update
                    .iter()
                    .map(|expression| self.expression_at(expression, depth))
                    .collect::<Result<Vec<_>, _>>()?
                    .join(", ");
                write!(output, "for ({init}; {condition}; {update}) ")?;
                pending.push(PrintTask::ControlBody(body, depth));
            }
            JavaStmt::ForEach {
                label,
                ty,
                variable,
                iterable,
                body,
            } => {
                self.label(output, label, depth)?;
                self.indent(output, depth);
                write!(
                    output,
                    "for ({} {} : {}) ",
                    ty,
                    variable,
                    self.expression_at(iterable, depth)?
                )?;
                pending.push(PrintTask::ControlBody(body, depth));
            }
            JavaStmt::Switch {
                label,
                selector,
                cases,
            } => {
                self.label(output, label, depth)?;
                self.indent(output, depth);
                writeln!(
                    output,
                    "switch ({}) {{",
                    self.expression_at(selector, depth)?
                )?;
                pending.push(PrintTask::CloseBrace(depth));
                pending.extend(
                    cases
                        .iter()
                        .rev()
                        .map(|case| PrintTask::SwitchCase(case, depth + 1)),
                );
            }
            JavaStmt::Try {
                body,
                catches,
                finally,
            } => {
                self.indent(output, depth);
                write!(output, "try ")?;
                if let Some(finally) = finally {
                    pending.push(PrintTask::Finally(finally, depth));
                }
                pending.extend(
                    catches
                        .iter()
                        .rev()
                        .map(|catch| PrintTask::Catch(catch, depth)),
                );
                pending.push(PrintTask::ControlBody(body, depth));
            }
            JavaStmt::Synchronized { lock, body } => {
                self.indent(output, depth);
                write!(
                    output,
                    "synchronized ({}) ",
                    self.expression_at(lock, depth)?
                )?;
                pending.push(PrintTask::ControlBody(body, depth));
            }
            JavaStmt::Return(value) => {
                self.indent(output, depth);
                match value {
                    Some(value) => writeln!(
                        output,
                        "return {};",
                        self.target_typed_expression_at(value, depth)?
                    )?,
                    None => writeln!(output, "return;")?,
                }
            }
            JavaStmt::Throw(value) => {
                self.indent(output, depth);
                writeln!(output, "throw {};", self.expression_at(value, depth)?)?;
            }
            JavaStmt::Break(label) => {
                self.indent(output, depth);
                Self::control(output, "break", label)?;
            }
            JavaStmt::Continue(label) => {
                self.indent(output, depth);
                Self::control(output, "continue", label)?;
            }
        }
        Ok(())
    }

    fn expression_at(&self, expression: &JavaExpr, depth: usize) -> Result<String, JavaPrintError> {
        self.render_expression(
            expression,
            ExpressionRequirement::Any,
            TargetTypingContext::Standalone,
            depth,
        )
    }

    fn target_typed_expression_at(
        &self,
        expression: &JavaExpr,
        depth: usize,
    ) -> Result<String, JavaPrintError> {
        self.render_expression(
            expression,
            ExpressionRequirement::Any,
            TargetTypingContext::TargetTyped,
            depth,
        )
    }

    fn render_expression(
        &self,
        expression: &JavaExpr,
        requirement: ExpressionRequirement,
        target_typing: TargetTypingContext,
        depth: usize,
    ) -> Result<String, JavaPrintError> {
        let mut pending = vec![ExpressionTask::Visit {
            expression,
            requirement,
            target_typing,
        }];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                ExpressionTask::Visit {
                    expression,
                    requirement,
                    target_typing,
                } => match expression {
                    JavaExpr::This => results.push(RenderedExpression::primary("this")),
                    JavaExpr::QualifiedThis(ty) => {
                        results.push(RenderedExpression::primary(format!("{ty}.this")))
                    }
                    JavaExpr::Super => results.push(RenderedExpression::primary("super")),
                    JavaExpr::Name(value) => {
                        results.push(RenderedExpression::primary(value.to_string()))
                    }
                    JavaExpr::Literal(value) => {
                        results.push(RenderedExpression::primary(JavaLiterals::render(value)))
                    }
                    JavaExpr::ClassLiteral(ty) => {
                        results.push(RenderedExpression::primary(format!("{ty}.class")))
                    }
                    JavaExpr::StaticField { owner, name } => {
                        results.push(RenderedExpression::primary(format!("{owner}.{name}")))
                    }
                    JavaExpr::Field { owner, name } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Field {
                            name,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit {
                            expression: owner,
                            requirement: ExpressionRequirement::Primary,
                            target_typing: TargetTypingContext::Standalone,
                        });
                    }
                    JavaExpr::ArrayAccess { array, index } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::ArrayAccess {
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit {
                            expression: index,
                            requirement: ExpressionRequirement::Any,
                            target_typing: TargetTypingContext::Standalone,
                        });
                        pending.push(ExpressionTask::Visit {
                            expression: array,
                            requirement: ExpressionRequirement::Primary,
                            target_typing: TargetTypingContext::Standalone,
                        });
                    }
                    JavaExpr::Call {
                        receiver,
                        owner,
                        type_arguments,
                        method,
                        args,
                    } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Call {
                            has_receiver: receiver.is_some(),
                            owner: owner.as_ref(),
                            type_arguments,
                            method,
                            args: args.len(),
                            requirement,
                        }));
                        pending.extend(args.iter().rev().map(|argument| ExpressionTask::Visit {
                            expression: argument,
                            requirement: ExpressionRequirement::Any,
                            target_typing: TargetTypingContext::TargetTyped,
                        }));
                        if let Some(receiver) = receiver {
                            pending.push(ExpressionTask::Visit {
                                expression: receiver,
                                requirement: ExpressionRequirement::Primary,
                                target_typing: TargetTypingContext::Standalone,
                            });
                        }
                    }
                    JavaExpr::MethodReference { receiver, method } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::MethodReference {
                            method,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit {
                            expression: receiver,
                            requirement: ExpressionRequirement::Primary,
                            target_typing: TargetTypingContext::Standalone,
                        });
                    }
                    JavaExpr::Lambda { parameters, body } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Lambda {
                            parameters,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit {
                            expression: body,
                            requirement: ExpressionRequirement::Any,
                            target_typing: TargetTypingContext::TargetTyped,
                        });
                    }
                    JavaExpr::BlockLambda { parameters, body } => {
                        let parameters = Self::lambda_parameters(parameters);
                        let mut rendered_body = String::new();
                        self.render(&mut rendered_body, vec![PrintTask::Statement(body, depth)])?;
                        results.push(
                            RenderedExpression {
                                text: format!("{parameters} -> {}", rendered_body.trim_end()),
                                precedence: ExpressionPrecedence::Assignment,
                                binary: None,
                            }
                            .requiring(requirement),
                        );
                    }
                    JavaExpr::New {
                        enclosing,
                        ty,
                        target_type,
                        args,
                        anonymous_body,
                    } => {
                        let diamond = target_typing == TargetTypingContext::TargetTyped
                            && target_type.is_some()
                            && anonymous_body.is_none()
                            && matches!(
                                ty,
                                JavaType::Class(class)
                                    if class
                                        .segments
                                        .last()
                                        .is_some_and(|segment| !segment.arguments.is_empty())
                            );
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::New {
                            has_enclosing: enclosing.is_some(),
                            ty,
                            diamond,
                            args: args.len(),
                            anonymous_body: anonymous_body
                                .as_deref()
                                .map(|body| self.print_anonymous_body(body, depth))
                                .transpose()?,
                            requirement,
                        }));
                        pending.extend(args.iter().rev().map(|argument| ExpressionTask::Visit {
                            expression: argument,
                            requirement: ExpressionRequirement::Any,
                            target_typing: TargetTypingContext::TargetTyped,
                        }));
                        if let Some(enclosing) = enclosing {
                            pending.push(ExpressionTask::Visit {
                                expression: enclosing,
                                requirement: ExpressionRequirement::Primary,
                                target_typing: TargetTypingContext::Standalone,
                            });
                        }
                    }
                    JavaExpr::NewArray {
                        element_type,
                        dimensions,
                        initializer,
                    } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::NewArray {
                            element_type,
                            dimensions: dimensions.len(),
                            initializer: initializer.len(),
                            requirement,
                        }));
                        pending.extend(initializer.iter().rev().map(|item| {
                            ExpressionTask::Visit {
                                expression: item,
                                requirement: ExpressionRequirement::Any,
                                target_typing: TargetTypingContext::TargetTyped,
                            }
                        }));
                        pending.extend(dimensions.iter().rev().map(|dimension| {
                            ExpressionTask::Visit {
                                expression: dimension,
                                requirement: ExpressionRequirement::Any,
                                target_typing: TargetTypingContext::Standalone,
                            }
                        }));
                    }
                    JavaExpr::Unary { op, operand } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Unary {
                            op: *op,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit {
                            expression: operand,
                            requirement: ExpressionRequirement::Unary,
                            target_typing: TargetTypingContext::Standalone,
                        });
                    }
                    JavaExpr::Update { op, target, prefix } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Update {
                            op: *op,
                            prefix: *prefix,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit {
                            expression: target,
                            requirement: ExpressionRequirement::Primary,
                            target_typing: TargetTypingContext::Standalone,
                        });
                    }
                    JavaExpr::Binary { left, op, right } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Binary {
                            op: *op,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit {
                            expression: right,
                            requirement: ExpressionRequirement::Any,
                            target_typing: TargetTypingContext::Standalone,
                        });
                        pending.push(ExpressionTask::Visit {
                            expression: left,
                            requirement: ExpressionRequirement::Any,
                            target_typing: TargetTypingContext::Standalone,
                        });
                    }
                    JavaExpr::Cast { ty, value } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Cast {
                            ty,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit {
                            expression: value,
                            requirement: ExpressionRequirement::Unary,
                            target_typing: TargetTypingContext::Standalone,
                        });
                    }
                    JavaExpr::InstanceOf { value, ty } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::InstanceOf {
                            ty,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit {
                            expression: value,
                            requirement: ExpressionRequirement::Any,
                            target_typing: TargetTypingContext::Standalone,
                        });
                    }
                    JavaExpr::Conditional {
                        condition,
                        when_true,
                        when_false,
                    } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Conditional {
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit {
                            expression: when_false,
                            requirement: ExpressionRequirement::Any,
                            target_typing,
                        });
                        pending.push(ExpressionTask::Visit {
                            expression: when_true,
                            requirement: ExpressionRequirement::Any,
                            target_typing,
                        });
                        pending.push(ExpressionTask::Visit {
                            expression: condition,
                            requirement: ExpressionRequirement::Any,
                            target_typing: TargetTypingContext::Standalone,
                        });
                    }
                    JavaExpr::Assignment { target, op, value } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Assignment {
                            op: *op,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit {
                            expression: value,
                            requirement: ExpressionRequirement::Any,
                            target_typing: TargetTypingContext::TargetTyped,
                        });
                        pending.push(ExpressionTask::Visit {
                            expression: target,
                            requirement: ExpressionRequirement::Any,
                            target_typing: TargetTypingContext::Standalone,
                        });
                    }
                },
                ExpressionTask::Rebuild(frame) => {
                    let count = frame.child_count();
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(JavaPrintError::MalformedExpression)?;
                    let children = results.drain(start..).collect();
                    results.push(frame.render(children)?);
                }
            }
        }
        if results.len() != 1 {
            return Err(JavaPrintError::MalformedExpression);
        }
        results
            .pop()
            .map(|rendered| rendered.text)
            .ok_or(JavaPrintError::MalformedExpression)
    }

    fn label(
        &self,
        output: &mut String,
        label: &Option<JavaIdentifier>,
        depth: usize,
    ) -> Result<(), JavaPrintError> {
        if let Some(label) = label {
            self.indent(output, depth);
            writeln!(output, "{label}:")?;
        }
        Ok(())
    }

    fn control(
        output: &mut String,
        keyword: &str,
        label: &Option<JavaIdentifier>,
    ) -> Result<(), JavaPrintError> {
        match label {
            Some(label) => writeln!(output, "{keyword} {label};")?,
            None => writeln!(output, "{keyword};")?,
        }
        Ok(())
    }

    fn inline_statement(
        &self,
        statement: &JavaStmt,
        depth: usize,
    ) -> Result<String, JavaPrintError> {
        Ok(match statement {
            JavaStmt::Variable { ty, name, value } => match value {
                Some(value) => format!(
                    "{ty} {name} = {}",
                    self.target_typed_expression_at(value, depth)?
                ),
                None => format!("{ty} {name}"),
            },
            JavaStmt::Assign { target, op, value } => format!(
                "{} {} {}",
                self.expression_at(target, depth)?,
                op.token(),
                self.target_typed_expression_at(value, depth)?
            ),
            JavaStmt::Expression(expression) => self.expression_at(expression, depth)?,
            _ => return Err(JavaPrintError::InvalidInlineStatement),
        })
    }

    fn indent(&self, output: &mut String, depth: usize) {
        for _ in 0..depth {
            output.push_str(&self.indent);
        }
    }

    fn lambda_parameters(parameters: &[JavaIdentifier]) -> String {
        match parameters {
            [] => "()".to_string(),
            [parameter] => parameter.to_string(),
            parameters => format!(
                "({})",
                parameters
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

enum TypePrintTask<'a> {
    Declaration {
        declaration: &'a JavaTypeDeclaration,
        depth: usize,
        leading_blank: bool,
    },
    End {
        depth: usize,
    },
}

enum PrintTask<'a> {
    Statement(&'a JavaStmt, usize),
    ControlBody(&'a JavaStmt, usize),
    CloseBrace(usize),
    Else(&'a JavaStmt, usize),
    DoWhileTail(&'a JavaExpr, usize),
    Catch(&'a JavaCatch, usize),
    Finally(&'a JavaStmt, usize),
    SwitchCase(&'a JavaSwitchCase, usize),
}

enum ExpressionTask<'a> {
    Visit {
        expression: &'a JavaExpr,
        requirement: ExpressionRequirement,
        target_typing: TargetTypingContext,
    },
    Rebuild(ExpressionFrame<'a>),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TargetTypingContext {
    Standalone,
    TargetTyped,
}

#[derive(Clone, Copy)]
enum ExpressionRequirement {
    Any,
    Unary,
    Primary,
}

impl ExpressionRequirement {
    fn accepts(self, shape: ExpressionShape) -> bool {
        match self {
            Self::Any => true,
            Self::Unary => matches!(shape, ExpressionShape::Primary | ExpressionShape::Unary),
            Self::Primary => shape == ExpressionShape::Primary,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ExpressionShape {
    Primary,
    Unary,
    Other,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum ExpressionPrecedence {
    Assignment,
    Conditional,
    LogicalOr,
    LogicalAnd,
    BitOr,
    BitXor,
    BitAnd,
    Equality,
    Relational,
    Shift,
    Additive,
    Multiplicative,
    Unary,
    Primary,
}

struct RenderedExpression {
    text: String,
    precedence: ExpressionPrecedence,
    binary: Option<JavaBinaryOp>,
}

impl RenderedExpression {
    fn primary(text: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            precedence: ExpressionPrecedence::Primary,
            binary: None,
        }
    }

    fn parenthesized(self) -> String {
        format!("({})", self.text)
    }

    fn requiring(self, requirement: ExpressionRequirement) -> Self {
        let shape = match self.precedence {
            ExpressionPrecedence::Primary => ExpressionShape::Primary,
            ExpressionPrecedence::Unary => ExpressionShape::Unary,
            _ => ExpressionShape::Other,
        };
        if requirement.accepts(shape) {
            self
        } else {
            Self::primary(self.parenthesized())
        }
    }
}

enum ExpressionFrame<'a> {
    Field {
        name: &'a JavaIdentifier,
        requirement: ExpressionRequirement,
    },
    ArrayAccess {
        requirement: ExpressionRequirement,
    },
    Call {
        has_receiver: bool,
        owner: Option<&'a JavaType>,
        type_arguments: &'a [JavaType],
        method: &'a JavaIdentifier,
        args: usize,
        requirement: ExpressionRequirement,
    },
    MethodReference {
        method: &'a JavaIdentifier,
        requirement: ExpressionRequirement,
    },
    Lambda {
        parameters: &'a [JavaIdentifier],
        requirement: ExpressionRequirement,
    },
    New {
        has_enclosing: bool,
        ty: &'a JavaType,
        diamond: bool,
        args: usize,
        anonymous_body: Option<String>,
        requirement: ExpressionRequirement,
    },
    NewArray {
        element_type: &'a JavaType,
        dimensions: usize,
        initializer: usize,
        requirement: ExpressionRequirement,
    },
    Unary {
        op: JavaUnaryOp,
        requirement: ExpressionRequirement,
    },
    Update {
        op: super::JavaUpdateOp,
        prefix: bool,
        requirement: ExpressionRequirement,
    },
    Binary {
        op: JavaBinaryOp,
        requirement: ExpressionRequirement,
    },
    Cast {
        ty: &'a JavaType,
        requirement: ExpressionRequirement,
    },
    InstanceOf {
        ty: &'a JavaType,
        requirement: ExpressionRequirement,
    },
    Conditional {
        requirement: ExpressionRequirement,
    },
    Assignment {
        op: JavaAssignOp,
        requirement: ExpressionRequirement,
    },
}

impl ExpressionFrame<'_> {
    fn child_count(&self) -> usize {
        match self {
            Self::Field { .. }
            | Self::MethodReference { .. }
            | Self::Lambda { .. }
            | Self::Unary { .. }
            | Self::Update { .. }
            | Self::Cast { .. }
            | Self::InstanceOf { .. } => 1,
            Self::ArrayAccess { .. } | Self::Binary { .. } | Self::Assignment { .. } => 2,
            Self::Conditional { .. } => 3,
            Self::Call {
                has_receiver, args, ..
            } => usize::from(*has_receiver) + args,
            Self::New {
                has_enclosing,
                args,
                ..
            } => usize::from(*has_enclosing) + args,
            Self::NewArray {
                dimensions,
                initializer,
                ..
            } => dimensions + initializer,
        }
    }

    fn render(
        self,
        children: Vec<RenderedExpression>,
    ) -> Result<RenderedExpression, JavaPrintError> {
        let expected = self.child_count();
        if children.len() != expected {
            return Err(JavaPrintError::MalformedExpression);
        }
        let mut children = children.into_iter();
        let (rendered, precedence, binary, requirement) = match self {
            Self::Field { name, requirement } => (
                format!("{}.{}", Self::child(&mut children)?, name),
                ExpressionPrecedence::Primary,
                None,
                requirement,
            ),
            Self::ArrayAccess { requirement } => (
                format!(
                    "{}[{}]",
                    Self::child(&mut children)?,
                    Self::child(&mut children)?
                ),
                ExpressionPrecedence::Primary,
                None,
                requirement,
            ),
            Self::Call {
                has_receiver,
                owner,
                type_arguments,
                method,
                args,
                requirement,
            } => {
                let receiver = if has_receiver {
                    Some(Self::child(&mut children)?)
                } else {
                    None
                };
                let arguments = children
                    .take(args)
                    .map(|child| child.text)
                    .collect::<Vec<_>>()
                    .join(", ");
                let prefix = receiver.or_else(|| owner.map(ToString::to_string));
                let type_arguments = (!type_arguments.is_empty()).then(|| {
                    format!(
                        "<{}>",
                        type_arguments
                            .iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                });
                let method = match type_arguments {
                    Some(type_arguments) => format!("{type_arguments}{method}"),
                    None => method.to_string(),
                };
                (
                    match prefix {
                        Some(prefix) => format!("{prefix}.{method}({arguments})"),
                        None => format!("{method}({arguments})"),
                    },
                    ExpressionPrecedence::Primary,
                    None,
                    requirement,
                )
            }
            Self::MethodReference {
                method,
                requirement,
            } => (
                format!("{}::{method}", Self::child(&mut children)?),
                ExpressionPrecedence::Primary,
                None,
                requirement,
            ),
            Self::Lambda {
                parameters,
                requirement,
            } => {
                let parameters = JavaPrinter::lambda_parameters(parameters);
                (
                    format!("{parameters} -> {}", Self::child(&mut children)?),
                    ExpressionPrecedence::Assignment,
                    None,
                    requirement,
                )
            }
            Self::New {
                has_enclosing,
                ty,
                diamond,
                args,
                anonymous_body,
                requirement,
            } => {
                let enclosing = has_enclosing
                    .then(|| Self::child(&mut children))
                    .transpose()?;
                let arguments = children
                    .take(args)
                    .map(|child| child.text)
                    .collect::<Vec<_>>()
                    .join(", ");
                let mut expression = match enclosing {
                    Some(enclosing) => {
                        let JavaType::Class(class) = ty else {
                            return Err(JavaPrintError::MalformedExpression);
                        };
                        let member = class
                            .segments
                            .last()
                            .ok_or(JavaPrintError::MalformedExpression)?;
                        let mut member = member.clone();
                        if diamond {
                            member.arguments.clear();
                        }
                        format!(
                            "{enclosing}.new {member}{}({arguments})",
                            if diamond { "<>" } else { "" }
                        )
                    }
                    None => {
                        let mut ty = ty.clone();
                        if diamond {
                            let JavaType::Class(class) = &mut ty else {
                                return Err(JavaPrintError::MalformedExpression);
                            };
                            class
                                .segments
                                .last_mut()
                                .ok_or(JavaPrintError::MalformedExpression)?
                                .arguments
                                .clear();
                        }
                        format!("new {ty}{}({arguments})", if diamond { "<>" } else { "" })
                    }
                };
                if let Some(body) = anonymous_body {
                    expression.push(' ');
                    expression.push_str(&body);
                }
                (expression, ExpressionPrecedence::Primary, None, requirement)
            }
            Self::NewArray {
                element_type,
                dimensions,
                initializer,
                requirement,
            } => {
                let (base_type, trailing_rank) = element_type.array_shape();
                let dimensions = children
                    .by_ref()
                    .take(dimensions)
                    .map(|dimension| format!("[{}]", dimension.text))
                    .collect::<String>();
                let dimensions = if dimensions.is_empty() {
                    "[]".to_owned()
                } else {
                    dimensions
                };
                let initializer = children
                    .take(initializer)
                    .map(|child| child.text)
                    .collect::<Vec<_>>();
                let initializer = if initializer.is_empty() {
                    String::new()
                } else {
                    format!(" {{ {} }}", initializer.join(", "))
                };
                (
                    format!(
                        "new {base_type}{dimensions}{}{initializer}",
                        "[]".repeat(trailing_rank)
                    ),
                    ExpressionPrecedence::Primary,
                    None,
                    requirement,
                )
            }
            Self::Unary { op, requirement } => {
                let operand = Self::child_expression(&mut children)?;
                let operand = if operand.precedence <= ExpressionPrecedence::Unary {
                    operand.parenthesized()
                } else {
                    operand.text
                };
                (
                    format!("{}{operand}", op.token()),
                    ExpressionPrecedence::Unary,
                    None,
                    requirement,
                )
            }
            Self::Update {
                op,
                prefix,
                requirement,
            } => {
                let target = Self::child(&mut children)?;
                (
                    if prefix {
                        format!("{}{target}", op.token())
                    } else {
                        format!("{target}{}", op.token())
                    },
                    ExpressionPrecedence::Unary,
                    None,
                    requirement,
                )
            }
            Self::Binary { op, requirement } => {
                let precedence = Self::binary_precedence(op);
                let left = Self::child_expression(&mut children)?;
                let right = Self::child_expression(&mut children)?;
                let left = if left.precedence < precedence {
                    left.parenthesized()
                } else {
                    left.text
                };
                let right = if right.precedence < precedence
                    || (right.precedence == precedence && !Self::right_associative_with(op, &right))
                {
                    right.parenthesized()
                } else {
                    right.text
                };
                (
                    format!("{left} {} {right}", op.token()),
                    precedence,
                    Some(op),
                    requirement,
                )
            }
            Self::Cast { ty, requirement } => (
                format!("({ty}) {}", Self::child(&mut children)?),
                ExpressionPrecedence::Unary,
                None,
                requirement,
            ),
            Self::InstanceOf { ty, requirement } => {
                let value = Self::child_expression(&mut children)?;
                let value = if value.precedence <= ExpressionPrecedence::Relational {
                    value.parenthesized()
                } else {
                    value.text
                };
                (
                    format!("{value} instanceof {ty}"),
                    ExpressionPrecedence::Relational,
                    None,
                    requirement,
                )
            }
            Self::Conditional { requirement } => {
                let condition = Self::child_expression(&mut children)?;
                let when_true = Self::child_expression(&mut children)?;
                let when_false = Self::child_expression(&mut children)?;
                let condition = if condition.precedence <= ExpressionPrecedence::Conditional {
                    condition.parenthesized()
                } else {
                    condition.text
                };
                let when_false = if when_false.precedence < ExpressionPrecedence::Conditional {
                    when_false.parenthesized()
                } else {
                    when_false.text
                };
                (
                    format!("{condition} ? {} : {when_false}", when_true.text),
                    ExpressionPrecedence::Conditional,
                    None,
                    requirement,
                )
            }
            Self::Assignment { op, requirement } => (
                format!(
                    "{} {} {}",
                    Self::child(&mut children)?,
                    op.token(),
                    Self::child(&mut children)?
                ),
                ExpressionPrecedence::Assignment,
                None,
                requirement,
            ),
        };
        Ok(RenderedExpression {
            text: rendered,
            precedence,
            binary,
        }
        .requiring(requirement))
    }

    fn child(
        children: &mut impl Iterator<Item = RenderedExpression>,
    ) -> Result<String, JavaPrintError> {
        Ok(Self::child_expression(children)?.text)
    }

    fn child_expression(
        children: &mut impl Iterator<Item = RenderedExpression>,
    ) -> Result<RenderedExpression, JavaPrintError> {
        children.next().ok_or(JavaPrintError::MalformedExpression)
    }

    fn binary_precedence(operator: JavaBinaryOp) -> ExpressionPrecedence {
        match operator {
            JavaBinaryOp::Multiply | JavaBinaryOp::Divide | JavaBinaryOp::Remainder => {
                ExpressionPrecedence::Multiplicative
            }
            JavaBinaryOp::Add | JavaBinaryOp::Subtract => ExpressionPrecedence::Additive,
            JavaBinaryOp::ShiftLeft
            | JavaBinaryOp::ShiftRight
            | JavaBinaryOp::UnsignedShiftRight => ExpressionPrecedence::Shift,
            JavaBinaryOp::Less
            | JavaBinaryOp::GreaterEqual
            | JavaBinaryOp::Greater
            | JavaBinaryOp::LessEqual => ExpressionPrecedence::Relational,
            JavaBinaryOp::Equal | JavaBinaryOp::NotEqual => ExpressionPrecedence::Equality,
            JavaBinaryOp::BitAnd => ExpressionPrecedence::BitAnd,
            JavaBinaryOp::BitXor => ExpressionPrecedence::BitXor,
            JavaBinaryOp::BitOr => ExpressionPrecedence::BitOr,
            JavaBinaryOp::LogicalAnd => ExpressionPrecedence::LogicalAnd,
            JavaBinaryOp::LogicalOr => ExpressionPrecedence::LogicalOr,
        }
    }

    fn right_associative_with(operator: JavaBinaryOp, right: &RenderedExpression) -> bool {
        right.binary == Some(operator)
            && matches!(
                operator,
                JavaBinaryOp::BitAnd
                    | JavaBinaryOp::BitOr
                    | JavaBinaryOp::BitXor
                    | JavaBinaryOp::LogicalAnd
                    | JavaBinaryOp::LogicalOr
            )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language::java::JavaPrimitiveType;
    use crate::language::java::JavaTypeArgument;

    #[test]
    fn allocated_dimensions_precede_unallocated_array_rank() {
        let element_type = JavaType::array(JavaType::Primitive(JavaPrimitiveType::Byte));
        let expression = ExpressionFrame::NewArray {
            element_type: &element_type,
            dimensions: 1,
            initializer: 0,
            requirement: ExpressionRequirement::Any,
        }
        .render(vec![RenderedExpression::primary("3")])
        .expect("array expression")
        .text;

        assert_eq!(expression, "new byte[3][]");
    }

    #[test]
    fn array_initializer_preserves_the_complete_rank() {
        let element_type = JavaType::array(JavaType::Primitive(JavaPrimitiveType::Byte));
        let expression = ExpressionFrame::NewArray {
            element_type: &element_type,
            dimensions: 0,
            initializer: 1,
            requirement: ExpressionRequirement::Any,
        }
        .render(vec![RenderedExpression::primary("row")])
        .expect("array expression")
        .text;

        assert_eq!(expression, "new byte[][] { row }");
    }

    #[test]
    fn qualified_class_creation_uses_the_member_type_name() {
        let ty = JavaType::source_class("example.Outer.Inner");
        let expression = ExpressionFrame::New {
            has_enclosing: true,
            ty: &ty,
            diamond: false,
            args: 0,
            anonymous_body: None,
            requirement: ExpressionRequirement::Any,
        }
        .render(vec![RenderedExpression::primary("owner")])
        .expect("qualified class creation")
        .text;

        assert_eq!(expression, "owner.new Inner()");
    }

    #[test]
    fn target_typed_construction_uses_diamond_syntax() {
        let mut ty = match JavaType::source_class("java.util.ArrayList") {
            JavaType::Class(ty) => ty,
            _ => unreachable!(),
        };
        ty.segments.last_mut().unwrap().arguments = vec![JavaTypeArgument::Exact(
            JavaType::source_class("java.lang.String"),
        )];
        let ty = JavaType::Class(ty);
        let expression = JavaExpr::New {
            enclosing: None,
            ty: ty.clone(),
            target_type: Some(ty),
            args: Vec::new(),
            anonymous_body: None,
        };
        let expression = JavaPrinter::default()
            .target_typed_expression_at(&expression, 0)
            .expect("diamond construction");

        assert_eq!(expression, "new java.util.ArrayList<>()");
    }

    #[test]
    fn cast_operand_does_not_inherit_target_typing() {
        let mut class = match JavaType::source_class("java.util.ArrayList") {
            JavaType::Class(class) => class,
            _ => unreachable!(),
        };
        class.segments.last_mut().unwrap().arguments = vec![JavaTypeArgument::Exact(
            JavaType::source_class("java.lang.String"),
        )];
        let ty = JavaType::Class(class);
        let expression = JavaExpr::Cast {
            ty: JavaType::source_class("java.lang.Object"),
            value: Box::new(JavaExpr::New {
                enclosing: None,
                ty: ty.clone(),
                target_type: Some(ty),
                args: Vec::new(),
                anonymous_body: None,
            }),
        };
        let expression = JavaPrinter::default()
            .target_typed_expression_at(&expression, 0)
            .expect("cast construction");

        assert_eq!(
            expression,
            "(java.lang.Object) new java.util.ArrayList<java.lang.String>()"
        );
    }
}
