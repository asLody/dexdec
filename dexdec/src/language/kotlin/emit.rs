use std::fmt::Write;

use super::ast::{
    KotlinAssignOp, KotlinBinaryOp, KotlinCallArguments, KotlinCatch, KotlinConstructorTarget,
    KotlinExpr, KotlinIdentifier, KotlinMethodBody, KotlinStmt, KotlinSwitchCase, KotlinType,
    KotlinUnaryOp,
};
use super::literals::KotlinLiterals;
use super::unit::{
    KotlinAnnotation, KotlinAnnotationValue, KotlinAnonymousClassBody, KotlinCompilationUnit,
    KotlinFieldDeclaration, KotlinMethodDeclaration, KotlinMethodDeclarationKind, KotlinModifier,
    KotlinTypeDeclaration,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KotlinPrintError {
    MalformedExpression,
    MalformedDeclaration,
    InvalidInlineStatement,
    Formatting,
}

impl std::fmt::Display for KotlinPrintError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedExpression => formatter.write_str("malformed Kotlin expression tree"),
            Self::MalformedDeclaration => formatter.write_str("malformed Kotlin declaration tree"),
            Self::InvalidInlineStatement => {
                formatter.write_str("for initializer is not an inline Kotlin statement")
            }
            Self::Formatting => formatter.write_str("failed to format Kotlin source"),
        }
    }
}

impl std::error::Error for KotlinPrintError {}

impl From<std::fmt::Error> for KotlinPrintError {
    fn from(_: std::fmt::Error) -> Self {
        Self::Formatting
    }
}

#[derive(Debug, Clone)]
pub struct KotlinPrinter {
    indent: String,
}

impl Default for KotlinPrinter {
    fn default() -> Self {
        Self {
            indent: "    ".to_string(),
        }
    }
}

impl KotlinPrinter {
    pub fn new(indent: impl Into<String>) -> Self {
        Self {
            indent: indent.into(),
        }
    }

    pub fn print_method_body(&self, body: &KotlinMethodBody) -> Result<String, KotlinPrintError> {
        let mut output = String::new();
        self.render(&mut output, vec![PrintTask::Statement(&body.root, 0)])?;
        Ok(output)
    }

    pub fn print_method_body_at(
        &self,
        body: &KotlinMethodBody,
        depth: usize,
    ) -> Result<String, KotlinPrintError> {
        let mut output = String::new();
        let tasks = match &body.root {
            KotlinStmt::Block(statements) => statements
                .iter()
                .rev()
                .map(|statement| PrintTask::Statement(statement, depth))
                .collect(),
            statement => vec![PrintTask::Statement(statement, depth)],
        };
        self.render(&mut output, tasks)?;
        Ok(output)
    }

    fn print_constructor_body_at(
        &self,
        body: &KotlinMethodBody,
        depth: usize,
    ) -> Result<String, KotlinPrintError> {
        let mut output = String::new();
        let tasks = match &body.root {
            KotlinStmt::Block(statements) => statements
                .iter()
                .filter(|statement| !matches!(statement, KotlinStmt::ConstructorInvocation { .. }))
                .rev()
                .map(|statement| PrintTask::Statement(statement, depth))
                .collect(),
            KotlinStmt::ConstructorInvocation { .. } => Vec::new(),
            statement => vec![PrintTask::Statement(statement, depth)],
        };
        self.render(&mut output, tasks)?;
        Ok(output)
    }

    pub fn print_compilation_unit(
        &self,
        unit: &KotlinCompilationUnit,
    ) -> Result<String, KotlinPrintError> {
        let mut output = String::new();
        if let Some(package) = &unit.package {
            writeln!(output, "package {package}\n")?;
        }
        if !unit.imports.is_empty() {
            for import in &unit.imports {
                writeln!(output, "import {import}")?;
            }
            writeln!(output)?;
        }
        self.print_type_tree(&mut output, &unit.declaration)?;
        Ok(output)
    }

    pub fn print_method_declaration(
        &self,
        declaration: &KotlinMethodDeclaration,
        depth: usize,
    ) -> Result<String, KotlinPrintError> {
        let mut output = String::new();
        self.print_method_into(&mut output, declaration, depth)?;
        Ok(output)
    }

    fn print_type_tree(
        &self,
        output: &mut String,
        root: &KotlinTypeDeclaration,
    ) -> Result<(), KotlinPrintError> {
        self.print_type_subtree(output, root, 0)
    }

    fn print_anonymous_body(
        &self,
        body: &KotlinAnonymousClassBody,
        depth: usize,
    ) -> Result<String, KotlinPrintError> {
        let mut output = String::from("{\n");
        let mut wrote_member = false;
        for field in &body.fields {
            if wrote_member {
                writeln!(output)?;
            }
            self.print_field_into(&mut output, field, depth + 1)?;
            wrote_member = true;
        }
        for property in &body.properties {
            if wrote_member {
                writeln!(output)?;
            }
            self.print_property_into(&mut output, property, depth + 1)?;
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
        root: &KotlinTypeDeclaration,
        root_depth: usize,
    ) -> Result<(), KotlinPrintError> {
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
        declaration: &KotlinTypeDeclaration,
        depth: usize,
    ) -> Result<bool, KotlinPrintError> {
        self.annotations(output, &declaration.annotations, depth)?;
        self.indent(output, depth);
        if depth != 0
            && declaration.kind == super::KotlinTypeDeclarationKind::Class
            && !declaration.modifiers.contains(&KotlinModifier::Static)
        {
            write!(output, "inner ")?;
        }
        self.modifiers(output, &declaration.modifiers)?;
        write!(
            output,
            "{} {}{}",
            declaration.kind.token(),
            declaration.name,
            Self::type_parameters(&declaration.type_parameters)
        )?;
        if !declaration.primary_parameters.is_empty() {
            let parameters = declaration
                .primary_parameters
                .iter()
                .map(|parameter| {
                    let (declaration, default) = match parameter {
                        super::KotlinPrimaryParameter::Property(property) => (
                            format!(
                                "{}{}: {}",
                                Self::property_binding(property),
                                property.name,
                                Self::source_type_with_nullability(&property.ty, property.nullable)
                            ),
                            property.initializer.as_ref(),
                        ),
                        super::KotlinPrimaryParameter::Value(value) => (
                            format!(
                                "{}: {}",
                                value.name,
                                Self::source_type_with_nullability(&value.ty, value.nullable)
                            ),
                            value.default_value.as_ref(),
                        ),
                    };
                    let default = default
                        .map(|value| self.expression_at(value, depth))
                        .transpose()?
                        .map(|value| format!(" = {value}"))
                        .unwrap_or_default();
                    Ok(format!("{declaration}{default}"))
                })
                .collect::<Result<Vec<_>, KotlinPrintError>>()?;
            write!(output, "({})", parameters.join(", "))?;
        }
        let has_constructor = declaration
            .methods
            .iter()
            .any(|method| method.kind == KotlinMethodDeclarationKind::Constructor);
        let mut supertypes = declaration
            .extends
            .iter()
            .map(|ty| {
                if !declaration.superclass_arguments.is_empty() {
                    let arguments = declaration
                        .superclass_arguments
                        .iter()
                        .map(|argument| self.expression_at(argument, depth))
                        .collect::<Result<Vec<_>, KotlinPrintError>>()?;
                    Ok(format!("{ty}({})", arguments.join(", ")))
                } else if matches!(
                    declaration.kind,
                    super::KotlinTypeDeclarationKind::Class
                        | super::KotlinTypeDeclarationKind::Object
                ) && !has_constructor
                {
                    Ok(format!("{ty}()"))
                } else {
                    Ok(ty.to_string())
                }
            })
            .collect::<Result<Vec<_>, KotlinPrintError>>()?;
        supertypes.extend(declaration.implements.iter().map(ToString::to_string));
        if !supertypes.is_empty() {
            write!(output, " : {}", supertypes.join(", "))?;
        }
        write!(
            output,
            "{}",
            Self::where_clause(&declaration.type_parameters)
        )?;
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
                        .map(|argument| self.expression(argument))
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
        for field in declaration
            .fields
            .iter()
            .filter(|field| !field.modifiers.contains(&KotlinModifier::Static))
        {
            if wrote_member {
                writeln!(output)?;
            }
            self.print_field_into(output, field, depth + 1)?;
            wrote_member = true;
        }
        for property in declaration
            .properties
            .iter()
            .filter(|property| !property.modifiers.contains(&KotlinModifier::Static))
        {
            if wrote_member {
                writeln!(output)?;
            }
            self.print_property_into(output, property, depth + 1)?;
            wrote_member = true;
        }
        for method in declaration.methods.iter().filter(|method| {
            (method.kind != KotlinMethodDeclarationKind::ClassInitializer
                || declaration.kind == super::KotlinTypeDeclarationKind::Object)
                && !method.modifiers.contains(&KotlinModifier::Static)
        }) {
            if wrote_member {
                writeln!(output)?;
            }
            self.print_method_into(output, method, depth + 1)?;
            wrote_member = true;
        }
        let static_fields = declaration
            .fields
            .iter()
            .filter(|field| field.modifiers.contains(&KotlinModifier::Static))
            .collect::<Vec<_>>();
        let static_methods = declaration
            .methods
            .iter()
            .filter(|method| {
                declaration.kind != super::KotlinTypeDeclarationKind::Object
                    && (method.kind == KotlinMethodDeclarationKind::ClassInitializer
                        || method.modifiers.contains(&KotlinModifier::Static))
            })
            .collect::<Vec<_>>();
        let static_properties = declaration
            .properties
            .iter()
            .filter(|property| property.modifiers.contains(&KotlinModifier::Static))
            .collect::<Vec<_>>();
        if !static_fields.is_empty() || !static_properties.is_empty() || !static_methods.is_empty()
        {
            if wrote_member {
                writeln!(output)?;
            }
            self.indent(output, depth + 1);
            writeln!(output, "companion object {{")?;
            let mut wrote_static = false;
            for field in static_fields {
                if wrote_static {
                    writeln!(output)?;
                }
                self.print_field_into(output, field, depth + 2)?;
                wrote_static = true;
            }
            for property in static_properties {
                if wrote_static {
                    writeln!(output)?;
                }
                self.print_property_into(output, property, depth + 2)?;
                wrote_static = true;
            }
            for method in static_methods {
                if wrote_static {
                    writeln!(output)?;
                }
                self.print_method_into(output, method, depth + 2)?;
                wrote_static = true;
            }
            self.indent(output, depth + 1);
            writeln!(output, "}}")?;
            wrote_member = true;
        }
        Ok(wrote_member)
    }

    /// The modifiers and binding word a property carries inside the header.
    fn property_binding(property: &KotlinFieldDeclaration) -> String {
        let mut text = String::new();
        for modifier in &property.modifiers {
            let token = modifier.token();
            if !token.is_empty() && *modifier != KotlinModifier::Final {
                text.push_str(token);
                text.push(' ');
            }
        }
        text.push_str(if property.modifiers.contains(&KotlinModifier::Final) {
            "val "
        } else {
            "var "
        });
        text
    }

    fn print_field_into(
        &self,
        output: &mut String,
        field: &KotlinFieldDeclaration,
        depth: usize,
    ) -> Result<(), KotlinPrintError> {
        self.annotations(output, &field.annotations, depth)?;
        self.indent(output, depth);
        self.modifiers(output, &field.modifiers)?;
        let binding = if field.modifiers.contains(&KotlinModifier::Final) {
            "val"
        } else {
            "var"
        };
        write!(
            output,
            "{binding} {}: {}",
            field.name,
            Self::source_type_with_nullability(&field.ty, field.nullable)
        )?;
        if let Some(initializer) = &field.initializer {
            write!(output, " = {}", self.expression_at(initializer, depth)?)?;
        } else if binding == "var" && !field.modifiers.contains(&KotlinModifier::Lateinit) {
            // A `lateinit` property is the one variable Kotlin leaves unset.
            write!(output, " = {}", Self::default_value(&field.ty))?;
        }
        writeln!(output)?;
        Ok(())
    }

    fn print_property_into(
        &self,
        output: &mut String,
        property: &super::KotlinPropertyDeclaration,
        depth: usize,
    ) -> Result<(), KotlinPrintError> {
        self.annotations(output, &property.annotations, depth)?;
        self.indent(output, depth);
        self.modifiers(output, &property.modifiers)?;
        writeln!(
            output,
            "val {}: {}",
            property.name,
            Self::source_type_with_nullability(&property.ty, property.nullable)
        )?;
        let Some(getter) = &property.getter else {
            return Ok(());
        };
        self.indent(output, depth + 1);
        writeln!(output, "get() {{")?;
        output.push_str(&self.print_method_body_at(getter, depth + 2)?);
        self.indent(output, depth + 1);
        writeln!(output, "}}")?;
        Ok(())
    }

    fn print_method_into(
        &self,
        output: &mut String,
        method: &KotlinMethodDeclaration,
        depth: usize,
    ) -> Result<(), KotlinPrintError> {
        self.annotations(output, &method.annotations, depth)?;
        self.indent(output, depth);
        if method.kind == KotlinMethodDeclarationKind::ClassInitializer {
            write!(output, "init")?;
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
                    let rendered_parameter = if parameter.varargs {
                        match &parameter.ty {
                            KotlinType::Array(element) => {
                                format!(
                                    "vararg {}: {}",
                                    parameter.name,
                                    Self::source_type_with_nullability(element, parameter.nullable)
                                )
                            }
                            ty => format!(
                                "vararg {}: {}",
                                parameter.name,
                                Self::source_type_with_nullability(ty, parameter.nullable)
                            ),
                        }
                    } else {
                        format!(
                            "{}: {}",
                            parameter.name,
                            Self::source_type_with_nullability(&parameter.ty, parameter.nullable)
                        )
                    };
                    let default_value = parameter
                        .default_value
                        .as_ref()
                        .map(|value| self.expression_at(value, depth))
                        .transpose()?
                        .map(|value| format!(" = {value}"))
                        .unwrap_or_default();
                    Ok(format!("{prefix}{rendered_parameter}{default_value}"))
                })
                .collect::<Result<Vec<_>, KotlinPrintError>>()?
                .join(", ");
            match method.kind {
                KotlinMethodDeclarationKind::Method => {
                    let return_type = method
                        .return_type
                        .as_ref()
                        .ok_or(KotlinPrintError::MalformedDeclaration)?;
                    let name = method
                        .name
                        .as_ref()
                        .ok_or(KotlinPrintError::MalformedDeclaration)?;
                    // Kotlin infers `Unit`, and source does not spell it out.
                    let returns_unit = matches!(
                        return_type,
                        KotlinType::Primitive(super::KotlinPrimitiveType::Void)
                    );
                    write!(
                        output,
                        "fun {}{}{name}({parameters})",
                        Self::type_parameters_prefix(&method.type_parameters),
                        method
                            .receiver
                            .as_ref()
                            .map(|receiver| format!(
                                "{}.",
                                Self::source_type_with_nullability(&receiver.ty, receiver.nullable)
                            ))
                            .unwrap_or_default(),
                    )?;
                    if !returns_unit {
                        write!(
                            output,
                            ": {}",
                            Self::source_type_with_nullability(return_type, method.return_nullable),
                        )?;
                    }
                }
                KotlinMethodDeclarationKind::Constructor => {
                    write!(
                        output,
                        "{}constructor({parameters})",
                        Self::type_parameters_prefix(&method.type_parameters)
                    )?;
                }
                KotlinMethodDeclarationKind::ClassInitializer => {
                    return Err(KotlinPrintError::MalformedDeclaration);
                }
            }
            write!(output, "{}", Self::where_clause(&method.type_parameters))?;
        }
        let Some(body) = &method.body else {
            writeln!(output)?;
            return Ok(());
        };
        if method.kind == KotlinMethodDeclarationKind::Constructor {
            if let Some((target, args)) = Self::constructor_delegation(body) {
                write!(
                    output,
                    " : {}({})",
                    match target {
                        KotlinConstructorTarget::This => "this",
                        KotlinConstructorTarget::Super => "super",
                    },
                    args.iter()
                        .map(|argument| self.expression_at(argument, depth))
                        .collect::<Result<Vec<_>, _>>()?
                        .join(", ")
                )?;
            }
        }
        writeln!(output, " {{")?;
        output.push_str(
            &if method.kind == KotlinMethodDeclarationKind::Constructor {
                self.print_constructor_body_at(body, depth + 1)?
            } else {
                self.print_method_body_at(body, depth + 1)?
            },
        );
        self.indent(output, depth);
        writeln!(output, "}}")?;
        Ok(())
    }

    fn annotations(
        &self,
        output: &mut String,
        annotations: &[KotlinAnnotation],
        depth: usize,
    ) -> Result<(), KotlinPrintError> {
        for annotation in annotations {
            self.indent(output, depth);
            writeln!(output, "{}", self.annotation(annotation)?)?;
        }
        Ok(())
    }

    fn annotation(&self, annotation: &KotlinAnnotation) -> Result<String, KotlinPrintError> {
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
            .collect::<Result<Vec<_>, KotlinPrintError>>()?;
        write!(output, "({})", elements.join(", "))?;
        Ok(output)
    }

    fn annotation_value(&self, value: &KotlinAnnotationValue) -> Result<String, KotlinPrintError> {
        match value {
            KotlinAnnotationValue::Expression(expression) => self.expression(expression),
            KotlinAnnotationValue::Annotation(annotation) => self.annotation(annotation),
            KotlinAnnotationValue::Array(values) => Ok(format!(
                "[{}]",
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
        modifiers: &[KotlinModifier],
    ) -> Result<(), KotlinPrintError> {
        for modifier in modifiers {
            let token = modifier.token();
            if !token.is_empty() && !matches!(modifier, KotlinModifier::Final) {
                write!(output, "{token} ")?;
            }
        }
        Ok(())
    }

    fn type_parameters(parameters: &[super::KotlinTypeParameter]) -> String {
        if parameters.is_empty() {
            return String::new();
        }
        format!(
            "<{}>",
            parameters
                .iter()
                .map(|parameter| {
                    parameter.bounds.first().map_or_else(
                        || parameter.name.to_string(),
                        |bound| format!("{} : {bound}", parameter.name),
                    )
                })
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    fn type_parameters_prefix(parameters: &[super::KotlinTypeParameter]) -> String {
        let parameters = Self::type_parameters(parameters);
        (!parameters.is_empty())
            .then(|| format!("{parameters} "))
            .unwrap_or_default()
    }

    fn where_clause(parameters: &[super::KotlinTypeParameter]) -> String {
        let bounds = parameters
            .iter()
            .flat_map(|parameter| {
                parameter
                    .bounds
                    .iter()
                    .skip(1)
                    .map(|bound| format!("{} : {bound}", parameter.name))
            })
            .collect::<Vec<_>>();
        if bounds.is_empty() {
            String::new()
        } else {
            format!(" where {}", bounds.join(", "))
        }
    }

    fn source_type(ty: &KotlinType) -> String {
        Self::source_type_with_nullability(ty, true)
    }

    fn source_type_with_nullability(ty: &KotlinType, nullable: bool) -> String {
        let rendered = ty.to_string();
        if nullable && matches!(ty, KotlinType::Class(_) | KotlinType::Array(_)) {
            format!("{rendered}?")
        } else {
            rendered
        }
    }

    fn default_value(ty: &KotlinType) -> &'static str {
        match ty {
            KotlinType::Primitive(super::KotlinPrimitiveType::Boolean) => "false",
            KotlinType::Primitive(super::KotlinPrimitiveType::Char) => "'\\u0000'",
            KotlinType::Primitive(super::KotlinPrimitiveType::Long) => "0L",
            KotlinType::Primitive(super::KotlinPrimitiveType::Float) => "0.0f",
            KotlinType::Primitive(super::KotlinPrimitiveType::Double) => "0.0",
            KotlinType::Primitive(_) => "0",
            KotlinType::Class(_) | KotlinType::Variable(_) | KotlinType::Array(_) => "null",
        }
    }

    fn assignment(target: &str, op: KotlinAssignOp, value: &str) -> String {
        let method = match op {
            KotlinAssignOp::BitAnd => Some("and"),
            KotlinAssignOp::BitOr => Some("or"),
            KotlinAssignOp::BitXor => Some("xor"),
            KotlinAssignOp::ShiftLeft => Some("shl"),
            KotlinAssignOp::ShiftRight => Some("shr"),
            KotlinAssignOp::UnsignedShiftRight => Some("ushr"),
            _ => None,
        };
        match method {
            Some(method) => format!("{target} = {target}.{method}({value})"),
            None => format!("{target} {} {value}", op.token()),
        }
    }

    fn constructor_delegation(
        body: &KotlinMethodBody,
    ) -> Option<(&KotlinConstructorTarget, &[KotlinExpr])> {
        let statement = match &body.root {
            KotlinStmt::Block(statements) => statements.first()?,
            statement => statement,
        };
        let KotlinStmt::ConstructorInvocation { target, args } = statement else {
            return None;
        };
        Some((target, args))
    }

    fn render<'a>(
        &self,
        output: &mut String,
        mut pending: Vec<PrintTask<'a>>,
    ) -> Result<(), KotlinPrintError> {
        while let Some(task) = pending.pop() {
            match task {
                PrintTask::Statement(statement, depth) => {
                    self.schedule_statement(output, statement, depth, &mut pending)?
                }
                PrintTask::ControlBody(body, depth) => {
                    if matches!(body, KotlinStmt::Block(_)) {
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
                    writeln!(output, "while ({})", self.expression_at(condition, depth)?)?;
                }
                PrintTask::Catch(catch, type_index, depth) => {
                    let ty = catch
                        .types
                        .get(type_index)
                        .ok_or(KotlinPrintError::MalformedDeclaration)?;
                    Self::continue_clause(output, &format!("catch ({}: {ty}) ", catch.variable))?;
                    pending.push(PrintTask::ControlBody(&catch.body, depth));
                }
                PrintTask::Finally(body, depth) => {
                    Self::continue_clause(output, "finally ")?;
                    pending.push(PrintTask::ControlBody(body, depth));
                }
                PrintTask::SwitchCase(case, depth) => {
                    self.indent(output, depth);
                    let labels = case
                        .labels
                        .iter()
                        .map(|label| self.expression_at(label, depth))
                        .collect::<Result<Vec<_>, _>>()?;
                    write!(
                        output,
                        "{} -> {{\n",
                        if case.is_default {
                            "else".to_string()
                        } else {
                            labels.join(", ")
                        }
                    )?;
                    pending.push(PrintTask::CloseBrace(depth));
                    pending.extend(
                        case.body
                            .iter()
                            .rev()
                            .map(|statement| PrintTask::Statement(statement, depth + 1)),
                    );
                }
                PrintTask::ForLoop {
                    label,
                    condition,
                    update,
                    body,
                    depth,
                } => {
                    self.label(output, label, depth)?;
                    self.indent(output, depth);
                    writeln!(output, "while ({condition}) {{")?;
                    pending.push(PrintTask::CloseBrace(depth));
                    pending.push(PrintTask::ForUpdate(update, depth + 1));
                    match body {
                        KotlinStmt::Block(statements) => pending.extend(
                            statements
                                .iter()
                                .rev()
                                .map(|statement| PrintTask::Statement(statement, depth + 1)),
                        ),
                        statement => {
                            pending.push(PrintTask::Statement(statement, depth + 1));
                        }
                    }
                }
                PrintTask::ForUpdate(update, depth) => {
                    for expression in update {
                        self.indent(output, depth);
                        writeln!(output, "{}", self.expression_at(expression, depth)?)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn continue_clause(output: &mut String, clause: &str) -> Result<(), KotlinPrintError> {
        if output.ends_with('\n') {
            output.pop();
        }
        write!(output, " {clause}")?;
        Ok(())
    }

    fn schedule_statement<'a>(
        &self,
        output: &mut String,
        statement: &'a KotlinStmt,
        depth: usize,
        pending: &mut Vec<PrintTask<'a>>,
    ) -> Result<(), KotlinPrintError> {
        match statement {
            KotlinStmt::Empty => {}
            KotlinStmt::Block(statements) => {
                writeln!(output, "{{")?;
                pending.push(PrintTask::CloseBrace(depth));
                pending.extend(
                    statements
                        .iter()
                        .rev()
                        .map(|statement| PrintTask::Statement(statement, depth + 1)),
                );
            }
            KotlinStmt::Labeled { label, body } => {
                self.indent(output, depth);
                write!(output, "{label}@ ")?;
                match body.as_ref() {
                    KotlinStmt::Block(statements) => {
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
            KotlinStmt::Variable {
                binding,
                ty,
                name,
                value,
            } => {
                self.indent(output, depth);
                let keyword = if binding.mutable { "var" } else { "val" };
                write!(
                    output,
                    "{keyword} {name}: {}",
                    Self::source_type_with_nullability(ty, binding.nullable)
                )?;
                if let Some(value) = value {
                    write!(output, " = {}", self.expression_at(value, depth)?)?;
                }
                writeln!(output)?;
            }
            KotlinStmt::Expression(expression) => {
                self.indent(output, depth);
                writeln!(output, "{}", self.expression_at(expression, depth)?)?;
            }
            KotlinStmt::ConstructorInvocation { target, args } => {
                self.indent(output, depth);
                let target = match target {
                    KotlinConstructorTarget::This => "this",
                    KotlinConstructorTarget::Super => "super",
                };
                writeln!(
                    output,
                    "{}({})",
                    target,
                    args.iter()
                        .map(|argument| self.expression_at(argument, depth))
                        .collect::<Result<Vec<_>, _>>()?
                        .join(", ")
                )?;
            }
            KotlinStmt::Assign { target, op, value } => {
                self.indent(output, depth);
                let target = self.expression_at(target, depth)?;
                let value = self.expression_at(value, depth)?;
                writeln!(output, "{}", Self::assignment(&target, *op, &value))?;
            }
            KotlinStmt::If {
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
            KotlinStmt::While {
                label,
                condition,
                body,
            } => {
                self.label(output, label, depth)?;
                self.indent(output, depth);
                write!(output, "while ({}) ", self.expression_at(condition, depth)?)?;
                pending.push(PrintTask::ControlBody(body, depth));
            }
            KotlinStmt::DoWhile {
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
            KotlinStmt::For {
                label,
                init,
                condition,
                update,
                body,
            } => {
                self.indent(output, depth);
                let condition = condition
                    .as_ref()
                    .map(|condition| self.expression_at(condition, depth))
                    .transpose()?
                    .unwrap_or_else(|| "true".to_string());
                writeln!(output, "run {{")?;
                pending.push(PrintTask::CloseBrace(depth));
                pending.push(PrintTask::ForLoop {
                    label,
                    condition,
                    update,
                    body,
                    depth: depth + 1,
                });
                pending.extend(
                    init.iter()
                        .rev()
                        .map(|statement| PrintTask::Statement(statement, depth + 1)),
                );
            }
            KotlinStmt::ForEach {
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
                    "for ({}: {} in {}) ",
                    variable,
                    Self::source_type(ty),
                    self.expression_at(iterable, depth)?
                )?;
                pending.push(PrintTask::ControlBody(body, depth));
            }
            KotlinStmt::Switch {
                label,
                selector,
                cases,
            } => {
                self.label(output, label, depth)?;
                self.indent(output, depth);
                writeln!(output, "when ({}) {{", self.expression_at(selector, depth)?)?;
                pending.push(PrintTask::CloseBrace(depth));
                pending.extend(
                    cases
                        .iter()
                        .rev()
                        .map(|case| PrintTask::SwitchCase(case, depth + 1)),
                );
            }
            KotlinStmt::Try {
                body,
                catches,
                finally,
            } => {
                self.indent(output, depth);
                write!(output, "try ")?;
                if let Some(finally) = finally {
                    pending.push(PrintTask::Finally(finally, depth));
                }
                for catch in catches.iter().rev() {
                    for type_index in (0..catch.types.len()).rev() {
                        pending.push(PrintTask::Catch(catch, type_index, depth));
                    }
                }
                pending.push(PrintTask::ControlBody(body, depth));
            }
            KotlinStmt::Synchronized { lock, body } => {
                self.indent(output, depth);
                let lock = ExpressionFrame::asserted_receiver(self.render_expression(
                    lock,
                    ExpressionRequirement::Primary,
                    depth,
                )?);
                write!(output, "synchronized({}) ", lock)?;
                pending.push(PrintTask::ControlBody(body, depth));
            }
            KotlinStmt::Return(value) => {
                self.indent(output, depth);
                match value {
                    Some(value) => {
                        writeln!(output, "return {}", self.expression_at(value, depth)?)?
                    }
                    None => writeln!(output, "return")?,
                }
            }
            KotlinStmt::Throw(value) => {
                self.indent(output, depth);
                writeln!(output, "throw {}", self.expression_at(value, depth)?)?;
            }
            KotlinStmt::Break(label) => {
                self.indent(output, depth);
                Self::control(output, "break", label)?;
            }
            KotlinStmt::Continue(label) => {
                self.indent(output, depth);
                Self::control(output, "continue", label)?;
            }
        }
        Ok(())
    }

    fn expression(&self, expression: &KotlinExpr) -> Result<String, KotlinPrintError> {
        self.expression_at(expression, 0)
    }

    fn expression_at(
        &self,
        expression: &KotlinExpr,
        depth: usize,
    ) -> Result<String, KotlinPrintError> {
        self.render_expression(expression, ExpressionRequirement::Any, depth)
    }

    fn render_expression(
        &self,
        expression: &KotlinExpr,
        requirement: ExpressionRequirement,
        depth: usize,
    ) -> Result<String, KotlinPrintError> {
        let mut pending = vec![ExpressionTask::Visit(expression, requirement)];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                ExpressionTask::Visit(expression, requirement) => match expression {
                    KotlinExpr::This => results.push(RenderedExpression::primary("this")),
                    KotlinExpr::QualifiedThis(ty) => {
                        results.push(RenderedExpression::primary(format!("this@{ty}")))
                    }
                    KotlinExpr::Super => results.push(RenderedExpression::primary("super")),
                    KotlinExpr::Name(value) => {
                        results.push(RenderedExpression::primary(value.to_string()))
                    }
                    KotlinExpr::Literal(value) => {
                        let rendered = KotlinLiterals::render(value);
                        // A negative literal carries a sign, and the sign binds
                        // like any other unary minus: `-1.toByte()` reads as
                        // `-(1.toByte())`, which is a different expression.
                        let precedence = if rendered.starts_with('-') {
                            ExpressionPrecedence::Unary
                        } else {
                            ExpressionPrecedence::Primary
                        };
                        results.push(RenderedExpression {
                            text: rendered,
                            precedence,
                            binary: None,
                            non_null: matches!(value, super::KotlinLiteral::String(_)),
                        })
                    }
                    KotlinExpr::ClassLiteral(ty) => {
                        results.push(RenderedExpression::non_null(format!("{ty}::class.java")))
                    }
                    KotlinExpr::ObjectReference(ty) => {
                        results.push(RenderedExpression::non_null(ty.to_string()))
                    }
                    KotlinExpr::StaticField { owner, name } => {
                        results.push(RenderedExpression::primary(format!("{owner}.{name}")))
                    }
                    KotlinExpr::SmartCast(value) => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::SmartCast {
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit(value, ExpressionRequirement::Primary));
                    }
                    KotlinExpr::NonNullAssertion(value) => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::NonNullAssertion {
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit(value, ExpressionRequirement::Any));
                    }
                    KotlinExpr::JvmIntrinsic { expression, .. } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::JvmIntrinsic {
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit(expression, requirement));
                    }
                    KotlinExpr::Field { owner, name } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Field {
                            name,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit(owner, ExpressionRequirement::Primary));
                    }
                    KotlinExpr::ArrayAccess { array, index } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::ArrayAccess {
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit(index, ExpressionRequirement::Any));
                        pending.push(ExpressionTask::Visit(array, ExpressionRequirement::Primary));
                    }
                    KotlinExpr::Call {
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
                            arguments: args,
                            requirement,
                        }));
                        pending.extend(args.iter().rev().map(|argument| {
                            ExpressionTask::Visit(argument, ExpressionRequirement::Any)
                        }));
                        if let Some(receiver) = receiver {
                            pending.push(ExpressionTask::Visit(
                                receiver,
                                ExpressionRequirement::Primary,
                            ));
                        }
                    }
                    KotlinExpr::MethodReference { receiver, method } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::MethodReference {
                            method,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit(
                            receiver,
                            ExpressionRequirement::Primary,
                        ));
                    }
                    KotlinExpr::Lambda { parameters, body } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Lambda {
                            parameters,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit(body, ExpressionRequirement::Any));
                    }
                    KotlinExpr::BlockLambda { parameters, body } => {
                        let parameters = Self::lambda_parameters(parameters);
                        let mut rendered_body = String::new();
                        self.render(
                            &mut rendered_body,
                            vec![PrintTask::Statement(body, depth + 1)],
                        )?;
                        results.push(
                            RenderedExpression {
                                text: format!(
                                    "{{{parameters} ->\n{}\n{}}}",
                                    rendered_body.trim_end(),
                                    self.indent.repeat(depth)
                                ),
                                precedence: ExpressionPrecedence::Assignment,
                                binary: None,
                                non_null: true,
                            }
                            .requiring(requirement),
                        );
                    }
                    KotlinExpr::New {
                        enclosing,
                        ty,
                        args,
                        anonymous_body,
                        ..
                    } => {
                        let anonymous_super_constructor = anonymous_body
                            .as_deref()
                            .is_some_and(|body| body.super_constructor_call);
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::New {
                            has_enclosing: enclosing.is_some(),
                            ty,
                            args: args.len(),
                            anonymous_super_constructor,
                            anonymous_body: anonymous_body
                                .as_deref()
                                .map(|body| self.print_anonymous_body(body, depth))
                                .transpose()?,
                            requirement,
                        }));
                        pending.extend(args.iter().rev().map(|argument| {
                            ExpressionTask::Visit(argument, ExpressionRequirement::Any)
                        }));
                        if let Some(enclosing) = enclosing {
                            pending.push(ExpressionTask::Visit(
                                enclosing,
                                ExpressionRequirement::Primary,
                            ));
                        }
                    }
                    KotlinExpr::NewArray {
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
                        pending.extend(
                            initializer.iter().rev().map(|item| {
                                ExpressionTask::Visit(item, ExpressionRequirement::Any)
                            }),
                        );
                        pending.extend(dimensions.iter().rev().map(|dimension| {
                            ExpressionTask::Visit(dimension, ExpressionRequirement::Any)
                        }));
                    }
                    KotlinExpr::Unary { op, operand } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Unary {
                            op: *op,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit(operand, ExpressionRequirement::Unary));
                    }
                    KotlinExpr::Update { op, target, prefix } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Update {
                            op: *op,
                            prefix: *prefix,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit(
                            target,
                            ExpressionRequirement::Primary,
                        ));
                    }
                    KotlinExpr::Binary { left, op, right } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Binary {
                            op: *op,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit(right, ExpressionRequirement::Any));
                        pending.push(ExpressionTask::Visit(left, ExpressionRequirement::Any));
                    }
                    KotlinExpr::Cast { ty, value } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Cast {
                            ty,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit(value, ExpressionRequirement::Unary));
                    }
                    KotlinExpr::InstanceOf { value, ty } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::InstanceOf {
                            ty,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit(value, ExpressionRequirement::Any));
                    }
                    KotlinExpr::Conditional {
                        condition,
                        when_true,
                        when_false,
                    } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Conditional {
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit(
                            when_false,
                            ExpressionRequirement::Any,
                        ));
                        pending.push(ExpressionTask::Visit(when_true, ExpressionRequirement::Any));
                        pending.push(ExpressionTask::Visit(condition, ExpressionRequirement::Any));
                    }
                    KotlinExpr::Assignment { target, op, value } => {
                        pending.push(ExpressionTask::Rebuild(ExpressionFrame::Assignment {
                            op: *op,
                            requirement,
                        }));
                        pending.push(ExpressionTask::Visit(value, ExpressionRequirement::Any));
                        pending.push(ExpressionTask::Visit(target, ExpressionRequirement::Any));
                    }
                },
                ExpressionTask::Rebuild(frame) => {
                    let count = frame.child_count();
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(KotlinPrintError::MalformedExpression)?;
                    let children = results.drain(start..).collect();
                    results.push(frame.render(children)?);
                }
            }
        }
        if results.len() != 1 {
            return Err(KotlinPrintError::MalformedExpression);
        }
        results
            .pop()
            .map(|rendered| rendered.text)
            .ok_or(KotlinPrintError::MalformedExpression)
    }

    fn label(
        &self,
        output: &mut String,
        label: &Option<KotlinIdentifier>,
        depth: usize,
    ) -> Result<(), KotlinPrintError> {
        if let Some(label) = label {
            self.indent(output, depth);
            writeln!(output, "{label}@")?;
        }
        Ok(())
    }

    fn control(
        output: &mut String,
        keyword: &str,
        label: &Option<KotlinIdentifier>,
    ) -> Result<(), KotlinPrintError> {
        match label {
            Some(label) => writeln!(output, "{keyword}@{label}")?,
            None => writeln!(output, "{keyword}")?,
        }
        Ok(())
    }

    fn inline_statement(
        &self,
        statement: &KotlinStmt,
        depth: usize,
    ) -> Result<String, KotlinPrintError> {
        Ok(match statement {
            KotlinStmt::Variable {
                binding,
                ty,
                name,
                value,
            } => match value {
                Some(value) => {
                    format!(
                        "{} {name}: {} = {}",
                        if binding.mutable { "var" } else { "val" },
                        Self::source_type_with_nullability(ty, binding.nullable),
                        self.expression_at(value, depth)?
                    )
                }
                None => format!(
                    "{} {name}: {}",
                    if binding.mutable { "var" } else { "val" },
                    Self::source_type_with_nullability(ty, binding.nullable)
                ),
            },
            KotlinStmt::Assign { target, op, value } => Self::assignment(
                &self.expression_at(target, depth)?,
                *op,
                &self.expression_at(value, depth)?,
            ),
            KotlinStmt::Expression(expression) => self.expression_at(expression, depth)?,
            _ => return Err(KotlinPrintError::InvalidInlineStatement),
        })
    }

    fn indent(&self, output: &mut String, depth: usize) {
        for _ in 0..depth {
            output.push_str(&self.indent);
        }
    }

    fn lambda_parameters(parameters: &[KotlinIdentifier]) -> String {
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
        declaration: &'a KotlinTypeDeclaration,
        depth: usize,
        leading_blank: bool,
    },
    End {
        depth: usize,
    },
}

enum PrintTask<'a> {
    Statement(&'a KotlinStmt, usize),
    ControlBody(&'a KotlinStmt, usize),
    CloseBrace(usize),
    Else(&'a KotlinStmt, usize),
    DoWhileTail(&'a KotlinExpr, usize),
    Catch(&'a KotlinCatch, usize, usize),
    Finally(&'a KotlinStmt, usize),
    SwitchCase(&'a KotlinSwitchCase, usize),
    ForLoop {
        label: &'a Option<KotlinIdentifier>,
        condition: String,
        update: &'a [KotlinExpr],
        body: &'a KotlinStmt,
        depth: usize,
    },
    ForUpdate(&'a [KotlinExpr], usize),
}

enum ExpressionTask<'a> {
    Visit(&'a KotlinExpr, ExpressionRequirement),
    Rebuild(ExpressionFrame<'a>),
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
    binary: Option<KotlinBinaryOp>,
    non_null: bool,
}

impl RenderedExpression {
    fn primary(text: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            precedence: ExpressionPrecedence::Primary,
            binary: None,
            non_null: false,
        }
    }

    fn non_null(text: impl Into<String>) -> Self {
        Self {
            non_null: true,
            ..Self::primary(text)
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
    SmartCast {
        requirement: ExpressionRequirement,
    },
    NonNullAssertion {
        requirement: ExpressionRequirement,
    },
    JvmIntrinsic {
        requirement: ExpressionRequirement,
    },
    Field {
        name: &'a KotlinIdentifier,
        requirement: ExpressionRequirement,
    },
    ArrayAccess {
        requirement: ExpressionRequirement,
    },
    Call {
        has_receiver: bool,
        owner: Option<&'a KotlinType>,
        type_arguments: &'a [KotlinType],
        method: &'a KotlinIdentifier,
        arguments: &'a KotlinCallArguments,
        requirement: ExpressionRequirement,
    },
    MethodReference {
        method: &'a KotlinIdentifier,
        requirement: ExpressionRequirement,
    },
    Lambda {
        parameters: &'a [KotlinIdentifier],
        requirement: ExpressionRequirement,
    },
    New {
        has_enclosing: bool,
        ty: &'a KotlinType,
        args: usize,
        anonymous_super_constructor: bool,
        anonymous_body: Option<String>,
        requirement: ExpressionRequirement,
    },
    NewArray {
        element_type: &'a KotlinType,
        dimensions: usize,
        initializer: usize,
        requirement: ExpressionRequirement,
    },
    Unary {
        op: KotlinUnaryOp,
        requirement: ExpressionRequirement,
    },
    Update {
        op: super::KotlinUpdateOp,
        prefix: bool,
        requirement: ExpressionRequirement,
    },
    Binary {
        op: KotlinBinaryOp,
        requirement: ExpressionRequirement,
    },
    Cast {
        ty: &'a KotlinType,
        requirement: ExpressionRequirement,
    },
    InstanceOf {
        ty: &'a KotlinType,
        requirement: ExpressionRequirement,
    },
    Conditional {
        requirement: ExpressionRequirement,
    },
    Assignment {
        op: KotlinAssignOp,
        requirement: ExpressionRequirement,
    },
}

impl ExpressionFrame<'_> {
    fn child_count(&self) -> usize {
        match self {
            Self::SmartCast { .. }
            | Self::NonNullAssertion { .. }
            | Self::JvmIntrinsic { .. }
            | Self::Field { .. }
            | Self::MethodReference { .. }
            | Self::Lambda { .. }
            | Self::Unary { .. }
            | Self::Update { .. }
            | Self::Cast { .. }
            | Self::InstanceOf { .. } => 1,
            Self::ArrayAccess { .. } | Self::Binary { .. } | Self::Assignment { .. } => 2,
            Self::Conditional { .. } => 3,
            Self::Call {
                has_receiver,
                arguments,
                ..
            } => usize::from(*has_receiver) + arguments.len(),
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
    ) -> Result<RenderedExpression, KotlinPrintError> {
        let inherently_non_null = matches!(
            self,
            Self::Lambda { .. } | Self::New { .. } | Self::NewArray { .. }
        );
        let expected = self.child_count();
        if children.len() != expected {
            return Err(KotlinPrintError::MalformedExpression);
        }
        let mut children = children.into_iter();
        if let Self::SmartCast { requirement } = self {
            let mut expression = Self::child_expression(&mut children)?;
            expression.non_null = true;
            return Ok(expression.requiring(requirement));
        }
        if let Self::NonNullAssertion { requirement } = self {
            let expression = Self::child_expression(&mut children)?;
            let value = if expression.precedence == ExpressionPrecedence::Primary {
                expression.text
            } else {
                expression.parenthesized()
            };
            return Ok(RenderedExpression {
                text: format!("{value}!!"),
                precedence: ExpressionPrecedence::Primary,
                binary: None,
                non_null: true,
            }
            .requiring(requirement));
        }
        if let Self::JvmIntrinsic { requirement } = self {
            return Ok(Self::child_expression(&mut children)?.requiring(requirement));
        }
        let (rendered, precedence, binary, requirement) = match self {
            Self::Field { name, requirement } => (
                format!(
                    "{}.{name}",
                    Self::receiver(Self::child_expression(&mut children)?)
                ),
                ExpressionPrecedence::Primary,
                None,
                requirement,
            ),
            Self::ArrayAccess { requirement } => (
                format!(
                    "{}[{}]",
                    Self::receiver(Self::child_expression(&mut children)?),
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
                arguments,
                requirement,
            } => {
                let receiver = if has_receiver {
                    Some(Self::child_expression(&mut children)?)
                } else {
                    None
                };
                let arguments = children
                    .take(arguments.len())
                    .enumerate()
                    .map(|(index, child)| {
                        let value = if arguments.is_spread(index) {
                            format!("*{}", child.text)
                        } else {
                            child.text
                        };
                        match arguments.name(index) {
                            Some(name) => format!("{name} = {value}"),
                            None => value,
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                let prefix = receiver
                    .map(Self::receiver)
                    .or_else(|| owner.map(ToString::to_string));
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
                    Some(type_arguments) => format!("{method}{type_arguments}"),
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
                format!(
                    "{}::{method}",
                    Self::receiver(Self::child_expression(&mut children)?)
                ),
                ExpressionPrecedence::Primary,
                None,
                requirement,
            ),
            Self::Lambda {
                parameters,
                requirement,
            } => {
                let parameters = KotlinPrinter::lambda_parameters(parameters);
                (
                    format!("{{ {parameters} -> {} }}", Self::child(&mut children)?),
                    ExpressionPrecedence::Assignment,
                    None,
                    requirement,
                )
            }
            Self::New {
                has_enclosing,
                ty,
                args,
                anonymous_super_constructor,
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
                        let KotlinType::Class(class) = ty else {
                            return Err(KotlinPrintError::MalformedExpression);
                        };
                        let member = class
                            .segments
                            .last()
                            .ok_or(KotlinPrintError::MalformedExpression)?;
                        format!("{enclosing}.{member}({arguments})")
                    }
                    None => format!("{ty}({arguments})"),
                };
                if let Some(body) = anonymous_body {
                    let supertype = if anonymous_super_constructor {
                        format!("{ty}({arguments})")
                    } else {
                        ty.to_string()
                    };
                    expression = format!("object : {supertype} {body}");
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
                let dimension_values = children
                    .by_ref()
                    .take(dimensions)
                    .map(|dimension| dimension.text)
                    .collect::<Vec<_>>();
                let initializer_values = children
                    .take(initializer)
                    .map(|child| child.text)
                    .collect::<Vec<_>>();
                let expression = if !initializer_values.is_empty() {
                    Self::array_initializer(base_type, trailing_rank, &initializer_values)
                } else if let Some(first) = dimension_values.first() {
                    Self::array_allocation(element_type, first)
                } else {
                    Self::array_initializer(base_type, trailing_rank, &[])
                };
                (expression, ExpressionPrecedence::Primary, None, requirement)
            }
            Self::Unary { op, requirement } => {
                let operand = Self::child_expression(&mut children)?;
                let operand = if operand.precedence <= ExpressionPrecedence::Unary {
                    operand.parenthesized()
                } else {
                    operand.text
                };
                (
                    if op == KotlinUnaryOp::BitwiseNot {
                        format!("{operand}.inv()")
                    } else {
                        format!("{}{operand}", op.token())
                    },
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
                let rendered = match op {
                    KotlinBinaryOp::BitAnd => format!("{left}.and({right})"),
                    KotlinBinaryOp::BitOr => format!("{left}.or({right})"),
                    KotlinBinaryOp::BitXor => format!("{left}.xor({right})"),
                    KotlinBinaryOp::ShiftLeft => format!("{left}.shl({right})"),
                    KotlinBinaryOp::ShiftRight => format!("{left}.shr({right})"),
                    KotlinBinaryOp::UnsignedShiftRight => {
                        format!("{left}.ushr({right})")
                    }
                    _ => format!("{left} {} {right}", op.token()),
                };
                (rendered, precedence, Some(op), requirement)
            }
            Self::Cast { ty, requirement } => {
                let value = Self::child_expression(&mut children)?;
                let target = KotlinPrinter::source_type_with_nullability(ty, !value.non_null);
                let non_null = value.non_null;
                // A primitive conversion renders as a call on the value, so it
                // binds like one; an `as` cast does not.
                let (rendered, precedence) = match ty {
                    KotlinType::Primitive(primitive) => {
                        let name = Self::primitive_name(*primitive);
                        let value = value.requiring(ExpressionRequirement::Primary);
                        (
                            format!("{}.to{name}()", value.text),
                            ExpressionPrecedence::Primary,
                        )
                    }
                    _ => (
                        format!("{} as {target}", value.text),
                        ExpressionPrecedence::Unary,
                    ),
                };
                return Ok(RenderedExpression {
                    text: rendered,
                    precedence,
                    binary: None,
                    non_null,
                }
                .requiring(requirement));
            }
            Self::InstanceOf { ty, requirement } => {
                let value = Self::child_expression(&mut children)?;
                let value = if value.precedence <= ExpressionPrecedence::Relational {
                    value.parenthesized()
                } else {
                    value.text
                };
                (
                    format!("{value} is {ty}"),
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
                    format!("if ({condition}) {} else {when_false}", when_true.text),
                    ExpressionPrecedence::Conditional,
                    None,
                    requirement,
                )
            }
            Self::Assignment { op, requirement } => {
                let target = Self::child(&mut children)?;
                let value = Self::child(&mut children)?;
                (
                    format!(
                        "run {{ {}; {} }}",
                        KotlinPrinter::assignment(&target, op, &value),
                        target
                    ),
                    ExpressionPrecedence::Primary,
                    None,
                    requirement,
                )
            }
            Self::SmartCast { .. } | Self::NonNullAssertion { .. } | Self::JvmIntrinsic { .. } => {
                unreachable!("nullability frame is rendered before other frames")
            }
        };
        Ok(RenderedExpression {
            text: rendered,
            precedence,
            binary,
            non_null: inherently_non_null,
        }
        .requiring(requirement))
    }

    fn array_initializer(
        base_type: &KotlinType,
        trailing_rank: usize,
        values: &[String],
    ) -> String {
        let elements = values.join(", ");
        if trailing_rank != 0 {
            return format!("arrayOf({elements})");
        }
        let factory = match base_type {
            KotlinType::Primitive(super::KotlinPrimitiveType::Boolean) => "booleanArrayOf",
            KotlinType::Primitive(super::KotlinPrimitiveType::Byte) => "byteArrayOf",
            KotlinType::Primitive(super::KotlinPrimitiveType::Short) => "shortArrayOf",
            KotlinType::Primitive(super::KotlinPrimitiveType::Char) => "charArrayOf",
            KotlinType::Primitive(super::KotlinPrimitiveType::Int) => "intArrayOf",
            KotlinType::Primitive(super::KotlinPrimitiveType::Long) => "longArrayOf",
            KotlinType::Primitive(super::KotlinPrimitiveType::Float) => "floatArrayOf",
            KotlinType::Primitive(super::KotlinPrimitiveType::Double) => "doubleArrayOf",
            _ => "arrayOf",
        };
        format!("{factory}({elements})")
    }

    fn primitive_name(primitive: super::KotlinPrimitiveType) -> &'static str {
        match primitive {
            super::KotlinPrimitiveType::Void => "Unit",
            super::KotlinPrimitiveType::Boolean => "Boolean",
            super::KotlinPrimitiveType::Byte => "Byte",
            super::KotlinPrimitiveType::Short => "Short",
            super::KotlinPrimitiveType::Char => "Char",
            super::KotlinPrimitiveType::Int => "Int",
            super::KotlinPrimitiveType::Long => "Long",
            super::KotlinPrimitiveType::Float => "Float",
            super::KotlinPrimitiveType::Double => "Double",
        }
    }

    fn array_allocation(element_type: &KotlinType, size: &str) -> String {
        match element_type {
            KotlinType::Primitive(super::KotlinPrimitiveType::Boolean) => {
                format!("BooleanArray({size})")
            }
            KotlinType::Primitive(super::KotlinPrimitiveType::Byte) => {
                format!("ByteArray({size})")
            }
            KotlinType::Primitive(super::KotlinPrimitiveType::Short) => {
                format!("ShortArray({size})")
            }
            KotlinType::Primitive(super::KotlinPrimitiveType::Char) => {
                format!("CharArray({size})")
            }
            KotlinType::Primitive(super::KotlinPrimitiveType::Int) => {
                format!("IntArray({size})")
            }
            KotlinType::Primitive(super::KotlinPrimitiveType::Long) => {
                format!("LongArray({size})")
            }
            KotlinType::Primitive(super::KotlinPrimitiveType::Float) => {
                format!("FloatArray({size})")
            }
            KotlinType::Primitive(super::KotlinPrimitiveType::Double) => {
                format!("DoubleArray({size})")
            }
            _ => format!("arrayOfNulls<{element_type}>({size})"),
        }
    }

    fn child(
        children: &mut impl Iterator<Item = RenderedExpression>,
    ) -> Result<String, KotlinPrintError> {
        Ok(Self::child_expression(children)?.text)
    }

    fn receiver(expression: RenderedExpression) -> String {
        if expression.non_null
            || matches!(expression.text.as_str(), "this" | "super")
            || expression.text.ends_with("::class.java")
        {
            expression.text
        } else {
            format!(
                "{}!!",
                expression.requiring(ExpressionRequirement::Primary).text
            )
        }
    }

    fn asserted_receiver(expression: String) -> String {
        if matches!(expression.as_str(), "this" | "super") {
            expression
        } else {
            format!("{expression}!!")
        }
    }

    fn child_expression(
        children: &mut impl Iterator<Item = RenderedExpression>,
    ) -> Result<RenderedExpression, KotlinPrintError> {
        children.next().ok_or(KotlinPrintError::MalformedExpression)
    }

    fn binary_precedence(operator: KotlinBinaryOp) -> ExpressionPrecedence {
        match operator {
            KotlinBinaryOp::Multiply | KotlinBinaryOp::Divide | KotlinBinaryOp::Remainder => {
                ExpressionPrecedence::Multiplicative
            }
            KotlinBinaryOp::Add | KotlinBinaryOp::Subtract => ExpressionPrecedence::Additive,
            KotlinBinaryOp::ShiftLeft
            | KotlinBinaryOp::ShiftRight
            | KotlinBinaryOp::UnsignedShiftRight => ExpressionPrecedence::Shift,
            KotlinBinaryOp::Less
            | KotlinBinaryOp::GreaterEqual
            | KotlinBinaryOp::Greater
            | KotlinBinaryOp::LessEqual => ExpressionPrecedence::Relational,
            KotlinBinaryOp::Equal
            | KotlinBinaryOp::NotEqual
            | KotlinBinaryOp::ReferentialEqual
            | KotlinBinaryOp::ReferentialNotEqual => ExpressionPrecedence::Equality,
            KotlinBinaryOp::BitAnd => ExpressionPrecedence::BitAnd,
            KotlinBinaryOp::BitXor => ExpressionPrecedence::BitXor,
            KotlinBinaryOp::BitOr => ExpressionPrecedence::BitOr,
            KotlinBinaryOp::LogicalAnd => ExpressionPrecedence::LogicalAnd,
            KotlinBinaryOp::LogicalOr => ExpressionPrecedence::LogicalOr,
        }
    }

    fn right_associative_with(operator: KotlinBinaryOp, right: &RenderedExpression) -> bool {
        right.binary == Some(operator)
            && matches!(
                operator,
                KotlinBinaryOp::BitAnd
                    | KotlinBinaryOp::BitOr
                    | KotlinBinaryOp::BitXor
                    | KotlinBinaryOp::LogicalAnd
                    | KotlinBinaryOp::LogicalOr
            )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language::kotlin::KotlinPrimitiveType;

    #[test]
    fn allocated_dimensions_precede_unallocated_array_rank() {
        let element_type = KotlinType::array(KotlinType::Primitive(KotlinPrimitiveType::Byte));
        let expression = ExpressionFrame::NewArray {
            element_type: &element_type,
            dimensions: 1,
            initializer: 0,
            requirement: ExpressionRequirement::Any,
        }
        .render(vec![RenderedExpression::primary("3")])
        .expect("array expression")
        .text;

        assert_eq!(expression, "arrayOfNulls<ByteArray>(3)");
    }

    #[test]
    fn array_initializer_preserves_the_complete_rank() {
        let element_type = KotlinType::array(KotlinType::Primitive(KotlinPrimitiveType::Byte));
        let expression = ExpressionFrame::NewArray {
            element_type: &element_type,
            dimensions: 0,
            initializer: 1,
            requirement: ExpressionRequirement::Any,
        }
        .render(vec![RenderedExpression::primary("row")])
        .expect("array expression")
        .text;

        assert_eq!(expression, "arrayOf(row)");
    }

    #[test]
    fn qualified_class_creation_uses_the_member_type_name() {
        let ty = KotlinType::source_class("example.Outer.Inner");
        let expression = ExpressionFrame::New {
            has_enclosing: true,
            ty: &ty,
            args: 0,
            anonymous_super_constructor: false,
            anonymous_body: None,
            requirement: ExpressionRequirement::Any,
        }
        .render(vec![RenderedExpression::primary("owner")])
        .expect("qualified class creation")
        .text;

        assert_eq!(expression, "owner.Inner()");
    }
}
