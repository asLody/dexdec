use super::{
    KotlinAnnotation, KotlinAnnotationValue, KotlinAnonymousClassBody, KotlinCatch, KotlinExpr,
    KotlinMethodBody, KotlinPrimaryParameter, KotlinStmt, KotlinType, KotlinTypeArgument,
    KotlinTypeDeclaration,
};

/// Structural Kotlin AST rewriting with one post-order expression hook.
///
/// Implementations describe only their semantic rewrite. Child traversal is
/// centralized here so declaration-level recovery never grows its own syntax
/// shape library.
pub trait KotlinAstRewriter {
    fn rewrite_nested_functions(&self) -> bool {
        true
    }

    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        expression
    }

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        statement
    }

    fn finish_type(&mut self, ty: KotlinType) -> KotlinType {
        ty
    }

    fn finish_anonymous_body(&mut self, _body: &mut KotlinAnonymousClassBody) {}

    fn finish_type_declaration(&mut self, _declaration: &mut KotlinTypeDeclaration) {}

    fn rewrite_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        let expression = match expression {
            KotlinExpr::QualifiedThis(ty) => KotlinExpr::QualifiedThis(self.rewrite_type(ty)),
            KotlinExpr::ClassLiteral(ty) => KotlinExpr::ClassLiteral(self.rewrite_type(ty)),
            KotlinExpr::ObjectReference(ty) => KotlinExpr::ObjectReference(self.rewrite_type(ty)),
            KotlinExpr::SmartCast(value) => {
                KotlinExpr::SmartCast(Box::new(self.rewrite_expression(*value)))
            }
            KotlinExpr::NonNullAssertion(value) => {
                KotlinExpr::NonNullAssertion(Box::new(self.rewrite_expression(*value)))
            }
            KotlinExpr::JvmIntrinsic { kind, expression } => KotlinExpr::JvmIntrinsic {
                kind,
                expression: Box::new(self.rewrite_expression(*expression)),
            },
            KotlinExpr::Field { owner, name } => KotlinExpr::Field {
                owner: Box::new(self.rewrite_expression(*owner)),
                name,
            },
            KotlinExpr::StaticField { owner, name } => KotlinExpr::StaticField {
                owner: self.rewrite_type(owner),
                name,
            },
            KotlinExpr::ArrayAccess { array, index } => KotlinExpr::ArrayAccess {
                array: Box::new(self.rewrite_expression(*array)),
                index: Box::new(self.rewrite_expression(*index)),
            },
            KotlinExpr::Call {
                receiver,
                owner,
                type_arguments,
                method,
                args,
            } => KotlinExpr::Call {
                receiver: receiver.map(|value| Box::new(self.rewrite_expression(*value))),
                owner: owner.map(|ty| self.rewrite_type(ty)),
                type_arguments: self.rewrite_types(type_arguments),
                method,
                args: args.map_values(|value| self.rewrite_expression(value)),
            },
            KotlinExpr::MethodReference { receiver, method } => KotlinExpr::MethodReference {
                receiver: Box::new(self.rewrite_expression(*receiver)),
                method,
            },
            KotlinExpr::Lambda { parameters, body } if self.rewrite_nested_functions() => {
                KotlinExpr::Lambda {
                    parameters,
                    body: Box::new(self.rewrite_expression(*body)),
                }
            }
            KotlinExpr::BlockLambda { parameters, body } if self.rewrite_nested_functions() => {
                KotlinExpr::BlockLambda {
                    parameters,
                    body: Box::new(self.rewrite_statement(*body)),
                }
            }
            KotlinExpr::New {
                enclosing,
                ty,
                target_type,
                args,
                anonymous_body,
            } => KotlinExpr::New {
                enclosing: enclosing.map(|value| Box::new(self.rewrite_expression(*value))),
                ty: self.rewrite_type(ty),
                target_type: target_type.map(|ty| self.rewrite_type(ty)),
                args: self.rewrite_expressions(args),
                anonymous_body: anonymous_body.map(|mut body| {
                    self.rewrite_anonymous_body(&mut body);
                    body
                }),
            },
            KotlinExpr::NewArray {
                element_type,
                dimensions,
                initializer,
            } => KotlinExpr::NewArray {
                element_type: self.rewrite_type(element_type),
                dimensions: self.rewrite_expressions(dimensions),
                initializer: self.rewrite_expressions(initializer),
            },
            KotlinExpr::Unary { op, operand } => KotlinExpr::Unary {
                op,
                operand: Box::new(self.rewrite_expression(*operand)),
            },
            KotlinExpr::Update { op, target, prefix } => KotlinExpr::Update {
                op,
                target: Box::new(self.rewrite_expression(*target)),
                prefix,
            },
            KotlinExpr::Binary { left, op, right } => KotlinExpr::Binary {
                left: Box::new(self.rewrite_expression(*left)),
                op,
                right: Box::new(self.rewrite_expression(*right)),
            },
            KotlinExpr::Cast { ty, value } => KotlinExpr::Cast {
                ty: self.rewrite_type(ty),
                value: Box::new(self.rewrite_expression(*value)),
            },
            KotlinExpr::InstanceOf { value, ty } => KotlinExpr::InstanceOf {
                value: Box::new(self.rewrite_expression(*value)),
                ty: self.rewrite_type(ty),
            },
            KotlinExpr::Conditional {
                condition,
                when_true,
                when_false,
            } => KotlinExpr::Conditional {
                condition: Box::new(self.rewrite_expression(*condition)),
                when_true: Box::new(self.rewrite_expression(*when_true)),
                when_false: Box::new(self.rewrite_expression(*when_false)),
            },
            KotlinExpr::Assignment { target, op, value } => KotlinExpr::Assignment {
                target: Box::new(self.rewrite_expression(*target)),
                op,
                value: Box::new(self.rewrite_expression(*value)),
            },
            leaf => leaf,
        };
        self.finish_expression(expression)
    }

    fn rewrite_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        let statement = match statement {
            KotlinStmt::Block(statements) => KotlinStmt::Block(self.rewrite_statements(statements)),
            KotlinStmt::Labeled { label, body } => KotlinStmt::Labeled {
                label,
                body: Box::new(self.rewrite_statement(*body)),
            },
            KotlinStmt::Variable {
                binding,
                ty,
                name,
                value,
            } => KotlinStmt::Variable {
                binding,
                ty: self.rewrite_type(ty),
                name,
                value: value.map(|value| self.rewrite_expression(value)),
            },
            KotlinStmt::Expression(expression) => {
                KotlinStmt::Expression(self.rewrite_expression(expression))
            }
            KotlinStmt::ConstructorInvocation { target, args } => {
                KotlinStmt::ConstructorInvocation {
                    target,
                    args: self.rewrite_expressions(args),
                }
            }
            KotlinStmt::Assign { target, op, value } => KotlinStmt::Assign {
                target: self.rewrite_expression(target),
                op,
                value: self.rewrite_expression(value),
            },
            KotlinStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => KotlinStmt::If {
                condition: self.rewrite_expression(condition),
                then_stmt: Box::new(self.rewrite_statement(*then_stmt)),
                else_stmt: else_stmt.map(|statement| Box::new(self.rewrite_statement(*statement))),
            },
            KotlinStmt::While {
                label,
                condition,
                body,
            } => KotlinStmt::While {
                label,
                condition: self.rewrite_expression(condition),
                body: Box::new(self.rewrite_statement(*body)),
            },
            KotlinStmt::DoWhile {
                label,
                body,
                condition,
            } => KotlinStmt::DoWhile {
                label,
                body: Box::new(self.rewrite_statement(*body)),
                condition: self.rewrite_expression(condition),
            },
            KotlinStmt::For {
                label,
                init,
                condition,
                update,
                body,
            } => KotlinStmt::For {
                label,
                init: self.rewrite_statements(init),
                condition: condition.map(|value| self.rewrite_expression(value)),
                update: self.rewrite_expressions(update),
                body: Box::new(self.rewrite_statement(*body)),
            },
            KotlinStmt::ForEach {
                label,
                ty,
                variable,
                iterable,
                body,
            } => KotlinStmt::ForEach {
                label,
                ty: self.rewrite_type(ty),
                variable,
                iterable: self.rewrite_expression(iterable),
                body: Box::new(self.rewrite_statement(*body)),
            },
            KotlinStmt::Switch {
                label,
                selector,
                mut cases,
            } => {
                for case in &mut cases {
                    case.labels = self.rewrite_expressions(std::mem::take(&mut case.labels));
                    case.body = self.rewrite_statements(std::mem::take(&mut case.body));
                }
                KotlinStmt::Switch {
                    label,
                    selector: self.rewrite_expression(selector),
                    cases,
                }
            }
            KotlinStmt::Try {
                body,
                mut catches,
                finally,
            } => {
                for KotlinCatch { types, body, .. } in &mut catches {
                    *types = self.rewrite_types(std::mem::take(types));
                    *body = self.rewrite_statement(std::mem::replace(body, KotlinStmt::Empty));
                }
                KotlinStmt::Try {
                    body: Box::new(self.rewrite_statement(*body)),
                    catches,
                    finally: finally.map(|body| Box::new(self.rewrite_statement(*body))),
                }
            }
            KotlinStmt::Synchronized { lock, body } => KotlinStmt::Synchronized {
                lock: self.rewrite_expression(lock),
                body: Box::new(self.rewrite_statement(*body)),
            },
            KotlinStmt::Return(value) => {
                KotlinStmt::Return(value.map(|value| self.rewrite_expression(value)))
            }
            KotlinStmt::Throw(value) => KotlinStmt::Throw(self.rewrite_expression(value)),
            leaf => leaf,
        };
        self.finish_statement(statement)
    }

    fn rewrite_body(&mut self, body: &mut KotlinMethodBody) {
        body.root = self.rewrite_statement(std::mem::replace(&mut body.root, KotlinStmt::Empty));
    }

    fn rewrite_type(&mut self, ty: KotlinType) -> KotlinType {
        let ty = match ty {
            KotlinType::Array(element) => KotlinType::Array(Box::new(
                element.map_type(|element| self.rewrite_type(element)),
            )),
            KotlinType::Class(mut class) => {
                for segment in &mut class.segments {
                    for argument in &mut segment.arguments {
                        *argument = match std::mem::replace(argument, KotlinTypeArgument::Any) {
                            KotlinTypeArgument::Any => KotlinTypeArgument::Any,
                            KotlinTypeArgument::Exact(ty) => {
                                KotlinTypeArgument::Exact(self.rewrite_type(ty))
                            }
                            KotlinTypeArgument::Extends(ty) => {
                                KotlinTypeArgument::Extends(self.rewrite_type(ty))
                            }
                            KotlinTypeArgument::Super(ty) => {
                                KotlinTypeArgument::Super(self.rewrite_type(ty))
                            }
                        };
                    }
                }
                KotlinType::Class(class)
            }
            ty => ty,
        };
        self.finish_type(ty)
    }

    fn rewrite_anonymous_body(&mut self, body: &mut KotlinAnonymousClassBody) {
        for field in &mut body.fields {
            self.rewrite_annotations(&mut field.annotations);
            field.ty = self.rewrite_type(field.ty.clone());
            field.initializer = field
                .initializer
                .take()
                .map(|value| self.rewrite_expression(value));
        }
        for property in &mut body.properties {
            self.rewrite_annotations(&mut property.annotations);
            property.ty = self.rewrite_type(property.ty.clone());
            if let Some(getter) = &mut property.getter {
                self.rewrite_body(getter);
            }
        }
        for method in &mut body.methods {
            self.rewrite_annotations(&mut method.annotations);
            Self::rewrite_type_parameters(self, &mut method.type_parameters);
            method.return_type = method.return_type.take().map(|ty| self.rewrite_type(ty));
            if let Some(receiver) = &mut method.receiver {
                receiver.ty = self.rewrite_type(receiver.ty.clone());
            }
            for parameter in &mut method.parameters {
                self.rewrite_annotations(&mut parameter.annotations);
                parameter.ty = self.rewrite_type(parameter.ty.clone());
                parameter.default_value = parameter
                    .default_value
                    .take()
                    .map(|value| self.rewrite_expression(value));
            }
            method.throws = self.rewrite_types(std::mem::take(&mut method.throws));
            if let Some(body) = &mut method.body {
                self.rewrite_body(body);
            }
        }
        for nested in &mut body.nested {
            self.rewrite_type_declaration(nested);
        }
        self.finish_anonymous_body(body);
    }

    fn rewrite_type_declaration(&mut self, declaration: &mut KotlinTypeDeclaration) {
        self.rewrite_annotations(&mut declaration.annotations);
        Self::rewrite_type_parameters(self, &mut declaration.type_parameters);
        declaration.extends = declaration.extends.take().map(|ty| self.rewrite_type(ty));
        declaration.implements = self.rewrite_types(std::mem::take(&mut declaration.implements));
        declaration.superclass_arguments =
            self.rewrite_expressions(std::mem::take(&mut declaration.superclass_arguments));
        for parameter in &mut declaration.primary_parameters {
            match parameter {
                KotlinPrimaryParameter::Property(field) => {
                    self.rewrite_annotations(&mut field.annotations);
                    field.ty = self.rewrite_type(field.ty.clone());
                    field.initializer = field
                        .initializer
                        .take()
                        .map(|value| self.rewrite_expression(value));
                }
                KotlinPrimaryParameter::Value(parameter) => {
                    self.rewrite_annotations(&mut parameter.annotations);
                    parameter.ty = self.rewrite_type(parameter.ty.clone());
                    parameter.default_value = parameter
                        .default_value
                        .take()
                        .map(|value| self.rewrite_expression(value));
                }
            }
        }
        for constant in &mut declaration.enum_constants {
            self.rewrite_annotations(&mut constant.annotations);
            constant.arguments = self.rewrite_expressions(std::mem::take(&mut constant.arguments));
            if let Some(body) = &mut constant.body {
                self.rewrite_anonymous_body(body);
            }
        }
        for field in &mut declaration.fields {
            self.rewrite_annotations(&mut field.annotations);
            field.ty = self.rewrite_type(field.ty.clone());
            field.initializer = field
                .initializer
                .take()
                .map(|value| self.rewrite_expression(value));
        }
        for property in &mut declaration.properties {
            self.rewrite_annotations(&mut property.annotations);
            property.ty = self.rewrite_type(property.ty.clone());
            if let Some(getter) = &mut property.getter {
                self.rewrite_body(getter);
            }
        }
        for method in &mut declaration.methods {
            self.rewrite_annotations(&mut method.annotations);
            Self::rewrite_type_parameters(self, &mut method.type_parameters);
            method.return_type = method.return_type.take().map(|ty| self.rewrite_type(ty));
            if let Some(receiver) = &mut method.receiver {
                receiver.ty = self.rewrite_type(receiver.ty.clone());
            }
            for parameter in &mut method.parameters {
                self.rewrite_annotations(&mut parameter.annotations);
                parameter.ty = self.rewrite_type(parameter.ty.clone());
            }
            method.throws = self.rewrite_types(std::mem::take(&mut method.throws));
            if let Some(body) = &mut method.body {
                self.rewrite_body(body);
            }
        }
        for nested in &mut declaration.nested {
            self.rewrite_type_declaration(nested);
        }
        self.finish_type_declaration(declaration);
    }

    fn rewrite_annotation_value(&mut self, value: KotlinAnnotationValue) -> KotlinAnnotationValue {
        match value {
            KotlinAnnotationValue::Expression(expression) => {
                KotlinAnnotationValue::Expression(self.rewrite_expression(expression))
            }
            KotlinAnnotationValue::Annotation(mut annotation) => {
                for element in &mut annotation.elements {
                    element.value = self.rewrite_annotation_value(std::mem::replace(
                        &mut element.value,
                        KotlinAnnotationValue::Array(Vec::new()),
                    ));
                }
                KotlinAnnotationValue::Annotation(annotation)
            }
            KotlinAnnotationValue::Array(values) => KotlinAnnotationValue::Array(
                values
                    .into_iter()
                    .map(|value| self.rewrite_annotation_value(value))
                    .collect(),
            ),
        }
    }

    fn rewrite_annotations(&mut self, annotations: &mut [KotlinAnnotation]) {
        for annotation in annotations {
            annotation.ty = self.rewrite_type(annotation.ty.clone());
            for element in &mut annotation.elements {
                element.value = self.rewrite_annotation_value(std::mem::replace(
                    &mut element.value,
                    KotlinAnnotationValue::Array(Vec::new()),
                ));
            }
        }
    }

    fn rewrite_expressions(&mut self, expressions: Vec<KotlinExpr>) -> Vec<KotlinExpr> {
        expressions
            .into_iter()
            .map(|expression| self.rewrite_expression(expression))
            .collect()
    }

    fn rewrite_types(&mut self, types: Vec<KotlinType>) -> Vec<KotlinType> {
        types.into_iter().map(|ty| self.rewrite_type(ty)).collect()
    }

    fn rewrite_type_parameters(&mut self, parameters: &mut [super::KotlinTypeParameter]) {
        for parameter in parameters {
            parameter.bounds = self.rewrite_types(std::mem::take(&mut parameter.bounds));
        }
    }

    fn rewrite_statements(&mut self, statements: Vec<KotlinStmt>) -> Vec<KotlinStmt> {
        statements
            .into_iter()
            .map(|statement| self.rewrite_statement(statement))
            .collect()
    }
}
