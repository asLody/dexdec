use super::{
    JavaAssignOp, JavaAstRewriter, JavaAstTransform, JavaExpr, JavaLiteral, JavaMethodBody,
    JavaStmt, JavaType,
};

#[derive(Debug, Default)]
pub struct AggregateInitializer {
    changed: bool,
}

impl AggregateInitializer {
    fn combine(&mut self, statements: Vec<JavaStmt>) -> Vec<JavaStmt> {
        let mut output = Vec::with_capacity(statements.len());
        let mut pending = statements.into_iter().peekable();

        while let Some(statement) = pending.next() {
            let JavaStmt::Variable {
                ty,
                name,
                value: Some(value),
            } = statement
            else {
                output.push(statement);
                continue;
            };
            let Some(mut allocation) = ArrayAllocation::analyze(value.clone()) else {
                output.push(JavaStmt::Variable {
                    ty,
                    name,
                    value: Some(value),
                });
                continue;
            };
            let [JavaExpr::Literal(JavaLiteral::Integer(length))] =
                allocation.dimensions.as_slice()
            else {
                output.push(JavaStmt::Variable {
                    ty,
                    name,
                    value: Some(allocation.into_expression()),
                });
                continue;
            };
            let length = *length;
            if length <= 0 || !allocation.initializer.is_empty() {
                output.push(JavaStmt::Variable {
                    ty,
                    name,
                    value: Some(allocation.into_expression()),
                });
                continue;
            }

            let mut values = Vec::with_capacity(length as usize);
            while values.len() < length as usize {
                let Some(JavaStmt::Assign {
                    target: JavaExpr::ArrayAccess { array, index },
                    op: JavaAssignOp::Assign,
                    ..
                }) = pending.peek()
                else {
                    break;
                };
                let expected = values.len() as i32;
                if !matches!(
                    (array.as_ref(), index.as_ref()),
                    (
                        JavaExpr::Name(array),
                        JavaExpr::Literal(JavaLiteral::Integer(index))
                    ) if array == &name && *index == expected
                ) {
                    break;
                }
                let JavaStmt::Assign { value, .. } =
                    pending.next().expect("peeked array assignment")
                else {
                    unreachable!();
                };
                values.push(value);
            }

            let complete = values.len() == length as usize;
            let self_referential = values
                .iter()
                .any(|value| ExpressionNameUse::contains(value, &name));
            if complete && !self_referential {
                self.changed = true;
                allocation.dimensions.clear();
                allocation.initializer = values;
                output.push(JavaStmt::Variable {
                    ty,
                    name,
                    value: Some(allocation.into_expression()),
                });
                continue;
            }

            output.push(JavaStmt::Variable {
                ty,
                name: name.clone(),
                value: Some(allocation.into_expression()),
            });
            for (index, value) in values.into_iter().enumerate() {
                output.push(JavaStmt::Assign {
                    target: JavaExpr::ArrayAccess {
                        array: Box::new(JavaExpr::Name(name.clone())),
                        index: Box::new(JavaExpr::Literal(JavaLiteral::Integer(index as i32))),
                    },
                    op: JavaAssignOp::Assign,
                    value,
                });
            }
        }
        self.inline(output)
    }

    fn inline(&mut self, statements: Vec<JavaStmt>) -> Vec<JavaStmt> {
        let mut output = Vec::with_capacity(statements.len());
        let mut pending = statements.into_iter().peekable();
        while let Some(statement) = pending.next() {
            let JavaStmt::Variable {
                name,
                value:
                    Some(
                        value @ JavaExpr::NewArray {
                            dimensions,
                            initializer,
                            ..
                        },
                    ),
                ..
            } = &statement
            else {
                output.push(statement);
                continue;
            };
            if !dimensions.is_empty() || initializer.is_empty() {
                output.push(statement);
                continue;
            }
            let Some(JavaStmt::Assign {
                target: JavaExpr::StaticField { .. },
                op: JavaAssignOp::Assign,
                value: JavaExpr::Name(source),
            }) = pending.peek_mut()
            else {
                output.push(statement);
                continue;
            };
            if source != name {
                output.push(statement);
                continue;
            }
            *pending
                .peek_mut()
                .and_then(|statement| match statement {
                    JavaStmt::Assign { value, .. } => Some(value),
                    _ => None,
                })
                .expect("matched static field assignment") = value.clone();
            self.changed = true;
        }
        output.extend(pending);
        output
    }
}

struct ArrayAllocation {
    casts: Vec<JavaType>,
    element_type: JavaType,
    dimensions: Vec<JavaExpr>,
    initializer: Vec<JavaExpr>,
}

impl ArrayAllocation {
    fn analyze(mut expression: JavaExpr) -> Option<Self> {
        let mut casts = Vec::new();
        while let JavaExpr::Cast { ty, value } = expression {
            casts.push(ty);
            expression = *value;
        }
        let JavaExpr::NewArray {
            element_type,
            dimensions,
            initializer,
        } = expression
        else {
            return None;
        };
        Some(Self {
            casts,
            element_type,
            dimensions,
            initializer,
        })
    }

    fn into_expression(self) -> JavaExpr {
        self.casts.into_iter().rev().fold(
            JavaExpr::NewArray {
                element_type: self.element_type,
                dimensions: self.dimensions,
                initializer: self.initializer,
            },
            |value, ty| JavaExpr::Cast {
                ty,
                value: Box::new(value),
            },
        )
    }
}

struct ExpressionNameUse<'a> {
    target: &'a super::JavaIdentifier,
    found: bool,
}

impl ExpressionNameUse<'_> {
    fn contains(expression: &JavaExpr, target: &super::JavaIdentifier) -> bool {
        let mut query = ExpressionNameUse {
            target,
            found: false,
        };
        query.rewrite_expression(expression.clone());
        query.found
    }
}

impl JavaAstRewriter for ExpressionNameUse<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        if matches!(&expression, JavaExpr::Name(name) if name == self.target) {
            self.found = true;
        }
        expression
    }
}

impl JavaAstRewriter for AggregateInitializer {
    fn rewrite_statements(&mut self, statements: Vec<JavaStmt>) -> Vec<JavaStmt> {
        let statements = statements
            .into_iter()
            .map(|statement| self.rewrite_statement(statement))
            .collect();
        self.combine(statements)
    }
}

impl JavaAstTransform for AggregateInitializer {
    type Error = super::JavaStructuralError;

    fn apply(&mut self, body: &mut JavaMethodBody) -> Result<bool, Self::Error> {
        self.changed = false;
        self.rewrite_body(body);
        Ok(self.changed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language::java::{JavaIdentifier, JavaPrimitiveType, JavaType};

    #[test]
    fn combines_complete_array_writes() {
        let name = JavaIdentifier::from_dex("values");
        let array = || JavaExpr::ArrayAccess {
            array: Box::new(JavaExpr::Name(name.clone())),
            index: Box::new(JavaExpr::Literal(JavaLiteral::Integer(0))),
        };
        let mut body = JavaMethodBody {
            root: JavaStmt::Block(vec![
                JavaStmt::Variable {
                    ty: JavaType::array(JavaType::Primitive(JavaPrimitiveType::Int)),
                    name: name.clone(),
                    value: Some(JavaExpr::NewArray {
                        element_type: JavaType::Primitive(JavaPrimitiveType::Int),
                        dimensions: vec![JavaExpr::Literal(JavaLiteral::Integer(1))],
                        initializer: Vec::new(),
                    }),
                },
                JavaStmt::Assign {
                    target: array(),
                    op: JavaAssignOp::Assign,
                    value: JavaExpr::Literal(JavaLiteral::Integer(4)),
                },
            ]),
        };

        assert!(AggregateInitializer::default().apply(&mut body).unwrap());
        let JavaStmt::Block(statements) = body.root else {
            panic!("expected block");
        };
        assert!(matches!(
            statements.as_slice(),
            [JavaStmt::Variable {
                value: Some(JavaExpr::NewArray {
                    dimensions,
                    initializer,
                    ..
                }),
                ..
            }] if dimensions.is_empty() && initializer.len() == 1
        ));
    }

    #[test]
    fn preserves_self_referential_array_writes() {
        let name = JavaIdentifier::from_dex("values");
        let array_type = JavaType::array(JavaType::source_class("java.lang.Object"));
        let mut body = JavaMethodBody {
            root: JavaStmt::Block(vec![
                JavaStmt::Variable {
                    ty: array_type,
                    name: name.clone(),
                    value: Some(JavaExpr::NewArray {
                        element_type: JavaType::source_class("java.lang.Object"),
                        dimensions: vec![JavaExpr::Literal(JavaLiteral::Integer(1))],
                        initializer: Vec::new(),
                    }),
                },
                JavaStmt::Assign {
                    target: JavaExpr::ArrayAccess {
                        array: Box::new(JavaExpr::Name(name.clone())),
                        index: Box::new(JavaExpr::Literal(JavaLiteral::Integer(0))),
                    },
                    op: JavaAssignOp::Assign,
                    value: JavaExpr::Name(name),
                },
            ]),
        };

        assert!(!AggregateInitializer::default().apply(&mut body).unwrap());
        assert!(matches!(body.root, JavaStmt::Block(ref statements) if statements.len() == 2));
    }
}
