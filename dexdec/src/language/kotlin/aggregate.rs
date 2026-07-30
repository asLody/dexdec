use super::{
    KotlinAssignOp, KotlinAstRewriter, KotlinAstTransform, KotlinExpr, KotlinLiteral,
    KotlinMethodBody, KotlinStmt, KotlinType,
};

#[derive(Debug, Default)]
pub struct AggregateInitializer {
    changed: bool,
}

impl AggregateInitializer {
    fn combine(&mut self, statements: Vec<KotlinStmt>) -> Vec<KotlinStmt> {
        let mut output = Vec::with_capacity(statements.len());
        let mut pending = statements.into_iter().peekable();

        while let Some(statement) = pending.next() {
            let KotlinStmt::Variable {
                binding,
                ty,
                name,
                value: Some(value),
            } = statement
            else {
                output.push(statement);
                continue;
            };
            let Some(mut allocation) = ArrayAllocation::analyze(value.clone()) else {
                output.push(KotlinStmt::Variable {
                    binding,
                    ty,
                    name,
                    value: Some(value),
                });
                continue;
            };
            let [KotlinExpr::Literal(KotlinLiteral::Integer(length))] =
                allocation.dimensions.as_slice()
            else {
                output.push(KotlinStmt::Variable {
                    binding,
                    ty,
                    name,
                    value: Some(allocation.into_expression()),
                });
                continue;
            };
            let length = *length;
            if length <= 0 || !allocation.initializer.is_empty() {
                output.push(KotlinStmt::Variable {
                    binding,
                    ty,
                    name,
                    value: Some(allocation.into_expression()),
                });
                continue;
            }

            let mut values = Vec::with_capacity(length as usize);
            while values.len() < length as usize {
                let Some(KotlinStmt::Assign {
                    target: KotlinExpr::ArrayAccess { array, index },
                    op: KotlinAssignOp::Assign,
                    ..
                }) = pending.peek()
                else {
                    break;
                };
                let expected = values.len() as i32;
                if !matches!(
                    (array.as_ref(), index.as_ref()),
                    (
                        KotlinExpr::Name(array),
                        KotlinExpr::Literal(KotlinLiteral::Integer(index))
                    ) if array == &name && *index == expected
                ) {
                    break;
                }
                let KotlinStmt::Assign { value, .. } =
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
                output.push(KotlinStmt::Variable {
                    binding,
                    ty,
                    name,
                    value: Some(allocation.into_expression()),
                });
                continue;
            }

            output.push(KotlinStmt::Variable {
                binding,
                ty,
                name: name.clone(),
                value: Some(allocation.into_expression()),
            });
            for (index, value) in values.into_iter().enumerate() {
                output.push(KotlinStmt::Assign {
                    target: KotlinExpr::ArrayAccess {
                        array: Box::new(KotlinExpr::Name(name.clone())),
                        index: Box::new(KotlinExpr::Literal(KotlinLiteral::Integer(index as i32))),
                    },
                    op: KotlinAssignOp::Assign,
                    value,
                });
            }
        }
        self.inline(output)
    }

    fn inline(&mut self, statements: Vec<KotlinStmt>) -> Vec<KotlinStmt> {
        let mut output = Vec::with_capacity(statements.len());
        let mut pending = statements.into_iter().peekable();
        while let Some(statement) = pending.next() {
            let KotlinStmt::Variable {
                name,
                value:
                    Some(
                        value @ KotlinExpr::NewArray {
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
            let Some(KotlinStmt::Assign {
                target: KotlinExpr::StaticField { .. },
                op: KotlinAssignOp::Assign,
                value: KotlinExpr::Name(source),
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
                    KotlinStmt::Assign { value, .. } => Some(value),
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
    casts: Vec<KotlinType>,
    element_type: KotlinType,
    dimensions: Vec<KotlinExpr>,
    initializer: Vec<KotlinExpr>,
}

impl ArrayAllocation {
    fn analyze(mut expression: KotlinExpr) -> Option<Self> {
        let mut casts = Vec::new();
        while let KotlinExpr::Cast { ty, value } = expression {
            casts.push(ty);
            expression = *value;
        }
        let KotlinExpr::NewArray {
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

    fn into_expression(self) -> KotlinExpr {
        self.casts.into_iter().rev().fold(
            KotlinExpr::NewArray {
                element_type: self.element_type,
                dimensions: self.dimensions,
                initializer: self.initializer,
            },
            |value, ty| KotlinExpr::Cast {
                ty,
                value: Box::new(value),
            },
        )
    }
}

struct ExpressionNameUse<'a> {
    target: &'a super::KotlinIdentifier,
    found: bool,
}

impl ExpressionNameUse<'_> {
    fn contains(expression: &KotlinExpr, target: &super::KotlinIdentifier) -> bool {
        let mut query = ExpressionNameUse {
            target,
            found: false,
        };
        query.rewrite_expression(expression.clone());
        query.found
    }
}

impl KotlinAstRewriter for ExpressionNameUse<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if matches!(&expression, KotlinExpr::Name(name) if name == self.target) {
            self.found = true;
        }
        expression
    }
}

impl KotlinAstRewriter for AggregateInitializer {
    fn rewrite_statements(&mut self, statements: Vec<KotlinStmt>) -> Vec<KotlinStmt> {
        let statements = statements
            .into_iter()
            .map(|statement| self.rewrite_statement(statement))
            .collect();
        self.combine(statements)
    }
}

impl KotlinAstTransform for AggregateInitializer {
    type Error = super::KotlinStructuralError;

    fn apply(&mut self, body: &mut KotlinMethodBody) -> Result<bool, Self::Error> {
        self.changed = false;
        self.rewrite_body(body);
        Ok(self.changed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language::kotlin::{KotlinIdentifier, KotlinPrimitiveType, KotlinType};

    #[test]
    fn combines_complete_array_writes() {
        let name = KotlinIdentifier::from_dex("values");
        let array = || KotlinExpr::ArrayAccess {
            array: Box::new(KotlinExpr::Name(name.clone())),
            index: Box::new(KotlinExpr::Literal(KotlinLiteral::Integer(0))),
        };
        let mut body = KotlinMethodBody {
            root: KotlinStmt::Block(vec![
                KotlinStmt::Variable {
                    binding: Default::default(),
                    ty: KotlinType::array(KotlinType::Primitive(KotlinPrimitiveType::Int)),
                    name: name.clone(),
                    value: Some(KotlinExpr::NewArray {
                        element_type: KotlinType::Primitive(KotlinPrimitiveType::Int),
                        dimensions: vec![KotlinExpr::Literal(KotlinLiteral::Integer(1))],
                        initializer: Vec::new(),
                    }),
                },
                KotlinStmt::Assign {
                    target: array(),
                    op: KotlinAssignOp::Assign,
                    value: KotlinExpr::Literal(KotlinLiteral::Integer(4)),
                },
            ]),
        };

        assert!(AggregateInitializer::default().apply(&mut body).unwrap());
        let KotlinStmt::Block(statements) = body.root else {
            panic!("expected block");
        };
        assert!(matches!(
            statements.as_slice(),
            [KotlinStmt::Variable {
                value: Some(KotlinExpr::NewArray {
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
        let name = KotlinIdentifier::from_dex("values");
        let array_type = KotlinType::array(KotlinType::source_class("java.lang.Object"));
        let mut body = KotlinMethodBody {
            root: KotlinStmt::Block(vec![
                KotlinStmt::Variable {
                    binding: Default::default(),
                    ty: array_type,
                    name: name.clone(),
                    value: Some(KotlinExpr::NewArray {
                        element_type: KotlinType::source_class("java.lang.Object"),
                        dimensions: vec![KotlinExpr::Literal(KotlinLiteral::Integer(1))],
                        initializer: Vec::new(),
                    }),
                },
                KotlinStmt::Assign {
                    target: KotlinExpr::ArrayAccess {
                        array: Box::new(KotlinExpr::Name(name.clone())),
                        index: Box::new(KotlinExpr::Literal(KotlinLiteral::Integer(0))),
                    },
                    op: KotlinAssignOp::Assign,
                    value: KotlinExpr::Name(name),
                },
            ]),
        };

        assert!(!AggregateInitializer::default().apply(&mut body).unwrap());
        assert!(matches!(body.root, KotlinStmt::Block(ref statements) if statements.len() == 2));
    }
}
