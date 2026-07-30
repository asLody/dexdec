use std::collections::BTreeSet;

use crate::language::kotlin::{
    KotlinAstRewriter, KotlinExpr, KotlinIdentifier, KotlinJvmIntrinsic, KotlinStmt,
    KotlinTypeDeclaration,
};

/// Removes checks inserted by the Kotlin/JVM compiler when the typed source
/// tree already carries the contract that will recreate them on recompilation.
pub(super) struct KotlinCompilerChecks {
    entry_non_null: BTreeSet<KotlinIdentifier>,
}

impl KotlinCompilerChecks {
    pub(super) fn apply(declaration: &mut KotlinTypeDeclaration) {
        for method in &mut declaration.methods {
            let Some(body) = method.body.as_mut() else {
                continue;
            };
            let mut checks = Self {
                entry_non_null: method
                    .parameters
                    .iter()
                    .filter(|parameter| !parameter.nullable)
                    .map(|parameter| parameter.name.clone())
                    .collect(),
            };
            body.root =
                checks.rewrite_statement(std::mem::replace(&mut body.root, KotlinStmt::Empty));
        }
        for nested in &mut declaration.nested {
            Self::apply(nested);
        }
    }

    fn is_expression_value_check(
        statement: &KotlinStmt,
        non_null: &BTreeSet<KotlinIdentifier>,
    ) -> bool {
        let Some(expression) =
            Self::intrinsic_expression(statement, KotlinJvmIntrinsic::ExpressionValueCheck)
        else {
            return false;
        };
        let KotlinExpr::Call { args, .. } = expression else {
            return false;
        };
        let [value, _] = args.as_slice() else {
            return false;
        };
        Self::checked_local(value).is_some_and(|value| non_null.contains(value))
    }

    fn is_receiver_null_check(
        statement: &KotlinStmt,
        non_null: &BTreeSet<KotlinIdentifier>,
    ) -> bool {
        let Some(expression) =
            Self::intrinsic_expression(statement, KotlinJvmIntrinsic::ReceiverNullCheck)
        else {
            return false;
        };
        let KotlinExpr::Call {
            receiver: Some(receiver),
            args,
            ..
        } = expression
        else {
            return false;
        };
        args.is_empty()
            && Self::checked_local(receiver.as_ref()).is_some_and(|value| non_null.contains(value))
    }

    fn intrinsic_expression(
        statement: &KotlinStmt,
        expected: KotlinJvmIntrinsic,
    ) -> Option<&KotlinExpr> {
        let KotlinStmt::Expression(expression) = statement else {
            return None;
        };
        let expression = Self::transparent(expression);
        match expression {
            KotlinExpr::JvmIntrinsic { kind, expression } if *kind == expected => {
                Some(expression.as_ref())
            }
            _ => None,
        }
    }

    fn transparent(expression: &KotlinExpr) -> &KotlinExpr {
        match expression {
            KotlinExpr::SmartCast(value) => Self::transparent(value),
            expression => expression,
        }
    }

    fn checked_local(expression: &KotlinExpr) -> Option<&KotlinIdentifier> {
        match expression {
            KotlinExpr::Name(value) => Some(value),
            KotlinExpr::SmartCast(value) | KotlinExpr::NonNullAssertion(value) => {
                Self::checked_local(value)
            }
            _ => None,
        }
    }
}

impl KotlinAstRewriter for KotlinCompilerChecks {
    fn rewrite_statements(&mut self, statements: Vec<KotlinStmt>) -> Vec<KotlinStmt> {
        let mut non_null = self.entry_non_null.clone();
        let mut rewritten = Vec::with_capacity(statements.len());
        for statement in statements {
            let statement = self.rewrite_statement(statement);
            if Self::is_expression_value_check(&statement, &non_null)
                || Self::is_receiver_null_check(&statement, &non_null)
            {
                continue;
            }
            if let KotlinStmt::Variable { binding, name, .. } = &statement {
                if !binding.nullable {
                    non_null.insert(name.clone());
                } else {
                    non_null.remove(name);
                }
            }
            rewritten.push(statement);
        }
        rewritten
    }
}
