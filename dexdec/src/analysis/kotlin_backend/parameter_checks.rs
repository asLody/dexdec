//! Removal of the null check the compiler adds for a non-null parameter.
//!
//! A function taking a non-null parameter opens with a call that raises if the
//! argument was null anyway, which is how Kotlin defends its types against Java
//! callers. The author wrote none of it, and it reappears on recompilation from
//! the parameter's own type, so carrying it costs a line per parameter and says
//! nothing the signature does not.
//!
//! DEX lowering marks the exact Kotlin/JVM intrinsic before source names are
//! rewritten. This pass additionally verifies that the argument is a non-null
//! source parameter and that the compiler's diagnostic name still identifies
//! that parameter.

use std::collections::BTreeSet;

use crate::language::kotlin::{
    KotlinExpr, KotlinIdentifier, KotlinJvmIntrinsic, KotlinLiteral, KotlinStmt,
    KotlinTypeDeclaration,
};

pub(super) struct KotlinParameterChecks;

impl KotlinParameterChecks {
    pub(super) fn apply(declaration: &mut KotlinTypeDeclaration) {
        for method in &mut declaration.methods {
            let checked = method
                .parameters
                .iter()
                .filter(|parameter| !parameter.nullable)
                .map(|parameter| parameter.name.clone())
                .collect::<BTreeSet<_>>();
            let receiver_non_null = method
                .receiver
                .as_ref()
                .is_some_and(|receiver| !receiver.nullable);
            if checked.is_empty() && !receiver_non_null {
                continue;
            }
            let Some(body) = &mut method.body else {
                continue;
            };
            let root = std::mem::replace(&mut body.root, KotlinStmt::Empty);
            body.root = Self::rewrite(root, &checked, receiver_non_null);
        }
        for nested in &mut declaration.nested {
            Self::apply(nested);
        }
    }

    fn rewrite(
        statement: KotlinStmt,
        checked: &BTreeSet<KotlinIdentifier>,
        receiver_non_null: bool,
    ) -> KotlinStmt {
        match statement {
            KotlinStmt::Block(statements) => KotlinStmt::Block(
                statements
                    .into_iter()
                    .filter(|statement| {
                        !Self::is_parameter_check(statement, checked, receiver_non_null)
                    })
                    .map(|statement| Self::rewrite(statement, checked, receiver_non_null))
                    .collect(),
            ),
            KotlinStmt::Labeled { label, body } => KotlinStmt::Labeled {
                label,
                body: Box::new(Self::rewrite(*body, checked, receiver_non_null)),
            },
            KotlinStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => KotlinStmt::If {
                condition,
                then_stmt: Box::new(Self::rewrite(*then_stmt, checked, receiver_non_null)),
                else_stmt: else_stmt
                    .map(|node| Box::new(Self::rewrite(*node, checked, receiver_non_null))),
            },
            statement => statement,
        }
    }

    /// Whether the statement is the compiler's check for one named parameter.
    fn is_parameter_check(
        statement: &KotlinStmt,
        checked: &BTreeSet<KotlinIdentifier>,
        receiver_non_null: bool,
    ) -> bool {
        let KotlinStmt::Expression(KotlinExpr::JvmIntrinsic {
            kind: KotlinJvmIntrinsic::ParameterCheck,
            expression,
        }) = statement
        else {
            return false;
        };
        let KotlinExpr::Call { args, .. } = expression.as_ref() else {
            return false;
        };
        let [argument, KotlinExpr::Literal(KotlinLiteral::String(reported))] = args.as_slice()
        else {
            return false;
        };
        // The identifier renders escaped where it needs to be, so the DEX name
        // is what the compiler would have passed.
        match Self::checked_argument(argument) {
            KotlinExpr::Name(argument) => {
                checked.contains(argument) && reported.to_string_lossy() == argument.dex_name()
            }
            KotlinExpr::This => receiver_non_null && reported.to_string_lossy() == "<this>",
            _ => false,
        }
    }

    fn checked_argument(expression: &KotlinExpr) -> &KotlinExpr {
        match expression {
            KotlinExpr::SmartCast(value) | KotlinExpr::NonNullAssertion(value) => {
                Self::checked_argument(value)
            }
            expression => expression,
        }
    }
}
