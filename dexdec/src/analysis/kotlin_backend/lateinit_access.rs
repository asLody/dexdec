//! Removal of the access check the compiler adds around a `lateinit` read.
//!
//! Reading a `lateinit` property compiles to a read of the backing field, a null
//! test, and a throw for the case where nothing has assigned it yet. The source
//! wrote only the read, so the test is the compiler's and not the author's, and
//! leaving it in costs several lines at every single access.
//!
//! The property being `lateinit` is what makes the removal sound, and that is a
//! fact the class states in its metadata rather than a shape read off the
//! statements: only a field already carrying the modifier is considered.

use std::collections::BTreeSet;

use crate::language::kotlin::{
    KotlinBinaryOp, KotlinExpr, KotlinIdentifier, KotlinModifier, KotlinStmt, KotlinTypeDeclaration,
};

pub(super) struct KotlinLateinitAccess;

impl KotlinLateinitAccess {
    pub(super) fn apply(declaration: &mut KotlinTypeDeclaration) {
        let fields = declaration
            .fields
            .iter()
            .filter(|field| field.modifiers.contains(&KotlinModifier::Lateinit))
            .map(|field| field.name.clone())
            .collect::<BTreeSet<_>>();
        if !fields.is_empty() {
            for method in &mut declaration.methods {
                if let Some(body) = &mut method.body {
                    let root = std::mem::replace(&mut body.root, KotlinStmt::Empty);
                    body.root = Self::rewrite(root, &fields);
                }
            }
            for property in &mut declaration.properties {
                if let Some(body) = &mut property.getter {
                    let root = std::mem::replace(&mut body.root, KotlinStmt::Empty);
                    body.root = Self::rewrite(root, &fields);
                }
            }
        }
        for nested in &mut declaration.nested {
            Self::apply(nested);
        }
    }

    fn rewrite(statement: KotlinStmt, fields: &BTreeSet<KotlinIdentifier>) -> KotlinStmt {
        match statement {
            KotlinStmt::Block(statements) => {
                KotlinStmt::Block(Self::rewrite_sequence(statements, fields))
            }
            KotlinStmt::Labeled { label, body } => KotlinStmt::Labeled {
                label,
                body: Box::new(Self::rewrite(*body, fields)),
            },
            KotlinStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => KotlinStmt::If {
                condition,
                then_stmt: Box::new(Self::rewrite(*then_stmt, fields)),
                else_stmt: else_stmt.map(|node| Box::new(Self::rewrite(*node, fields))),
            },
            KotlinStmt::While {
                label,
                condition,
                body,
            } => KotlinStmt::While {
                label,
                condition,
                body: Box::new(Self::rewrite(*body, fields)),
            },
            KotlinStmt::DoWhile {
                label,
                body,
                condition,
            } => KotlinStmt::DoWhile {
                label,
                body: Box::new(Self::rewrite(*body, fields)),
                condition,
            },
            KotlinStmt::For {
                label,
                init,
                condition,
                update,
                body,
            } => KotlinStmt::For {
                label,
                init: Self::rewrite_sequence(init, fields),
                condition,
                update,
                body: Box::new(Self::rewrite(*body, fields)),
            },
            statement => statement,
        }
    }

    /// Drops the check that follows a `lateinit` read and types the value it
    /// guarded as what the property declares.
    fn rewrite_sequence(
        statements: Vec<KotlinStmt>,
        fields: &BTreeSet<KotlinIdentifier>,
    ) -> Vec<KotlinStmt> {
        let mut rewritten = Vec::<KotlinStmt>::with_capacity(statements.len());
        for statement in statements {
            let guarded = rewritten
                .last()
                .and_then(|previous| Self::guarded_read(previous, &statement, fields))
                .is_some();
            if guarded {
                if let Some(KotlinStmt::Variable { binding, .. }) = rewritten.last_mut() {
                    binding.nullable = false;
                }
                continue;
            }
            rewritten.push(Self::rewrite(statement, fields));
        }
        rewritten
    }

    /// Whether `check` is the compiler's uninitialized test for `read`.
    fn guarded_read(
        read: &KotlinStmt,
        check: &KotlinStmt,
        fields: &BTreeSet<KotlinIdentifier>,
    ) -> Option<()> {
        let KotlinStmt::Variable { name, value, .. } = read else {
            return None;
        };
        Self::reads_lateinit_field(value.as_ref()?, fields)?;
        let KotlinStmt::If {
            condition,
            then_stmt,
            else_stmt: None,
        } = check
        else {
            return None;
        };
        Self::tests_null(condition, name)?;
        // `::property.isInitialized` compiles to the same null test on the same
        // backing field, and a guard the author wrote has to stay. What tells
        // them apart is the throw the compiler leaves behind to satisfy the
        // verifier after its no-return call: `throw null` is not something a
        // Kotlin author writes.
        Self::throws_null(then_stmt)?;
        // The guard exists only to raise, so removing it can leave no path
        // behind that the original did not already have.
        (!Self::completes_normally(then_stmt)).then_some(())
    }

    fn throws_null(statement: &KotlinStmt) -> Option<()> {
        match statement {
            KotlinStmt::Throw(value) => matches!(
                value,
                KotlinExpr::Literal(crate::language::kotlin::KotlinLiteral::Null)
            )
            .then_some(()),
            KotlinStmt::Block(statements) => Self::throws_null(statements.last()?),
            _ => None,
        }
    }

    fn reads_lateinit_field(value: &KotlinExpr, fields: &BTreeSet<KotlinIdentifier>) -> Option<()> {
        let KotlinExpr::Field { owner, name } = value else {
            return None;
        };
        (matches!(owner.as_ref(), KotlinExpr::This) && fields.contains(name)).then_some(())
    }

    fn tests_null(condition: &KotlinExpr, name: &KotlinIdentifier) -> Option<()> {
        let KotlinExpr::Binary { left, op, right } = condition else {
            return None;
        };
        if !matches!(op, KotlinBinaryOp::Equal | KotlinBinaryOp::ReferentialEqual) {
            return None;
        }
        let names = |expression: &KotlinExpr| matches!(expression, KotlinExpr::Name(local) if local == name);
        let is_null = |expression: &KotlinExpr| {
            matches!(
                expression,
                KotlinExpr::Literal(crate::language::kotlin::KotlinLiteral::Null)
            )
        };
        ((names(left) && is_null(right)) || (is_null(left) && names(right))).then_some(())
    }

    fn completes_normally(statement: &KotlinStmt) -> bool {
        match statement {
            KotlinStmt::Return(_)
            | KotlinStmt::Throw(_)
            | KotlinStmt::Break(_)
            | KotlinStmt::Continue(_) => false,
            KotlinStmt::Block(statements) => statements.iter().all(Self::completes_normally),
            KotlinStmt::Labeled { body, .. } => Self::completes_normally(body),
            KotlinStmt::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                Self::completes_normally(then_stmt)
                    || else_stmt.as_deref().is_none_or(Self::completes_normally)
            }
            _ => true,
        }
    }
}
