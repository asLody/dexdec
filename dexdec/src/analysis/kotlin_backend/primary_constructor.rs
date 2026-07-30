//! Promotion of a constructor that only assigns properties into the class header.
//!
//! Kotlin declares a class's properties in its primary constructor. Bytecode has
//! no such thing: it holds fields, and a constructor that copies its arguments
//! into them one by one. Read back literally that is three declarations of the
//! same thing — the field, the parameter, and the assignment joining them.
//!
//! A constructor doing only that says exactly what a primary constructor says,
//! so it can be written as one. A constructor doing anything else is left alone:
//! the rest of it would need somewhere to go, and there is no reason to guess.

use std::collections::{BTreeMap, BTreeSet};

use crate::language::kotlin::{
    KotlinConstructorTarget, KotlinExpr, KotlinIdentifier, KotlinMethodDeclarationKind,
    KotlinPrimaryParameter, KotlinStmt, KotlinTypeDeclaration, KotlinTypeDeclarationKind,
};

pub(super) struct KotlinPrimaryConstructor;

impl KotlinPrimaryConstructor {
    pub(super) fn apply(declaration: &mut KotlinTypeDeclaration) {
        Self::promote(declaration);
        for nested in &mut declaration.nested {
            Self::apply(nested);
        }
    }

    fn promote(declaration: &mut KotlinTypeDeclaration) {
        if declaration.kind != KotlinTypeDeclarationKind::Class {
            return;
        }
        let mut constructors = declaration
            .methods
            .iter()
            .enumerate()
            .filter(|(_, method)| method.kind == KotlinMethodDeclarationKind::Constructor);
        let Some((index, constructor)) = constructors.next() else {
            return;
        };
        // A secondary constructor has to delegate to the primary one, and this
        // pass has no way to write that delegation.
        if constructors.next().is_some() {
            return;
        }
        let Some((parameters, supertype_arguments)) =
            Self::promoted_header(declaration, constructor)
        else {
            return;
        };
        let promoted = parameters
            .iter()
            .filter_map(|parameter| match parameter {
                KotlinPrimaryParameter::Property(property) => Some(property.name.clone()),
                KotlinPrimaryParameter::Value(_) => None,
            })
            .collect::<BTreeSet<_>>();
        declaration
            .fields
            .retain(|field| !promoted.contains(&field.name));
        declaration.methods.remove(index);
        declaration.primary_parameters = parameters;
        declaration.superclass_arguments = supertype_arguments;
    }

    /// What a constructor would look like written into the class header.
    ///
    /// Returns nothing unless the constructor does only two things: hand some of
    /// its parameters to the supertype, and assign the rest to fields carrying
    /// their own names. Anything else would have to be left behind somewhere.
    fn promoted_header(
        declaration: &KotlinTypeDeclaration,
        constructor: &crate::language::kotlin::KotlinMethodDeclaration,
    ) -> Option<(Vec<KotlinPrimaryParameter>, Vec<KotlinExpr>)> {
        if constructor.parameters.is_empty() {
            return None;
        }
        let body = constructor.body.as_ref()?;
        let KotlinStmt::Block(statements) = &body.root else {
            return None;
        };
        let mut assigned = BTreeMap::new();
        let mut supertype_arguments = Vec::new();
        for statement in statements {
            match statement {
                KotlinStmt::ConstructorInvocation {
                    target: KotlinConstructorTarget::Super,
                    args,
                } => {
                    // The header can only hand on what it was given, so an
                    // argument that is anything but a parameter stops this.
                    if !args
                        .iter()
                        .all(|argument| matches!(argument, KotlinExpr::Name(_)))
                    {
                        return None;
                    }
                    supertype_arguments = args.clone();
                }
                KotlinStmt::Assign {
                    target,
                    op: crate::language::kotlin::KotlinAssignOp::Assign,
                    value,
                } => {
                    let (field, parameter) = Self::property_assignment(target, value)?;
                    // A field named differently from its parameter, or two
                    // assignments from one parameter, cannot become one
                    // declaration.
                    if field != parameter || assigned.insert(parameter, field).is_some() {
                        return None;
                    }
                }
                _ => return None,
            }
        }
        let handed_on = supertype_arguments
            .iter()
            .filter_map(|argument| match argument {
                KotlinExpr::Name(name) => Some(name.clone()),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let mut parameters = Vec::with_capacity(constructor.parameters.len());
        for parameter in &constructor.parameters {
            match assigned.get(&parameter.name) {
                Some(field) => {
                    let declared = declaration
                        .fields
                        .iter()
                        .find(|entry| entry.name == *field)?;
                    if declared.initializer.is_some()
                        && declared.initializer != parameter.default_value
                    {
                        return None;
                    }
                    let mut declared = declared.clone();
                    declared.initializer = parameter.default_value.clone();
                    parameters.push(KotlinPrimaryParameter::Property(declared));
                }
                // A parameter the constructor only handed to its supertype stays
                // a parameter; one it did nothing with has nowhere to go.
                None if handed_on.contains(&parameter.name) => {
                    parameters.push(KotlinPrimaryParameter::Value(parameter.clone()));
                }
                None => return None,
            }
        }
        Some((parameters, supertype_arguments))
    }

    /// The field and parameter a `this.field = parameter` statement joins.
    fn property_assignment(
        target: &KotlinExpr,
        value: &KotlinExpr,
    ) -> Option<(KotlinIdentifier, KotlinIdentifier)> {
        let KotlinExpr::Field { owner, name } = target else {
            return None;
        };
        if !matches!(owner.as_ref(), KotlinExpr::This) {
            return None;
        }
        let KotlinExpr::Name(parameter) = value else {
            return None;
        };
        Some((name.clone(), parameter.clone()))
    }
}
