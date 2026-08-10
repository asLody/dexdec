use std::collections::{BTreeMap, BTreeSet};

use crate::language::java::{
    JavaAssignOp, JavaAstRewriter, JavaBinaryOp, JavaConstructorTarget, JavaExpr,
    JavaFieldDeclaration, JavaIdentifier, JavaLiteral, JavaMethodBody, JavaMethodDeclaration,
    JavaMethodDeclarationKind, JavaMethodParameter, JavaModifier, JavaStmt, JavaType,
    JavaTypeArgument, JavaTypeDeclaration, JavaTypeDeclarationKind, JavaTypeParameter, JavaUnaryOp,
};

/// Removes constructor syntax that Java inserts implicitly.
pub(super) struct ConstructorSyntaxRecovery;

pub(super) type ConstructorMethodReturnTypes =
    BTreeMap<(JavaType, JavaIdentifier, usize), Option<JavaType>>;

struct ConstructorCarrierArguments {
    types: Vec<Option<JavaType>>,
    poly_expressions: BTreeSet<usize>,
}

impl ConstructorSyntaxRecovery {
    pub(super) fn apply(declaration: &mut JavaTypeDeclaration) {
        Self::apply_with_method_returns(declaration, &BTreeMap::new());
    }

    pub(super) fn apply_with_method_returns(
        declaration: &mut JavaTypeDeclaration,
        method_return_types: &ConstructorMethodReturnTypes,
    ) {
        let generated_null_guards =
            Self::flatten_generated_null_guarded_constructor_invocations(declaration);
        Self::extract_pre_super_field_values(declaration);
        Self::extract_shared_boxing_bindings(declaration);
        Self::extract_mutable_constructor_arguments(declaration);
        Self::extract_post_super_bindings(declaration);
        Self::extract_super_argument_preludes(declaration, method_return_types);
        let is_enum = declaration.kind == JavaTypeDeclarationKind::Enum;
        let directly_extends_object = declaration.extends.is_none();
        let final_fields = declaration
            .fields
            .iter()
            .filter(|field| {
                field
                    .modifiers
                    .contains(&crate::language::java::JavaModifier::Final)
            })
            .map(|field| field.name.clone())
            .collect::<BTreeSet<_>>();
        for constructor in declaration
            .methods
            .iter_mut()
            .filter(|method| method.kind == JavaMethodDeclarationKind::Constructor)
        {
            let preserve_delayed_object_guard = directly_extends_object
                && generated_null_guards.contains(&Self::constructor_signature(constructor));
            let Some(body) = constructor.body.as_mut() else {
                continue;
            };
            let JavaStmt::Block(statements) = &mut body.root else {
                continue;
            };
            let parameters = constructor
                .parameters
                .iter()
                .map(|parameter| parameter.name.clone())
                .collect::<BTreeSet<_>>();
            let guards = ConstructorParameterGuards::take(statements, &parameters);
            ConstructorCapturePrelude::schedule(statements, &parameters, &final_fields);
            Self::schedule_arguments(statements);
            ConstructorParameterGuards::restore(statements, guards);
            Self::remove_zero_mask_constructor_guards(statements, &parameters);
            if is_enum {
                // Java enum constructors invoke java.lang.Enum implicitly and
                // reject an explicit super(name, ordinal) invocation.
                statements.retain(|statement| {
                    !matches!(
                        statement,
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::Super,
                            ..
                        }
                    )
                });
            }
            // Keep only a generated null guard's delayed Object invocation
            // visible to the carrier recovery below.
            Self::remove_implicit_super(
                statements,
                directly_extends_object && !preserve_delayed_object_guard,
            );
        }
        // Leave simple bindings to the normal scheduling passes above. Only
        // synthesize a factory for control flow that still cannot legally be
        // placed before a Java constructor invocation.
        Self::extract_complex_constructor_bindings(declaration);
        // Preserve every remaining statically movable prelude together with
        // its final arguments in one typed, single-evaluation value.
        Self::extract_remaining_constructor_preludes(declaration, method_return_types);
        if directly_extends_object {
            for constructor in declaration
                .methods
                .iter_mut()
                .filter(|method| method.kind == JavaMethodDeclarationKind::Constructor)
            {
                let Some(body) = constructor.body.as_mut() else {
                    continue;
                };
                let JavaStmt::Block(statements) = &mut body.root else {
                    continue;
                };
                Self::remove_implicit_super(statements, true);
            }
        }
    }

    fn flatten_generated_null_guarded_constructor_invocations(
        declaration: &mut JavaTypeDeclaration,
    ) -> BTreeSet<Vec<JavaType>> {
        let mut flattened_signatures = BTreeSet::new();
        for constructor in declaration
            .methods
            .iter_mut()
            .filter(|method| method.kind == JavaMethodDeclarationKind::Constructor)
        {
            let signature = Self::constructor_signature(constructor);
            let parameters = constructor
                .parameters
                .iter()
                .map(|parameter| parameter.name.clone())
                .collect::<BTreeSet<_>>();
            let Some(body) = constructor.body.as_mut() else {
                continue;
            };
            let JavaStmt::Block(statements) = &mut body.root else {
                continue;
            };
            let Some((mut guards, invocation, trailing, _)) =
                Self::flatten_generated_null_guard_statements(statements, &parameters)
            else {
                continue;
            };
            if guards.is_empty() {
                continue;
            }
            guards.push(invocation);
            guards.extend(trailing);
            *statements = guards;
            flattened_signatures.insert(signature);
        }
        flattened_signatures
    }

    fn flatten_generated_null_guard_statements(
        statements: &[JavaStmt],
        parameters: &BTreeSet<JavaIdentifier>,
    ) -> Option<(Vec<JavaStmt>, JavaStmt, Vec<JavaStmt>, bool)> {
        if let [invocation @ JavaStmt::ConstructorInvocation { .. }, trailing @ ..] = statements {
            let mut trailing = trailing.to_vec();
            let terminates = matches!(trailing.last(), Some(JavaStmt::Return(None)));
            if terminates {
                trailing.pop();
            }
            return Some((Vec::new(), invocation.clone(), trailing, terminates));
        }

        let guarded = match statements {
            [JavaStmt::If {
                condition,
                then_stmt,
                else_stmt: Some(failure),
            }] => Some((condition, then_stmt.as_ref(), failure.as_ref(), false)),
            [JavaStmt::If {
                condition,
                then_stmt,
                else_stmt: None,
            }, failure] => Some((condition, then_stmt.as_ref(), failure, true)),
            _ => None,
        };
        let Some((condition, JavaStmt::Block(then_statements), failure, requires_termination)) =
            guarded
        else {
            return None;
        };
        let guard_condition = Self::generated_non_null_guard(condition, parameters)?;
        if !Self::generated_null_guard_failure(failure) {
            return None;
        }
        let (nested_guards, invocation, trailing, terminates) =
            Self::flatten_generated_null_guard_statements(then_statements, parameters)?;
        if requires_termination && !terminates {
            return None;
        }

        let mut guards = Vec::with_capacity(1 + nested_guards.len());
        guards.push(JavaStmt::If {
            condition: guard_condition,
            then_stmt: Box::new(failure.clone()),
            else_stmt: None,
        });
        guards.extend(nested_guards);
        Some((guards, invocation, trailing, terminates))
    }

    fn generated_non_null_guard(
        condition: &JavaExpr,
        parameters: &BTreeSet<JavaIdentifier>,
    ) -> Option<JavaExpr> {
        let JavaExpr::Binary {
            left,
            op: JavaBinaryOp::NotEqual,
            right,
        } = condition
        else {
            return None;
        };
        let parameter_and_null = |parameter: &JavaExpr, null: &JavaExpr| {
            matches!(parameter, JavaExpr::Name(name) if parameters.contains(name))
                && matches!(null, JavaExpr::Literal(JavaLiteral::Null))
        };
        if !parameter_and_null(left, right) && !parameter_and_null(right, left) {
            return None;
        }
        Some(JavaExpr::Binary {
            left: left.clone(),
            op: JavaBinaryOp::Equal,
            right: right.clone(),
        })
    }

    fn generated_null_guard_failure(statement: &JavaStmt) -> bool {
        match statement {
            JavaStmt::Block(statements) => {
                matches!(statements.as_slice(), [statement] if Self::generated_null_guard_failure(statement))
            }
            JavaStmt::Expression(JavaExpr::Call {
                receiver: None,
                owner: Some(JavaType::Class(owner)),
                method,
                args,
                ..
            }) => {
                let intrinsics_throw_npe = method.as_str() == "throwNpe"
                    && args.is_empty()
                    && owner
                        .name()
                        .components()
                        .last()
                        .is_some_and(|component| component.as_str() == "Intrinsics");
                let generated_report_null = method.as_str() == "$$$reportNull$$$0"
                    && matches!(
                        args.as_slice(),
                        [JavaExpr::Literal(JavaLiteral::Integer(_))]
                    );
                intrinsics_throw_npe || generated_report_null
            }
            _ => false,
        }
    }

    fn extract_pre_super_field_values(declaration: &mut JavaTypeDeclaration) {
        if declaration.kind != JavaTypeDeclarationKind::Class || declaration.extends.is_none() {
            return;
        }
        let field_types = declaration
            .fields
            .iter()
            .map(|field| (field.name.clone(), field.ty.clone()))
            .collect::<BTreeMap<_, _>>();
        let class_type_parameters = declaration.type_parameters.clone();
        let mut method_names = declaration
            .methods
            .iter()
            .filter_map(|method| method.name.clone())
            .collect::<BTreeSet<_>>();
        let mut type_names = declaration
            .nested
            .iter()
            .map(|nested| nested.name.clone())
            .chain(std::iter::once(declaration.name.clone()))
            .collect::<BTreeSet<_>>();
        let mut methods = Vec::new();
        let mut nested = Vec::new();

        for constructor in &mut declaration.methods {
            let factory_name =
                Self::claim_method_name(&mut method_names, "computeConstructorFieldValues");
            let carrier_name =
                Self::claim_method_name(&mut type_names, "DexdecConstructorFieldValues");
            let Some((delegation, helper, factory, carrier)) = Self::pre_super_field_value_helper(
                constructor,
                &field_types,
                &class_type_parameters,
                factory_name.clone(),
                carrier_name.clone(),
            ) else {
                method_names.remove(&factory_name);
                type_names.remove(&carrier_name);
                continue;
            };
            constructor.body = Some(delegation);
            methods.push(helper);
            methods.push(factory);
            nested.push(carrier);
        }
        declaration.methods.extend(methods);
        declaration.nested.extend(nested);
    }

    fn pre_super_field_value_helper(
        constructor: &JavaMethodDeclaration,
        field_types: &BTreeMap<JavaIdentifier, JavaType>,
        class_type_parameters: &[JavaTypeParameter],
        factory_name: JavaIdentifier,
        carrier_name: JavaIdentifier,
    ) -> Option<(
        JavaMethodBody,
        JavaMethodDeclaration,
        JavaMethodDeclaration,
        JavaTypeDeclaration,
    )> {
        if constructor.kind != JavaMethodDeclarationKind::Constructor
            || !constructor.type_parameters.is_empty()
            || constructor
                .parameters
                .iter()
                .any(|parameter| parameter.varargs)
        {
            return None;
        }
        let JavaStmt::Block(statements) = &constructor.body.as_ref()?.root else {
            return None;
        };
        let invocation_index = statements.iter().position(|statement| {
            matches!(
                statement,
                JavaStmt::ConstructorInvocation {
                    target: JavaConstructorTarget::Super,
                    ..
                }
            )
        })?;
        let (prelude, invocation_and_trailing) = statements.split_at(invocation_index);
        let [JavaStmt::ConstructorInvocation {
            target: JavaConstructorTarget::Super,
            args: super_arguments,
        }, trailing @ ..] = invocation_and_trailing
        else {
            return None;
        };
        let parameters = constructor
            .parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect::<BTreeSet<_>>();
        let mut local_names = parameters.clone();
        local_names.extend(prelude.iter().filter_map(|statement| match statement {
            JavaStmt::Variable { name, .. } => Some(name.clone()),
            _ => None,
        }));
        let mut factory_prelude = Vec::with_capacity(prelude.len());
        let mut captures = Vec::new();
        let mut factory_scope = parameters.clone();
        let mut requires_factory = false;
        for statement in prelude {
            if let JavaStmt::Assign {
                target: JavaExpr::Field { owner, name: field },
                op: JavaAssignOp::Assign,
                value,
            } = statement
            {
                if matches!(owner.as_ref(), JavaExpr::This)
                    && Self::static_expression(value, &factory_scope)
                {
                    requires_factory |= !Self::passive_constructor_argument(value, &factory_scope);
                    let ty = field_types.get(field)?.clone();
                    let value_name =
                        Self::claim_method_name(&mut local_names, "constructorFieldValue");
                    factory_scope.insert(value_name.clone());
                    factory_prelude.push(JavaStmt::Variable {
                        ty,
                        name: value_name.clone(),
                        value: Some(value.clone()),
                    });
                    captures.push((field.clone(), value_name));
                    continue;
                }
            }
            requires_factory |=
                !ConstructorParameterGuards::is_parameter_guard(statement, &parameters);
            if let JavaStmt::Variable { name, .. } = statement {
                factory_scope.insert(name.clone());
            }
            factory_prelude.push(statement.clone());
        }
        if captures.is_empty() || !requires_factory {
            return None;
        }

        let super_argument_count = super_arguments.len();
        let mut carrier_arguments = super_arguments.clone();
        carrier_arguments.extend(
            captures
                .iter()
                .map(|(_, value)| JavaExpr::Name(value.clone())),
        );
        factory_prelude.push(JavaStmt::ConstructorInvocation {
            target: JavaConstructorTarget::Super,
            args: carrier_arguments,
        });
        let mut prepared = constructor.clone();
        prepared.body = Some(JavaMethodBody {
            root: JavaStmt::Block(factory_prelude),
        });
        let (delegation, mut helper, factory, carrier) =
            Self::remaining_constructor_prelude_helper(
                &prepared,
                &BTreeMap::new(),
                &BTreeMap::new(),
                class_type_parameters,
                factory_name,
                carrier_name,
            )?;

        let JavaStmt::Block(helper_statements) = &mut helper.body.as_mut()?.root else {
            return None;
        };
        let [JavaStmt::ConstructorInvocation {
            target: JavaConstructorTarget::Super,
            args: helper_arguments,
        }] = helper_statements.as_mut_slice()
        else {
            return None;
        };
        let field_values = helper_arguments.split_off(super_argument_count);
        if field_values.len() != captures.len() {
            return None;
        }
        helper_statements.extend(captures.into_iter().zip(field_values).map(
            |((field, _), value)| JavaStmt::Assign {
                target: JavaExpr::Field {
                    owner: Box::new(JavaExpr::This),
                    name: field,
                },
                op: JavaAssignOp::Assign,
                value,
            },
        ));
        helper_statements.extend_from_slice(trailing);
        Some((delegation, helper, factory, carrier))
    }

    fn remove_zero_mask_constructor_guards(
        statements: &mut Vec<JavaStmt>,
        parameters: &BTreeSet<JavaIdentifier>,
    ) {
        let Some(mut invocation) = statements
            .iter()
            .position(|statement| matches!(statement, JavaStmt::ConstructorInvocation { .. }))
        else {
            return;
        };
        let mut index = 0;
        while index < invocation {
            if Self::is_zero_mask_constructor_guard(&statements[index], parameters) {
                statements.remove(index);
                invocation -= 1;
            } else {
                index += 1;
            }
        }
    }

    fn is_zero_mask_constructor_guard(
        statement: &JavaStmt,
        parameters: &BTreeSet<JavaIdentifier>,
    ) -> bool {
        let JavaStmt::If {
            condition:
                JavaExpr::Binary {
                    left,
                    op: JavaBinaryOp::NotEqual,
                    right,
                },
            else_stmt: None,
            ..
        } = statement
        else {
            return false;
        };
        let is_zero = |expression: &JavaExpr| {
            matches!(expression, JavaExpr::Literal(JavaLiteral::Integer(0)))
        };
        let is_parameter_zero_mask = |expression: &JavaExpr| {
            matches!(
                expression,
                JavaExpr::Binary {
                    left,
                    op: JavaBinaryOp::BitAnd,
                    right,
                } if (is_zero(left)
                    && matches!(right.as_ref(), JavaExpr::Name(name) if parameters.contains(name)))
                    || (is_zero(right)
                        && matches!(left.as_ref(), JavaExpr::Name(name) if parameters.contains(name)))
            )
        };
        (is_parameter_zero_mask(left) && is_zero(right))
            || (is_parameter_zero_mask(right) && is_zero(left))
    }

    fn extract_shared_boxing_bindings(declaration: &mut JavaTypeDeclaration) {
        if declaration.kind != JavaTypeDeclarationKind::Class {
            return;
        }
        let mut signatures = declaration
            .methods
            .iter()
            .filter(|method| method.kind == JavaMethodDeclarationKind::Constructor)
            .map(Self::constructor_signature)
            .collect::<Vec<_>>();
        let mut helpers = Vec::new();

        for constructor in &mut declaration.methods {
            let Some((signature, delegation, helper)) = Self::shared_boxing_helper(constructor)
            else {
                continue;
            };
            if signatures
                .iter()
                .any(|existing| Self::signatures_may_collide(existing, &signature))
            {
                continue;
            }
            signatures.push(signature);
            // Java forbids the binding before super/this. Evaluate it once as
            // an argument to a generated overload, then reuse that parameter
            // in the original invocation without changing object identity.
            constructor.body = Some(delegation);
            helpers.push(helper);
        }
        declaration.methods.extend(helpers);
    }

    fn extract_mutable_constructor_arguments(declaration: &mut JavaTypeDeclaration) {
        if declaration.kind != JavaTypeDeclarationKind::Class {
            return;
        }
        let mut signatures = declaration
            .methods
            .iter()
            .filter(|method| method.kind == JavaMethodDeclarationKind::Constructor)
            .map(Self::constructor_signature)
            .collect::<Vec<_>>();
        let mut method_names = declaration
            .methods
            .iter()
            .filter_map(|method| method.name.clone())
            .collect::<BTreeSet<_>>();
        let mut generated = Vec::new();

        for constructor in &mut declaration.methods {
            let helper_name =
                Self::claim_method_name(&mut method_names, "initializeConstructorArgument");
            let Some((signature, delegation, helper, factory)) =
                Self::mutable_constructor_helper(constructor, helper_name.clone())
            else {
                method_names.remove(&helper_name);
                continue;
            };
            if signatures
                .iter()
                .any(|existing| Self::signatures_may_collide(existing, &signature))
            {
                method_names.remove(&helper_name);
                continue;
            }
            signatures.push(signature);
            // The factory is evaluated before the helper constructor starts,
            // preserving the complete DEX prelude before its super invocation.
            constructor.body = Some(delegation);
            generated.push(helper);
            generated.push(factory);
        }
        declaration.methods.extend(generated);
    }

    fn extract_super_argument_preludes(
        declaration: &mut JavaTypeDeclaration,
        method_return_types: &ConstructorMethodReturnTypes,
    ) {
        if declaration.kind != JavaTypeDeclarationKind::Class {
            return;
        }
        let mut method_names = declaration
            .methods
            .iter()
            .filter_map(|method| method.name.clone())
            .collect::<BTreeSet<_>>();
        let class_type_parameters = declaration.type_parameters.clone();
        let mut factories = Vec::new();

        for constructor in &mut declaration.methods {
            let factory_name =
                Self::claim_method_name(&mut method_names, "evaluateConstructorArgument");
            let recovered = Self::super_argument_prelude_factory(
                constructor,
                &class_type_parameters,
                factory_name.clone(),
                method_return_types,
            )
            .or_else(|| {
                Self::prepared_super_argument_factory(
                    constructor,
                    &class_type_parameters,
                    factory_name.clone(),
                )
            });
            let Some((body, factory)) = recovered else {
                method_names.remove(&factory_name);
                continue;
            };
            constructor.body = Some(body);
            factories.push(factory);
        }
        declaration.methods.extend(factories);
    }

    fn extract_complex_constructor_bindings(declaration: &mut JavaTypeDeclaration) {
        if declaration.kind != JavaTypeDeclarationKind::Class {
            return;
        }
        let mut signatures = declaration
            .methods
            .iter()
            .filter(|method| method.kind == JavaMethodDeclarationKind::Constructor)
            .map(Self::constructor_signature)
            .collect::<Vec<_>>();
        let mut method_names = declaration
            .methods
            .iter()
            .filter_map(|method| method.name.clone())
            .collect::<BTreeSet<_>>();
        let class_type_parameters = declaration.type_parameters.clone();
        let mut generated = Vec::new();

        for constructor in &mut declaration.methods {
            let factory_name =
                Self::claim_method_name(&mut method_names, "computeConstructorBinding");
            let Some((signature, delegation, helper, factory)) =
                Self::complex_constructor_binding_helper(
                    constructor,
                    &class_type_parameters,
                    factory_name.clone(),
                )
            else {
                method_names.remove(&factory_name);
                continue;
            };
            if signatures
                .iter()
                .any(|existing| Self::signatures_may_collide(existing, &signature))
            {
                method_names.remove(&factory_name);
                continue;
            }
            signatures.push(signature);
            constructor.body = Some(delegation);
            generated.push(helper);
            generated.push(factory);
        }
        declaration.methods.extend(generated);
    }

    fn complex_constructor_binding_helper(
        constructor: &JavaMethodDeclaration,
        class_type_parameters: &[JavaTypeParameter],
        factory_name: JavaIdentifier,
    ) -> Option<(
        Vec<JavaType>,
        JavaMethodBody,
        JavaMethodDeclaration,
        JavaMethodDeclaration,
    )> {
        if constructor.kind != JavaMethodDeclarationKind::Constructor
            || !constructor.type_parameters.is_empty()
            || constructor
                .parameters
                .iter()
                .any(|parameter| parameter.varargs)
        {
            return None;
        }
        let JavaStmt::Block(statements) = &constructor.body.as_ref()?.root else {
            return None;
        };
        let [prelude @ .., invocation @ JavaStmt::ConstructorInvocation {
            target: JavaConstructorTarget::This,
            args,
        }] = statements.as_slice()
        else {
            return None;
        };
        if !prelude
            .iter()
            .any(|statement| matches!(statement, JavaStmt::If { .. }))
        {
            return None;
        }
        let uses = ImmediateExpressionUses::collect_expressions(args);
        let candidates = prelude
            .iter()
            .filter_map(|statement| match statement {
                JavaStmt::Variable { ty, name, value } if uses.contains_key(name) => {
                    Some((ty, name, value.as_ref()))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        let [(ty, name, Some(_))] = candidates.as_slice() else {
            return None;
        };
        let parameters = constructor
            .parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect::<BTreeSet<_>>();
        if !Self::static_statements(prelude, &parameters)
            || !Self::static_factory_types_in_scope(constructor, ty, class_type_parameters)
            || Self::parameter_slots(constructor.parameters.iter().map(|parameter| &parameter.ty))
                + Self::type_slots(ty)
                > 254
        {
            return None;
        }

        let mut helper_parameters = constructor.parameters.clone();
        helper_parameters.push(JavaMethodParameter {
            annotations: Vec::new(),
            ty: (*ty).clone(),
            name: (*name).clone(),
            varargs: false,
        });
        let signature = helper_parameters
            .iter()
            .map(|parameter| parameter.ty.clone().into_raw())
            .collect::<Vec<_>>();
        let mut delegation_args = constructor
            .parameters
            .iter()
            .map(|parameter| JavaExpr::Name(parameter.name.clone()))
            .collect::<Vec<_>>();
        delegation_args.push(JavaExpr::Call {
            receiver: None,
            owner: None,
            type_arguments: Vec::new(),
            method: factory_name.clone(),
            args: constructor
                .parameters
                .iter()
                .map(|parameter| JavaExpr::Name(parameter.name.clone()))
                .collect(),
        });
        let delegation = JavaMethodBody {
            root: JavaStmt::Block(vec![JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::This,
                args: delegation_args,
            }]),
        };
        let helper = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Private],
            compiler_generated: true,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: constructor.name.clone(),
            parameters: helper_parameters,
            throws: constructor.throws.clone(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![invocation.clone()]),
            }),
        };
        let mut factory_statements = prelude.to_vec();
        factory_statements.push(JavaStmt::Return(Some(JavaExpr::Name((*name).clone()))));
        let factory = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Private, JavaModifier::Static],
            compiler_generated: true,
            kind: JavaMethodDeclarationKind::Method,
            type_parameters: class_type_parameters.to_vec(),
            return_type: Some((*ty).clone()),
            name: Some(factory_name),
            parameters: constructor.parameters.clone(),
            throws: constructor.throws.clone(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(factory_statements),
            }),
        };
        Some((signature, delegation, helper, factory))
    }

    fn extract_remaining_constructor_preludes(
        declaration: &mut JavaTypeDeclaration,
        method_return_types: &ConstructorMethodReturnTypes,
    ) {
        if declaration.kind != JavaTypeDeclarationKind::Class {
            return;
        }
        let class_type_parameters = declaration.type_parameters.clone();
        let target_types = Self::constructor_parameter_types(declaration);
        let mut method_names = declaration
            .methods
            .iter()
            .filter_map(|method| method.name.clone())
            .collect::<BTreeSet<_>>();
        let mut type_names = declaration
            .nested
            .iter()
            .map(|nested| nested.name.clone())
            .chain(std::iter::once(declaration.name.clone()))
            .collect::<BTreeSet<_>>();
        let mut methods = Vec::new();
        let mut nested = Vec::new();

        for constructor in &mut declaration.methods {
            let factory_name =
                Self::claim_method_name(&mut method_names, "computeConstructorArguments");
            let carrier_name =
                Self::claim_method_name(&mut type_names, "DexdecConstructorArguments");
            let recovered = Self::remaining_constructor_prelude_helper(
                constructor,
                &target_types,
                method_return_types,
                &class_type_parameters,
                factory_name.clone(),
                carrier_name.clone(),
            )
            .or_else(|| {
                Self::remaining_synchronized_constructor_prelude_helper(
                    constructor,
                    &target_types,
                    method_return_types,
                    &class_type_parameters,
                    factory_name.clone(),
                    carrier_name.clone(),
                )
            })
            .or_else(|| {
                Self::remaining_constructor_prelude_with_trailing_helper(
                    constructor,
                    &target_types,
                    method_return_types,
                    &class_type_parameters,
                    factory_name.clone(),
                    carrier_name.clone(),
                )
            });
            let Some((delegation, helper, factory, carrier)) = recovered else {
                method_names.remove(&factory_name);
                type_names.remove(&carrier_name);
                continue;
            };
            constructor.body = Some(delegation);
            methods.push(helper);
            methods.push(factory);
            nested.push(carrier);
        }
        declaration.methods.extend(methods);
        declaration.nested.extend(nested);
    }

    fn constructor_parameter_types(
        declaration: &JavaTypeDeclaration,
    ) -> BTreeMap<usize, Option<Vec<Vec<JavaType>>>> {
        let mut types = BTreeMap::new();
        for constructor in declaration
            .methods
            .iter()
            .filter(|method| method.kind == JavaMethodDeclarationKind::Constructor)
        {
            let parameters = constructor.type_parameters.is_empty().then(|| {
                constructor
                    .parameters
                    .iter()
                    .map(|parameter| parameter.ty.clone())
                    .collect::<Vec<_>>()
            });
            let entry = types
                .entry(constructor.parameters.len())
                .or_insert_with(|| Some(Vec::new()));
            match (entry.as_mut(), parameters) {
                (Some(signatures), Some(parameters)) => signatures.push(parameters),
                _ => *entry = None,
            }
        }
        types
    }

    fn remaining_constructor_prelude_helper(
        constructor: &JavaMethodDeclaration,
        target_types: &BTreeMap<usize, Option<Vec<Vec<JavaType>>>>,
        method_return_types: &ConstructorMethodReturnTypes,
        class_type_parameters: &[JavaTypeParameter],
        factory_name: JavaIdentifier,
        carrier_name: JavaIdentifier,
    ) -> Option<(
        JavaMethodBody,
        JavaMethodDeclaration,
        JavaMethodDeclaration,
        JavaTypeDeclaration,
    )> {
        if constructor.kind != JavaMethodDeclarationKind::Constructor
            || !constructor.type_parameters.is_empty()
        {
            return None;
        }
        let JavaStmt::Block(statements) = &constructor.body.as_ref()?.root else {
            return None;
        };
        let [prelude @ .., JavaStmt::ConstructorInvocation { target, args }] =
            statements.as_slice()
        else {
            return None;
        };
        let parameters = constructor
            .parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect::<BTreeSet<_>>();
        let carrier_arguments = match target {
            JavaConstructorTarget::This => ConstructorCarrierArguments {
                types: Self::resolve_this_argument_types(
                    constructor,
                    prelude,
                    args,
                    target_types.get(&args.len())?.as_ref()?,
                    method_return_types,
                )?
                .into_iter()
                .map(Some)
                .collect(),
                poly_expressions: BTreeSet::new(),
            },
            JavaConstructorTarget::Super => Self::infer_super_carrier_argument_types(
                constructor,
                prelude,
                args,
                method_return_types,
                true,
            )?,
        };
        let argument_types = carrier_arguments.types;
        let poly_expressions = carrier_arguments.poly_expressions;
        let mut qualified_this_types = QualifiedThisTypes::default();
        for statement in prelude {
            qualified_this_types.rewrite_statement(statement.clone());
        }
        for (argument, ty) in args.iter().zip(&argument_types) {
            if ty.is_some() {
                qualified_this_types.rewrite_expression(argument.clone());
            }
        }
        let mut factory_scope = parameters.clone();
        let qualified_this_captures = qualified_this_types
            .types
            .into_iter()
            .map(|ty| {
                let name = Self::claim_method_name(&mut factory_scope, "outerInstance");
                (ty, name)
            })
            .collect::<Vec<_>>();
        let qualified_this_names = qualified_this_captures
            .iter()
            .cloned()
            .collect::<BTreeMap<_, _>>();
        let mut qualified_this_substitution = QualifiedThisSubstitution {
            names: &qualified_this_names,
        };
        let factory_prelude = prelude
            .iter()
            .cloned()
            .map(|statement| qualified_this_substitution.rewrite_statement(statement))
            .collect::<Vec<_>>();
        let carried_argument_types = argument_types
            .iter()
            .filter_map(Clone::clone)
            .collect::<Vec<_>>();
        if factory_prelude.is_empty()
            || !Self::static_statements(&factory_prelude, &factory_scope)
            || !qualified_this_captures.iter().all(|(ty, _)| {
                Self::static_factory_types_in_scope(constructor, ty, class_type_parameters)
            })
            || !carried_argument_types.iter().all(|ty| {
                Self::static_factory_types_in_scope(constructor, ty, class_type_parameters)
            })
            || Self::parameter_slots(&carried_argument_types) > 254
        {
            return None;
        }

        let mut carrier_type = JavaType::source_class(carrier_name.as_str());
        let JavaType::Class(carrier_class) = &mut carrier_type else {
            unreachable!("a source carrier name always produces a class type")
        };
        carrier_class
            .segments
            .last_mut()
            .expect("a source carrier name has one segment")
            .arguments = class_type_parameters
            .iter()
            .map(|parameter| JavaTypeArgument::Exact(JavaType::Variable(parameter.name.clone())))
            .collect();
        let mut helper_names = constructor
            .parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect::<BTreeSet<_>>();
        let carrier_parameter = Self::claim_method_name(&mut helper_names, "constructorArguments");
        let field_names = argument_types
            .iter()
            .enumerate()
            .map(|(index, ty)| {
                ty.as_ref()
                    .map(|_| JavaIdentifier::from_hint(&format!("argument{index}")))
            })
            .collect::<Vec<_>>();
        let delegation = JavaMethodBody {
            root: JavaStmt::Block(vec![JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::This,
                args: vec![JavaExpr::Call {
                    receiver: None,
                    owner: None,
                    type_arguments: Vec::new(),
                    method: factory_name.clone(),
                    args: qualified_this_captures
                        .iter()
                        .map(|(ty, _)| JavaExpr::QualifiedThis(ty.clone()))
                        .chain(
                            constructor
                                .parameters
                                .iter()
                                .map(|parameter| JavaExpr::Name(parameter.name.clone())),
                        )
                        .collect(),
                }],
            }]),
        };
        let helper = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Private],
            compiler_generated: true,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: constructor.name.clone(),
            parameters: vec![JavaMethodParameter {
                annotations: Vec::new(),
                ty: carrier_type.clone(),
                name: carrier_parameter.clone(),
                varargs: false,
            }],
            throws: constructor.throws.clone(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![JavaStmt::ConstructorInvocation {
                    target: *target,
                    args: args
                        .iter()
                        .enumerate()
                        .zip(&field_names)
                        .map(|((index, argument), field)| match field {
                            Some(field) if poly_expressions.contains(&index) => JavaExpr::Call {
                                receiver: Some(Box::new(JavaExpr::Name(carrier_parameter.clone()))),
                                owner: None,
                                type_arguments: Vec::new(),
                                method: JavaIdentifier::from_dex("castArgument"),
                                args: vec![JavaExpr::Field {
                                    owner: Box::new(JavaExpr::Name(carrier_parameter.clone())),
                                    name: field.clone(),
                                }],
                            },
                            Some(field) => JavaExpr::Field {
                                owner: Box::new(JavaExpr::Name(carrier_parameter.clone())),
                                name: field.clone(),
                            },
                            None => argument.clone(),
                        })
                        .collect(),
                }]),
            }),
        };
        let mut factory_statements = factory_prelude;
        factory_statements.push(JavaStmt::Return(Some(JavaExpr::New {
            enclosing: None,
            ty: carrier_type.clone(),
            target_type: None,
            args: args
                .iter()
                .zip(&field_names)
                .filter_map(|(argument, field)| {
                    field
                        .as_ref()
                        .map(|_| qualified_this_substitution.rewrite_expression(argument.clone()))
                })
                .collect(),
            anonymous_body: None,
        })));
        let factory = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Private, JavaModifier::Static],
            compiler_generated: true,
            kind: JavaMethodDeclarationKind::Method,
            type_parameters: class_type_parameters.to_vec(),
            return_type: Some(carrier_type),
            name: Some(factory_name),
            parameters: qualified_this_captures
                .iter()
                .map(|(ty, name)| JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: ty.clone(),
                    name: name.clone(),
                    varargs: false,
                })
                .chain(constructor.parameters.iter().cloned())
                .collect(),
            throws: constructor.throws.clone(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(factory_statements),
            }),
        };
        let fields = argument_types
            .iter()
            .zip(&field_names)
            .filter_map(|(ty, name)| {
                Some(JavaFieldDeclaration {
                    annotations: Vec::new(),
                    modifiers: vec![JavaModifier::Private, JavaModifier::Final],
                    ty: ty.as_ref()?.clone(),
                    name: name.as_ref()?.clone(),
                    initializer: None,
                })
            })
            .collect::<Vec<_>>();
        let carrier_constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Private],
            compiler_generated: true,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(carrier_name.clone()),
            parameters: argument_types
                .iter()
                .zip(&field_names)
                .filter_map(|(ty, name)| {
                    Some(JavaMethodParameter {
                        annotations: Vec::new(),
                        ty: ty.as_ref()?.clone(),
                        name: name.as_ref()?.clone(),
                        varargs: false,
                    })
                })
                .collect(),
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(
                    field_names
                        .iter()
                        .flatten()
                        .map(|field| JavaStmt::Assign {
                            target: JavaExpr::Field {
                                owner: Box::new(JavaExpr::This),
                                name: field.clone(),
                            },
                            op: JavaAssignOp::Assign,
                            value: JavaExpr::Name(field.clone()),
                        })
                        .collect(),
                ),
            }),
        };
        let mut carrier_methods = vec![carrier_constructor];
        if !poly_expressions.is_empty() {
            let mut type_names = class_type_parameters
                .iter()
                .map(|parameter| parameter.name.clone())
                .collect::<BTreeSet<_>>();
            let cast_type_name = Self::claim_method_name(&mut type_names, "TValue");
            let cast_value = JavaIdentifier::from_dex("value");
            carrier_methods.push(JavaMethodDeclaration {
                annotations: Vec::new(),
                modifiers: vec![JavaModifier::Private],
                // Synthetic-member liveness is scoped to the nested carrier and cannot see
                // the enclosing helper constructor's call to this method.
                compiler_generated: false,
                kind: JavaMethodDeclarationKind::Method,
                type_parameters: vec![JavaTypeParameter {
                    name: cast_type_name.clone(),
                    bounds: Vec::new(),
                }],
                return_type: Some(JavaType::Variable(cast_type_name.clone())),
                name: Some(JavaIdentifier::from_dex("castArgument")),
                parameters: vec![JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: JavaType::source_class("java.lang.Object"),
                    name: cast_value.clone(),
                    varargs: false,
                }],
                throws: Vec::new(),
                body: Some(JavaMethodBody {
                    root: JavaStmt::Block(vec![JavaStmt::Return(Some(JavaExpr::Cast {
                        ty: JavaType::Variable(cast_type_name),
                        value: Box::new(JavaExpr::Name(cast_value)),
                    }))]),
                }),
            });
        }
        let carrier = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![
                JavaModifier::Private,
                JavaModifier::Static,
                JavaModifier::Final,
            ],
            kind: JavaTypeDeclarationKind::Class,
            name: carrier_name,
            type_parameters: class_type_parameters.to_vec(),
            extends: None,
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields,
            methods: carrier_methods,
            nested: Vec::new(),
        };
        Some((delegation, helper, factory, carrier))
    }

    fn remaining_synchronized_constructor_prelude_helper(
        constructor: &JavaMethodDeclaration,
        target_types: &BTreeMap<usize, Option<Vec<Vec<JavaType>>>>,
        method_return_types: &ConstructorMethodReturnTypes,
        class_type_parameters: &[JavaTypeParameter],
        factory_name: JavaIdentifier,
        carrier_name: JavaIdentifier,
    ) -> Option<(
        JavaMethodBody,
        JavaMethodDeclaration,
        JavaMethodDeclaration,
        JavaTypeDeclaration,
    )> {
        let JavaStmt::Block(outer) = &constructor.body.as_ref()?.root else {
            return None;
        };
        let [JavaStmt::Synchronized { lock, body }] = outer.as_slice() else {
            return None;
        };
        let JavaStmt::Block(inner) = body.as_ref() else {
            return None;
        };
        let [prelude @ .., invocation @ JavaStmt::ConstructorInvocation { .. }] = inner.as_slice()
        else {
            return None;
        };
        let parameters = constructor
            .parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect::<BTreeSet<_>>();
        if !Self::static_expression(lock, &parameters) {
            return None;
        }

        let mut prepared = constructor.clone();
        let mut statements = prelude.to_vec();
        statements.push(invocation.clone());
        prepared.body = Some(JavaMethodBody {
            root: JavaStmt::Block(statements),
        });
        let (delegation, helper, mut factory, carrier) =
            Self::remaining_constructor_prelude_helper(
                &prepared,
                target_types,
                method_return_types,
                class_type_parameters,
                factory_name,
                carrier_name,
            )?;
        let factory_body = factory.body.as_mut()?;
        let JavaStmt::Block(_) = &factory_body.root else {
            return None;
        };
        let statements = std::mem::replace(&mut factory_body.root, JavaStmt::Empty);
        factory_body.root = JavaStmt::Block(vec![JavaStmt::Synchronized {
            lock: lock.clone(),
            body: Box::new(statements),
        }]);
        Some((delegation, helper, factory, carrier))
    }

    fn remaining_constructor_prelude_with_trailing_helper(
        constructor: &JavaMethodDeclaration,
        target_types: &BTreeMap<usize, Option<Vec<Vec<JavaType>>>>,
        method_return_types: &ConstructorMethodReturnTypes,
        class_type_parameters: &[JavaTypeParameter],
        factory_name: JavaIdentifier,
        carrier_name: JavaIdentifier,
    ) -> Option<(
        JavaMethodBody,
        JavaMethodDeclaration,
        JavaMethodDeclaration,
        JavaTypeDeclaration,
    )> {
        let JavaStmt::Block(statements) = &constructor.body.as_ref()?.root else {
            return None;
        };
        let invocation_index = statements
            .iter()
            .position(|statement| matches!(statement, JavaStmt::ConstructorInvocation { .. }))?;
        let (prelude, invocation_and_trailing) = statements.split_at(invocation_index);
        let [JavaStmt::ConstructorInvocation {
            target,
            args: constructor_arguments,
        }, trailing @ ..] = invocation_and_trailing
        else {
            return None;
        };
        if trailing.is_empty() {
            return None;
        }
        let trailing_uses = ImmediateExpressionUses::collect_statements(trailing);
        let carried_bindings = constructor
            .parameters
            .iter()
            .filter(|parameter| trailing_uses.contains_key(&parameter.name))
            .map(|parameter| (parameter.ty.clone(), parameter.name.clone()))
            .chain(prelude.iter().filter_map(|statement| match statement {
                JavaStmt::Variable { ty, name, .. } if trailing_uses.contains_key(name) => {
                    Some((ty.clone(), name.clone()))
                }
                _ => None,
            }))
            .collect::<Vec<_>>();
        let constructor_argument_count = constructor_arguments.len();
        let mut carrier_arguments = constructor_arguments.clone();
        carrier_arguments.extend(
            carried_bindings
                .iter()
                .map(|(_, name)| JavaExpr::Name(name.clone())),
        );
        let mut prepared = constructor.clone();
        let mut factory_prelude = prelude.to_vec();
        factory_prelude.push(JavaStmt::ConstructorInvocation {
            target: JavaConstructorTarget::Super,
            args: carrier_arguments,
        });
        prepared.body = Some(JavaMethodBody {
            root: JavaStmt::Block(factory_prelude),
        });
        let (delegation, mut helper, factory, carrier) =
            Self::remaining_constructor_prelude_helper(
                &prepared,
                target_types,
                method_return_types,
                class_type_parameters,
                factory_name,
                carrier_name,
            )?;

        let JavaStmt::Block(helper_statements) = &mut helper.body.as_mut()?.root else {
            return None;
        };
        let [JavaStmt::ConstructorInvocation {
            target: helper_target,
            args: helper_arguments,
        }] = helper_statements.as_mut_slice()
        else {
            return None;
        };
        *helper_target = *target;
        let parameter_values = helper_arguments.split_off(constructor_argument_count);
        if parameter_values.len() != carried_bindings.len() {
            return None;
        }
        helper_statements.extend(carried_bindings.into_iter().zip(parameter_values).map(
            |((ty, name), value)| JavaStmt::Variable {
                ty,
                name,
                value: Some(value),
            },
        ));
        helper_statements.extend_from_slice(trailing);
        Some((delegation, helper, factory, carrier))
    }

    fn infer_super_argument_types(
        constructor: &JavaMethodDeclaration,
        prelude: &[JavaStmt],
        arguments: &[JavaExpr],
        method_return_types: &ConstructorMethodReturnTypes,
    ) -> Option<Vec<JavaType>> {
        Self::infer_super_carrier_argument_types(
            constructor,
            prelude,
            arguments,
            method_return_types,
            false,
        )?
        .types
        .into_iter()
        .collect()
    }

    fn infer_super_carrier_argument_types(
        constructor: &JavaMethodDeclaration,
        prelude: &[JavaStmt],
        arguments: &[JavaExpr],
        method_return_types: &ConstructorMethodReturnTypes,
        allow_poly_expressions: bool,
    ) -> Option<ConstructorCarrierArguments> {
        let mut values = constructor
            .parameters
            .iter()
            .map(|parameter| (parameter.name.clone(), parameter.ty.clone()))
            .collect::<BTreeMap<_, _>>();
        for statement in prelude {
            if let JavaStmt::Variable { ty, name, .. } = statement {
                values.insert(name.clone(), ty.clone());
            }
        }
        let default_mask_range = Self::kotlin_default_constructor_mask_range(arguments, &values);
        let mut poly_expressions = BTreeSet::new();
        let types = arguments
            .iter()
            .enumerate()
            .map(|(index, argument)| {
                Self::infer_constructor_argument_type_with_returns(
                    constructor,
                    prelude,
                    argument,
                    &values,
                    method_return_types,
                )
                .or_else(|| {
                    default_mask_range
                        .as_ref()
                        .is_some_and(|range| range.contains(&index))
                        .then(JavaType::int)
                })
                .map(Some)
                .or_else(|| Self::uncarried_super_argument(argument).then_some(None))
                .or_else(|| {
                    (allow_poly_expressions
                        && Self::poly_reference_constructor_argument(
                            constructor,
                            prelude,
                            argument,
                            &values,
                            method_return_types,
                        ))
                    .then(|| {
                        poly_expressions.insert(index);
                        Some(JavaType::source_class("java.lang.Object"))
                    })
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some(ConstructorCarrierArguments {
            types,
            poly_expressions,
        })
    }

    fn poly_reference_constructor_argument(
        constructor: &JavaMethodDeclaration,
        prelude: &[JavaStmt],
        expression: &JavaExpr,
        values: &BTreeMap<JavaIdentifier, JavaType>,
        method_return_types: &ConstructorMethodReturnTypes,
    ) -> bool {
        let JavaExpr::Conditional {
            when_true,
            when_false,
            ..
        } = expression
        else {
            return false;
        };
        let Some(true_type) = Self::infer_constructor_argument_type_with_returns(
            constructor,
            prelude,
            when_true,
            values,
            method_return_types,
        ) else {
            return false;
        };
        let Some(false_type) = Self::infer_constructor_argument_type_with_returns(
            constructor,
            prelude,
            when_false,
            values,
            method_return_types,
        ) else {
            return false;
        };
        true_type != false_type
            && Self::reference_constructor_type(&true_type)
            && Self::reference_constructor_type(&false_type)
    }

    fn reference_constructor_type(ty: &JavaType) -> bool {
        matches!(
            ty,
            JavaType::Class(_) | JavaType::Array(_) | JavaType::Variable(_)
        )
    }

    fn infer_constructor_argument_type_with_returns(
        constructor: &JavaMethodDeclaration,
        prelude: &[JavaStmt],
        expression: &JavaExpr,
        values: &BTreeMap<JavaIdentifier, JavaType>,
        method_return_types: &ConstructorMethodReturnTypes,
    ) -> Option<JavaType> {
        Self::infer_constructor_argument_type(expression, values)
            .or_else(|| {
                Self::method_call_return_type(constructor, prelude, expression, method_return_types)
            })
            .or_else(|| {
                let JavaExpr::Conditional {
                    when_true,
                    when_false,
                    ..
                } = expression
                else {
                    return None;
                };
                let true_type = Self::infer_constructor_argument_type_with_returns(
                    constructor,
                    prelude,
                    when_true,
                    values,
                    method_return_types,
                );
                let false_type = Self::infer_constructor_argument_type_with_returns(
                    constructor,
                    prelude,
                    when_false,
                    values,
                    method_return_types,
                );
                match (true_type, false_type) {
                    (Some(left), Some(right)) if left == right => Some(left),
                    (Some(left), Some(right))
                        if Self::is_string_type(&left) && Self::is_string_type(&right) =>
                    {
                        Some(left)
                    }
                    (Some(ty), Some(_))
                        if Self::string_literal(when_false) && Self::is_string_type(&ty) =>
                    {
                        Some(ty)
                    }
                    (Some(_), Some(ty))
                        if Self::string_literal(when_true) && Self::is_string_type(&ty) =>
                    {
                        Some(ty)
                    }
                    (Some(ty), None)
                        if Self::contextual_integer_literal(when_false)
                            && Self::numeric_constructor_type(&ty) =>
                    {
                        Some(ty)
                    }
                    (None, Some(ty))
                        if Self::contextual_integer_literal(when_true)
                            && Self::numeric_constructor_type(&ty) =>
                    {
                        Some(ty)
                    }
                    (Some(ty), None)
                        if matches!(when_false.as_ref(), JavaExpr::Literal(JavaLiteral::Null)) =>
                    {
                        Some(ty)
                    }
                    (None, Some(ty))
                        if matches!(when_true.as_ref(), JavaExpr::Literal(JavaLiteral::Null)) =>
                    {
                        Some(ty)
                    }
                    _ => None,
                }
            })
    }

    fn string_literal(expression: &JavaExpr) -> bool {
        matches!(expression, JavaExpr::Literal(JavaLiteral::String(_)))
    }

    fn contextual_integer_literal(expression: &JavaExpr) -> bool {
        match expression {
            JavaExpr::Literal(JavaLiteral::Integer(value)) => (-32768..=65535).contains(value),
            JavaExpr::Unary {
                op: JavaUnaryOp::Negate | JavaUnaryOp::BitwiseNot,
                operand,
            } => Self::contextual_integer_literal(operand),
            _ => false,
        }
    }

    fn numeric_constructor_type(ty: &JavaType) -> bool {
        matches!(
            ty,
            JavaType::Primitive(
                crate::language::java::JavaPrimitiveType::Byte
                    | crate::language::java::JavaPrimitiveType::Short
                    | crate::language::java::JavaPrimitiveType::Char
                    | crate::language::java::JavaPrimitiveType::Int
                    | crate::language::java::JavaPrimitiveType::Long
                    | crate::language::java::JavaPrimitiveType::Float
                    | crate::language::java::JavaPrimitiveType::Double
            )
        )
    }

    fn is_string_type(ty: &JavaType) -> bool {
        matches!(
            ty,
            JavaType::Class(class)
                if class
                    .segments
                    .last()
                    .is_some_and(|segment| segment.name.as_str() == "String")
        )
    }

    fn uncarried_super_argument(argument: &JavaExpr) -> bool {
        matches!(
            argument,
            JavaExpr::Literal(JavaLiteral::Null | JavaLiteral::Integer(_))
                | JavaExpr::StaticField { .. }
        ) && Self::literal_type(argument).is_none()
    }

    fn kotlin_default_constructor_mask_range(
        arguments: &[JavaExpr],
        values: &BTreeMap<JavaIdentifier, JavaType>,
    ) -> Option<std::ops::Range<usize>> {
        let Some(marker_index) = arguments.iter().rposition(|argument| {
            matches!(
                argument,
                JavaExpr::Cast { value, .. }
                    if matches!(value.as_ref(), JavaExpr::Literal(JavaLiteral::Null))
            ) && Self::infer_constructor_argument_type(argument, values)
                .is_some_and(|ty| Self::is_kotlin_default_constructor_marker(&ty))
        }) else {
            return None;
        };
        let mask_count = (1..=marker_index).find(|mask_count| {
            let original_count = marker_index - mask_count;
            original_count > 0 && original_count.div_ceil(32) == *mask_count
        })?;
        Some(marker_index - mask_count..marker_index)
    }

    fn is_kotlin_default_constructor_marker(ty: &JavaType) -> bool {
        matches!(
            ty,
            JavaType::Class(class)
                if class
                    .segments
                    .last()
                    .is_some_and(|segment| segment.name.as_str() == "DefaultConstructorMarker")
        )
    }

    fn resolve_this_argument_types(
        constructor: &JavaMethodDeclaration,
        prelude: &[JavaStmt],
        arguments: &[JavaExpr],
        candidates: &[Vec<JavaType>],
        method_return_types: &ConstructorMethodReturnTypes,
    ) -> Option<Vec<JavaType>> {
        if let [candidate] = candidates {
            return Some(candidate.clone());
        }
        let inferred =
            Self::infer_super_argument_types(constructor, prelude, arguments, method_return_types)?;
        let matches = candidates
            .iter()
            .filter(|candidate| {
                candidate.len() == inferred.len()
                    && inferred
                        .iter()
                        .zip(candidate.iter())
                        .all(|(actual, expected)| {
                            Self::inferred_constructor_argument_matches(actual, expected)
                        })
            })
            .collect::<Vec<_>>();
        match matches.as_slice() {
            [matched] => Some((*matched).clone()),
            [_, _, ..] => Some(inferred),
            [] => None,
        }
    }

    fn inferred_constructor_argument_matches(actual: &JavaType, expected: &JavaType) -> bool {
        if actual == expected {
            return true;
        }
        match (actual, expected) {
            (JavaType::Primitive(left), JavaType::Primitive(right)) => left == right,
            (JavaType::Class(_), JavaType::Class(_)) => true,
            (JavaType::Array(left), JavaType::Array(right)) => {
                Self::inferred_constructor_argument_matches(left, right)
            }
            (JavaType::Array(_), JavaType::Class(_)) => true,
            (JavaType::Variable(_), _) | (_, JavaType::Variable(_)) => true,
            _ => false,
        }
    }

    fn infer_constructor_argument_type(
        expression: &JavaExpr,
        values: &BTreeMap<JavaIdentifier, JavaType>,
    ) -> Option<JavaType> {
        match expression {
            JavaExpr::Name(name) => values.get(name).cloned(),
            JavaExpr::Cast { ty, .. } | JavaExpr::New { ty, .. } => Some(ty.clone()),
            JavaExpr::Field { owner, name }
                if name.as_str() == "length"
                    && matches!(
                        Self::infer_constructor_argument_type(owner, values),
                        Some(JavaType::Array(_))
                    ) =>
            {
                Some(JavaType::int())
            }
            JavaExpr::Unary {
                op: JavaUnaryOp::LogicalNot,
                ..
            }
            | JavaExpr::InstanceOf { .. } => Some(JavaType::boolean()),
            JavaExpr::Binary {
                op:
                    JavaBinaryOp::LogicalAnd
                    | JavaBinaryOp::LogicalOr
                    | JavaBinaryOp::Equal
                    | JavaBinaryOp::NotEqual
                    | JavaBinaryOp::Less
                    | JavaBinaryOp::GreaterEqual
                    | JavaBinaryOp::Greater
                    | JavaBinaryOp::LessEqual,
                ..
            } => Some(JavaType::boolean()),
            JavaExpr::Literal(_) => Self::literal_type(expression),
            JavaExpr::Conditional {
                when_true,
                when_false,
                ..
            } => {
                let when_true = Self::infer_constructor_argument_type(when_true, values)?;
                let when_false = Self::infer_constructor_argument_type(when_false, values)?;
                (when_true == when_false).then_some(when_true)
            }
            _ => None,
        }
    }

    fn method_call_return_type(
        constructor: &JavaMethodDeclaration,
        prelude: &[JavaStmt],
        expression: &JavaExpr,
        method_return_types: &ConstructorMethodReturnTypes,
    ) -> Option<JavaType> {
        let JavaExpr::Call {
            receiver,
            owner,
            method,
            args,
            ..
        } = expression
        else {
            return None;
        };
        if receiver.is_some() && method.as_str() == "toString" && args.is_empty() {
            return Some(JavaType::source_class("java.lang.String"));
        }
        let mut values = constructor
            .parameters
            .iter()
            .map(|parameter| (parameter.name.clone(), parameter.ty.clone()))
            .collect::<BTreeMap<_, _>>();
        for statement in prelude {
            if let JavaStmt::Variable { ty, name, .. } = statement {
                values.insert(name.clone(), ty.clone());
            }
        }
        let owner = match (owner, receiver.as_deref()) {
            (Some(owner), _) => Some(owner.clone()),
            (None, Some(JavaExpr::Name(name))) => values.get(name).cloned(),
            (None, Some(JavaExpr::Cast { ty, .. })) => Some(ty.clone()),
            _ => None,
        }
        .map(JavaType::into_raw);
        if let Some(return_type) =
            owner.and_then(|owner| method_return_types.get(&(owner, method.clone(), args.len())))
        {
            return return_type.clone();
        }

        // A static-field receiver does not carry its field type in JavaExpr,
        // even though the referenced method still appears in this unit's
        // return catalog. Use the owner-independent result only when every
        // matching method agrees, so unrelated same-name calls cannot select
        // an arbitrary constructor argument type.
        let mut candidates =
            method_return_types
                .iter()
                .filter_map(|((_, candidate, arity), return_type)| {
                    (candidate == method && *arity == args.len()).then_some(return_type)
                });
        let return_type = candidates.next()?.clone()?;
        candidates
            .all(|candidate| candidate.as_ref() == Some(&return_type))
            .then_some(return_type)
    }

    fn static_statements(statements: &[JavaStmt], parameters: &BTreeSet<JavaIdentifier>) -> bool {
        let mut scope = parameters.clone();
        statements
            .iter()
            .all(|statement| Self::static_statement(statement, &mut scope, parameters))
    }

    fn static_statements_with_result(
        statements: &[JavaStmt],
        result: &JavaExpr,
        parameters: &BTreeSet<JavaIdentifier>,
    ) -> bool {
        let mut scope = parameters.clone();
        statements
            .iter()
            .all(|statement| Self::static_statement(statement, &mut scope, parameters))
            && Self::static_expression(result, &scope)
    }

    fn static_statement(
        statement: &JavaStmt,
        scope: &mut BTreeSet<JavaIdentifier>,
        parameters: &BTreeSet<JavaIdentifier>,
    ) -> bool {
        Self::static_statement_with_loop_context(statement, scope, parameters, false)
    }

    fn static_statement_with_loop_context(
        statement: &JavaStmt,
        scope: &mut BTreeSet<JavaIdentifier>,
        parameters: &BTreeSet<JavaIdentifier>,
        in_loop: bool,
    ) -> bool {
        match statement {
            JavaStmt::Empty => true,
            JavaStmt::Block(statements) => {
                let mut nested = scope.clone();
                statements.iter().all(|statement| {
                    Self::static_statement_with_loop_context(
                        statement,
                        &mut nested,
                        parameters,
                        in_loop,
                    )
                })
            }
            JavaStmt::Variable { name, value, .. } => {
                value
                    .as_ref()
                    .is_none_or(|value| Self::static_expression(value, scope))
                    && scope.insert(name.clone())
            }
            JavaStmt::Expression(expression) => Self::static_for_update(expression, scope),
            JavaStmt::Throw(expression) => Self::static_expression(expression, scope),
            JavaStmt::Assign { target, value, .. } => {
                Self::static_assignment_target(target, scope)
                    && Self::static_expression(value, scope)
            }
            JavaStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => {
                Self::static_expression(condition, scope)
                    && Self::static_statement_with_loop_context(
                        then_stmt,
                        &mut scope.clone(),
                        parameters,
                        in_loop,
                    )
                    && else_stmt.as_deref().is_none_or(|statement| {
                        Self::static_statement_with_loop_context(
                            statement,
                            &mut scope.clone(),
                            parameters,
                            in_loop,
                        )
                    })
            }
            JavaStmt::While {
                condition, body, ..
            } => {
                Self::static_expression(condition, scope)
                    && Self::static_statement_with_loop_context(
                        body,
                        &mut scope.clone(),
                        parameters,
                        true,
                    )
            }
            JavaStmt::For {
                init,
                condition,
                update,
                body,
                ..
            } => {
                let mut nested = scope.clone();
                init.iter()
                    .all(|statement| Self::static_statement(statement, &mut nested, parameters))
                    && condition
                        .as_ref()
                        .is_none_or(|condition| Self::static_expression(condition, &nested))
                    && update
                        .iter()
                        .all(|update| Self::static_for_update(update, &nested))
                    && Self::static_statement_with_loop_context(body, &mut nested, parameters, true)
            }
            JavaStmt::ForEach {
                variable,
                iterable,
                body,
                ..
            } => {
                let mut nested = scope.clone();
                nested.insert(variable.clone());
                Self::static_expression(iterable, scope)
                    && Self::static_statement_with_loop_context(body, &mut nested, parameters, true)
            }
            JavaStmt::Synchronized { lock, body } => {
                Self::static_expression(lock, scope)
                    && Self::static_statement_with_loop_context(
                        body,
                        &mut scope.clone(),
                        parameters,
                        in_loop,
                    )
            }
            JavaStmt::Try {
                body,
                catches,
                finally,
            } => {
                let mut body_scope = scope.clone();
                Self::static_statement_with_loop_context(body, &mut body_scope, parameters, in_loop)
                    && catches.iter().all(|catch| {
                        let mut catch_scope = scope.clone();
                        catch_scope.insert(catch.variable.clone());
                        Self::static_statement_with_loop_context(
                            &catch.body,
                            &mut catch_scope,
                            parameters,
                            in_loop,
                        )
                    })
                    && finally.as_deref().is_none_or(|finally| {
                        Self::static_statement_with_loop_context(
                            finally,
                            &mut scope.clone(),
                            parameters,
                            in_loop,
                        )
                    })
            }
            JavaStmt::Break(None) | JavaStmt::Continue(None) => in_loop,
            _ => false,
        }
    }

    fn static_for_update(expression: &JavaExpr, scope: &BTreeSet<JavaIdentifier>) -> bool {
        match expression {
            JavaExpr::Update { target, .. } => Self::static_assignment_target(target, scope),
            JavaExpr::Assignment { target, value, .. } => {
                Self::static_assignment_target(target, scope)
                    && Self::static_expression(value, scope)
            }
            expression => Self::static_expression(expression, scope),
        }
    }

    fn static_expression(expression: &JavaExpr, scope: &BTreeSet<JavaIdentifier>) -> bool {
        match expression {
            JavaExpr::Name(name) => scope.contains(name),
            JavaExpr::Literal(_) | JavaExpr::ClassLiteral(_) | JavaExpr::StaticField { .. } => true,
            JavaExpr::Field { owner, .. } => Self::static_expression(owner, scope),
            JavaExpr::ArrayAccess { array, index } => {
                Self::static_expression(array, scope) && Self::static_expression(index, scope)
            }
            JavaExpr::Call {
                receiver,
                owner,
                args,
                ..
            } => {
                (receiver.is_some() || owner.is_some())
                    && receiver
                        .as_deref()
                        .is_none_or(|receiver| Self::static_expression(receiver, scope))
                    && args
                        .iter()
                        .all(|argument| Self::static_expression(argument, scope))
            }
            JavaExpr::New {
                enclosing: None,
                args,
                anonymous_body: None,
                ..
            } => args
                .iter()
                .all(|argument| Self::static_expression(argument, scope)),
            JavaExpr::NewArray {
                dimensions,
                initializer,
                ..
            } => dimensions
                .iter()
                .chain(initializer)
                .all(|value| Self::static_expression(value, scope)),
            JavaExpr::Unary { operand, .. }
            | JavaExpr::Cast { value: operand, .. }
            | JavaExpr::InstanceOf { value: operand, .. } => {
                Self::static_expression(operand, scope)
            }
            JavaExpr::Binary { left, right, .. } => {
                Self::static_expression(left, scope) && Self::static_expression(right, scope)
            }
            JavaExpr::Conditional {
                condition,
                when_true,
                when_false,
            } => {
                Self::static_expression(condition, scope)
                    && Self::static_expression(when_true, scope)
                    && Self::static_expression(when_false, scope)
            }
            JavaExpr::This
            | JavaExpr::QualifiedThis(_)
            | JavaExpr::Super
            | JavaExpr::MethodReference { .. }
            | JavaExpr::Lambda { .. }
            | JavaExpr::BlockLambda { .. }
            | JavaExpr::Update { .. }
            | JavaExpr::Assignment { .. }
            | JavaExpr::New { .. } => false,
        }
    }

    fn static_assignment_target(expression: &JavaExpr, scope: &BTreeSet<JavaIdentifier>) -> bool {
        match expression {
            JavaExpr::Name(name) => scope.contains(name),
            JavaExpr::StaticField { .. } => true,
            JavaExpr::Field { owner, .. } => Self::static_expression(owner, scope),
            JavaExpr::ArrayAccess { array, index } => {
                Self::static_expression(array, scope) && Self::static_expression(index, scope)
            }
            _ => false,
        }
    }

    fn parameter_slots<'a>(types: impl IntoIterator<Item = &'a JavaType>) -> usize {
        types.into_iter().map(Self::type_slots).sum()
    }

    fn type_slots(ty: &JavaType) -> usize {
        usize::from(matches!(
            ty,
            JavaType::Primitive(
                crate::language::java::JavaPrimitiveType::Long
                    | crate::language::java::JavaPrimitiveType::Double
            )
        )) + 1
    }

    fn super_argument_prelude_factory(
        constructor: &JavaMethodDeclaration,
        class_type_parameters: &[JavaTypeParameter],
        factory_name: JavaIdentifier,
        method_return_types: &ConstructorMethodReturnTypes,
    ) -> Option<(JavaMethodBody, JavaMethodDeclaration)> {
        if constructor.kind != JavaMethodDeclarationKind::Constructor
            || !constructor.type_parameters.is_empty()
            || constructor
                .parameters
                .iter()
                .any(|parameter| parameter.varargs)
        {
            return None;
        }
        let JavaStmt::Block(statements) = &constructor.body.as_ref()?.root else {
            return None;
        };
        let invocation_index = statements.iter().position(|statement| {
            matches!(
                statement,
                JavaStmt::ConstructorInvocation {
                    target: JavaConstructorTarget::Super,
                    ..
                }
            )
        })?;
        let (prelude, invocation_and_trailing) = statements.split_at(invocation_index);
        let [JavaStmt::ConstructorInvocation {
            target: JavaConstructorTarget::Super,
            args,
        }, trailing @ ..] = invocation_and_trailing
        else {
            return None;
        };
        let [earlier_args @ .., return_value] = args.as_slice() else {
            return None;
        };
        let parameters = constructor
            .parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect::<BTreeSet<_>>();
        let return_type = if let Some(return_type) = Self::literal_type(return_value) {
            let guard_count = prelude
                .iter()
                .take_while(|statement| {
                    ConstructorParameterGuards::is_parameter_guard(statement, &parameters)
                })
                .count();
            if guard_count == 0
                || guard_count == prelude.len()
                || !prelude[guard_count..]
                    .iter()
                    .all(|statement| Self::parameter_side_effect(statement, &parameters))
                || !earlier_args
                    .iter()
                    .all(|argument| Self::passive_constructor_argument(argument, &parameters))
            {
                return None;
            }
            return_type
        } else {
            if !earlier_args.is_empty()
                || !prelude
                    .iter()
                    .any(|statement| matches!(statement, JavaStmt::Variable { .. }))
                || !Self::static_statements_with_result(prelude, return_value, &parameters)
            {
                return None;
            }
            Self::method_call_return_type(constructor, prelude, return_value, method_return_types)?
        };
        if !Self::static_factory_types_in_scope(constructor, &return_type, class_type_parameters) {
            return None;
        }

        let factory_call = JavaExpr::Call {
            receiver: None,
            owner: None,
            type_arguments: Vec::new(),
            method: factory_name.clone(),
            args: constructor
                .parameters
                .iter()
                .map(|parameter| JavaExpr::Name(parameter.name.clone()))
                .collect(),
        };
        let mut invocation_args = earlier_args.to_vec();
        invocation_args.push(factory_call);
        let mut constructor_statements = Vec::with_capacity(1 + trailing.len());
        constructor_statements.push(JavaStmt::ConstructorInvocation {
            target: JavaConstructorTarget::Super,
            args: invocation_args,
        });
        constructor_statements.extend_from_slice(trailing);

        let mut factory_statements = prelude.to_vec();
        factory_statements.push(JavaStmt::Return(Some(return_value.clone())));
        let factory = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Private, JavaModifier::Static],
            compiler_generated: true,
            kind: JavaMethodDeclarationKind::Method,
            type_parameters: class_type_parameters.to_vec(),
            return_type: Some(return_type),
            name: Some(factory_name),
            parameters: constructor.parameters.clone(),
            throws: constructor.throws.clone(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(factory_statements),
            }),
        };
        Some((
            JavaMethodBody {
                root: JavaStmt::Block(constructor_statements),
            },
            factory,
        ))
    }

    fn prepared_super_argument_factory(
        constructor: &JavaMethodDeclaration,
        class_type_parameters: &[JavaTypeParameter],
        factory_name: JavaIdentifier,
    ) -> Option<(JavaMethodBody, JavaMethodDeclaration)> {
        if constructor.kind != JavaMethodDeclarationKind::Constructor
            || !constructor.type_parameters.is_empty()
            || constructor
                .parameters
                .iter()
                .any(|parameter| parameter.varargs)
        {
            return None;
        }
        let JavaStmt::Block(statements) = &constructor.body.as_ref()?.root else {
            return None;
        };
        let invocation_index = statements.iter().position(|statement| {
            matches!(
                statement,
                JavaStmt::ConstructorInvocation {
                    target: JavaConstructorTarget::Super,
                    ..
                }
            )
        })?;
        let (prelude, invocation_and_trailing) = statements.split_at(invocation_index);
        let [JavaStmt::ConstructorInvocation {
            target: JavaConstructorTarget::Super,
            args,
        }, trailing @ ..] = invocation_and_trailing
        else {
            return None;
        };
        let parameters = constructor
            .parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect::<BTreeSet<_>>();
        let candidates = args
            .iter()
            .enumerate()
            .filter_map(|(index, argument)| {
                let JavaExpr::Name(name) = argument else {
                    return None;
                };
                prelude.iter().find_map(|statement| match statement {
                    JavaStmt::Variable {
                        ty, name: declared, ..
                    } if declared == name => Some((index, name, ty)),
                    _ => None,
                })
            })
            .collect::<Vec<_>>();
        let [(candidate_index, candidate, candidate_type)] = candidates.as_slice() else {
            return None;
        };
        if !Self::static_statements(prelude, &parameters)
            || !args.iter().enumerate().all(|(index, argument)| {
                index == *candidate_index
                    || Self::passive_constructor_argument(argument, &parameters)
            })
            || !prelude.iter().any(|statement| {
                matches!(
                    statement,
                    JavaStmt::Expression(JavaExpr::Call {
                        receiver: Some(receiver),
                        owner: None,
                        ..
                    }) if matches!(receiver.as_ref(), JavaExpr::Name(name) if name == *candidate)
                )
            })
            || !Self::static_factory_types_in_scope(
                constructor,
                candidate_type,
                class_type_parameters,
            )
        {
            return None;
        }

        let factory_call = JavaExpr::Call {
            receiver: None,
            owner: None,
            type_arguments: Vec::new(),
            method: factory_name.clone(),
            args: constructor
                .parameters
                .iter()
                .map(|parameter| JavaExpr::Name(parameter.name.clone()))
                .collect(),
        };
        let mut invocation_args = args.clone();
        invocation_args[*candidate_index] = factory_call;
        let mut constructor_statements = Vec::with_capacity(1 + trailing.len());
        constructor_statements.push(JavaStmt::ConstructorInvocation {
            target: JavaConstructorTarget::Super,
            args: invocation_args,
        });
        constructor_statements.extend_from_slice(trailing);

        let mut factory_statements = prelude.to_vec();
        factory_statements.push(JavaStmt::Return(Some(JavaExpr::Name((*candidate).clone()))));
        let factory = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Private, JavaModifier::Static],
            compiler_generated: true,
            kind: JavaMethodDeclarationKind::Method,
            type_parameters: class_type_parameters.to_vec(),
            return_type: Some((*candidate_type).clone()),
            name: Some(factory_name),
            parameters: constructor.parameters.clone(),
            throws: constructor.throws.clone(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(factory_statements),
            }),
        };
        Some((
            JavaMethodBody {
                root: JavaStmt::Block(constructor_statements),
            },
            factory,
        ))
    }

    fn parameter_side_effect(statement: &JavaStmt, parameters: &BTreeSet<JavaIdentifier>) -> bool {
        let JavaStmt::Expression(JavaExpr::Call {
            receiver: Some(receiver),
            owner: None,
            args,
            ..
        }) = statement
        else {
            return false;
        };
        matches!(receiver.as_ref(), JavaExpr::Name(name) if parameters.contains(name))
            && args
                .iter()
                .all(|argument| Self::static_factory_input(argument, parameters))
    }

    fn passive_constructor_argument(
        expression: &JavaExpr,
        parameters: &BTreeSet<JavaIdentifier>,
    ) -> bool {
        match expression {
            JavaExpr::Name(name) => parameters.contains(name),
            JavaExpr::Literal(_) | JavaExpr::ClassLiteral(_) => true,
            JavaExpr::Cast { value, .. } => Self::passive_constructor_argument(value, parameters),
            _ => false,
        }
    }

    fn literal_type(expression: &JavaExpr) -> Option<JavaType> {
        match expression {
            JavaExpr::Literal(JavaLiteral::Null) => None,
            JavaExpr::Literal(JavaLiteral::Boolean(_)) => Some(JavaType::boolean()),
            JavaExpr::Literal(JavaLiteral::Integer(value)) if !(-32768..=65535).contains(value) => {
                Some(JavaType::int())
            }
            JavaExpr::Literal(JavaLiteral::Integer(_)) => None,
            JavaExpr::Literal(JavaLiteral::Long(_)) => Some(JavaType::Primitive(
                crate::language::java::JavaPrimitiveType::Long,
            )),
            JavaExpr::Literal(JavaLiteral::Float(_)) => Some(JavaType::Primitive(
                crate::language::java::JavaPrimitiveType::Float,
            )),
            JavaExpr::Literal(JavaLiteral::Double(_)) => Some(JavaType::Primitive(
                crate::language::java::JavaPrimitiveType::Double,
            )),
            JavaExpr::Literal(JavaLiteral::Character(_)) => Some(JavaType::Primitive(
                crate::language::java::JavaPrimitiveType::Char,
            )),
            JavaExpr::Literal(JavaLiteral::String(_)) => {
                Some(JavaType::source_class("java.lang.String"))
            }
            _ => None,
        }
    }

    fn extract_post_super_bindings(declaration: &mut JavaTypeDeclaration) {
        if declaration.kind != JavaTypeDeclarationKind::Class {
            return;
        }
        let mut signatures = declaration
            .methods
            .iter()
            .filter(|method| method.kind == JavaMethodDeclarationKind::Constructor)
            .map(Self::constructor_signature)
            .collect::<Vec<_>>();
        let mut method_names = declaration
            .methods
            .iter()
            .filter_map(|method| method.name.clone())
            .collect::<BTreeSet<_>>();
        let class_type_parameters = declaration.type_parameters.clone();
        let mut generated = Vec::new();

        for constructor in &mut declaration.methods {
            let factory_name =
                Self::claim_method_name(&mut method_names, "initializeConstructorBinding");
            let Some((signature, delegation, helper, factory)) = Self::post_super_binding_helper(
                constructor,
                &class_type_parameters,
                factory_name.clone(),
            ) else {
                method_names.remove(&factory_name);
                continue;
            };
            if signatures
                .iter()
                .any(|existing| Self::signatures_may_collide(existing, &signature))
            {
                method_names.remove(&factory_name);
                continue;
            }
            signatures.push(signature);
            constructor.body = Some(delegation);
            generated.push(helper);
            generated.push(factory);
        }
        declaration.methods.extend(generated);
    }

    fn post_super_binding_helper(
        constructor: &JavaMethodDeclaration,
        class_type_parameters: &[crate::language::java::JavaTypeParameter],
        factory_name: JavaIdentifier,
    ) -> Option<(
        Vec<JavaType>,
        JavaMethodBody,
        JavaMethodDeclaration,
        JavaMethodDeclaration,
    )> {
        if constructor.kind != JavaMethodDeclarationKind::Constructor
            || !constructor.type_parameters.is_empty()
            || constructor
                .parameters
                .iter()
                .any(|parameter| parameter.varargs)
        {
            return None;
        }
        let JavaStmt::Block(statements) = &constructor.body.as_ref()?.root else {
            return None;
        };
        let invocation_index = statements.iter().position(|statement| {
            matches!(
                statement,
                JavaStmt::ConstructorInvocation {
                    target: JavaConstructorTarget::Super,
                    args,
                } if args.is_empty()
            )
        })?;
        let (prelude, invocation_and_trailing) = statements.split_at(invocation_index);
        let [guards @ .., JavaStmt::Variable {
            ty,
            name,
            value: Some(value),
        }] = prelude
        else {
            return None;
        };
        let [invocation, trailing @ ..] = invocation_and_trailing else {
            return None;
        };
        let parameters = constructor
            .parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect::<BTreeSet<_>>();
        if guards.is_empty()
            || trailing.is_empty()
            || !guards
                .iter()
                .all(|guard| ConstructorParameterGuards::is_parameter_guard(guard, &parameters))
            || !Self::static_factory_expression(value, &parameters)
            || !Self::static_factory_types_in_scope(constructor, ty, class_type_parameters)
            || ImmediateExpressionUses::collect_statements(trailing)
                .get(name)
                .is_none()
        {
            return None;
        }

        let mut helper_parameters = constructor.parameters.clone();
        helper_parameters.push(JavaMethodParameter {
            annotations: Vec::new(),
            ty: ty.clone(),
            name: name.clone(),
            varargs: false,
        });
        let signature = helper_parameters
            .iter()
            .map(|parameter| parameter.ty.clone().into_raw())
            .collect::<Vec<_>>();
        let mut delegation_args = constructor
            .parameters
            .iter()
            .map(|parameter| JavaExpr::Name(parameter.name.clone()))
            .collect::<Vec<_>>();
        delegation_args.push(JavaExpr::Call {
            receiver: None,
            owner: None,
            type_arguments: Vec::new(),
            method: factory_name.clone(),
            args: constructor
                .parameters
                .iter()
                .map(|parameter| JavaExpr::Name(parameter.name.clone()))
                .collect(),
        });
        let delegation = JavaMethodBody {
            root: JavaStmt::Block(vec![JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::This,
                args: delegation_args,
            }]),
        };

        let mut helper_statements = Vec::with_capacity(1 + trailing.len());
        helper_statements.push(invocation.clone());
        helper_statements.extend_from_slice(trailing);
        let helper = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Private],
            compiler_generated: true,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: constructor.name.clone(),
            parameters: helper_parameters,
            throws: constructor.throws.clone(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(helper_statements),
            }),
        };

        let mut factory_statements = prelude.to_vec();
        factory_statements.push(JavaStmt::Return(Some(JavaExpr::Name(name.clone()))));
        let factory = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Private, JavaModifier::Static],
            compiler_generated: true,
            kind: JavaMethodDeclarationKind::Method,
            type_parameters: class_type_parameters.to_vec(),
            return_type: Some(ty.clone()),
            name: Some(factory_name),
            parameters: constructor.parameters.clone(),
            throws: constructor.throws.clone(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(factory_statements),
            }),
        };
        Some((signature, delegation, helper, factory))
    }

    fn static_factory_types_in_scope(
        constructor: &JavaMethodDeclaration,
        binding_type: &JavaType,
        type_parameters: &[JavaTypeParameter],
    ) -> bool {
        let declared = type_parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect::<BTreeSet<_>>();
        let mut used = BTreeSet::new();
        for ty in constructor
            .parameters
            .iter()
            .map(|parameter| &parameter.ty)
            .chain(std::iter::once(binding_type))
            .chain(
                type_parameters
                    .iter()
                    .flat_map(|parameter| parameter.bounds.iter()),
            )
        {
            Self::collect_type_variables(ty, &mut used);
        }
        used.is_subset(&declared)
    }

    fn collect_type_variables(ty: &JavaType, variables: &mut BTreeSet<JavaIdentifier>) {
        match ty {
            JavaType::Variable(variable) => {
                variables.insert(variable.clone());
            }
            JavaType::Class(class) => {
                for argument in class.segments.iter().flat_map(|segment| &segment.arguments) {
                    match argument {
                        JavaTypeArgument::Any => {}
                        JavaTypeArgument::Exact(ty)
                        | JavaTypeArgument::Extends(ty)
                        | JavaTypeArgument::Super(ty) => {
                            Self::collect_type_variables(ty, variables);
                        }
                    }
                }
            }
            JavaType::Array(element) => Self::collect_type_variables(element, variables),
            JavaType::Primitive(_) => {}
        }
    }

    fn static_factory_expression(
        expression: &JavaExpr,
        parameters: &BTreeSet<JavaIdentifier>,
    ) -> bool {
        match expression {
            JavaExpr::Call {
                receiver: None,
                owner: Some(_),
                args,
                ..
            } => args
                .iter()
                .all(|argument| Self::static_factory_input(argument, parameters)),
            JavaExpr::Cast { value, .. } => Self::static_factory_expression(value, parameters),
            _ => false,
        }
    }

    fn static_factory_input(expression: &JavaExpr, parameters: &BTreeSet<JavaIdentifier>) -> bool {
        match expression {
            JavaExpr::Name(name) => parameters.contains(name),
            JavaExpr::Literal(_) | JavaExpr::ClassLiteral(_) | JavaExpr::StaticField { .. } => true,
            JavaExpr::Cast { value, .. } => Self::static_factory_input(value, parameters),
            _ => false,
        }
    }

    fn mutable_constructor_helper(
        constructor: &JavaMethodDeclaration,
        factory_name: JavaIdentifier,
    ) -> Option<(
        Vec<JavaType>,
        JavaMethodBody,
        JavaMethodDeclaration,
        JavaMethodDeclaration,
    )> {
        if constructor.kind != JavaMethodDeclarationKind::Constructor
            || !constructor.parameters.is_empty()
            || !constructor.type_parameters.is_empty()
        {
            return None;
        }
        let JavaStmt::Block(statements) = &constructor.body.as_ref()?.root else {
            return None;
        };
        let (invocation, prelude) = statements.split_last()?;
        let invocation @ JavaStmt::ConstructorInvocation { args, .. } = invocation else {
            return None;
        };
        let [JavaStmt::Variable {
            ty,
            name,
            value: Some(value),
        }, rest @ ..] = prelude
        else {
            return None;
        };
        let JavaExpr::New {
            enclosing: None,
            ty: constructed_type,
            args: constructor_args,
            anonymous_body: None,
            ..
        } = value
        else {
            return None;
        };
        if ty.clone().into_raw() != constructed_type.clone().into_raw()
            || !constructor_args.iter().all(Self::factory_literal)
            || ImmediateExpressionUses::collect_expressions(args).get(name) != Some(&1)
            || !Self::mutable_factory_statements(rest, name)
        {
            return None;
        }

        let parameter = JavaMethodParameter {
            annotations: Vec::new(),
            ty: ty.clone(),
            name: name.clone(),
            varargs: false,
        };
        let signature = vec![ty.clone().into_raw()];
        let delegation = JavaMethodBody {
            root: JavaStmt::Block(vec![JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::This,
                args: vec![JavaExpr::Call {
                    receiver: None,
                    owner: None,
                    type_arguments: Vec::new(),
                    method: factory_name.clone(),
                    args: Vec::new(),
                }],
            }]),
        };
        let helper = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Private],
            compiler_generated: true,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: constructor.name.clone(),
            parameters: vec![parameter],
            throws: constructor.throws.clone(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![invocation.clone()]),
            }),
        };
        let mut factory_statements = prelude.to_vec();
        factory_statements.push(JavaStmt::Return(Some(JavaExpr::Name(name.clone()))));
        let factory = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Private, JavaModifier::Static],
            compiler_generated: true,
            kind: JavaMethodDeclarationKind::Method,
            type_parameters: Vec::new(),
            return_type: Some(ty.clone()),
            name: Some(factory_name),
            parameters: Vec::new(),
            throws: constructor.throws.clone(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(factory_statements),
            }),
        };
        Some((signature, delegation, helper, factory))
    }

    fn mutable_factory_statements(statements: &[JavaStmt], binding: &JavaIdentifier) -> bool {
        let uses = ImmediateExpressionUses::collect_statements(statements);
        statements.iter().all(|statement| match statement {
            JavaStmt::Expression(JavaExpr::Call {
                receiver: Some(receiver),
                owner: None,
                args,
                ..
            }) => {
                matches!(receiver.as_ref(), JavaExpr::Name(name) if name == binding)
                    && args.iter().all(Self::factory_literal)
            }
            JavaStmt::Variable {
                name,
                value: Some(JavaExpr::StaticField { .. }),
                ..
            } => !uses.contains_key(name),
            _ => false,
        })
    }

    fn factory_literal(expression: &JavaExpr) -> bool {
        match expression {
            JavaExpr::Literal(_) | JavaExpr::ClassLiteral(_) | JavaExpr::StaticField { .. } => true,
            JavaExpr::Cast { value, .. } => Self::factory_literal(value),
            _ => false,
        }
    }

    fn claim_method_name(names: &mut BTreeSet<JavaIdentifier>, preferred: &str) -> JavaIdentifier {
        for suffix in 0usize.. {
            let source = if suffix == 0 {
                preferred.to_owned()
            } else {
                format!("{preferred}{suffix}")
            };
            let candidate = JavaIdentifier::from_dex(&source);
            if names.insert(candidate.clone()) {
                return candidate;
            }
        }
        unreachable!("method suffix space is unbounded")
    }

    fn shared_boxing_helper(
        constructor: &JavaMethodDeclaration,
    ) -> Option<(Vec<JavaType>, JavaMethodBody, JavaMethodDeclaration)> {
        if constructor.kind != JavaMethodDeclarationKind::Constructor
            || !constructor.type_parameters.is_empty()
            || constructor
                .parameters
                .iter()
                .any(|parameter| parameter.varargs)
        {
            return None;
        }
        let JavaStmt::Block(statements) = &constructor.body.as_ref()?.root else {
            return None;
        };
        let [JavaStmt::Variable {
            ty,
            name,
            value: Some(value),
        }, invocation @ JavaStmt::ConstructorInvocation { args, .. }] = statements.as_slice()
        else {
            return None;
        };
        if ConstructorBindings::stable(value)
            || !Self::literal_boxing_value(value)
            || ImmediateExpressionUses::collect_expressions(args)
                .get(name)
                .is_none_or(|uses| *uses < 2)
        {
            return None;
        }

        let mut helper_parameters = constructor.parameters.clone();
        helper_parameters.push(JavaMethodParameter {
            annotations: Vec::new(),
            ty: ty.clone(),
            name: name.clone(),
            varargs: false,
        });
        let signature = helper_parameters
            .iter()
            .map(|parameter| parameter.ty.clone().into_raw())
            .collect::<Vec<_>>();
        let mut delegation_args = constructor
            .parameters
            .iter()
            .map(|parameter| JavaExpr::Name(parameter.name.clone()))
            .collect::<Vec<_>>();
        delegation_args.push(value.clone());

        let delegation = JavaMethodBody {
            root: JavaStmt::Block(vec![JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::This,
                args: delegation_args,
            }]),
        };
        let helper = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Private],
            compiler_generated: true,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: constructor.name.clone(),
            parameters: helper_parameters,
            throws: constructor.throws.clone(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![invocation.clone()]),
            }),
        };
        Some((signature, delegation, helper))
    }

    fn literal_boxing_value(expression: &JavaExpr) -> bool {
        let JavaExpr::Call {
            receiver: None,
            owner: Some(JavaType::Class(owner)),
            method,
            args,
            ..
        } = expression
        else {
            return false;
        };
        if method.as_str() != "valueOf" || !matches!(args.as_slice(), [JavaExpr::Literal(_)]) {
            return false;
        }
        matches!(
            owner.name().components(),
            [wrapper]
                if matches!(
                    wrapper.as_str(),
                    "Boolean"
                        | "Byte"
                        | "Short"
                        | "Integer"
                        | "Long"
                        | "Float"
                        | "Double"
                        | "Character"
                )
        ) || matches!(
            owner.name().components(),
            [java, lang, wrapper]
                if java.as_str() == "java"
                    && lang.as_str() == "lang"
                    && matches!(
                        wrapper.as_str(),
                        "Boolean"
                            | "Byte"
                            | "Short"
                            | "Integer"
                            | "Long"
                            | "Float"
                            | "Double"
                            | "Character"
                    )
        )
    }

    fn constructor_signature(constructor: &JavaMethodDeclaration) -> Vec<JavaType> {
        constructor
            .parameters
            .iter()
            .map(|parameter| parameter.ty.clone().into_raw())
            .collect()
    }

    fn signatures_may_collide(left: &[JavaType], right: &[JavaType]) -> bool {
        left.len() == right.len()
            && left
                .iter()
                .zip(right)
                .all(|(left, right)| Self::types_may_share_erasure(left, right))
    }

    fn types_may_share_erasure(left: &JavaType, right: &JavaType) -> bool {
        match (left, right) {
            (JavaType::Variable(_), JavaType::Primitive(_))
            | (JavaType::Primitive(_), JavaType::Variable(_)) => false,
            (JavaType::Variable(_), _) | (_, JavaType::Variable(_)) => true,
            (JavaType::Primitive(left), JavaType::Primitive(right)) => left == right,
            (JavaType::Class(left), JavaType::Class(right)) => left.name() == right.name(),
            (JavaType::Array(left), JavaType::Array(right)) => {
                Self::types_may_share_erasure(left, right)
            }
            _ => false,
        }
    }

    fn remove_implicit_super(statements: &mut Vec<JavaStmt>, directly_extends_object: bool) {
        let Some(invocation) = statements.iter().position(|statement| {
            matches!(
                statement,
                JavaStmt::ConstructorInvocation {
                    target: JavaConstructorTarget::Super,
                    args,
                } if args.is_empty()
            )
        }) else {
            return;
        };
        if invocation == 0 || directly_extends_object {
            statements.remove(invocation);
        }
    }

    fn schedule_arguments(statements: &mut Vec<JavaStmt>) {
        ConstructorEvaluationOrder::recover(statements);
        let Some(invocation) = statements
            .iter()
            .position(|statement| matches!(statement, JavaStmt::ConstructorInvocation { .. }))
        else {
            return;
        };
        if invocation == 0 {
            return;
        }

        let Some(bindings) = ConstructorBindings::analyze(&statements[..invocation]) else {
            return;
        };
        let JavaStmt::ConstructorInvocation { args, .. } = &statements[invocation] else {
            unreachable!("constructor invocation index was selected above")
        };
        if !bindings.can_schedule(args) {
            return;
        }

        let mut substitution = ConstructorSubstitution {
            values: &bindings.values,
        };
        let JavaStmt::ConstructorInvocation { args, .. } = &mut statements[invocation] else {
            unreachable!("constructor invocation index was selected above")
        };
        *args = std::mem::take(args)
            .into_iter()
            .map(|argument| substitution.rewrite_expression(argument))
            .collect();
        statements.drain(..invocation);
    }
}

#[derive(Default)]
struct QualifiedThisTypes {
    types: BTreeSet<JavaType>,
}

impl JavaAstRewriter for QualifiedThisTypes {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        if let JavaExpr::QualifiedThis(ty) = &expression {
            self.types.insert(ty.clone());
        }
        expression
    }
}

struct QualifiedThisSubstitution<'a> {
    names: &'a BTreeMap<JavaType, JavaIdentifier>,
}

impl JavaAstRewriter for QualifiedThisSubstitution<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        match expression {
            JavaExpr::QualifiedThis(ty) => self
                .names
                .get(&ty)
                .cloned()
                .map(JavaExpr::Name)
                .unwrap_or(JavaExpr::QualifiedThis(ty)),
            expression => expression,
        }
    }
}

struct ConstructorCapturePrelude;

struct ConstructorParameterGuards;

impl ConstructorParameterGuards {
    fn take(
        statements: &mut Vec<JavaStmt>,
        parameters: &BTreeSet<JavaIdentifier>,
    ) -> Vec<JavaStmt> {
        let Some(invocation) = statements
            .iter()
            .position(|statement| matches!(statement, JavaStmt::ConstructorInvocation { .. }))
        else {
            return Vec::new();
        };
        let leading = statements[..invocation]
            .iter()
            .take_while(|statement| Self::is_parameter_guard(statement, parameters))
            .count();
        statements.drain(..leading).collect()
    }

    fn restore(statements: &mut Vec<JavaStmt>, guards: Vec<JavaStmt>) {
        if guards.is_empty() {
            return;
        }
        let Some(0) = statements
            .iter()
            .position(|statement| matches!(statement, JavaStmt::ConstructorInvocation { .. }))
        else {
            statements.splice(0..0, guards);
            return;
        };
        statements.splice(1..1, guards);
    }

    fn is_parameter_guard(statement: &JavaStmt, parameters: &BTreeSet<JavaIdentifier>) -> bool {
        let JavaStmt::Expression(JavaExpr::Call {
            receiver: None,
            owner: Some(JavaType::Class(owner)),
            method,
            args,
            ..
        }) = statement
        else {
            return false;
        };
        let is_intrinsics = owner
            .name()
            .components()
            .last()
            .is_some_and(|component| component.as_str() == "Intrinsics");
        is_intrinsics
            && matches!(
                method.as_str(),
                "checkNotNull" | "checkNotNullParameter" | "checkParameterIsNotNull"
            )
            && args
                .first()
                .is_some_and(|value| ConstructorCapturePrelude::is_capture_value(value, parameters))
    }
}

impl ConstructorCapturePrelude {
    fn schedule(
        statements: &mut Vec<JavaStmt>,
        parameters: &BTreeSet<JavaIdentifier>,
        final_fields: &BTreeSet<JavaIdentifier>,
    ) {
        let Some(invocation) = statements
            .iter()
            .position(|statement| matches!(statement, JavaStmt::ConstructorInvocation { .. }))
        else {
            return;
        };
        if invocation == 0
            || !statements[..invocation].iter().all(|statement| {
                Self::is_capture_store(statement, parameters, final_fields)
                    || ConstructorParameterGuards::is_parameter_guard(statement, parameters)
            })
        {
            return;
        }
        let invocation = statements.remove(invocation);
        statements.insert(0, invocation);
    }

    fn is_capture_store(
        statement: &JavaStmt,
        parameters: &BTreeSet<JavaIdentifier>,
        final_fields: &BTreeSet<JavaIdentifier>,
    ) -> bool {
        matches!(
            statement,
            JavaStmt::Assign {
                target: JavaExpr::Field { owner, name: field },
                value,
                ..
            } if matches!(owner.as_ref(), JavaExpr::This)
                && final_fields.contains(field)
                && Self::is_capture_value(value, parameters)
        )
    }

    fn is_capture_value(value: &JavaExpr, parameters: &BTreeSet<JavaIdentifier>) -> bool {
        match value {
            JavaExpr::Name(parameter) => parameters.contains(parameter),
            JavaExpr::QualifiedThis(_) => true,
            JavaExpr::Literal(_) => true,
            JavaExpr::Cast { value, .. } => Self::is_capture_value(value, parameters),
            _ => false,
        }
    }
}

struct ConstructorEvaluationOrder;

impl ConstructorEvaluationOrder {
    fn recover(statements: &mut Vec<JavaStmt>) {
        let Some(mut invocation) = statements
            .iter()
            .position(|statement| matches!(statement, JavaStmt::ConstructorInvocation { .. }))
        else {
            return;
        };
        let mut index = 0;
        while index < invocation {
            let Some(evaluation) = IdentityEvaluation::analyze(&statements[index]) else {
                index += 1;
                continue;
            };
            let mut binder = BoundReceiverBinder {
                input: &evaluation.input,
                evaluation: &evaluation.expression,
                replaced: false,
            };
            for candidate in &mut statements[index + 1..=invocation] {
                *candidate =
                    binder.rewrite_statement(std::mem::replace(candidate, JavaStmt::Empty));
                if binder.replaced {
                    break;
                }
            }
            if binder.replaced {
                statements.remove(index);
                invocation -= 1;
            } else {
                index += 1;
            }
        }
    }
}

struct IdentityEvaluation {
    input: JavaExpr,
    expression: JavaExpr,
}

impl IdentityEvaluation {
    fn analyze(statement: &JavaStmt) -> Option<Self> {
        let JavaStmt::Expression(
            expression @ JavaExpr::Call {
                receiver: None,
                owner: Some(JavaType::Class(owner)),
                method,
                args,
                ..
            },
        ) = statement
        else {
            return None;
        };
        let [input] = args.as_slice() else {
            return None;
        };
        let owner = owner.name();
        let components = owner.components();
        let is_objects = components
            .last()
            .is_some_and(|component| component == &JavaIdentifier::from_dex("Objects"));
        (is_objects && method == &JavaIdentifier::from_dex("requireNonNull")).then(|| Self {
            input: input.clone(),
            expression: expression.clone(),
        })
    }
}

struct BoundReceiverBinder<'a> {
    input: &'a JavaExpr,
    evaluation: &'a JavaExpr,
    replaced: bool,
}

impl BoundReceiverBinder<'_> {
    fn bind(&self, expression: JavaExpr) -> Option<JavaExpr> {
        if &expression == self.input {
            return Some(self.evaluation.clone());
        }
        let JavaExpr::Cast { ty, value } = expression else {
            return None;
        };
        Some(JavaExpr::Cast {
            ty,
            value: Box::new(self.bind(*value)?),
        })
    }
}

impl JavaAstRewriter for BoundReceiverBinder<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        if self.replaced {
            return expression;
        }
        match expression {
            JavaExpr::MethodReference { receiver, method } => {
                let original = *receiver;
                let Some(receiver) = self.bind(original.clone()) else {
                    return JavaExpr::MethodReference {
                        receiver: Box::new(original),
                        method,
                    };
                };
                self.replaced = true;
                JavaExpr::MethodReference {
                    receiver: Box::new(receiver),
                    method,
                }
            }
            JavaExpr::New {
                enclosing,
                ty,
                target_type,
                mut args,
                anonymous_body,
            } => {
                if let Some((index, value)) =
                    args.iter().enumerate().find_map(|(index, argument)| {
                        self.bind(argument.clone()).map(|value| (index, value))
                    })
                {
                    args[index] = value;
                    self.replaced = true;
                }
                JavaExpr::New {
                    enclosing,
                    ty,
                    target_type,
                    args,
                    anonymous_body,
                }
            }
            expression => expression,
        }
    }
}

struct ConstructorBindings {
    order: Vec<JavaIdentifier>,
    values: BTreeMap<JavaIdentifier, JavaExpr>,
    dependencies: BTreeMap<JavaIdentifier, BTreeSet<JavaIdentifier>>,
}

impl ConstructorBindings {
    fn analyze(statements: &[JavaStmt]) -> Option<Self> {
        let mut dataflow = ConstructorDataflow::default();
        dataflow.evaluate(statements)?;
        dataflow.finalize_arrays()?;
        Some(Self {
            order: dataflow.order,
            values: dataflow.values,
            dependencies: dataflow.dependencies,
        })
    }

    fn can_schedule(&self, args: &[JavaExpr]) -> bool {
        let positions = args
            .iter()
            .enumerate()
            .flat_map(|(index, argument)| {
                ExpressionNames::collect(argument)
                    .into_iter()
                    .filter(|name| self.values.contains_key(name))
                    .map(move |name| (name, index))
            })
            .fold(
                BTreeMap::<JavaIdentifier, Vec<usize>>::new(),
                |mut positions, (name, index)| {
                    positions.entry(name).or_default().push(index);
                    positions
                },
            );

        let mut last_position = None;
        for name in &self.order {
            let mut visiting = BTreeSet::new();
            let Some(binding_positions) = self.binding_positions(name, &positions, &mut visiting)
            else {
                return false;
            };
            match binding_positions.as_slice() {
                [] if Self::stable(&self.values[name]) => continue,
                [position] if last_position.is_none_or(|previous| previous <= *position) => {
                    last_position = Some(*position);
                }
                _ => return false,
            }
        }

        let Some(last_position) = last_position else {
            return true;
        };
        args.iter().take(last_position).all(|argument| {
            let names = ExpressionNames::collect(argument);
            names.iter().any(|name| self.values.contains_key(name))
                || ReplayableExpression::check(argument)
        })
    }

    fn binding_positions(
        &self,
        name: &JavaIdentifier,
        direct: &BTreeMap<JavaIdentifier, Vec<usize>>,
        visiting: &mut BTreeSet<JavaIdentifier>,
    ) -> Option<Vec<usize>> {
        if !visiting.insert(name.clone()) {
            return None;
        }
        let mut positions = direct.get(name).cloned().unwrap_or_default();
        for (dependent, dependencies) in &self.dependencies {
            if dependencies.contains(name) {
                positions.extend(self.binding_positions(dependent, direct, visiting)?);
            }
        }
        visiting.remove(name);
        positions.sort_unstable();
        positions.dedup();
        Some(positions)
    }

    fn stable(expression: &JavaExpr) -> bool {
        match expression {
            JavaExpr::This
            | JavaExpr::QualifiedThis(_)
            | JavaExpr::Super
            | JavaExpr::Name(_)
            | JavaExpr::Literal(_)
            | JavaExpr::ClassLiteral(_)
            | JavaExpr::StaticField { .. } => true,
            JavaExpr::Cast { value, .. } => Self::stable(value),
            JavaExpr::Call {
                receiver: None,
                owner: Some(JavaType::Class(owner)),
                method,
                args,
                ..
            } => Self::cached_boxing_value(owner.name().components(), method, args),
            _ => false,
        }
    }

    fn cached_boxing_value(
        owner: &[JavaIdentifier],
        method: &JavaIdentifier,
        args: &[JavaExpr],
    ) -> bool {
        let wrapper = match owner {
            [wrapper] => wrapper,
            [package, module, wrapper]
                if package.as_str() == "java" && module.as_str() == "lang" =>
            {
                wrapper
            }
            _ => return false,
        };
        if method.as_str() != "valueOf" {
            return false;
        }
        let [value] = args else {
            return false;
        };
        match (wrapper.as_str(), value) {
            ("Boolean", JavaExpr::Literal(JavaLiteral::Boolean(_))) => true,
            ("Byte" | "Short" | "Integer", JavaExpr::Literal(JavaLiteral::Integer(-128..=127))) => {
                true
            }
            ("Long", JavaExpr::Literal(JavaLiteral::Long(-128..=127))) => true,
            ("Character", JavaExpr::Literal(JavaLiteral::Character(0..=127))) => true,
            _ => false,
        }
    }
}

#[derive(Clone, Default)]
struct ConstructorDataflow {
    order: Vec<JavaIdentifier>,
    declared: BTreeSet<JavaIdentifier>,
    values: BTreeMap<JavaIdentifier, JavaExpr>,
    dependencies: BTreeMap<JavaIdentifier, BTreeSet<JavaIdentifier>>,
    array_writes: BTreeMap<JavaIdentifier, Vec<JavaExpr>>,
}

impl ConstructorDataflow {
    fn evaluate(&mut self, statements: &[JavaStmt]) -> Option<()> {
        for statement in statements {
            self.evaluate_statement(statement)?;
        }
        Some(())
    }

    fn evaluate_statement(&mut self, statement: &JavaStmt) -> Option<()> {
        match statement {
            JavaStmt::Variable {
                name,
                value: Some(value),
                ..
            } => self.declare(name, value),
            JavaStmt::Variable {
                name, value: None, ..
            } => self.declare_uninitialized(name),
            JavaStmt::Assign {
                target: JavaExpr::Name(name),
                op: JavaAssignOp::Assign,
                value,
            } => self.assign(name, value),
            JavaStmt::Assign {
                target: JavaExpr::ArrayAccess { array, index },
                op: JavaAssignOp::Assign,
                value,
            } => self.assign_array_element(array, index, value),
            JavaStmt::Expression(expression) => self.append_to_string_builder(expression),
            JavaStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => self.branch(condition, then_stmt, else_stmt.as_deref()),
            JavaStmt::Block(statements) => self.evaluate(statements),
            _ => None,
        }
    }

    fn declare(&mut self, name: &JavaIdentifier, value: &JavaExpr) -> Option<()> {
        if !self.declared.insert(name.clone()) {
            return None;
        }
        let dependencies = self.binding_dependencies(value);
        let value = self.resolve(value.clone());
        self.record_evaluation(name, &value);
        self.values.insert(name.clone(), value);
        self.dependencies.insert(name.clone(), dependencies);
        Some(())
    }

    fn declare_uninitialized(&mut self, name: &JavaIdentifier) -> Option<()> {
        self.declared.insert(name.clone()).then_some(())
    }

    fn assign(&mut self, name: &JavaIdentifier, value: &JavaExpr) -> Option<()> {
        if !self.declared.contains(name)
            || self
                .values
                .get(name)
                .is_some_and(|prior| !ConstructorBindings::stable(prior))
        {
            return None;
        }
        let dependencies = self.binding_dependencies(value);
        let value = self.resolve(value.clone());
        self.record_evaluation(name, &value);
        self.values.insert(name.clone(), value);
        self.dependencies.insert(name.clone(), dependencies);
        Some(())
    }

    fn append_to_string_builder(&mut self, expression: &JavaExpr) -> Option<()> {
        let JavaExpr::Call {
            receiver: Some(receiver),
            owner: None,
            method,
            args,
            ..
        } = expression
        else {
            return None;
        };
        let JavaExpr::Name(name) = receiver.as_ref() else {
            return None;
        };
        if method.as_str() != "append"
            || !self
                .values
                .get(name)
                .is_some_and(Self::is_string_builder_chain)
            || args
                .iter()
                .any(|argument| ExpressionNames::collect(argument).contains(name))
        {
            return None;
        }

        let mut dependencies = self.dependencies.get(name).cloned().unwrap_or_default();
        dependencies.extend(
            args.iter()
                .flat_map(ExpressionNames::collect)
                .filter(|dependency| self.values.contains_key(dependency)),
        );
        let value = self.resolve(expression.clone());
        self.values.insert(name.clone(), value);
        self.dependencies.insert(name.clone(), dependencies);
        Some(())
    }

    fn is_string_builder_chain(expression: &JavaExpr) -> bool {
        match expression {
            JavaExpr::New {
                ty: JavaType::Class(class),
                ..
            } => match class.name().components() {
                [builder] if matches!(builder.as_str(), "StringBuilder" | "StringBuffer") => true,
                [java, lang, builder]
                    if java.as_str() == "java"
                        && lang.as_str() == "lang"
                        && matches!(builder.as_str(), "StringBuilder" | "StringBuffer") =>
                {
                    true
                }
                _ => false,
            },
            JavaExpr::Call {
                receiver: Some(receiver),
                owner: None,
                method,
                ..
            } => method.as_str() == "append" && Self::is_string_builder_chain(receiver),
            JavaExpr::Cast { value, .. } => Self::is_string_builder_chain(value),
            _ => false,
        }
    }

    fn assign_array_element(
        &mut self,
        array: &JavaExpr,
        index: &JavaExpr,
        value: &JavaExpr,
    ) -> Option<()> {
        let JavaExpr::Name(name) = array else {
            return None;
        };
        let JavaExpr::Literal(JavaLiteral::Integer(index)) = index else {
            return None;
        };
        let index = usize::try_from(*index).ok()?;
        let (dimensions, initializer) = Self::array_construction(self.values.get(name)?)?;
        if dimensions.len() != 1 || !initializer.is_empty() {
            return None;
        }
        let dependencies = self.binding_dependencies(value);
        let value = self.resolve(value.clone());
        let writes = self.array_writes.entry(name.clone()).or_default();
        if index != writes.len() {
            return None;
        }
        writes.push(value);
        self.dependencies
            .entry(name.clone())
            .or_default()
            .extend(dependencies);
        Some(())
    }

    fn finalize_arrays(&mut self) -> Option<()> {
        let names = self.array_writes.keys().cloned().collect::<Vec<_>>();
        self.finalize_array_writes(names)
    }

    fn finalize_arrays_created_after(&mut self, baseline: &Self) -> Option<()> {
        let names = self
            .array_writes
            .keys()
            .filter(|name| !baseline.array_writes.contains_key(*name))
            .cloned()
            .collect::<Vec<_>>();
        self.finalize_array_writes(names)
    }

    fn finalize_array_writes(
        &mut self,
        names: impl IntoIterator<Item = JavaIdentifier>,
    ) -> Option<()> {
        for name in names {
            let initializer = self.array_writes.remove(&name)?;
            let (dimensions, current) = Self::array_construction_mut(self.values.get_mut(&name)?)?;
            let [JavaExpr::Literal(JavaLiteral::Integer(length))] = dimensions.as_slice() else {
                return None;
            };
            if usize::try_from(*length).ok()? != initializer.len() || !current.is_empty() {
                return None;
            }
            dimensions.clear();
            *current = initializer;
        }
        Some(())
    }

    fn array_construction(expression: &JavaExpr) -> Option<(&Vec<JavaExpr>, &Vec<JavaExpr>)> {
        match expression {
            JavaExpr::NewArray {
                dimensions,
                initializer,
                ..
            } => Some((dimensions, initializer)),
            JavaExpr::Cast { value, .. } => Self::array_construction(value),
            _ => None,
        }
    }

    fn array_construction_mut(
        expression: &mut JavaExpr,
    ) -> Option<(&mut Vec<JavaExpr>, &mut Vec<JavaExpr>)> {
        match expression {
            JavaExpr::NewArray {
                dimensions,
                initializer,
                ..
            } => Some((dimensions, initializer)),
            JavaExpr::Cast { value, .. } => Self::array_construction_mut(value),
            _ => None,
        }
    }

    fn branch(
        &mut self,
        condition: &JavaExpr,
        then_stmt: &JavaStmt,
        else_stmt: Option<&JavaStmt>,
    ) -> Option<()> {
        let condition_dependencies = self.binding_dependencies(condition);
        let condition = self.resolve(condition.clone());

        let baseline = self.clone();
        let mut when_true = baseline.clone();
        when_true.evaluate_statement(then_stmt)?;
        let mut when_false = baseline.clone();
        if let Some(else_stmt) = else_stmt {
            when_false.evaluate_statement(else_stmt)?;
        }
        when_true.finalize_arrays_created_after(&baseline)?;
        when_false.finalize_arrays_created_after(&baseline)?;
        when_true.prune_branch_locals(&baseline, then_stmt)?;
        if let Some(else_stmt) = else_stmt {
            when_false.prune_branch_locals(&baseline, else_stmt)?;
        }
        if when_true.values.keys().ne(when_false.values.keys())
            || when_true.array_writes != when_false.array_writes
        {
            return None;
        }

        let changed = when_true
            .values
            .iter()
            .filter(|(name, value)| when_false.values.get(*name) != Some(*value))
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();
        if changed.len() > 1 && !ReplayableExpression::check(&condition) {
            return None;
        }

        self.values = when_true
            .values
            .into_iter()
            .map(|(name, true_value)| {
                let false_value = when_false.values.get(&name)?.clone();
                let value = if true_value == false_value {
                    true_value
                } else {
                    JavaExpr::Conditional {
                        condition: Box::new(condition.clone()),
                        when_true: Box::new(true_value),
                        when_false: Box::new(false_value),
                    }
                };
                Some((name, value))
            })
            .collect::<Option<_>>()?;
        self.dependencies = when_true
            .dependencies
            .into_iter()
            .map(|(name, mut dependencies)| {
                dependencies.extend(
                    when_false
                        .dependencies
                        .get(&name)
                        .into_iter()
                        .flatten()
                        .cloned(),
                );
                if changed.contains(&name) {
                    dependencies.extend(condition_dependencies.iter().cloned());
                }
                (name, dependencies)
            })
            .collect();
        self.array_writes = when_true.array_writes;
        self.order = baseline.order;
        self.extend_order(&when_true.order);
        self.extend_order(&when_false.order);
        Some(())
    }

    fn prune_branch_locals(&mut self, baseline: &Self, statement: &JavaStmt) -> Option<()> {
        let locals = self
            .declared
            .difference(&baseline.declared)
            .cloned()
            .collect::<BTreeSet<_>>();
        if locals.is_empty() {
            return Some(());
        }

        let uses = ImmediateExpressionUses::collect(statement);
        if locals.iter().any(|name| {
            !self.values.contains_key(name)
                || uses.get(name) != Some(&1)
                || self.array_writes.contains_key(name)
        }) {
            return None;
        }

        // Substitution is only legal when every local has one retained owner.
        // Otherwise it could duplicate an allocation or leave a branch value
        // with no representation after the local binding is removed.
        let roots = locals
            .iter()
            .map(|name| {
                let mut visiting = BTreeSet::new();
                let roots = self.retained_dependents(name, &locals, &mut visiting)?;
                if roots.len() != 1 {
                    return None;
                }
                Some((name.clone(), roots.into_iter().next()?))
            })
            .collect::<Option<BTreeMap<_, _>>>()?;

        let mut mapped_order = Vec::new();
        for name in &self.order {
            let name = roots.get(name).unwrap_or(name);
            if mapped_order.last() != Some(name) {
                mapped_order.push(name.clone());
            }
        }
        let retained_order = self
            .order
            .iter()
            .filter(|name| !locals.contains(*name))
            .cloned()
            .collect::<Vec<_>>();
        // Mapping a local evaluation to its retained owner must only collapse
        // adjacent events. A retained event between them would be reordered by
        // embedding the local expression into its owner.
        if mapped_order != retained_order {
            return None;
        }

        let retained = self
            .dependencies
            .keys()
            .filter(|name| !locals.contains(*name))
            .cloned()
            .collect::<Vec<_>>();
        let mut dependencies = BTreeMap::new();
        for name in retained {
            let mut visiting = BTreeSet::new();
            dependencies.insert(
                name.clone(),
                self.flatten_local_dependencies(&name, &locals, &mut visiting)?,
            );
        }

        self.order.retain(|name| !locals.contains(name));
        self.declared.retain(|name| !locals.contains(name));
        self.values.retain(|name, _| !locals.contains(name));
        self.dependencies = dependencies;
        Some(())
    }

    fn retained_dependents(
        &self,
        name: &JavaIdentifier,
        locals: &BTreeSet<JavaIdentifier>,
        visiting: &mut BTreeSet<JavaIdentifier>,
    ) -> Option<BTreeSet<JavaIdentifier>> {
        if !visiting.insert(name.clone()) {
            return None;
        }
        let mut roots = BTreeSet::new();
        for (dependent, dependencies) in &self.dependencies {
            if !dependencies.contains(name) {
                continue;
            }
            if locals.contains(dependent) {
                roots.extend(self.retained_dependents(dependent, locals, visiting)?);
            } else {
                roots.insert(dependent.clone());
            }
        }
        visiting.remove(name);
        Some(roots)
    }

    fn flatten_local_dependencies(
        &self,
        name: &JavaIdentifier,
        locals: &BTreeSet<JavaIdentifier>,
        visiting: &mut BTreeSet<JavaIdentifier>,
    ) -> Option<BTreeSet<JavaIdentifier>> {
        if !visiting.insert(name.clone()) {
            return None;
        }
        let mut flattened = BTreeSet::new();
        for dependency in self.dependencies.get(name).into_iter().flatten() {
            if locals.contains(dependency) {
                flattened.extend(self.flatten_local_dependencies(dependency, locals, visiting)?);
            } else {
                flattened.insert(dependency.clone());
            }
        }
        visiting.remove(name);
        Some(flattened)
    }

    fn binding_dependencies(&self, expression: &JavaExpr) -> BTreeSet<JavaIdentifier> {
        ExpressionNames::collect(expression)
            .into_iter()
            .filter(|name| self.values.contains_key(name))
            .collect()
    }

    fn resolve(&self, expression: JavaExpr) -> JavaExpr {
        ConstructorSubstitution {
            values: &self.values,
        }
        .rewrite_expression(expression)
    }

    fn record_evaluation(&mut self, name: &JavaIdentifier, value: &JavaExpr) {
        if !ConstructorBindings::stable(value) && !self.order.contains(name) {
            self.order.push(name.clone());
        }
    }

    fn extend_order(&mut self, order: &[JavaIdentifier]) {
        for name in order {
            if !self.order.contains(name) {
                self.order.push(name.clone());
            }
        }
    }
}

struct ReplayableExpression;

impl ReplayableExpression {
    fn check(expression: &JavaExpr) -> bool {
        match expression {
            JavaExpr::This
            | JavaExpr::QualifiedThis(_)
            | JavaExpr::Super
            | JavaExpr::Name(_)
            | JavaExpr::Literal(_)
            | JavaExpr::ClassLiteral(_) => true,
            JavaExpr::Unary { operand, .. }
            | JavaExpr::Cast { value: operand, .. }
            | JavaExpr::InstanceOf { value: operand, .. } => Self::check(operand),
            JavaExpr::Binary { left, right, .. } => Self::check(left) && Self::check(right),
            JavaExpr::Conditional {
                condition,
                when_true,
                when_false,
            } => Self::check(condition) && Self::check(when_true) && Self::check(when_false),
            _ => false,
        }
    }
}

struct ConstructorSubstitution<'a> {
    values: &'a BTreeMap<JavaIdentifier, JavaExpr>,
}

impl JavaAstRewriter for ConstructorSubstitution<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        match expression {
            JavaExpr::Name(name) => self
                .values
                .get(&name)
                .cloned()
                .unwrap_or(JavaExpr::Name(name)),
            JavaExpr::Conditional {
                condition,
                when_true,
                when_false,
            } => ConstructorConditional::reduce(*condition, *when_true, *when_false),
            expression => expression,
        }
    }
}

struct ConstructorConditional;

impl ConstructorConditional {
    fn reduce(condition: JavaExpr, when_true: JavaExpr, when_false: JavaExpr) -> JavaExpr {
        let when_true = Self::under_assumption(&condition, true, when_true);
        let when_false = Self::under_assumption(&condition, false, when_false);
        if when_true == when_false {
            return when_true;
        }
        JavaExpr::Conditional {
            condition: Box::new(condition),
            when_true: Box::new(when_true),
            when_false: Box::new(when_false),
        }
    }

    fn under_assumption(condition: &JavaExpr, truth: bool, expression: JavaExpr) -> JavaExpr {
        let JavaExpr::Conditional {
            condition: nested_condition,
            when_true,
            when_false,
        } = expression
        else {
            return expression;
        };
        if !ReplayableExpression::check(condition)
            || !ReplayableExpression::check(&nested_condition)
        {
            return JavaExpr::Conditional {
                condition: nested_condition,
                when_true,
                when_false,
            };
        }
        match PredicateRelation::between(condition, &nested_condition) {
            PredicateRelation::Equivalent => {
                if truth {
                    *when_true
                } else {
                    *when_false
                }
            }
            PredicateRelation::Complement => {
                if truth {
                    *when_false
                } else {
                    *when_true
                }
            }
            PredicateRelation::Independent => JavaExpr::Conditional {
                condition: nested_condition,
                when_true,
                when_false,
            },
        }
    }
}

enum PredicateRelation {
    Equivalent,
    Complement,
    Independent,
}

impl PredicateRelation {
    fn between(left: &JavaExpr, right: &JavaExpr) -> Self {
        if left == right {
            return Self::Equivalent;
        }
        if matches!(
            (left, right),
            (
                JavaExpr::Unary {
                    op: JavaUnaryOp::LogicalNot,
                    operand
                },
                other
            ) | (
                other,
                JavaExpr::Unary {
                    op: JavaUnaryOp::LogicalNot,
                    operand
                }
            ) if operand.as_ref() == other
        ) {
            return Self::Complement;
        }
        let (
            JavaExpr::Binary {
                left: left_operand,
                op: left_operator,
                right: left_right_operand,
            },
            JavaExpr::Binary {
                left: right_operand,
                op: right_operator,
                right: right_right_operand,
            },
        ) = (left, right)
        else {
            return Self::Independent;
        };
        let complementary_operator = matches!(
            (left_operator, right_operator),
            (JavaBinaryOp::Equal, JavaBinaryOp::NotEqual)
                | (JavaBinaryOp::NotEqual, JavaBinaryOp::Equal)
        );
        if complementary_operator
            && left_operand == right_operand
            && left_right_operand == right_right_operand
        {
            Self::Complement
        } else {
            Self::Independent
        }
    }
}

struct ExpressionNames;

impl ExpressionNames {
    fn collect(expression: &JavaExpr) -> BTreeSet<JavaIdentifier> {
        let mut names = BTreeSet::new();
        let mut pending = vec![expression];
        while let Some(expression) = pending.pop() {
            match expression {
                JavaExpr::Name(name) => {
                    names.insert(name.clone());
                }
                JavaExpr::This
                | JavaExpr::QualifiedThis(_)
                | JavaExpr::Super
                | JavaExpr::Literal(_)
                | JavaExpr::ClassLiteral(_)
                | JavaExpr::StaticField { .. } => {}
                JavaExpr::Field { owner, .. } => pending.push(owner),
                JavaExpr::ArrayAccess { array, index } => {
                    pending.push(index);
                    pending.push(array);
                }
                JavaExpr::Call { receiver, args, .. } => {
                    pending.extend(args.iter().rev());
                    pending.extend(receiver.iter().map(|value| value.as_ref()));
                }
                JavaExpr::MethodReference { receiver, .. } => pending.push(receiver),
                JavaExpr::Lambda { body, .. } => pending.push(body),
                JavaExpr::BlockLambda { .. } => {}
                JavaExpr::New {
                    enclosing, args, ..
                } => {
                    pending.extend(args.iter().rev());
                    pending.extend(enclosing.iter().map(|value| value.as_ref()));
                }
                JavaExpr::NewArray {
                    dimensions,
                    initializer,
                    ..
                } => {
                    pending.extend(initializer.iter().rev());
                    pending.extend(dimensions.iter().rev());
                }
                JavaExpr::Unary { operand, .. }
                | JavaExpr::Cast { value: operand, .. }
                | JavaExpr::InstanceOf { value: operand, .. } => pending.push(operand),
                JavaExpr::Update { target, .. } => pending.push(target),
                JavaExpr::Binary { left, right, .. } => {
                    pending.push(right);
                    pending.push(left);
                }
                JavaExpr::Conditional {
                    condition,
                    when_true,
                    when_false,
                } => {
                    pending.push(when_false);
                    pending.push(when_true);
                    pending.push(condition);
                }
                JavaExpr::Assignment { target, value, .. } => {
                    pending.push(value);
                    pending.push(target);
                }
            }
        }
        names
    }
}

struct ImmediateExpressionUses;

impl ImmediateExpressionUses {
    fn collect(statement: &JavaStmt) -> BTreeMap<JavaIdentifier, usize> {
        let mut uses = BTreeMap::new();
        Self::statement(statement, &mut uses);
        uses
    }

    fn collect_expressions(expressions: &[JavaExpr]) -> BTreeMap<JavaIdentifier, usize> {
        let mut uses = BTreeMap::new();
        for expression in expressions {
            Self::expression(expression, &mut uses);
        }
        uses
    }

    fn collect_statements(statements: &[JavaStmt]) -> BTreeMap<JavaIdentifier, usize> {
        let mut uses = BTreeMap::new();
        for statement in statements {
            Self::statement(statement, &mut uses);
        }
        uses
    }

    fn statement(statement: &JavaStmt, uses: &mut BTreeMap<JavaIdentifier, usize>) {
        match statement {
            JavaStmt::Block(statements) => {
                for statement in statements {
                    Self::statement(statement, uses);
                }
            }
            JavaStmt::Variable { value, .. } => {
                if let Some(value) = value {
                    Self::expression(value, uses);
                }
            }
            JavaStmt::Expression(expression) => Self::expression(expression, uses),
            JavaStmt::Assign { target, value, .. } => {
                Self::expression(target, uses);
                Self::expression(value, uses);
            }
            JavaStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => {
                Self::expression(condition, uses);
                Self::statement(then_stmt, uses);
                if let Some(else_stmt) = else_stmt {
                    Self::statement(else_stmt, uses);
                }
            }
            _ => {}
        }
    }

    fn expression(expression: &JavaExpr, uses: &mut BTreeMap<JavaIdentifier, usize>) {
        match expression {
            JavaExpr::Name(name) => *uses.entry(name.clone()).or_default() += 1,
            JavaExpr::This
            | JavaExpr::QualifiedThis(_)
            | JavaExpr::Super
            | JavaExpr::Literal(_)
            | JavaExpr::ClassLiteral(_)
            | JavaExpr::StaticField { .. } => {}
            // Captured names are evaluated when the nested function runs, not
            // when the enclosing expression is constructed.
            JavaExpr::Lambda { .. } | JavaExpr::BlockLambda { .. } => {}
            JavaExpr::Field { owner, .. } => Self::expression(owner, uses),
            JavaExpr::ArrayAccess { array, index } => {
                Self::expression(array, uses);
                Self::expression(index, uses);
            }
            JavaExpr::Call { receiver, args, .. } => {
                if let Some(receiver) = receiver {
                    Self::expression(receiver, uses);
                }
                for argument in args {
                    Self::expression(argument, uses);
                }
            }
            JavaExpr::MethodReference { receiver, .. } => Self::expression(receiver, uses),
            JavaExpr::New {
                enclosing, args, ..
            } => {
                if let Some(enclosing) = enclosing {
                    Self::expression(enclosing, uses);
                }
                for argument in args {
                    Self::expression(argument, uses);
                }
            }
            JavaExpr::NewArray {
                dimensions,
                initializer,
                ..
            } => {
                for dimension in dimensions {
                    Self::expression(dimension, uses);
                }
                for value in initializer {
                    Self::expression(value, uses);
                }
            }
            JavaExpr::Unary { operand, .. }
            | JavaExpr::Update {
                target: operand, ..
            }
            | JavaExpr::Cast { value: operand, .. }
            | JavaExpr::InstanceOf { value: operand, .. } => Self::expression(operand, uses),
            JavaExpr::Binary { left, right, .. } => {
                Self::expression(left, uses);
                Self::expression(right, uses);
            }
            JavaExpr::Conditional {
                condition,
                when_true,
                when_false,
            } => {
                Self::expression(condition, uses);
                Self::expression(when_true, uses);
                Self::expression(when_false, uses);
            }
            JavaExpr::Assignment { target, value, .. } => {
                Self::expression(target, uses);
                Self::expression(value, uses);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::{
        ConstructorCapturePrelude, ConstructorDataflow, ConstructorParameterGuards,
        ConstructorSyntaxRecovery, QualifiedThisTypes,
    };
    use crate::language::java::{
        JavaAssignOp, JavaAstRewriter, JavaBinaryOp, JavaCatch, JavaConstructorTarget, JavaExpr,
        JavaFieldDeclaration, JavaIdentifier, JavaLiteral, JavaMethodBody, JavaMethodDeclaration,
        JavaMethodDeclarationKind, JavaMethodParameter, JavaModifier, JavaStmt, JavaType,
        JavaTypeArgument, JavaTypeDeclaration, JavaTypeDeclarationKind, JavaTypeParameter,
        JavaUnaryOp, JavaUpdateOp,
    };

    #[test]
    fn casted_capture_stores_move_after_the_super_invocation() {
        let parameter = JavaIdentifier::from_dex("captured");
        let field = JavaIdentifier::from_dex("field");
        let constant_field = JavaIdentifier::from_dex("constantField");
        let mut statements = vec![
            JavaStmt::Assign {
                target: JavaExpr::Field {
                    owner: Box::new(JavaExpr::This),
                    name: field.clone(),
                },
                op: JavaAssignOp::Assign,
                value: JavaExpr::Cast {
                    ty: JavaType::source_class("java.util.List"),
                    value: Box::new(JavaExpr::Name(parameter.clone())),
                },
            },
            JavaStmt::Assign {
                target: JavaExpr::Field {
                    owner: Box::new(JavaExpr::This),
                    name: constant_field.clone(),
                },
                op: JavaAssignOp::Assign,
                value: JavaExpr::Literal(crate::language::java::JavaLiteral::Integer(0)),
            },
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                args: vec![JavaExpr::Literal(
                    crate::language::java::JavaLiteral::Integer(2),
                )],
            },
        ];

        ConstructorCapturePrelude::schedule(
            &mut statements,
            &BTreeSet::from([parameter]),
            &BTreeSet::from([field, constant_field]),
        );

        assert!(matches!(
            statements.first(),
            Some(JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                ..
            })
        ));
    }

    #[test]
    fn pre_super_field_value_uses_a_typed_carrier() {
        let class_name = JavaIdentifier::from_dex("CachedView");
        let context = JavaIdentifier::from_dex("context");
        let checked_context = JavaIdentifier::from_dex("checkedContext");
        let cache = JavaIdentifier::from_dex("cache");
        let map_type = JavaType::source_class("java.util.Map");
        let mut declaration = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Class,
            name: class_name.clone(),
            type_parameters: Vec::new(),
            extends: Some(JavaType::source_class("android.view.View")),
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: vec![JavaFieldDeclaration {
                annotations: Vec::new(),
                modifiers: Vec::new(),
                ty: map_type,
                name: cache.clone(),
                initializer: None,
            }],
            methods: vec![JavaMethodDeclaration {
                annotations: Vec::new(),
                modifiers: vec![JavaModifier::Public],
                compiler_generated: false,
                kind: JavaMethodDeclarationKind::Constructor,
                type_parameters: Vec::new(),
                return_type: None,
                name: Some(class_name),
                parameters: vec![JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: JavaType::source_class("android.content.Context"),
                    name: context.clone(),
                    varargs: false,
                }],
                throws: Vec::new(),
                body: Some(JavaMethodBody {
                    root: JavaStmt::Block(vec![
                        JavaStmt::Expression(JavaExpr::Call {
                            receiver: None,
                            owner: Some(JavaType::source_class("kotlin.jvm.internal.Intrinsics")),
                            type_arguments: Vec::new(),
                            method: JavaIdentifier::from_dex("checkNotNullParameter"),
                            args: vec![
                                JavaExpr::Name(context.clone()),
                                JavaExpr::Literal(JavaLiteral::String(
                                    crate::ir::Utf16String::from("context"),
                                )),
                            ],
                        }),
                        JavaStmt::Assign {
                            target: JavaExpr::Field {
                                owner: Box::new(JavaExpr::This),
                                name: cache.clone(),
                            },
                            op: JavaAssignOp::Assign,
                            value: JavaExpr::New {
                                enclosing: None,
                                ty: JavaType::source_class("java.util.LinkedHashMap"),
                                target_type: None,
                                args: Vec::new(),
                                anonymous_body: None,
                            },
                        },
                        JavaStmt::Variable {
                            ty: JavaType::source_class("android.content.Context"),
                            name: checked_context.clone(),
                            value: Some(JavaExpr::Call {
                                receiver: Some(Box::new(JavaExpr::Name(context))),
                                owner: None,
                                type_arguments: Vec::new(),
                                method: JavaIdentifier::from_dex("getApplicationContext"),
                                args: Vec::new(),
                            }),
                        },
                        JavaStmt::Expression(JavaExpr::Call {
                            receiver: None,
                            owner: Some(JavaType::source_class("kotlin.jvm.internal.Intrinsics")),
                            type_arguments: Vec::new(),
                            method: JavaIdentifier::from_dex("checkNotNull"),
                            args: vec![JavaExpr::Name(checked_context.clone())],
                        }),
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::Super,
                            args: vec![JavaExpr::Name(checked_context)],
                        },
                        JavaStmt::Expression(JavaExpr::Call {
                            receiver: None,
                            owner: Some(JavaType::source_class("com.example.Events")),
                            type_arguments: Vec::new(),
                            method: JavaIdentifier::from_dex("initialized"),
                            args: Vec::new(),
                        }),
                    ]),
                }),
            }],
            nested: Vec::new(),
        };

        ConstructorSyntaxRecovery::apply(&mut declaration);

        assert_eq!(declaration.methods.len(), 3);
        assert_eq!(declaration.nested.len(), 1);
        assert!(matches!(
            &declaration.methods[0].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::This,
                        args,
                    }] if matches!(args.as_slice(), [JavaExpr::Call { .. }])
                )
        ));
        assert!(matches!(
            &declaration.methods[1].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::Super,
                            ..
                        },
                        JavaStmt::Assign {
                            target: JavaExpr::Field { name, .. },
                            ..
                        },
                        JavaStmt::Expression(JavaExpr::Call { .. }),
                    ] if name == &cache
                )
        ));
        assert!(matches!(
            &declaration.methods[2].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(statements.first(), Some(JavaStmt::Expression(JavaExpr::Call { .. })))
                    && matches!(statements.get(1), Some(JavaStmt::Variable { value: Some(JavaExpr::New { .. }), .. }))
                    && matches!(statements.get(2), Some(JavaStmt::Variable { value: Some(JavaExpr::Call { .. }), .. }))
                    && matches!(statements.get(3), Some(JavaStmt::Expression(JavaExpr::Call { .. })))
                    && matches!(statements.last(), Some(JavaStmt::Return(Some(JavaExpr::New { .. }))))
        ));
        assert_eq!(declaration.nested[0].fields.len(), 2);
    }

    #[test]
    fn passive_pre_super_field_value_uses_normal_scheduling() {
        let class_name = JavaIdentifier::from_dex("Listener");
        let value = JavaIdentifier::from_dex("value");
        let field = JavaIdentifier::from_dex("field");
        let field_type = JavaType::source_class("com.example.Value");
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(class_name),
            parameters: vec![JavaMethodParameter {
                annotations: Vec::new(),
                ty: field_type.clone(),
                name: value.clone(),
                varargs: false,
            }],
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![
                    JavaStmt::Assign {
                        target: JavaExpr::Field {
                            owner: Box::new(JavaExpr::This),
                            name: field.clone(),
                        },
                        op: JavaAssignOp::Assign,
                        value: JavaExpr::Name(value),
                    },
                    JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        args: Vec::new(),
                    },
                ]),
            }),
        };

        assert!(ConstructorSyntaxRecovery::pre_super_field_value_helper(
            &constructor,
            &BTreeMap::from([(field, field_type)]),
            &[],
            JavaIdentifier::from_dex("computeConstructorFieldValues"),
            JavaIdentifier::from_dex("DexdecConstructorFieldValues"),
        )
        .is_none());
    }

    #[test]
    fn capture_store_before_parameter_guards_moves_after_super() {
        let captured = JavaIdentifier::from_dex("captured");
        let checked = JavaIdentifier::from_dex("checked");
        let field = JavaIdentifier::from_dex("field");
        let mut statements = vec![
            JavaStmt::Assign {
                target: JavaExpr::Field {
                    owner: Box::new(JavaExpr::This),
                    name: field.clone(),
                },
                op: JavaAssignOp::Assign,
                value: JavaExpr::Name(captured.clone()),
            },
            JavaStmt::Expression(JavaExpr::Call {
                receiver: None,
                owner: Some(JavaType::source_class("kotlin.jvm.internal.Intrinsics")),
                type_arguments: Vec::new(),
                method: JavaIdentifier::from_dex("checkNotNull"),
                args: vec![JavaExpr::Name(checked.clone())],
            }),
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                args: vec![JavaExpr::Name(checked.clone())],
            },
        ];

        ConstructorCapturePrelude::schedule(
            &mut statements,
            &BTreeSet::from([captured, checked]),
            &BTreeSet::from([field]),
        );

        assert!(matches!(
            statements.as_slice(),
            [
                JavaStmt::ConstructorInvocation {
                    target: JavaConstructorTarget::Super,
                    ..
                },
                JavaStmt::Assign {
                    target: JavaExpr::Field { .. },
                    ..
                },
                JavaStmt::Expression(JavaExpr::Call { method, .. }),
            ] if method == &JavaIdentifier::from_dex("checkNotNull")
        ));
    }

    #[test]
    fn zero_mask_constructor_guard_is_removed_before_super() {
        let mask = JavaIdentifier::from_dex("mask");
        let mut statements = vec![
            JavaStmt::If {
                condition: JavaExpr::Binary {
                    left: Box::new(JavaExpr::Binary {
                        left: Box::new(JavaExpr::Name(mask.clone())),
                        op: JavaBinaryOp::BitAnd,
                        right: Box::new(JavaExpr::Literal(JavaLiteral::Integer(0))),
                    }),
                    op: JavaBinaryOp::NotEqual,
                    right: Box::new(JavaExpr::Literal(JavaLiteral::Integer(0))),
                },
                then_stmt: Box::new(JavaStmt::Expression(JavaExpr::Call {
                    receiver: None,
                    owner: Some(JavaType::source_class("com.example.Serializer")),
                    type_arguments: Vec::new(),
                    method: JavaIdentifier::from_dex("throwMissingFieldException"),
                    args: Vec::new(),
                })),
                else_stmt: None,
            },
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                args: Vec::new(),
            },
        ];

        ConstructorSyntaxRecovery::remove_zero_mask_constructor_guards(
            &mut statements,
            &BTreeSet::from([mask]),
        );

        assert!(matches!(
            statements.as_slice(),
            [JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                args,
            }] if args.is_empty()
        ));
    }

    #[test]
    fn zero_mask_removal_preserves_locals_used_after_super() {
        let class_name = JavaIdentifier::from_dex("SerializableModel");
        let mask = JavaIdentifier::from_dex("mask");
        let default_value = JavaIdentifier::from_dex("defaultValue");
        let mut declaration = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Class,
            name: class_name.clone(),
            type_parameters: Vec::new(),
            extends: None,
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: Vec::new(),
            methods: vec![JavaMethodDeclaration {
                annotations: Vec::new(),
                modifiers: vec![JavaModifier::Public],
                compiler_generated: false,
                kind: JavaMethodDeclarationKind::Constructor,
                type_parameters: Vec::new(),
                return_type: None,
                name: Some(class_name),
                parameters: vec![JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: JavaType::int(),
                    name: mask.clone(),
                    varargs: false,
                }],
                throws: Vec::new(),
                body: Some(JavaMethodBody {
                    root: JavaStmt::Block(vec![
                        JavaStmt::Variable {
                            ty: JavaType::source_class("java.lang.Integer"),
                            name: default_value.clone(),
                            value: Some(JavaExpr::Call {
                                receiver: None,
                                owner: Some(JavaType::source_class("java.lang.Integer")),
                                type_arguments: Vec::new(),
                                method: JavaIdentifier::from_dex("valueOf"),
                                args: vec![JavaExpr::Literal(JavaLiteral::Integer(0))],
                            }),
                        },
                        JavaStmt::If {
                            condition: JavaExpr::Binary {
                                left: Box::new(JavaExpr::Binary {
                                    left: Box::new(JavaExpr::Name(mask)),
                                    op: JavaBinaryOp::BitAnd,
                                    right: Box::new(JavaExpr::Literal(JavaLiteral::Integer(0))),
                                }),
                                op: JavaBinaryOp::NotEqual,
                                right: Box::new(JavaExpr::Literal(JavaLiteral::Integer(0))),
                            },
                            then_stmt: Box::new(JavaStmt::Empty),
                            else_stmt: None,
                        },
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::Super,
                            args: Vec::new(),
                        },
                        JavaStmt::Expression(JavaExpr::Call {
                            receiver: None,
                            owner: Some(JavaType::source_class("com.example.Consumer")),
                            type_arguments: Vec::new(),
                            method: JavaIdentifier::from_dex("accept"),
                            args: vec![JavaExpr::Name(default_value.clone())],
                        }),
                    ]),
                }),
            }],
            nested: Vec::new(),
        };

        ConstructorSyntaxRecovery::apply(&mut declaration);

        assert!(matches!(
            &declaration.methods[0].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [
                        JavaStmt::Variable { name, .. },
                        JavaStmt::Expression(JavaExpr::Call { args, .. }),
                    ] if name == &default_value
                        && matches!(args.as_slice(), [JavaExpr::Name(name)] if name == &default_value)
                )
        ));
    }

    #[test]
    fn kotlin_parameter_guards_move_after_the_super_invocation() {
        let parameter = JavaIdentifier::from_dex("context");
        let alias = JavaIdentifier::from_dex("checkedContext");
        let mut statements = vec![
            JavaStmt::Expression(JavaExpr::Call {
                receiver: None,
                owner: Some(JavaType::source_class("kotlin.jvm.internal.Intrinsics")),
                type_arguments: Vec::new(),
                method: JavaIdentifier::from_dex("checkNotNullParameter"),
                args: vec![
                    JavaExpr::Name(parameter.clone()),
                    JavaExpr::Literal(crate::language::java::JavaLiteral::String(
                        crate::ir::Utf16String::from("context"),
                    )),
                ],
            }),
            JavaStmt::Variable {
                ty: JavaType::source_class("android.content.Context"),
                name: alias.clone(),
                value: Some(JavaExpr::Name(parameter.clone())),
            },
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                args: vec![JavaExpr::Name(alias)],
            },
        ];

        let parameters = BTreeSet::from([parameter]);
        let guards = ConstructorParameterGuards::take(&mut statements, &parameters);
        ConstructorSyntaxRecovery::schedule_arguments(&mut statements);
        ConstructorParameterGuards::restore(&mut statements, guards);

        assert!(matches!(
            statements.first(),
            Some(JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                ..
            })
        ));
    }

    #[test]
    fn kotlin_check_not_null_guard_moves_after_the_super_invocation() {
        let parameter = JavaIdentifier::from_dex("context");
        let mut statements = vec![
            JavaStmt::Expression(JavaExpr::Call {
                receiver: None,
                owner: Some(JavaType::source_class("kotlin.jvm.internal.Intrinsics")),
                type_arguments: Vec::new(),
                method: JavaIdentifier::from_dex("checkNotNull"),
                args: vec![JavaExpr::Name(parameter.clone())],
            }),
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                args: vec![JavaExpr::Name(parameter.clone())],
            },
        ];

        let parameters = BTreeSet::from([parameter]);
        let guards = ConstructorParameterGuards::take(&mut statements, &parameters);
        ConstructorSyntaxRecovery::schedule_arguments(&mut statements);
        ConstructorParameterGuards::restore(&mut statements, guards);

        assert!(matches!(
            statements.as_slice(),
            [
                JavaStmt::ConstructorInvocation {
                    target: JavaConstructorTarget::Super,
                    ..
                },
                JavaStmt::Expression(JavaExpr::Call { method, .. }),
            ] if method == &JavaIdentifier::from_dex("checkNotNull")
        ));
    }

    #[test]
    fn legacy_kotlin_throw_npe_guard_runs_before_super() {
        let class_name = JavaIdentifier::from_dex("GuardedView");
        let context = JavaIdentifier::from_dex("context");
        let initialized = JavaIdentifier::from_dex("initialized");
        let context_type = JavaType::source_class("android.content.Context");
        let mut declaration = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Class,
            name: class_name.clone(),
            type_parameters: Vec::new(),
            extends: Some(JavaType::source_class("android.view.View")),
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: vec![JavaFieldDeclaration {
                annotations: Vec::new(),
                modifiers: Vec::new(),
                ty: JavaType::boolean(),
                name: initialized.clone(),
                initializer: None,
            }],
            methods: vec![JavaMethodDeclaration {
                annotations: Vec::new(),
                modifiers: vec![JavaModifier::Public],
                compiler_generated: false,
                kind: JavaMethodDeclarationKind::Constructor,
                type_parameters: Vec::new(),
                return_type: None,
                name: Some(class_name),
                parameters: vec![JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: context_type,
                    name: context.clone(),
                    varargs: false,
                }],
                throws: Vec::new(),
                body: Some(JavaMethodBody {
                    root: JavaStmt::Block(vec![
                        JavaStmt::If {
                            condition: JavaExpr::Binary {
                                left: Box::new(JavaExpr::Name(context.clone())),
                                op: JavaBinaryOp::NotEqual,
                                right: Box::new(JavaExpr::Literal(JavaLiteral::Null)),
                            },
                            then_stmt: Box::new(JavaStmt::Block(vec![
                                JavaStmt::ConstructorInvocation {
                                    target: JavaConstructorTarget::Super,
                                    args: vec![JavaExpr::Name(context.clone())],
                                },
                                JavaStmt::Assign {
                                    target: JavaExpr::Field {
                                        owner: Box::new(JavaExpr::This),
                                        name: initialized,
                                    },
                                    op: JavaAssignOp::Assign,
                                    value: JavaExpr::Literal(JavaLiteral::Boolean(true)),
                                },
                                JavaStmt::Return(None),
                            ])),
                            else_stmt: None,
                        },
                        JavaStmt::Expression(JavaExpr::Call {
                            receiver: None,
                            owner: Some(JavaType::source_class("kotlin.jvm.internal.Intrinsics")),
                            type_arguments: Vec::new(),
                            method: JavaIdentifier::from_dex("throwNpe"),
                            args: Vec::new(),
                        }),
                    ]),
                }),
            }],
            nested: Vec::new(),
        };

        ConstructorSyntaxRecovery::apply(&mut declaration);

        assert_eq!(declaration.methods.len(), 3);
        assert_eq!(declaration.nested.len(), 1);
        assert!(matches!(
            &declaration.methods[0].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(statements.as_slice(), [JavaStmt::ConstructorInvocation {
                    target: JavaConstructorTarget::This,
                    ..
                }])
        ));
        let factory = declaration
            .methods
            .iter()
            .find(|method| {
                method
                    .name
                    .as_ref()
                    .is_some_and(|name| name.as_str() == "computeConstructorArguments")
            })
            .expect("constructor argument factory");
        assert!(matches!(
            &factory.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(statements.first(), Some(JavaStmt::If {
                    condition: JavaExpr::Binary { op: JavaBinaryOp::Equal, .. },
                    ..
                }))
        ));
    }

    #[test]
    fn generated_report_null_is_a_constructor_guard_failure() {
        let failure = JavaStmt::Expression(JavaExpr::Call {
            receiver: None,
            owner: Some(JavaType::source_class("example.Guarded")),
            type_arguments: Vec::new(),
            method: JavaIdentifier::from_dex("$$$reportNull$$$0"),
            args: vec![JavaExpr::Literal(JavaLiteral::Integer(0))],
        });

        assert!(ConstructorSyntaxRecovery::generated_null_guard_failure(
            &failure
        ));
    }

    #[test]
    fn nested_generated_null_guards_flatten_before_constructor_invocation() {
        let first = JavaIdentifier::from_dex("first");
        let second = JavaIdentifier::from_dex("second");
        let condition = |parameter: &JavaIdentifier| JavaExpr::Binary {
            left: Box::new(JavaExpr::Name(parameter.clone())),
            op: JavaBinaryOp::NotEqual,
            right: Box::new(JavaExpr::Literal(JavaLiteral::Null)),
        };
        let failure = |index| {
            JavaStmt::Expression(JavaExpr::Call {
                receiver: None,
                owner: Some(JavaType::source_class("example.Guarded")),
                type_arguments: Vec::new(),
                method: JavaIdentifier::from_dex("$$$reportNull$$$0"),
                args: vec![JavaExpr::Literal(JavaLiteral::Integer(index))],
            })
        };
        let statements = vec![
            JavaStmt::If {
                condition: condition(&first),
                then_stmt: Box::new(JavaStmt::Block(vec![
                    JavaStmt::If {
                        condition: condition(&second),
                        then_stmt: Box::new(JavaStmt::Block(vec![
                            JavaStmt::ConstructorInvocation {
                                target: JavaConstructorTarget::Super,
                                args: vec![
                                    JavaExpr::Name(first.clone()),
                                    JavaExpr::Name(second.clone()),
                                ],
                            },
                            JavaStmt::Return(None),
                        ])),
                        else_stmt: None,
                    },
                    failure(1),
                ])),
                else_stmt: None,
            },
            failure(0),
        ];

        let (guards, invocation, trailing, terminates) =
            ConstructorSyntaxRecovery::flatten_generated_null_guard_statements(
                &statements,
                &BTreeSet::from([first, second]),
            )
            .expect("nested generated guards");

        assert_eq!(guards.len(), 2);
        assert!(matches!(invocation, JavaStmt::ConstructorInvocation { .. }));
        assert!(trailing.is_empty());
        assert!(terminates);
    }

    #[test]
    fn static_field_bindings_inline_into_constructor_arguments() {
        let binding = JavaIdentifier::from_dex("trueValue");
        let value = JavaExpr::StaticField {
            owner: JavaType::source_class("java.lang.Boolean"),
            name: JavaIdentifier::from_dex("TRUE"),
        };
        let mut statements = vec![
            JavaStmt::Variable {
                ty: JavaType::source_class("java.lang.Boolean"),
                name: binding.clone(),
                value: Some(value.clone()),
            },
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                args: vec![JavaExpr::Name(binding.clone()), JavaExpr::Name(binding)],
            },
        ];

        ConstructorSyntaxRecovery::schedule_arguments(&mut statements);

        assert!(matches!(
            statements.as_slice(),
            [JavaStmt::ConstructorInvocation { args, .. }]
                if args == &vec![value.clone(), value]
        ));
    }

    #[test]
    fn cached_boxing_bindings_inline_into_constructor_arguments() {
        let binding = JavaIdentifier::from_dex("valueOf");
        let value = JavaExpr::Call {
            receiver: None,
            owner: Some(JavaType::source_class("Integer")),
            type_arguments: Vec::new(),
            method: JavaIdentifier::from_dex("valueOf"),
            args: vec![JavaExpr::Literal(JavaLiteral::Integer(1))],
        };
        let mut statements = vec![
            JavaStmt::Variable {
                ty: JavaType::source_class("java.lang.Integer"),
                name: binding.clone(),
                value: Some(value.clone()),
            },
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                args: vec![JavaExpr::Name(binding.clone()), JavaExpr::Name(binding)],
            },
        ];

        ConstructorSyntaxRecovery::schedule_arguments(&mut statements);

        assert!(matches!(
            statements.as_slice(),
            [JavaStmt::ConstructorInvocation { args, .. }]
                if args == &vec![value.clone(), value]
        ));
    }

    #[test]
    fn uncached_boxing_bindings_are_not_duplicated() {
        let binding = JavaIdentifier::from_dex("valueOf");
        let value = JavaExpr::Call {
            receiver: None,
            owner: Some(JavaType::source_class("java.lang.Integer")),
            type_arguments: Vec::new(),
            method: JavaIdentifier::from_dex("valueOf"),
            args: vec![JavaExpr::Literal(JavaLiteral::Integer(9000))],
        };
        let mut statements = vec![
            JavaStmt::Variable {
                ty: JavaType::source_class("java.lang.Integer"),
                name: binding.clone(),
                value: Some(value),
            },
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                args: vec![JavaExpr::Name(binding.clone()), JavaExpr::Name(binding)],
            },
        ];

        ConstructorSyntaxRecovery::schedule_arguments(&mut statements);

        assert!(matches!(
            statements.as_slice(),
            [
                JavaStmt::Variable { .. },
                JavaStmt::ConstructorInvocation { .. }
            ]
        ));
    }

    #[test]
    fn shared_uncached_boxing_uses_a_helper_constructor() {
        let class_name = JavaIdentifier::from_dex("SharedBoxing");
        let binding = JavaIdentifier::from_dex("valueOf");
        let value = JavaExpr::Call {
            receiver: None,
            owner: Some(JavaType::source_class("java.lang.Long")),
            type_arguments: Vec::new(),
            method: JavaIdentifier::from_dex("valueOf"),
            args: vec![JavaExpr::Literal(JavaLiteral::Long(200))],
        };
        let mut declaration = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Class,
            name: class_name.clone(),
            type_parameters: Vec::new(),
            extends: Some(JavaType::source_class("example.Parent")),
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: Vec::new(),
            methods: vec![JavaMethodDeclaration {
                annotations: Vec::new(),
                modifiers: vec![JavaModifier::Public],
                compiler_generated: false,
                kind: JavaMethodDeclarationKind::Constructor,
                type_parameters: Vec::new(),
                return_type: None,
                name: Some(class_name),
                parameters: Vec::new(),
                throws: Vec::new(),
                body: Some(JavaMethodBody {
                    root: JavaStmt::Block(vec![
                        JavaStmt::Variable {
                            ty: JavaType::source_class("java.lang.Long"),
                            name: binding.clone(),
                            value: Some(value.clone()),
                        },
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::Super,
                            args: vec![
                                JavaExpr::Literal(JavaLiteral::String(
                                    crate::ir::Utf16String::from("key"),
                                )),
                                JavaExpr::Name(binding.clone()),
                                JavaExpr::Name(binding.clone()),
                            ],
                        },
                    ]),
                }),
            }],
            nested: Vec::new(),
        };

        ConstructorSyntaxRecovery::apply(&mut declaration);

        assert_eq!(declaration.methods.len(), 2);
        let JavaStmt::Block(original) = &declaration.methods[0].body.as_ref().unwrap().root else {
            panic!("original constructor body");
        };
        assert!(matches!(
            original.as_slice(),
            [JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::This,
                args,
            }] if args == &vec![value]
        ));
        let helper = &declaration.methods[1];
        assert_eq!(helper.modifiers, vec![JavaModifier::Private]);
        assert_eq!(
            helper
                .parameters
                .iter()
                .map(|parameter| &parameter.ty)
                .collect::<Vec<_>>(),
            vec![&JavaType::source_class("java.lang.Long")]
        );
        let JavaStmt::Block(helper_body) = &helper.body.as_ref().unwrap().root else {
            panic!("helper constructor body");
        };
        assert!(matches!(
            helper_body.as_slice(),
            [JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                args,
            }] if matches!(
                args.as_slice(),
                [JavaExpr::Literal(_), JavaExpr::Name(left), JavaExpr::Name(right)]
                    if left == &binding && right == &binding
            )
        ));
    }

    #[test]
    fn shared_boxing_signature_collision_falls_back_to_carrier() {
        let class_name = JavaIdentifier::from_dex("SharedBoxing");
        let binding = JavaIdentifier::from_dex("valueOf");
        let long_type = JavaType::source_class("java.lang.Long");
        let constructor = |parameters, statements| JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(class_name.clone()),
            parameters,
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(statements),
            }),
        };
        let mut declaration = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Class,
            name: class_name.clone(),
            type_parameters: Vec::new(),
            extends: Some(JavaType::source_class("example.Parent")),
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: Vec::new(),
            methods: vec![
                constructor(
                    Vec::new(),
                    vec![
                        JavaStmt::Variable {
                            ty: long_type.clone(),
                            name: binding.clone(),
                            value: Some(JavaExpr::Call {
                                receiver: None,
                                owner: Some(long_type.clone()),
                                type_arguments: Vec::new(),
                                method: JavaIdentifier::from_dex("valueOf"),
                                args: vec![JavaExpr::Literal(JavaLiteral::Long(200))],
                            }),
                        },
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::Super,
                            args: vec![JavaExpr::Name(binding.clone()), JavaExpr::Name(binding)],
                        },
                    ],
                ),
                constructor(
                    vec![JavaMethodParameter {
                        annotations: Vec::new(),
                        ty: long_type,
                        name: JavaIdentifier::from_dex("existing"),
                        varargs: false,
                    }],
                    vec![JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        args: Vec::new(),
                    }],
                ),
            ],
            nested: Vec::new(),
        };

        ConstructorSyntaxRecovery::apply(&mut declaration);

        assert_eq!(declaration.methods.len(), 4);
        assert_eq!(declaration.nested.len(), 1);
        assert!(matches!(
            &declaration.methods[0].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::This,
                        args,
                    }] if matches!(args.as_slice(), [JavaExpr::Call { .. }])
                )
        ));
        assert!(matches!(
            &declaration.methods[2].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        args,
                    }] if matches!(
                        args.as_slice(),
                        [JavaExpr::Field { name: left, .. }, JavaExpr::Field { name: right, .. }]
                            if left != right
                    )
                )
        ));
        assert_eq!(declaration.nested[0].fields.len(), 2);
        assert!(declaration.nested[0]
            .fields
            .iter()
            .all(|field| field.ty == JavaType::source_class("java.lang.Long")));
    }

    #[test]
    fn mutable_constructor_argument_uses_a_factory_and_helper() {
        let class_name = JavaIdentifier::from_dex("MutableArgument");
        let binding = JavaIdentifier::from_dex("config");
        let config_type = JavaType::source_class("example.Config");
        let mut declaration = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Class,
            name: class_name.clone(),
            type_parameters: Vec::new(),
            extends: Some(JavaType::source_class("example.Parent")),
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: Vec::new(),
            methods: vec![JavaMethodDeclaration {
                annotations: Vec::new(),
                modifiers: vec![JavaModifier::Public],
                compiler_generated: false,
                kind: JavaMethodDeclarationKind::Constructor,
                type_parameters: Vec::new(),
                return_type: None,
                name: Some(class_name),
                parameters: Vec::new(),
                throws: Vec::new(),
                body: Some(JavaMethodBody {
                    root: JavaStmt::Block(vec![
                        JavaStmt::Variable {
                            ty: config_type.clone(),
                            name: binding.clone(),
                            value: Some(JavaExpr::New {
                                enclosing: None,
                                ty: config_type.clone(),
                                target_type: None,
                                args: Vec::new(),
                                anonymous_body: None,
                            }),
                        },
                        JavaStmt::Expression(JavaExpr::Call {
                            receiver: Some(Box::new(JavaExpr::Name(binding.clone()))),
                            owner: None,
                            type_arguments: Vec::new(),
                            method: JavaIdentifier::from_dex("setValue"),
                            args: vec![JavaExpr::Literal(JavaLiteral::String(
                                crate::ir::Utf16String::from("value"),
                            ))],
                        }),
                        JavaStmt::Variable {
                            ty: JavaType::source_class("kotlin.Unit"),
                            name: JavaIdentifier::from_dex("instance"),
                            value: Some(JavaExpr::StaticField {
                                owner: JavaType::source_class("kotlin.Unit"),
                                name: JavaIdentifier::from_dex("INSTANCE"),
                            }),
                        },
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::Super,
                            args: vec![
                                JavaExpr::Literal(JavaLiteral::String(
                                    crate::ir::Utf16String::from("key"),
                                )),
                                JavaExpr::Name(binding.clone()),
                            ],
                        },
                    ]),
                }),
            }],
            nested: Vec::new(),
        };

        ConstructorSyntaxRecovery::apply(&mut declaration);

        assert_eq!(declaration.methods.len(), 3);
        let JavaStmt::Block(original) = &declaration.methods[0].body.as_ref().unwrap().root else {
            panic!("original constructor body");
        };
        let factory_name = match original.as_slice() {
            [JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::This,
                args,
            }] => match args.as_slice() {
                [JavaExpr::Call {
                    receiver: None,
                    owner: None,
                    method,
                    args,
                    ..
                }] if args.is_empty() => method.clone(),
                _ => panic!("factory call argument"),
            },
            _ => panic!("delegating constructor"),
        };
        let helper = &declaration.methods[1];
        assert_eq!(helper.modifiers, vec![JavaModifier::Private]);
        assert_eq!(helper.parameters.len(), 1);
        assert_eq!(helper.parameters[0].ty, config_type.clone());
        let factory = &declaration.methods[2];
        assert_eq!(
            factory.modifiers,
            vec![JavaModifier::Private, JavaModifier::Static]
        );
        assert_eq!(factory.name.as_ref(), Some(&factory_name));
        assert_eq!(factory.return_type, Some(config_type));
        assert!(matches!(
            &factory.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(statements.last(), Some(JavaStmt::Return(Some(JavaExpr::Name(name))))
                    if name == &binding)
        ));
    }

    #[test]
    fn mutable_constructor_factory_rejects_nonliteral_setter_arguments() {
        let binding = JavaIdentifier::from_dex("config");
        let statement = JavaStmt::Expression(JavaExpr::Call {
            receiver: Some(Box::new(JavaExpr::Name(binding.clone()))),
            owner: None,
            type_arguments: Vec::new(),
            method: JavaIdentifier::from_dex("setValue"),
            args: vec![JavaExpr::Name(JavaIdentifier::from_dex("external"))],
        });

        assert!(!ConstructorSyntaxRecovery::mutable_factory_statements(
            &[statement],
            &binding,
        ));
    }

    #[test]
    fn post_super_binding_uses_a_generic_factory_and_helper() {
        let class_name = JavaIdentifier::from_dex("PostSuperBinding");
        let type_variable = JavaIdentifier::from_dex("T");
        let parameter = JavaIdentifier::from_dex("initialValue");
        let binding = JavaIdentifier::from_dex("subject");
        let subject_type = JavaType::source_class("example.Subject");
        let guard = JavaStmt::Expression(JavaExpr::Call {
            receiver: None,
            owner: Some(JavaType::source_class("kotlin.jvm.internal.Intrinsics")),
            type_arguments: Vec::new(),
            method: JavaIdentifier::from_dex("checkNotNullParameter"),
            args: vec![
                JavaExpr::Name(parameter.clone()),
                JavaExpr::Literal(JavaLiteral::String(crate::ir::Utf16String::from(
                    "initialValue",
                ))),
            ],
        });
        let mut declaration = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Class,
            name: class_name.clone(),
            type_parameters: vec![JavaTypeParameter {
                name: type_variable.clone(),
                bounds: Vec::new(),
            }],
            extends: Some(JavaType::source_class("example.Parent")),
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: Vec::new(),
            methods: vec![JavaMethodDeclaration {
                annotations: Vec::new(),
                modifiers: vec![JavaModifier::Public],
                compiler_generated: false,
                kind: JavaMethodDeclarationKind::Constructor,
                type_parameters: Vec::new(),
                return_type: None,
                name: Some(class_name),
                parameters: vec![JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: JavaType::Variable(type_variable.clone()),
                    name: parameter.clone(),
                    varargs: false,
                }],
                throws: Vec::new(),
                body: Some(JavaMethodBody {
                    root: JavaStmt::Block(vec![
                        guard,
                        JavaStmt::Variable {
                            ty: subject_type.clone(),
                            name: binding.clone(),
                            value: Some(JavaExpr::Call {
                                receiver: None,
                                owner: Some(subject_type.clone()),
                                type_arguments: Vec::new(),
                                method: JavaIdentifier::from_dex("create"),
                                args: Vec::new(),
                            }),
                        },
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::Super,
                            args: Vec::new(),
                        },
                        JavaStmt::Assign {
                            target: JavaExpr::Field {
                                owner: Box::new(JavaExpr::This),
                                name: JavaIdentifier::from_dex("subject"),
                            },
                            op: JavaAssignOp::Assign,
                            value: JavaExpr::Name(binding.clone()),
                        },
                    ]),
                }),
            }],
            nested: Vec::new(),
        };

        ConstructorSyntaxRecovery::apply(&mut declaration);

        assert_eq!(declaration.methods.len(), 3);
        let helper = &declaration.methods[1];
        assert_eq!(helper.modifiers, vec![JavaModifier::Private]);
        assert_eq!(helper.parameters.len(), 2);
        assert_eq!(helper.parameters[1].ty, subject_type.clone());
        assert!(matches!(
            &helper.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(statements.as_slice(), [JavaStmt::Assign { value: JavaExpr::Name(name), .. }]
                    if name == &binding)
        ));
        let factory = &declaration.methods[2];
        assert_eq!(
            factory.modifiers,
            vec![JavaModifier::Private, JavaModifier::Static]
        );
        assert_eq!(factory.return_type, Some(subject_type));
        assert_eq!(
            factory.type_parameters,
            vec![JavaTypeParameter {
                name: type_variable,
                bounds: Vec::new(),
            }]
        );
        assert!(matches!(
            &factory.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if statements.len() == 3
                    && matches!(statements.last(), Some(JavaStmt::Return(Some(JavaExpr::Name(name))))
                        if name == &binding)
        ));
    }

    #[test]
    fn post_super_factory_rejects_instance_calls() {
        let parameters = BTreeSet::from([JavaIdentifier::from_dex("value")]);
        let expression = JavaExpr::Call {
            receiver: Some(Box::new(JavaExpr::Name(JavaIdentifier::from_dex(
                "receiver",
            )))),
            owner: None,
            type_arguments: Vec::new(),
            method: JavaIdentifier::from_dex("create"),
            args: Vec::new(),
        };

        assert!(!ConstructorSyntaxRecovery::static_factory_expression(
            &expression,
            &parameters,
        ));
    }

    #[test]
    fn post_super_factory_rejects_out_of_scope_type_variables() {
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: Vec::new(),
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("Nested")),
            parameters: vec![JavaMethodParameter {
                annotations: Vec::new(),
                ty: JavaType::Variable(JavaIdentifier::from_dex("OuterT")),
                name: JavaIdentifier::from_dex("value"),
                varargs: false,
            }],
            throws: Vec::new(),
            body: None,
        };

        assert!(!ConstructorSyntaxRecovery::static_factory_types_in_scope(
            &constructor,
            &JavaType::source_class("example.Subject"),
            &[],
        ));
    }

    #[test]
    fn discarded_constructor_call_moves_into_a_super_argument_factory() {
        let class_name = JavaIdentifier::from_dex("Dialog");
        let context = JavaIdentifier::from_dex("context");
        let parameters = JavaIdentifier::from_dex("parameters");
        let guard = |name: &JavaIdentifier, label: &str| {
            JavaStmt::Expression(JavaExpr::Call {
                receiver: None,
                owner: Some(JavaType::source_class("kotlin.jvm.internal.Intrinsics")),
                type_arguments: Vec::new(),
                method: JavaIdentifier::from_dex("checkNotNullParameter"),
                args: vec![
                    JavaExpr::Name(name.clone()),
                    JavaExpr::Literal(JavaLiteral::String(crate::ir::Utf16String::from(label))),
                ],
            })
        };
        let mut declaration = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Class,
            name: class_name.clone(),
            type_parameters: Vec::new(),
            extends: Some(JavaType::source_class("example.Parent")),
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: Vec::new(),
            methods: vec![JavaMethodDeclaration {
                annotations: Vec::new(),
                modifiers: vec![JavaModifier::Public],
                compiler_generated: false,
                kind: JavaMethodDeclarationKind::Constructor,
                type_parameters: Vec::new(),
                return_type: None,
                name: Some(class_name),
                parameters: vec![
                    JavaMethodParameter {
                        annotations: Vec::new(),
                        ty: JavaType::source_class("example.Context"),
                        name: context.clone(),
                        varargs: false,
                    },
                    JavaMethodParameter {
                        annotations: Vec::new(),
                        ty: JavaType::source_class("example.Parameters"),
                        name: parameters.clone(),
                        varargs: false,
                    },
                ],
                throws: Vec::new(),
                body: Some(JavaMethodBody {
                    root: JavaStmt::Block(vec![
                        guard(&context, "context"),
                        guard(&parameters, "parameters"),
                        JavaStmt::Expression(JavaExpr::Call {
                            receiver: Some(Box::new(JavaExpr::Name(parameters.clone()))),
                            owner: None,
                            type_arguments: Vec::new(),
                            method: JavaIdentifier::from_dex("isPortrait"),
                            args: Vec::new(),
                        }),
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::Super,
                            args: vec![
                                JavaExpr::Name(context),
                                JavaExpr::Literal(JavaLiteral::Integer(2131953226)),
                            ],
                        },
                        JavaStmt::Assign {
                            target: JavaExpr::Field {
                                owner: Box::new(JavaExpr::This),
                                name: JavaIdentifier::from_dex("parameters"),
                            },
                            op: JavaAssignOp::Assign,
                            value: JavaExpr::Name(parameters),
                        },
                    ]),
                }),
            }],
            nested: Vec::new(),
        };

        ConstructorSyntaxRecovery::apply(&mut declaration);

        assert_eq!(declaration.methods.len(), 2);
        let JavaStmt::Block(constructor) = &declaration.methods[0].body.as_ref().unwrap().root
        else {
            panic!("constructor body");
        };
        assert!(matches!(
            constructor.as_slice(),
            [
                JavaStmt::ConstructorInvocation {
                    target: JavaConstructorTarget::Super,
                    args,
                },
                JavaStmt::Assign { .. },
            ] if matches!(args.as_slice(), [JavaExpr::Name(_), JavaExpr::Call { .. }])
        ));
        let factory = &declaration.methods[1];
        assert_eq!(
            factory.modifiers,
            vec![JavaModifier::Private, JavaModifier::Static]
        );
        assert_eq!(factory.return_type, Some(JavaType::int()));
        assert!(matches!(
            &factory.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if statements.len() == 4
                    && matches!(
                        statements.last(),
                        Some(JavaStmt::Return(Some(JavaExpr::Literal(JavaLiteral::Integer(2131953226)))))
                    )
        ));
    }

    #[test]
    fn method_call_super_argument_uses_recorded_return_type() {
        let context = JavaIdentifier::from_dex("context");
        let source = JavaIdentifier::from_dex("source");
        let provider = JavaIdentifier::from_dex("provider");
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("ViewHolder")),
            parameters: vec![
                JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: JavaType::source_class("android.content.Context"),
                    name: context.clone(),
                    varargs: false,
                },
                JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: JavaType::source_class("example.Source"),
                    name: source.clone(),
                    varargs: false,
                },
            ],
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![
                    JavaStmt::Variable {
                        ty: JavaType::source_class("example.Provider"),
                        name: provider.clone(),
                        value: Some(JavaExpr::Call {
                            receiver: Some(Box::new(JavaExpr::Name(source))),
                            owner: None,
                            type_arguments: Vec::new(),
                            method: JavaIdentifier::from_dex("getProvider"),
                            args: Vec::new(),
                        }),
                    },
                    JavaStmt::Expression(JavaExpr::Call {
                        receiver: None,
                        owner: Some(JavaType::source_class("kotlin.jvm.internal.Intrinsics")),
                        type_arguments: Vec::new(),
                        method: JavaIdentifier::from_dex("checkNotNull"),
                        args: vec![JavaExpr::Name(provider.clone())],
                    }),
                    JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        args: vec![JavaExpr::Call {
                            receiver: Some(Box::new(JavaExpr::Name(provider))),
                            owner: None,
                            type_arguments: Vec::new(),
                            method: JavaIdentifier::from_dex("createView"),
                            args: vec![JavaExpr::Name(context)],
                        }],
                    },
                    JavaStmt::Expression(JavaExpr::Call {
                        receiver: None,
                        owner: Some(JavaType::source_class("example.Events")),
                        type_arguments: Vec::new(),
                        method: JavaIdentifier::from_dex("initialized"),
                        args: Vec::new(),
                    }),
                ]),
            }),
        };

        let view_type = JavaType::source_class("android.view.View");
        let mut method_return_types = BTreeMap::from([(
            (
                JavaType::source_class("example.Provider"),
                JavaIdentifier::from_dex("createView"),
                1,
            ),
            Some(view_type.clone()),
        )]);
        let (body, factory) = ConstructorSyntaxRecovery::super_argument_prelude_factory(
            &constructor,
            &[],
            JavaIdentifier::from_dex("evaluateConstructorArgument"),
            &method_return_types,
        )
        .expect("typed factory");

        assert!(matches!(
            body.root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::Super,
                            args,
                        },
                        JavaStmt::Expression(JavaExpr::Call { .. }),
                    ] if matches!(args.as_slice(), [JavaExpr::Call { .. }])
                )
        ));
        assert!(factory.type_parameters.is_empty());
        assert_eq!(factory.return_type, Some(view_type));
        assert!(matches!(
            &factory.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if statements.len() == 3
                    && matches!(
                        statements.last(),
                        Some(JavaStmt::Return(Some(JavaExpr::Call { .. })))
                    )
        ));
        method_return_types.values_mut().for_each(|ty| *ty = None);
        assert!(ConstructorSyntaxRecovery::super_argument_prelude_factory(
            &constructor,
            &[],
            JavaIdentifier::from_dex("evaluateConstructorArgument"),
            &method_return_types,
        )
        .is_none());
    }

    #[test]
    fn static_field_receiver_uses_unique_recorded_return_type() {
        let input = JavaIdentifier::from_dex("input");
        let compiler = JavaIdentifier::from_dex("compiler");
        let compile = JavaIdentifier::from_dex("compile");
        let compiler_field = JavaExpr::StaticField {
            owner: JavaType::source_class("example.Compilers"),
            name: JavaIdentifier::from_dex("DEFAULT"),
        };
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("PatternPredicate")),
            parameters: vec![JavaMethodParameter {
                annotations: Vec::new(),
                ty: JavaType::source_class("String"),
                name: input.clone(),
                varargs: false,
            }],
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![
                    JavaStmt::Variable {
                        ty: JavaType::source_class("example.Compiler"),
                        name: compiler,
                        value: Some(compiler_field.clone()),
                    },
                    JavaStmt::Expression(JavaExpr::Call {
                        receiver: None,
                        owner: Some(JavaType::source_class("example.Preconditions")),
                        type_arguments: Vec::new(),
                        method: JavaIdentifier::from_dex("checkNotNull"),
                        args: vec![JavaExpr::Name(input.clone())],
                    }),
                    JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        args: vec![JavaExpr::Call {
                            receiver: Some(Box::new(compiler_field)),
                            owner: None,
                            type_arguments: Vec::new(),
                            method: compile.clone(),
                            args: vec![JavaExpr::Name(input)],
                        }],
                    },
                ]),
            }),
        };
        let pattern_type = JavaType::source_class("example.Pattern");
        let mut method_return_types = BTreeMap::from([(
            (
                JavaType::source_class("example.CompilerApi"),
                compile.clone(),
                1,
            ),
            Some(pattern_type.clone()),
        )]);

        let (_, factory) = ConstructorSyntaxRecovery::super_argument_prelude_factory(
            &constructor,
            &[],
            JavaIdentifier::from_dex("evaluateConstructorArgument"),
            &method_return_types,
        )
        .expect("a unique source method return should type the factory");

        assert_eq!(factory.return_type, Some(pattern_type));
        assert!(matches!(
            &factory.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if statements.len() == 3
                    && matches!(statements.last(), Some(JavaStmt::Return(Some(JavaExpr::Call { .. }))))
        ));

        method_return_types.insert(
            (JavaType::source_class("example.OtherCompiler"), compile, 1),
            Some(JavaType::source_class("example.OtherPattern")),
        );
        assert!(ConstructorSyntaxRecovery::super_argument_prelude_factory(
            &constructor,
            &[],
            JavaIdentifier::from_dex("evaluateConstructorArgument"),
            &method_return_types,
        )
        .is_none());
    }

    #[test]
    fn configured_super_argument_uses_a_typed_factory() {
        let first = JavaIdentifier::from_dex("first");
        let last = JavaIdentifier::from_dex("last");
        let prepared = JavaIdentifier::from_dex("prepared");
        let prepared_type = JavaType::source_class("example.Prepared");
        let mut constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("Subject")),
            parameters: vec![
                JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: JavaType::source_class("example.First"),
                    name: first.clone(),
                    varargs: false,
                },
                JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: JavaType::source_class("example.Last"),
                    name: last.clone(),
                    varargs: false,
                },
            ],
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![
                    JavaStmt::Variable {
                        ty: prepared_type.clone(),
                        name: prepared.clone(),
                        value: Some(JavaExpr::New {
                            enclosing: None,
                            ty: prepared_type.clone(),
                            target_type: None,
                            args: Vec::new(),
                            anonymous_body: None,
                        }),
                    },
                    JavaStmt::Expression(JavaExpr::Call {
                        receiver: Some(Box::new(JavaExpr::Name(prepared.clone()))),
                        owner: None,
                        type_arguments: Vec::new(),
                        method: JavaIdentifier::from_dex("configure"),
                        args: Vec::new(),
                    }),
                    JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        args: vec![
                            JavaExpr::Name(first),
                            JavaExpr::Name(prepared.clone()),
                            JavaExpr::Name(last),
                        ],
                    },
                    JavaStmt::Expression(JavaExpr::Call {
                        receiver: None,
                        owner: Some(JavaType::source_class("example.Events")),
                        type_arguments: Vec::new(),
                        method: JavaIdentifier::from_dex("initialized"),
                        args: Vec::new(),
                    }),
                ]),
            }),
        };

        let (body, factory) = ConstructorSyntaxRecovery::prepared_super_argument_factory(
            &constructor,
            &[],
            JavaIdentifier::from_dex("evaluateConstructorArgument"),
        )
        .expect("configured argument factory");

        assert!(matches!(
            body.root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::Super,
                            args,
                        },
                        JavaStmt::Expression(JavaExpr::Call { .. }),
                    ] if matches!(
                        args.as_slice(),
                        [JavaExpr::Name(_), JavaExpr::Call { .. }, JavaExpr::Name(_)]
                    )
                )
        ));
        assert_eq!(factory.return_type, Some(prepared_type));
        assert!(matches!(
            &factory.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if statements.len() == 3
                    && matches!(
                        statements.last(),
                        Some(JavaStmt::Return(Some(JavaExpr::Name(name)))) if name == &prepared
                    )
        ));

        let JavaStmt::Block(statements) = &mut constructor.body.as_mut().unwrap().root else {
            panic!("constructor block");
        };
        statements.remove(1);
        assert!(ConstructorSyntaxRecovery::prepared_super_argument_factory(
            &constructor,
            &[],
            JavaIdentifier::from_dex("evaluateConstructorArgument"),
        )
        .is_none());
    }

    #[test]
    fn super_argument_factory_rejects_effectful_earlier_arguments() {
        let parameters = BTreeSet::from([JavaIdentifier::from_dex("value")]);
        let expression = JavaExpr::Call {
            receiver: None,
            owner: Some(JavaType::source_class("example.Factory")),
            type_arguments: Vec::new(),
            method: JavaIdentifier::from_dex("create"),
            args: Vec::new(),
        };

        assert!(!ConstructorSyntaxRecovery::passive_constructor_argument(
            &expression,
            &parameters,
        ));
    }

    #[test]
    fn super_argument_factory_preserves_integer_narrowing_context() {
        assert_eq!(
            ConstructorSyntaxRecovery::literal_type(&JavaExpr::Literal(JavaLiteral::Integer(1))),
            None,
        );
        assert_eq!(
            ConstructorSyntaxRecovery::literal_type(&JavaExpr::Literal(JavaLiteral::Integer(
                2131953226,
            ))),
            Some(JavaType::int()),
        );
    }

    #[test]
    fn kotlin_default_constructor_mask_is_typed_as_int() {
        let mapping_type = JavaType::source_class("example.Mapping");
        let marker_type = JavaType::source_class("DefaultConstructorMarker");
        let carried_type = JavaType::source_class("example.Carried");
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("Child")),
            parameters: Vec::new(),
            throws: Vec::new(),
            body: None,
        };
        let arguments = vec![
            JavaExpr::New {
                enclosing: None,
                ty: mapping_type.clone(),
                target_type: None,
                args: Vec::new(),
                anonymous_body: None,
            },
            JavaExpr::Literal(JavaLiteral::Integer(1)),
            JavaExpr::Cast {
                ty: marker_type.clone(),
                value: Box::new(JavaExpr::Literal(JavaLiteral::Null)),
            },
            JavaExpr::Cast {
                ty: carried_type.clone(),
                value: Box::new(JavaExpr::Literal(JavaLiteral::Null)),
            },
        ];

        assert_eq!(
            ConstructorSyntaxRecovery::infer_super_argument_types(
                &constructor,
                &[],
                &arguments,
                &BTreeMap::new(),
            ),
            Some(vec![
                mapping_type,
                JavaType::int(),
                marker_type,
                carried_type,
            ]),
        );
        assert!(ConstructorSyntaxRecovery::infer_super_argument_types(
            &constructor,
            &[],
            &[JavaExpr::Literal(JavaLiteral::Integer(1))],
            &BTreeMap::new(),
        )
        .is_none());
    }

    #[test]
    fn complex_constructor_binding_uses_a_factory_and_helper() {
        let class_name = JavaIdentifier::from_dex("Defaults");
        let mask = JavaIdentifier::from_dex("mask");
        let fallback = JavaIdentifier::from_dex("fallback");
        let result = JavaIdentifier::from_dex("result");
        let room = JavaIdentifier::from_dex("room");
        let string_type = JavaType::source_class("java.lang.String");
        let mut declaration = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Class,
            name: class_name.clone(),
            type_parameters: Vec::new(),
            extends: None,
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: Vec::new(),
            methods: vec![JavaMethodDeclaration {
                annotations: Vec::new(),
                modifiers: vec![JavaModifier::Public],
                compiler_generated: true,
                kind: JavaMethodDeclarationKind::Constructor,
                type_parameters: Vec::new(),
                return_type: None,
                name: Some(class_name),
                parameters: vec![
                    JavaMethodParameter {
                        annotations: Vec::new(),
                        ty: JavaType::int(),
                        name: mask.clone(),
                        varargs: false,
                    },
                    JavaMethodParameter {
                        annotations: Vec::new(),
                        ty: string_type.clone(),
                        name: fallback.clone(),
                        varargs: false,
                    },
                ],
                throws: Vec::new(),
                body: Some(JavaMethodBody {
                    root: JavaStmt::Block(vec![
                        JavaStmt::Variable {
                            ty: string_type.clone(),
                            name: result.clone(),
                            value: Some(JavaExpr::Literal(JavaLiteral::Null)),
                        },
                        JavaStmt::If {
                            condition: JavaExpr::Binary {
                                left: Box::new(JavaExpr::Name(mask.clone())),
                                op: JavaBinaryOp::NotEqual,
                                right: Box::new(JavaExpr::Literal(JavaLiteral::Integer(0))),
                            },
                            then_stmt: Box::new(JavaStmt::Block(vec![
                                JavaStmt::Variable {
                                    ty: string_type.clone(),
                                    name: room.clone(),
                                    value: Some(JavaExpr::Call {
                                        receiver: None,
                                        owner: Some(JavaType::source_class("example.Host")),
                                        type_arguments: Vec::new(),
                                        method: JavaIdentifier::from_dex("room"),
                                        args: Vec::new(),
                                    }),
                                },
                                JavaStmt::If {
                                    condition: JavaExpr::Binary {
                                        left: Box::new(JavaExpr::Name(room.clone())),
                                        op: JavaBinaryOp::NotEqual,
                                        right: Box::new(JavaExpr::Literal(JavaLiteral::Null)),
                                    },
                                    then_stmt: Box::new(JavaStmt::Assign {
                                        target: JavaExpr::Name(result.clone()),
                                        op: JavaAssignOp::Assign,
                                        value: JavaExpr::Call {
                                            receiver: Some(Box::new(JavaExpr::Name(room))),
                                            owner: None,
                                            type_arguments: Vec::new(),
                                            method: JavaIdentifier::from_dex("toString"),
                                            args: Vec::new(),
                                        },
                                    }),
                                    else_stmt: None,
                                },
                            ])),
                            else_stmt: None,
                        },
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::This,
                            args: vec![JavaExpr::Conditional {
                                condition: Box::new(JavaExpr::Binary {
                                    left: Box::new(JavaExpr::Name(mask)),
                                    op: JavaBinaryOp::Equal,
                                    right: Box::new(JavaExpr::Literal(JavaLiteral::Integer(0))),
                                }),
                                when_true: Box::new(JavaExpr::Name(fallback)),
                                when_false: Box::new(JavaExpr::Name(result.clone())),
                            }],
                        },
                    ]),
                }),
            }],
            nested: Vec::new(),
        };

        ConstructorSyntaxRecovery::apply(&mut declaration);

        assert_eq!(declaration.methods.len(), 3);
        assert!(matches!(
            &declaration.methods[0].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::This,
                        args,
                    }] if matches!(args.last(), Some(JavaExpr::Call { .. }))
                )
        ));
        let helper = &declaration.methods[1];
        assert_eq!(helper.modifiers, vec![JavaModifier::Private]);
        assert_eq!(helper.parameters.len(), 3);
        let factory = &declaration.methods[2];
        assert_eq!(
            factory.modifiers,
            vec![JavaModifier::Private, JavaModifier::Static]
        );
        assert_eq!(factory.return_type, Some(string_type));
        assert!(matches!(
            &factory.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(statements.last(), Some(JavaStmt::Return(Some(JavaExpr::Name(name))))
                    if name == &result)
        ));
    }

    #[test]
    fn complex_constructor_factory_rejects_implicit_instance_calls() {
        let scope = BTreeSet::new();
        let expression = JavaExpr::Call {
            receiver: None,
            owner: None,
            type_arguments: Vec::new(),
            method: JavaIdentifier::from_dex("instanceMethod"),
            args: Vec::new(),
        };

        assert!(!ConstructorSyntaxRecovery::static_expression(
            &expression,
            &scope,
        ));
    }

    #[test]
    fn constructor_factory_accepts_scoped_parameter_mutations() {
        let parameter = JavaIdentifier::from_dex("parameter");
        let parameters = BTreeSet::from([parameter.clone()]);
        let mut scope = parameters.clone();
        let reassignment = JavaStmt::Assign {
            target: JavaExpr::Name(parameter.clone()),
            op: JavaAssignOp::Assign,
            value: JavaExpr::Literal(JavaLiteral::Integer(1)),
        };
        let array_store = JavaStmt::Assign {
            target: JavaExpr::ArrayAccess {
                array: Box::new(JavaExpr::Name(parameter.clone())),
                index: Box::new(JavaExpr::Literal(JavaLiteral::Integer(0))),
            },
            op: JavaAssignOp::Assign,
            value: JavaExpr::Literal(JavaLiteral::Integer(1)),
        };
        let compound_assignment = JavaStmt::Assign {
            target: JavaExpr::Name(parameter),
            op: JavaAssignOp::Subtract,
            value: JavaExpr::Literal(JavaLiteral::Integer(2)),
        };

        assert!(ConstructorSyntaxRecovery::static_statement(
            &reassignment,
            &mut scope,
            &parameters,
        ));
        assert!(ConstructorSyntaxRecovery::static_statement(
            &array_store,
            &mut scope,
            &parameters,
        ));
        assert!(ConstructorSyntaxRecovery::static_statement(
            &compound_assignment,
            &mut scope,
            &parameters,
        ));
    }

    #[test]
    fn constructor_factory_accepts_scoped_for_loops() {
        let input = JavaIdentifier::from_dex("input");
        let limit = JavaIdentifier::from_dex("limit");
        let values = JavaIdentifier::from_dex("values");
        let index = JavaIdentifier::from_dex("index");
        let parameters = BTreeSet::from([input.clone()]);
        let statements = vec![
            JavaStmt::Variable {
                ty: JavaType::int(),
                name: limit.clone(),
                value: Some(JavaExpr::Call {
                    receiver: Some(Box::new(JavaExpr::Name(input))),
                    owner: None,
                    type_arguments: Vec::new(),
                    method: JavaIdentifier::from_dex("size"),
                    args: Vec::new(),
                }),
            },
            JavaStmt::Variable {
                ty: JavaType::source_class("java.util.ArrayList"),
                name: values.clone(),
                value: Some(JavaExpr::New {
                    enclosing: None,
                    ty: JavaType::source_class("java.util.ArrayList"),
                    target_type: None,
                    args: vec![JavaExpr::Name(limit.clone())],
                    anonymous_body: None,
                }),
            },
            JavaStmt::For {
                label: None,
                init: vec![JavaStmt::Variable {
                    ty: JavaType::int(),
                    name: index.clone(),
                    value: Some(JavaExpr::Literal(JavaLiteral::Integer(0))),
                }],
                condition: Some(JavaExpr::Binary {
                    left: Box::new(JavaExpr::Name(index.clone())),
                    op: JavaBinaryOp::Less,
                    right: Box::new(JavaExpr::Name(limit)),
                }),
                update: vec![JavaExpr::Update {
                    op: JavaUpdateOp::Increment,
                    target: Box::new(JavaExpr::Name(index)),
                    prefix: false,
                }],
                body: Box::new(JavaStmt::Expression(JavaExpr::Call {
                    receiver: Some(Box::new(JavaExpr::Name(values))),
                    owner: None,
                    type_arguments: Vec::new(),
                    method: JavaIdentifier::from_dex("add"),
                    args: vec![JavaExpr::StaticField {
                        owner: JavaType::source_class("com.example.Defaults"),
                        name: JavaIdentifier::from_dex("VALUE"),
                    }],
                })),
            },
        ];

        assert!(ConstructorSyntaxRecovery::static_statements(
            &statements,
            &parameters,
        ));
    }

    #[test]
    fn constructor_factory_accepts_loop_local_jumps() {
        let stop = JavaIdentifier::from_dex("stop");
        let index = JavaIdentifier::from_dex("index");
        let parameters = BTreeSet::from([stop.clone()]);
        let loop_statement = JavaStmt::For {
            label: None,
            init: vec![JavaStmt::Variable {
                ty: JavaType::int(),
                name: index.clone(),
                value: Some(JavaExpr::Literal(JavaLiteral::Integer(0))),
            }],
            condition: Some(JavaExpr::Binary {
                left: Box::new(JavaExpr::Name(index.clone())),
                op: JavaBinaryOp::Less,
                right: Box::new(JavaExpr::Literal(JavaLiteral::Integer(10))),
            }),
            update: vec![JavaExpr::Update {
                op: JavaUpdateOp::Increment,
                target: Box::new(JavaExpr::Name(index.clone())),
                prefix: false,
            }],
            body: Box::new(JavaStmt::Block(vec![
                JavaStmt::If {
                    condition: JavaExpr::Name(stop),
                    then_stmt: Box::new(JavaStmt::Break(None)),
                    else_stmt: None,
                },
                JavaStmt::Expression(JavaExpr::Update {
                    op: JavaUpdateOp::Increment,
                    target: Box::new(JavaExpr::Name(index)),
                    prefix: false,
                }),
                JavaStmt::Continue(None),
            ])),
        };

        assert!(ConstructorSyntaxRecovery::static_statements(
            &[loop_statement],
            &parameters,
        ));
        assert!(!ConstructorSyntaxRecovery::static_statements(
            &[JavaStmt::Break(None), JavaStmt::Continue(None)],
            &parameters,
        ));
    }

    #[test]
    fn constructor_factory_accepts_scoped_for_each_loops() {
        let input = JavaIdentifier::from_dex("input");
        let values = JavaIdentifier::from_dex("values");
        let element = JavaIdentifier::from_dex("element");
        let parameters = BTreeSet::from([input.clone()]);
        let statements = vec![
            JavaStmt::Variable {
                ty: JavaType::source_class("java.util.ArrayList"),
                name: values.clone(),
                value: Some(JavaExpr::New {
                    enclosing: None,
                    ty: JavaType::source_class("java.util.ArrayList"),
                    target_type: None,
                    args: Vec::new(),
                    anonymous_body: None,
                }),
            },
            JavaStmt::ForEach {
                label: None,
                ty: JavaType::source_class("java.lang.Object"),
                variable: element.clone(),
                iterable: JavaExpr::Name(input),
                body: Box::new(JavaStmt::Expression(JavaExpr::Call {
                    receiver: Some(Box::new(JavaExpr::Name(values))),
                    owner: None,
                    type_arguments: Vec::new(),
                    method: JavaIdentifier::from_dex("add"),
                    args: vec![JavaExpr::Name(element)],
                })),
            },
        ];

        assert!(ConstructorSyntaxRecovery::static_statements(
            &statements,
            &parameters,
        ));
    }

    #[test]
    fn constructor_factory_accepts_static_synchronized_blocks() {
        let input = JavaIdentifier::from_dex("input");
        let parameters = BTreeSet::from([input.clone()]);
        let synchronized = JavaStmt::Synchronized {
            lock: JavaExpr::ClassLiteral(JavaType::source_class("com.example.Cache")),
            body: Box::new(JavaStmt::Assign {
                target: JavaExpr::StaticField {
                    owner: JavaType::source_class("com.example.Cache"),
                    name: JavaIdentifier::from_dex("value"),
                },
                op: JavaAssignOp::Assign,
                value: JavaExpr::Name(input),
            }),
        };

        assert!(ConstructorSyntaxRecovery::static_statements(
            &[synchronized],
            &parameters,
        ));
        assert!(!ConstructorSyntaxRecovery::static_statements(
            &[JavaStmt::Synchronized {
                lock: JavaExpr::This,
                body: Box::new(JavaStmt::Empty),
            }],
            &parameters,
        ));
    }

    #[test]
    fn constructor_factory_accepts_static_try_catch_preludes() {
        let origin = JavaIdentifier::from_dex("origin");
        let result = JavaIdentifier::from_dex("result");
        let exception = JavaIdentifier::from_dex("exception");
        let parameters = BTreeSet::from([origin.clone()]);
        let statements = vec![
            JavaStmt::Variable {
                ty: JavaType::source_class("java.lang.Object"),
                name: result.clone(),
                value: None,
            },
            JavaStmt::Try {
                body: Box::new(JavaStmt::Block(vec![JavaStmt::Assign {
                    target: JavaExpr::Name(result.clone()),
                    op: JavaAssignOp::Assign,
                    value: JavaExpr::Call {
                        receiver: None,
                        owner: Some(JavaType::source_class("com.example.Parser")),
                        type_arguments: Vec::new(),
                        method: JavaIdentifier::from_dex("parse"),
                        args: vec![JavaExpr::Name(origin)],
                    },
                }])),
                catches: vec![JavaCatch {
                    types: vec![JavaType::source_class("java.lang.Throwable")],
                    variable: exception.clone(),
                    body: JavaStmt::Block(vec![JavaStmt::Assign {
                        target: JavaExpr::Name(result),
                        op: JavaAssignOp::Assign,
                        value: JavaExpr::Call {
                            receiver: None,
                            owner: Some(JavaType::source_class("com.example.Failures")),
                            type_arguments: Vec::new(),
                            method: JavaIdentifier::from_dex("create"),
                            args: vec![JavaExpr::Name(exception)],
                        },
                    }]),
                }],
                finally: None,
            },
        ];

        assert!(ConstructorSyntaxRecovery::static_statements(
            &statements,
            &parameters,
        ));
    }

    #[test]
    fn constructor_factory_accepts_empty_catch_preludes() {
        let class_name = JavaIdentifier::from_dex("ParsedValue");
        let input = JavaIdentifier::from_dex("input");
        let parsed = JavaIdentifier::from_dex("parsed");
        let exception = JavaIdentifier::from_dex("exception");
        let string_type = JavaType::source_class("java.lang.String");
        let object_type = JavaType::source_class("java.lang.Object");
        let parameter = |ty, name| JavaMethodParameter {
            annotations: Vec::new(),
            ty,
            name,
            varargs: false,
        };
        let constructor = |parameters, statements| JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Private],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(class_name.clone()),
            parameters,
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(statements),
            }),
        };
        let mut declaration = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Class,
            name: class_name.clone(),
            type_parameters: Vec::new(),
            extends: None,
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: Vec::new(),
            methods: vec![
                constructor(
                    vec![parameter(string_type.clone(), input.clone())],
                    vec![
                        JavaStmt::Variable {
                            ty: object_type.clone(),
                            name: parsed.clone(),
                            value: Some(JavaExpr::Literal(JavaLiteral::Null)),
                        },
                        JavaStmt::If {
                            condition: JavaExpr::Binary {
                                left: Box::new(JavaExpr::Name(input.clone())),
                                op: JavaBinaryOp::NotEqual,
                                right: Box::new(JavaExpr::Literal(JavaLiteral::Null)),
                            },
                            then_stmt: Box::new(JavaStmt::Try {
                                body: Box::new(JavaStmt::Assign {
                                    target: JavaExpr::Name(parsed.clone()),
                                    op: JavaAssignOp::Assign,
                                    value: JavaExpr::Cast {
                                        ty: object_type.clone(),
                                        value: Box::new(JavaExpr::Name(input)),
                                    },
                                }),
                                catches: vec![JavaCatch {
                                    types: vec![JavaType::source_class("java.lang.Exception")],
                                    variable: exception,
                                    body: JavaStmt::Empty,
                                }],
                                finally: None,
                            }),
                            else_stmt: None,
                        },
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::This,
                            args: vec![JavaExpr::Name(parsed)],
                        },
                    ],
                ),
                constructor(
                    vec![parameter(object_type, JavaIdentifier::from_dex("value"))],
                    Vec::new(),
                ),
            ],
            nested: Vec::new(),
        };

        ConstructorSyntaxRecovery::apply(&mut declaration);

        assert_eq!(declaration.methods.len(), 4);
        assert!(declaration.nested.is_empty());
        assert!(matches!(
            &declaration.methods[0].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(statements.as_slice(), [JavaStmt::ConstructorInvocation {
                    target: JavaConstructorTarget::This,
                    args,
                }] if args.len() == 2 && matches!(args.last(), Some(JavaExpr::Call { .. })))
        ));
        assert!(matches!(
            &declaration.methods[3].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(statements.get(1), Some(JavaStmt::If {
                    then_stmt,
                    ..
                }) if matches!(then_stmt.as_ref(), JavaStmt::Try {
                    catches,
                    ..
                } if matches!(catches.as_slice(), [JavaCatch {
                    body: JavaStmt::Empty,
                    ..
                }])))
        ));
    }

    #[test]
    fn rewritten_parameter_prelude_uses_a_typed_carrier() {
        let class_name = JavaIdentifier::from_dex("Defaults");
        let value = JavaIdentifier::from_dex("value");
        let mask = JavaIdentifier::from_dex("mask");
        let parameter = |name| JavaMethodParameter {
            annotations: Vec::new(),
            ty: JavaType::int(),
            name,
            varargs: false,
        };
        let constructor = |parameters, statements| JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(class_name.clone()),
            parameters,
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(statements),
            }),
        };
        let target = constructor(vec![parameter(value.clone())], Vec::new());
        let defaults = constructor(
            vec![parameter(value.clone()), parameter(mask.clone())],
            vec![
                JavaStmt::If {
                    condition: JavaExpr::Binary {
                        left: Box::new(JavaExpr::Binary {
                            left: Box::new(JavaExpr::Name(mask)),
                            op: JavaBinaryOp::BitAnd,
                            right: Box::new(JavaExpr::Literal(JavaLiteral::Integer(1))),
                        }),
                        op: JavaBinaryOp::NotEqual,
                        right: Box::new(JavaExpr::Literal(JavaLiteral::Integer(0))),
                    },
                    then_stmt: Box::new(JavaStmt::Assign {
                        target: JavaExpr::Name(value.clone()),
                        op: JavaAssignOp::Assign,
                        value: JavaExpr::Literal(JavaLiteral::Integer(42)),
                    }),
                    else_stmt: None,
                },
                JavaStmt::ConstructorInvocation {
                    target: JavaConstructorTarget::This,
                    args: vec![JavaExpr::Name(value)],
                },
            ],
        );
        let mut declaration = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Class,
            name: class_name,
            type_parameters: Vec::new(),
            extends: None,
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: Vec::new(),
            methods: vec![target, defaults],
            nested: Vec::new(),
        };

        ConstructorSyntaxRecovery::extract_remaining_constructor_preludes(
            &mut declaration,
            &BTreeMap::new(),
        );

        assert_eq!(declaration.methods.len(), 4);
        assert_eq!(declaration.nested.len(), 1);
        assert!(matches!(
            &declaration.methods[1].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::This,
                        args,
                    }] if matches!(args.as_slice(), [JavaExpr::Call { .. }])
                )
        ));
        assert!(matches!(
            &declaration.methods[3].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(statements.first(), Some(JavaStmt::If { .. }))
                    && matches!(statements.last(), Some(JavaStmt::Return(Some(JavaExpr::New { .. }))))
        ));
    }

    #[test]
    fn overloaded_this_prelude_uses_argument_types_to_select_target() {
        let class_name = JavaIdentifier::from_dex("InputReader");
        let values = JavaIdentifier::from_dex("values");
        let length = JavaIdentifier::from_dex("length");
        let input = JavaIdentifier::from_dex("input");
        let stream = JavaIdentifier::from_dex("stream");
        let byte_array = JavaType::array(JavaType::Primitive(
            crate::language::java::JavaPrimitiveType::Byte,
        ));
        let input_stream = JavaType::source_class("java.io.InputStream");
        let byte_array_input_stream = JavaType::source_class("java.io.ByteArrayInputStream");
        let parameter = |ty, name| JavaMethodParameter {
            annotations: Vec::new(),
            ty,
            name,
            varargs: false,
        };
        let constructor = |parameters, statements| JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(class_name.clone()),
            parameters,
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(statements),
            }),
        };
        let length_stream = constructor(
            vec![
                parameter(JavaType::int(), length),
                parameter(input_stream.clone(), input),
            ],
            Vec::new(),
        );
        let bytes_limit = constructor(
            vec![
                parameter(byte_array.clone(), values.clone()),
                parameter(JavaType::int(), JavaIdentifier::from_dex("limit")),
            ],
            Vec::new(),
        );
        let bytes = constructor(
            vec![parameter(byte_array.clone(), values.clone())],
            vec![
                JavaStmt::Variable {
                    ty: byte_array_input_stream.clone(),
                    name: stream.clone(),
                    value: Some(JavaExpr::New {
                        enclosing: None,
                        ty: byte_array_input_stream,
                        target_type: None,
                        args: vec![JavaExpr::Name(values.clone())],
                        anonymous_body: None,
                    }),
                },
                JavaStmt::ConstructorInvocation {
                    target: JavaConstructorTarget::This,
                    args: vec![
                        JavaExpr::Field {
                            owner: Box::new(JavaExpr::Name(values)),
                            name: JavaIdentifier::from_dex("length"),
                        },
                        JavaExpr::Name(stream),
                    ],
                },
            ],
        );
        let mut declaration = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Class,
            name: class_name,
            type_parameters: Vec::new(),
            extends: None,
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: Vec::new(),
            methods: vec![length_stream, bytes_limit, bytes],
            nested: Vec::new(),
        };

        ConstructorSyntaxRecovery::extract_remaining_constructor_preludes(
            &mut declaration,
            &BTreeMap::new(),
        );

        assert_eq!(declaration.methods.len(), 5);
        assert_eq!(declaration.nested.len(), 1);
        assert_eq!(
            declaration.nested[0]
                .fields
                .iter()
                .map(|field| field.ty.clone())
                .collect::<Vec<_>>(),
            vec![JavaType::int(), input_stream]
        );
        assert!(matches!(
            &declaration.methods[2].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::This,
                        args,
                    }] if matches!(args.as_slice(), [JavaExpr::Call { .. }])
                )
        ));
    }

    #[test]
    fn varargs_overload_keeps_fixed_constructor_candidates() {
        let class_name = JavaIdentifier::from_dex("LocaleList");
        let constructor = |ty, varargs| JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(class_name.clone()),
            parameters: vec![JavaMethodParameter {
                annotations: Vec::new(),
                ty,
                name: JavaIdentifier::from_dex("value"),
                varargs,
            }],
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(Vec::new()),
            }),
        };
        let string_type = JavaType::source_class("java.lang.String");
        let list_type = JavaType::source_class("java.util.List");
        let locale_array = JavaType::array(JavaType::source_class("example.Locale"));
        let declaration = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Class,
            name: class_name.clone(),
            type_parameters: Vec::new(),
            extends: None,
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: Vec::new(),
            methods: vec![
                constructor(string_type.clone(), false),
                constructor(list_type.clone(), false),
                constructor(locale_array.clone(), true),
            ],
            nested: Vec::new(),
        };

        assert_eq!(
            ConstructorSyntaxRecovery::constructor_parameter_types(&declaration).get(&1),
            Some(&Some(vec![
                vec![string_type],
                vec![list_type],
                vec![locale_array],
            ])),
        );
    }

    #[test]
    fn constructor_argument_inference_recognizes_boolean_operations() {
        let left = JavaIdentifier::from_dex("left");
        let right = JavaIdentifier::from_dex("right");
        let values = BTreeMap::from([
            (left.clone(), JavaType::boolean()),
            (right.clone(), JavaType::boolean()),
        ]);
        let logical_and = JavaExpr::Binary {
            left: Box::new(JavaExpr::Name(left.clone())),
            op: JavaBinaryOp::LogicalAnd,
            right: Box::new(JavaExpr::Name(right)),
        };
        let comparison = JavaExpr::Binary {
            left: Box::new(JavaExpr::Literal(JavaLiteral::Integer(1))),
            op: JavaBinaryOp::Less,
            right: Box::new(JavaExpr::Literal(JavaLiteral::Integer(2))),
        };
        let logical_not = JavaExpr::Unary {
            op: JavaUnaryOp::LogicalNot,
            operand: Box::new(JavaExpr::Name(left.clone())),
        };
        let instance_of = JavaExpr::InstanceOf {
            value: Box::new(JavaExpr::Name(left)),
            ty: JavaType::source_class("java.lang.Boolean"),
        };

        for expression in [logical_and, comparison, logical_not, instance_of] {
            assert_eq!(
                ConstructorSyntaxRecovery::infer_constructor_argument_type(&expression, &values,),
                Some(JavaType::boolean()),
            );
        }
    }

    #[test]
    fn conditional_constructor_argument_uses_the_typed_numeric_arm() {
        let value = JavaIdentifier::from_dex("value");
        let values = BTreeMap::from([(value.clone(), JavaType::int())]);
        let expression = JavaExpr::Conditional {
            condition: Box::new(JavaExpr::Literal(JavaLiteral::Boolean(true))),
            when_true: Box::new(JavaExpr::Unary {
                op: JavaUnaryOp::Negate,
                operand: Box::new(JavaExpr::Literal(JavaLiteral::Integer(1))),
            }),
            when_false: Box::new(JavaExpr::Name(value)),
        };
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: Vec::new(),
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("Child")),
            parameters: Vec::new(),
            throws: Vec::new(),
            body: None,
        };

        assert_eq!(
            ConstructorSyntaxRecovery::infer_constructor_argument_type_with_returns(
                &constructor,
                &[],
                &expression,
                &values,
                &BTreeMap::new(),
            ),
            Some(JavaType::int()),
        );
    }

    #[test]
    fn constructor_argument_inference_uses_the_object_to_string_contract() {
        let value = JavaIdentifier::from_dex("value");
        let expression = JavaExpr::Call {
            receiver: Some(Box::new(JavaExpr::Name(value.clone()))),
            owner: None,
            type_arguments: Vec::new(),
            method: JavaIdentifier::from_dex("toString"),
            args: Vec::new(),
        };
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: Vec::new(),
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("Child")),
            parameters: vec![JavaMethodParameter {
                annotations: Vec::new(),
                ty: JavaType::source_class("String"),
                name: value,
                varargs: false,
            }],
            throws: Vec::new(),
            body: None,
        };

        assert_eq!(
            ConstructorSyntaxRecovery::method_call_return_type(
                &constructor,
                &[],
                &expression,
                &BTreeMap::new(),
            ),
            Some(JavaType::source_class("java.lang.String")),
        );
        assert_eq!(
            ConstructorSyntaxRecovery::infer_super_argument_types(
                &constructor,
                &[],
                &[JavaExpr::Conditional {
                    condition: Box::new(JavaExpr::Literal(JavaLiteral::Boolean(true))),
                    when_true: Box::new(JavaExpr::Name(JavaIdentifier::from_dex("value"))),
                    when_false: Box::new(expression),
                }],
                &BTreeMap::new(),
            ),
            Some(vec![JavaType::source_class("String")]),
        );
    }

    #[test]
    fn ambiguous_reference_this_overloads_preserve_inferred_argument_types() {
        let string = JavaIdentifier::from_dex("string");
        let values = JavaIdentifier::from_dex("values");
        let encoding = JavaIdentifier::from_dex("encoding");
        let string_type = JavaType::source_class("java.lang.String");
        let array_list_type = JavaType::source_class("java.util.ArrayList");
        let encoding_type = JavaType::source_class("example.Encoding");
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("Header")),
            parameters: vec![
                JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: string_type.clone(),
                    name: string.clone(),
                    varargs: false,
                },
                JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: encoding_type.clone(),
                    name: encoding.clone(),
                    varargs: false,
                },
            ],
            throws: Vec::new(),
            body: None,
        };
        let prelude = vec![JavaStmt::Variable {
            ty: array_list_type.clone(),
            name: values.clone(),
            value: None,
        }];
        let arguments = vec![
            JavaExpr::Name(string),
            JavaExpr::Name(values),
            JavaExpr::Name(encoding),
        ];
        let candidates = vec![
            vec![
                string_type.clone(),
                JavaType::source_class("java.util.List"),
                encoding_type.clone(),
            ],
            vec![
                string_type.clone(),
                JavaType::source_class("java.util.Map"),
                encoding_type.clone(),
            ],
        ];

        let resolved = ConstructorSyntaxRecovery::resolve_this_argument_types(
            &constructor,
            &prelude,
            &arguments,
            &candidates,
            &BTreeMap::new(),
        );

        assert_eq!(
            resolved,
            Some(vec![string_type, array_list_type, encoding_type])
        );
    }

    #[test]
    fn generic_rewritten_parameter_prelude_uses_a_generic_carrier() {
        let class_name = JavaIdentifier::from_dex("GenericDefaults");
        let type_name = JavaIdentifier::from_dex("DATA");
        let value = JavaIdentifier::from_dex("value");
        let mask = JavaIdentifier::from_dex("mask");
        let target = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(class_name.clone()),
            parameters: vec![JavaMethodParameter {
                annotations: Vec::new(),
                ty: JavaType::Variable(type_name.clone()),
                name: value.clone(),
                varargs: false,
            }],
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(Vec::new()),
            }),
        };
        let defaults = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(class_name.clone()),
            parameters: vec![
                JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: JavaType::Variable(type_name.clone()),
                    name: value.clone(),
                    varargs: false,
                },
                JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: JavaType::int(),
                    name: mask.clone(),
                    varargs: false,
                },
            ],
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![
                    JavaStmt::If {
                        condition: JavaExpr::Binary {
                            left: Box::new(JavaExpr::Name(mask)),
                            op: JavaBinaryOp::NotEqual,
                            right: Box::new(JavaExpr::Literal(JavaLiteral::Integer(0))),
                        },
                        then_stmt: Box::new(JavaStmt::Assign {
                            target: JavaExpr::Name(value.clone()),
                            op: JavaAssignOp::Assign,
                            value: JavaExpr::Literal(JavaLiteral::Null),
                        }),
                        else_stmt: None,
                    },
                    JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::This,
                        args: vec![JavaExpr::Name(value)],
                    },
                ]),
            }),
        };
        let type_parameter = JavaTypeParameter {
            name: type_name.clone(),
            bounds: Vec::new(),
        };
        let mut declaration = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Class,
            name: class_name,
            type_parameters: vec![type_parameter.clone()],
            extends: None,
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: Vec::new(),
            methods: vec![target, defaults],
            nested: Vec::new(),
        };

        ConstructorSyntaxRecovery::extract_remaining_constructor_preludes(
            &mut declaration,
            &BTreeMap::new(),
        );

        assert_eq!(declaration.methods.len(), 4);
        assert_eq!(declaration.nested.len(), 1);
        assert_eq!(
            declaration.methods[3].type_parameters,
            vec![type_parameter.clone()]
        );
        assert_eq!(declaration.nested[0].type_parameters, vec![type_parameter]);
        assert!(matches!(
            &declaration.methods[2].parameters[0].ty,
            JavaType::Class(class)
                if matches!(
                    class.segments.last().unwrap().arguments.as_slice(),
                    [JavaTypeArgument::Exact(JavaType::Variable(name))] if name == &type_name
                )
        ));
    }

    #[test]
    fn synchronized_super_prelude_moves_into_the_argument_factory() {
        let input = JavaIdentifier::from_dex("input");
        let prepared = JavaIdentifier::from_dex("prepared");
        let string_type = JavaType::source_class("java.lang.String");
        let static_lock = JavaExpr::ClassLiteral(JavaType::source_class("com.example.Locks"));
        let constructor = |lock| JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("Child")),
            parameters: vec![JavaMethodParameter {
                annotations: Vec::new(),
                ty: string_type.clone(),
                name: input.clone(),
                varargs: false,
            }],
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![JavaStmt::Synchronized {
                    lock,
                    body: Box::new(JavaStmt::Block(vec![
                        JavaStmt::Variable {
                            ty: string_type.clone(),
                            name: prepared.clone(),
                            value: Some(JavaExpr::Call {
                                receiver: None,
                                owner: Some(JavaType::source_class("com.example.Values")),
                                type_arguments: Vec::new(),
                                method: JavaIdentifier::from_dex("prepare"),
                                args: vec![JavaExpr::Name(input.clone())],
                            }),
                        },
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::Super,
                            args: vec![JavaExpr::Name(prepared.clone())],
                        },
                    ])),
                }]),
            }),
        };

        let (delegation, helper, factory, carrier) =
            ConstructorSyntaxRecovery::remaining_synchronized_constructor_prelude_helper(
                &constructor(static_lock.clone()),
                &BTreeMap::new(),
                &BTreeMap::new(),
                &[],
                JavaIdentifier::from_dex("computeConstructorArguments"),
                JavaIdentifier::from_dex("DexdecConstructorArguments"),
            )
            .expect("a static synchronized prelude should use an argument factory");

        assert!(matches!(
            &delegation.root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::This,
                        ..
                    }]
                )
        ));
        assert!(matches!(
            &helper.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        ..
                    }]
                )
        ));
        assert!(matches!(
            &factory.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::Synchronized { lock, body }]
                        if lock == &static_lock
                            && matches!(
                                body.as_ref(),
                                JavaStmt::Block(factory_statements)
                                    if matches!(
                                        factory_statements.last(),
                                        Some(JavaStmt::Return(Some(JavaExpr::New { .. })))
                                    )
                            )
                )
        ));
        assert_eq!(carrier.fields.len(), 1);
        assert_eq!(carrier.fields[0].ty, string_type);
        assert!(
            ConstructorSyntaxRecovery::remaining_synchronized_constructor_prelude_helper(
                &constructor(JavaExpr::This),
                &BTreeMap::new(),
                &BTreeMap::new(),
                &[],
                JavaIdentifier::from_dex("computeConstructorArguments"),
                JavaIdentifier::from_dex("DexdecConstructorArguments"),
            )
            .is_none()
        );
    }

    #[test]
    fn conditional_reference_super_argument_uses_a_poly_carrier_access() {
        let map = JavaIdentifier::from_dex("map");
        let map_type = JavaType::source_class("java.util.Map");
        let constructor_argument = JavaExpr::Conditional {
            condition: Box::new(JavaExpr::Binary {
                left: Box::new(JavaExpr::Name(map.clone())),
                op: JavaBinaryOp::Equal,
                right: Box::new(JavaExpr::Literal(JavaLiteral::Null)),
            }),
            when_true: Box::new(JavaExpr::New {
                enclosing: None,
                ty: JavaType::source_class("java.util.HashMap"),
                target_type: None,
                args: Vec::new(),
                anonymous_body: None,
            }),
            when_false: Box::new(JavaExpr::Name(map.clone())),
        };
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("Child")),
            parameters: vec![JavaMethodParameter {
                annotations: Vec::new(),
                ty: map_type,
                name: map.clone(),
                varargs: false,
            }],
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![
                    JavaStmt::Expression(JavaExpr::Call {
                        receiver: None,
                        owner: Some(JavaType::source_class("com.example.Guards")),
                        type_arguments: Vec::new(),
                        method: JavaIdentifier::from_dex("check"),
                        args: vec![JavaExpr::Name(map)],
                    }),
                    JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        args: vec![constructor_argument.clone()],
                    },
                ]),
            }),
        };

        let (_, helper, factory, carrier) =
            ConstructorSyntaxRecovery::remaining_constructor_prelude_helper(
                &constructor,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &[],
                JavaIdentifier::from_dex("computeConstructorArguments"),
                JavaIdentifier::from_dex("DexdecConstructorArguments"),
            )
            .expect("the conditional value should be evaluated into an Object carrier field");

        assert_eq!(carrier.fields.len(), 1);
        assert_eq!(
            carrier.fields[0].ty,
            JavaType::source_class("java.lang.Object")
        );
        assert!(carrier.methods.iter().any(|method| {
            method
                .name
                .as_ref()
                .is_some_and(|name| name.as_str() == "castArgument")
                && method.type_parameters.len() == 1
        }));
        assert!(matches!(
            &helper.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::ConstructorInvocation { args, .. }]
                        if matches!(
                            args.as_slice(),
                            [JavaExpr::Call { method, .. }]
                                if method.as_str() == "castArgument"
                        )
                )
        ));
        assert!(matches!(
            &factory.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.last(),
                    Some(JavaStmt::Return(Some(JavaExpr::New { args, .. })))
                        if args == &[constructor_argument]
                )
        ));
    }

    #[test]
    fn super_constructor_prelude_uses_a_typed_carrier() {
        let class_name = JavaIdentifier::from_dex("Child");
        let value = JavaIdentifier::from_dex("value");
        let string_type = JavaType::source_class("java.lang.String");
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(class_name),
            parameters: Vec::new(),
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![
                    JavaStmt::Variable {
                        ty: string_type.clone(),
                        name: value.clone(),
                        value: Some(JavaExpr::Call {
                            receiver: None,
                            owner: Some(JavaType::source_class("com.example.Loader")),
                            type_arguments: Vec::new(),
                            method: JavaIdentifier::from_dex("load"),
                            args: Vec::new(),
                        }),
                    },
                    JavaStmt::If {
                        condition: JavaExpr::Binary {
                            left: Box::new(JavaExpr::Name(value.clone())),
                            op: JavaBinaryOp::Equal,
                            right: Box::new(JavaExpr::Literal(JavaLiteral::Null)),
                        },
                        then_stmt: Box::new(JavaStmt::Throw(JavaExpr::New {
                            enclosing: None,
                            ty: JavaType::source_class("java.lang.NullPointerException"),
                            target_type: None,
                            args: vec![JavaExpr::Literal(JavaLiteral::String(
                                crate::ir::Utf16String::from("missing"),
                            ))],
                            anonymous_body: None,
                        })),
                        else_stmt: None,
                    },
                    JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        args: vec![
                            JavaExpr::Literal(JavaLiteral::String(crate::ir::Utf16String::from(
                                "key",
                            ))),
                            JavaExpr::Name(value),
                        ],
                    },
                ]),
            }),
        };

        let (delegation, helper, factory, carrier) =
            ConstructorSyntaxRecovery::remaining_constructor_prelude_helper(
                &constructor,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &[],
                JavaIdentifier::from_dex("computeConstructorArguments"),
                JavaIdentifier::from_dex("DexdecConstructorArguments"),
            )
            .expect("static super prelude should use a carrier");

        assert!(matches!(
            &delegation.root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::This,
                        args,
                    }] if matches!(args.as_slice(), [JavaExpr::Call { .. }])
                )
        ));
        assert!(matches!(
            &helper.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        args,
                    }] if args.len() == 2
                )
        ));
        assert!(matches!(
            &factory.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(statements.get(1), Some(JavaStmt::If { .. }))
                    && matches!(statements.last(), Some(JavaStmt::Return(Some(JavaExpr::New { .. }))))
        ));
        assert_eq!(carrier.fields.len(), 2);
        assert!(carrier.fields.iter().all(|field| field.ty == string_type));
    }

    #[test]
    fn untyped_static_super_argument_is_replayed_by_the_helper() {
        let value = JavaIdentifier::from_dex("value");
        let string_type = JavaType::source_class("java.lang.String");
        let static_field = JavaExpr::StaticField {
            owner: JavaType::source_class("com.example.SpecialNames"),
            name: JavaIdentifier::from_dex("THIS"),
        };
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("Child")),
            parameters: vec![JavaMethodParameter {
                annotations: Vec::new(),
                ty: string_type.clone(),
                name: value.clone(),
                varargs: false,
            }],
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![
                    JavaStmt::Expression(JavaExpr::Call {
                        receiver: None,
                        owner: Some(JavaType::source_class("com.example.Guards")),
                        type_arguments: Vec::new(),
                        method: JavaIdentifier::from_dex("check"),
                        args: vec![JavaExpr::Name(value.clone())],
                    }),
                    JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        args: vec![JavaExpr::Name(value), static_field.clone()],
                    },
                ]),
            }),
        };

        let (_, helper, _, carrier) =
            ConstructorSyntaxRecovery::remaining_constructor_prelude_helper(
                &constructor,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &[],
                JavaIdentifier::from_dex("computeConstructorArguments"),
                JavaIdentifier::from_dex("DexdecConstructorArguments"),
            )
            .expect("the static field does not require an inferred carrier type");

        assert_eq!(carrier.fields.len(), 1);
        assert_eq!(carrier.fields[0].ty, string_type);
        assert!(matches!(
            &helper.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::ConstructorInvocation { args, .. }]
                        if args.get(1) == Some(&static_field)
                )
        ));
    }

    #[test]
    fn qualified_outer_this_is_captured_by_the_constructor_factory() {
        let outer_type = JavaType::source_class("com.example.Outer");
        let input = JavaIdentifier::from_dex("input");
        let prepared = JavaIdentifier::from_dex("prepared");
        let string_type = JavaType::source_class("java.lang.String");
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("Inner")),
            parameters: vec![JavaMethodParameter {
                annotations: Vec::new(),
                ty: string_type.clone(),
                name: input.clone(),
                varargs: false,
            }],
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![
                    JavaStmt::Variable {
                        ty: string_type.clone(),
                        name: prepared.clone(),
                        value: Some(JavaExpr::Call {
                            receiver: Some(Box::new(JavaExpr::QualifiedThis(outer_type.clone()))),
                            owner: None,
                            type_arguments: Vec::new(),
                            method: JavaIdentifier::from_dex("prepare"),
                            args: vec![JavaExpr::Name(input)],
                        }),
                    },
                    JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        args: vec![JavaExpr::Name(prepared)],
                    },
                ]),
            }),
        };

        let (delegation, _, factory, carrier) =
            ConstructorSyntaxRecovery::remaining_constructor_prelude_helper(
                &constructor,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &[],
                JavaIdentifier::from_dex("computeConstructorArguments"),
                JavaIdentifier::from_dex("DexdecConstructorArguments"),
            )
            .expect("the enclosing instance should become a factory parameter");

        assert_eq!(factory.parameters.len(), 2);
        assert_eq!(factory.parameters[0].ty, outer_type.clone());
        assert!(matches!(
            &delegation.root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::ConstructorInvocation { args, .. }]
                        if matches!(
                            args.as_slice(),
                            [JavaExpr::Call { args, .. }]
                                if matches!(args.first(), Some(JavaExpr::QualifiedThis(ty)) if ty == &outer_type)
                        )
                )
        ));
        let mut qualified_this_types = QualifiedThisTypes::default();
        qualified_this_types.rewrite_statement(factory.body.unwrap().root);
        assert!(qualified_this_types.types.is_empty());
        assert_eq!(carrier.fields.len(), 1);
        assert_eq!(carrier.fields[0].ty, string_type);
    }

    #[test]
    fn super_constructor_prelude_uses_method_call_return_type() {
        let class_name = JavaIdentifier::from_dex("Child");
        let values = JavaIdentifier::from_dex("values");
        let collections = JavaType::source_class("kotlin.collections.CollectionsKt");
        let to_set = JavaIdentifier::from_dex("toSet");
        let set_type = JavaType::source_class("java.util.Set");
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(class_name),
            parameters: Vec::new(),
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![
                    JavaStmt::Variable {
                        ty: JavaType::source_class("java.util.ArrayList"),
                        name: values.clone(),
                        value: Some(JavaExpr::New {
                            enclosing: None,
                            ty: JavaType::source_class("java.util.ArrayList"),
                            target_type: None,
                            args: Vec::new(),
                            anonymous_body: None,
                        }),
                    },
                    JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        args: vec![JavaExpr::Call {
                            receiver: None,
                            owner: Some(collections.clone()),
                            type_arguments: Vec::new(),
                            method: to_set.clone(),
                            args: vec![JavaExpr::Name(values)],
                        }],
                    },
                ]),
            }),
        };
        let method_return_types =
            BTreeMap::from([((collections, to_set, 1), Some(set_type.clone()))]);

        let (_, _, _, carrier) = ConstructorSyntaxRecovery::remaining_constructor_prelude_helper(
            &constructor,
            &BTreeMap::new(),
            &method_return_types,
            &[],
            JavaIdentifier::from_dex("computeConstructorArguments"),
            JavaIdentifier::from_dex("DexdecConstructorArguments"),
        )
        .expect("method call return type should type the carrier");

        assert_eq!(carrier.fields.len(), 1);
        assert_eq!(carrier.fields[0].ty, set_type);
    }

    #[test]
    fn conditional_super_argument_uses_branch_method_return_types() {
        let view_type = JavaType::source_class("android.view.View");
        let fast_factory = JavaType::source_class("example.FastFactory");
        let fallback_factory = JavaType::source_class("example.FallbackFactory");
        let create = JavaIdentifier::from_dex("create");
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("Holder")),
            parameters: Vec::new(),
            throws: Vec::new(),
            body: None,
        };
        let call = |owner| JavaExpr::Call {
            receiver: None,
            owner: Some(owner),
            type_arguments: Vec::new(),
            method: create.clone(),
            args: Vec::new(),
        };
        let arguments = vec![JavaExpr::Conditional {
            condition: Box::new(JavaExpr::Literal(JavaLiteral::Boolean(true))),
            when_true: Box::new(call(fast_factory.clone())),
            when_false: Box::new(call(fallback_factory.clone())),
        }];
        let method_return_types = BTreeMap::from([
            ((fast_factory, create.clone(), 0), Some(view_type.clone())),
            ((fallback_factory, create, 0), Some(view_type.clone())),
        ]);

        assert_eq!(
            ConstructorSyntaxRecovery::infer_super_argument_types(
                &constructor,
                &[],
                &arguments,
                &method_return_types,
            ),
            Some(vec![view_type]),
        );
    }

    #[test]
    fn conditional_super_argument_accepts_shortened_string_literal_type() {
        let value = JavaIdentifier::from_dex("value");
        let string_type = JavaType::source_class("String");
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("Message")),
            parameters: vec![JavaMethodParameter {
                annotations: Vec::new(),
                ty: string_type.clone(),
                name: value.clone(),
                varargs: false,
            }],
            throws: Vec::new(),
            body: None,
        };
        let arguments = vec![JavaExpr::Conditional {
            condition: Box::new(JavaExpr::Binary {
                left: Box::new(JavaExpr::Name(value.clone())),
                op: JavaBinaryOp::NotEqual,
                right: Box::new(JavaExpr::Literal(JavaLiteral::Null)),
            }),
            when_true: Box::new(JavaExpr::Name(value)),
            when_false: Box::new(JavaExpr::Literal(JavaLiteral::String(
                crate::ir::Utf16String::from(""),
            ))),
        }];

        assert_eq!(
            ConstructorSyntaxRecovery::infer_super_argument_types(
                &constructor,
                &[],
                &arguments,
                &BTreeMap::new(),
            ),
            Some(vec![string_type]),
        );
    }

    #[test]
    fn super_constructor_prelude_preserves_contextual_literals_and_trailing_parameter_uses() {
        let source = JavaIdentifier::from_dex("source");
        let manager = JavaIdentifier::from_dex("constructorArguments");
        let context = JavaIdentifier::from_dex("context");
        let timestamp = JavaIdentifier::from_dex("timestamp");
        let manager_field = JavaIdentifier::from_dex("managerField");
        let source_type = JavaType::source_class("example.Source");
        let manager_type = JavaType::source_class("example.Manager");
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("Worker")),
            parameters: vec![
                JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: source_type.clone(),
                    name: source.clone(),
                    varargs: false,
                },
                JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: manager_type.clone(),
                    name: manager.clone(),
                    varargs: false,
                },
            ],
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![
                    JavaStmt::Variable {
                        ty: JavaType::source_class("example.Context"),
                        name: context.clone(),
                        value: Some(JavaExpr::Call {
                            receiver: Some(Box::new(JavaExpr::Name(source.clone()))),
                            owner: None,
                            type_arguments: Vec::new(),
                            method: JavaIdentifier::from_dex("getContext"),
                            args: Vec::new(),
                        }),
                    },
                    JavaStmt::Variable {
                        ty: JavaType::int(),
                        name: timestamp.clone(),
                        value: Some(JavaExpr::Literal(JavaLiteral::Integer(0))),
                    },
                    JavaStmt::If {
                        condition: JavaExpr::Call {
                            receiver: Some(Box::new(JavaExpr::Name(source.clone()))),
                            owner: None,
                            type_arguments: Vec::new(),
                            method: JavaIdentifier::from_dex("isReady"),
                            args: Vec::new(),
                        },
                        then_stmt: Box::new(JavaStmt::Assign {
                            target: JavaExpr::Name(timestamp.clone()),
                            op: JavaAssignOp::Assign,
                            value: JavaExpr::Literal(JavaLiteral::Integer(1)),
                        }),
                        else_stmt: None,
                    },
                    JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        args: vec![
                            JavaExpr::Literal(JavaLiteral::Integer(1)),
                            JavaExpr::Name(context),
                            JavaExpr::Name(source.clone()),
                            JavaExpr::Name(timestamp),
                        ],
                    },
                    JavaStmt::Assign {
                        target: JavaExpr::Field {
                            owner: Box::new(JavaExpr::This),
                            name: manager_field,
                        },
                        op: JavaAssignOp::Assign,
                        value: JavaExpr::Name(manager.clone()),
                    },
                    JavaStmt::Expression(JavaExpr::Call {
                        receiver: Some(Box::new(JavaExpr::Name(source))),
                        owner: None,
                        type_arguments: Vec::new(),
                        method: JavaIdentifier::from_dex("afterConstruction"),
                        args: Vec::new(),
                    }),
                ]),
            }),
        };

        let (delegation, helper, factory, carrier) =
            ConstructorSyntaxRecovery::remaining_constructor_prelude_with_trailing_helper(
                &constructor,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &[],
                JavaIdentifier::from_dex("computeConstructorArguments"),
                JavaIdentifier::from_dex("DexdecConstructorArguments"),
            )
            .expect("trailing parameter uses should use a carrier");

        assert!(matches!(
            delegation.root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::This,
                        args,
                    }] if matches!(args.as_slice(), [JavaExpr::Call { .. }])
                )
        ));
        assert!(matches!(
            &helper.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::Super,
                            args,
                        },
                        JavaStmt::Variable { .. },
                        JavaStmt::Variable { .. },
                        JavaStmt::Assign { .. },
                        JavaStmt::Expression(JavaExpr::Call { .. }),
                    ] if args.len() == 4
                        && matches!(args.first(), Some(JavaExpr::Literal(JavaLiteral::Integer(1))))
                )
        ));
        assert_ne!(helper.parameters[0].name, manager);
        assert!(matches!(
            &factory.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(statements.get(2), Some(JavaStmt::If { .. }))
                    && matches!(statements.last(), Some(JavaStmt::Return(Some(JavaExpr::New { .. }))))
        ));
        assert_eq!(carrier.fields.len(), 5);
        assert_eq!(carrier.fields[0].name.as_str(), "argument1");
        assert_eq!(carrier.fields[3].ty, source_type);
        assert_eq!(carrier.fields[4].ty, manager_type);
    }

    #[test]
    fn this_constructor_prelude_carries_locals_used_after_delegation() {
        let phase = JavaIdentifier::from_dex("phase");
        let relation = JavaIdentifier::from_dex("relation");
        let shared = JavaIdentifier::from_dex("shared");
        let list_type = JavaType::source_class("java.util.List");
        let parameter = |ty, name| JavaMethodParameter {
            annotations: Vec::new(),
            ty,
            name,
            varargs: false,
        };
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("PhaseContent")),
            parameters: vec![
                parameter(JavaType::source_class("example.Phase"), phase.clone()),
                parameter(JavaType::source_class("example.Relation"), relation.clone()),
            ],
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![
                    JavaStmt::Variable {
                        ty: list_type.clone(),
                        name: shared.clone(),
                        value: Some(JavaExpr::StaticField {
                            owner: JavaType::source_class("example.PhaseContent"),
                            name: JavaIdentifier::from_dex("EMPTY"),
                        }),
                    },
                    JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::This,
                        args: vec![
                            JavaExpr::Name(phase),
                            JavaExpr::Name(relation),
                            JavaExpr::Name(shared.clone()),
                        ],
                    },
                    JavaStmt::Expression(JavaExpr::Call {
                        receiver: Some(Box::new(JavaExpr::Name(shared.clone()))),
                        owner: None,
                        type_arguments: Vec::new(),
                        method: JavaIdentifier::from_dex("isEmpty"),
                        args: Vec::new(),
                    }),
                ]),
            }),
        };

        let (_, helper, _, carrier) =
            ConstructorSyntaxRecovery::remaining_constructor_prelude_with_trailing_helper(
                &constructor,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &[],
                JavaIdentifier::from_dex("computeConstructorArguments"),
                JavaIdentifier::from_dex("DexdecConstructorArguments"),
            )
            .expect("this prelude and trailing local should use a carrier");

        assert!(matches!(
            &helper.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(statements.as_slice(), [
                    JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::This,
                        args,
                    },
                    JavaStmt::Variable { name, value: Some(JavaExpr::Field { .. }), .. },
                    JavaStmt::Expression(JavaExpr::Call { .. }),
                ] if args.len() == 3 && name == &shared)
        ));
        assert_eq!(carrier.fields.len(), 4);
        assert_eq!(carrier.fields[2].ty, list_type);
        assert_eq!(carrier.fields[3].ty, list_type);
    }

    #[test]
    fn varargs_super_prelude_carries_locals_used_after_super() {
        let values = JavaIdentifier::from_dex("values");
        let prepared = JavaIdentifier::from_dex("prepared");
        let value_type = JavaType::source_class("example.Value");
        let values_type = JavaType::array(value_type);
        let list_type = JavaType::source_class("java.util.List");
        let constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(JavaIdentifier::from_dex("Selector")),
            parameters: vec![JavaMethodParameter {
                annotations: Vec::new(),
                ty: values_type,
                name: values.clone(),
                varargs: true,
            }],
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![
                    JavaStmt::Variable {
                        ty: list_type.clone(),
                        name: prepared.clone(),
                        value: Some(JavaExpr::Call {
                            receiver: None,
                            owner: Some(JavaType::source_class("java.util.Arrays")),
                            type_arguments: Vec::new(),
                            method: JavaIdentifier::from_dex("asList"),
                            args: vec![JavaExpr::Name(values)],
                        }),
                    },
                    JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        args: Vec::new(),
                    },
                    JavaStmt::Expression(JavaExpr::Call {
                        receiver: Some(Box::new(JavaExpr::Name(prepared.clone()))),
                        owner: None,
                        type_arguments: Vec::new(),
                        method: JavaIdentifier::from_dex("clear"),
                        args: Vec::new(),
                    }),
                ]),
            }),
        };

        let (delegation, helper, factory, carrier) =
            ConstructorSyntaxRecovery::remaining_constructor_prelude_with_trailing_helper(
                &constructor,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &[],
                JavaIdentifier::from_dex("computeConstructorArguments"),
                JavaIdentifier::from_dex("DexdecConstructorArguments"),
            )
            .expect("a varargs prelude local should be carried across super");

        assert!(matches!(
            delegation.root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::This,
                        args,
                    }] if matches!(args.as_slice(), [JavaExpr::Call { .. }])
                )
        ));
        assert!(matches!(
            &helper.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::Super,
                            args,
                        },
                        JavaStmt::Variable { ty, name, value: Some(JavaExpr::Field { .. }) },
                        JavaStmt::Expression(JavaExpr::Call { receiver: Some(receiver), .. }),
                    ] if args.is_empty()
                        && ty == &list_type
                        && name == &prepared
                        && matches!(receiver.as_ref(), JavaExpr::Name(name) if name == &prepared)
                )
        ));
        assert!(factory.parameters[0].varargs);
        assert!(matches!(
            &factory.body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.last(),
                    Some(JavaStmt::Return(Some(JavaExpr::New { args, .. })))
                        if matches!(args.as_slice(), [JavaExpr::Name(name)] if name == &prepared)
                )
        ));
        assert_eq!(carrier.fields.len(), 1);
        assert_eq!(carrier.fields[0].ty, list_type);
    }

    #[test]
    fn multi_constructor_bindings_use_a_typed_carrier() {
        let class_name = JavaIdentifier::from_dex("Defaults");
        let input = JavaIdentifier::from_dex("input");
        let first = JavaIdentifier::from_dex("first");
        let second = JavaIdentifier::from_dex("second");
        let string_type = JavaType::source_class("java.lang.String");
        let target_constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(class_name.clone()),
            parameters: vec![
                JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: string_type.clone(),
                    name: first.clone(),
                    varargs: false,
                },
                JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: JavaType::int(),
                    name: second.clone(),
                    varargs: false,
                },
            ],
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(Vec::new()),
            }),
        };
        let parsing_constructor = JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            compiler_generated: false,
            kind: JavaMethodDeclarationKind::Constructor,
            type_parameters: Vec::new(),
            return_type: None,
            name: Some(class_name.clone()),
            parameters: vec![JavaMethodParameter {
                annotations: Vec::new(),
                ty: JavaType::source_class("java.lang.Object"),
                name: input.clone(),
                varargs: false,
            }],
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(vec![
                    JavaStmt::Variable {
                        ty: string_type,
                        name: first.clone(),
                        value: Some(JavaExpr::Literal(JavaLiteral::Null)),
                    },
                    JavaStmt::Variable {
                        ty: JavaType::int(),
                        name: second.clone(),
                        value: Some(JavaExpr::Literal(JavaLiteral::Integer(0))),
                    },
                    JavaStmt::If {
                        condition: JavaExpr::Binary {
                            left: Box::new(JavaExpr::Name(input.clone())),
                            op: JavaBinaryOp::NotEqual,
                            right: Box::new(JavaExpr::Literal(JavaLiteral::Null)),
                        },
                        then_stmt: Box::new(JavaStmt::Block(vec![
                            JavaStmt::Assign {
                                target: JavaExpr::Name(first.clone()),
                                op: JavaAssignOp::Assign,
                                value: JavaExpr::Call {
                                    receiver: Some(Box::new(JavaExpr::Name(input))),
                                    owner: None,
                                    type_arguments: Vec::new(),
                                    method: JavaIdentifier::from_dex("toString"),
                                    args: Vec::new(),
                                },
                            },
                            JavaStmt::Assign {
                                target: JavaExpr::Name(second.clone()),
                                op: JavaAssignOp::Assign,
                                value: JavaExpr::Literal(JavaLiteral::Integer(1)),
                            },
                        ])),
                        else_stmt: None,
                    },
                    JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::This,
                        args: vec![JavaExpr::Name(first), JavaExpr::Name(second)],
                    },
                ]),
            }),
        };
        let mut declaration = JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Class,
            name: class_name,
            type_parameters: Vec::new(),
            extends: None,
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: Vec::new(),
            methods: vec![target_constructor, parsing_constructor],
            nested: Vec::new(),
        };

        ConstructorSyntaxRecovery::extract_remaining_constructor_preludes(
            &mut declaration,
            &BTreeMap::new(),
        );

        assert_eq!(declaration.methods.len(), 4);
        assert_eq!(declaration.nested.len(), 1);
        assert_eq!(declaration.nested[0].fields.len(), 2);
        assert_eq!(
            declaration.nested[0].modifiers,
            vec![
                JavaModifier::Private,
                JavaModifier::Static,
                JavaModifier::Final
            ]
        );
        assert!(matches!(
            &declaration.methods[1].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.as_slice(),
                    [JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::This,
                        args,
                    }] if matches!(args.as_slice(), [JavaExpr::Call { .. }])
                )
        ));
        assert!(matches!(
            &declaration.methods[3].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(statements.last(), Some(JavaStmt::Return(Some(JavaExpr::New { args, .. }))) if args.len() == 2)
        ));
    }

    #[test]
    fn replayable_conditional_arguments_allow_later_evaluations_to_inline() {
        let mask = JavaIdentifier::from_dex("mask");
        let fallback = JavaIdentifier::from_dex("fallback");
        let current_time = JavaIdentifier::from_dex("currentTimeMillis");
        let condition = JavaExpr::Binary {
            op: JavaBinaryOp::NotEqual,
            left: Box::new(JavaExpr::Name(mask)),
            right: Box::new(JavaExpr::Literal(JavaLiteral::Integer(0))),
        };
        let mut statements = vec![
            JavaStmt::Variable {
                ty: JavaType::Primitive(crate::language::java::JavaPrimitiveType::Long),
                name: current_time.clone(),
                value: Some(JavaExpr::Literal(JavaLiteral::Long(0))),
            },
            JavaStmt::If {
                condition: condition.clone(),
                then_stmt: Box::new(JavaStmt::Assign {
                    target: JavaExpr::Name(current_time.clone()),
                    op: JavaAssignOp::Assign,
                    value: JavaExpr::Call {
                        receiver: None,
                        owner: Some(JavaType::source_class("java.lang.System")),
                        type_arguments: Vec::new(),
                        method: JavaIdentifier::from_dex("currentTimeMillis"),
                        args: Vec::new(),
                    },
                }),
                else_stmt: None,
            },
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::This,
                args: vec![
                    JavaExpr::Conditional {
                        condition: Box::new(condition),
                        when_true: Box::new(JavaExpr::Name(fallback)),
                        when_false: Box::new(JavaExpr::Literal(JavaLiteral::Long(0))),
                    },
                    JavaExpr::Name(current_time),
                ],
            },
        ];

        ConstructorSyntaxRecovery::schedule_arguments(&mut statements);

        assert!(matches!(
            statements.as_slice(),
            [JavaStmt::ConstructorInvocation { args, .. }]
                if matches!(
                    args.as_slice(),
                    [
                        JavaExpr::Conditional { .. },
                        JavaExpr::Conditional { when_true, .. },
                    ] if matches!(when_true.as_ref(), JavaExpr::Call { method, .. }
                        if method == &JavaIdentifier::from_dex("currentTimeMillis"))
                )
        ));
    }

    #[test]
    fn branch_local_array_writes_inline_as_an_initializer() {
        let condition = JavaExpr::Name(JavaIdentifier::from_dex("useDefault"));
        let array = JavaIdentifier::from_dex("values");
        let fallback = JavaIdentifier::from_dex("fallback");
        let mut statements = vec![
            JavaStmt::Variable {
                ty: JavaType::array(JavaType::source_class("java.lang.Long")),
                name: array.clone(),
                value: Some(JavaExpr::Literal(JavaLiteral::Null)),
            },
            JavaStmt::If {
                condition: condition.clone(),
                then_stmt: Box::new(JavaStmt::Block(vec![
                    JavaStmt::Assign {
                        target: JavaExpr::Name(array.clone()),
                        op: JavaAssignOp::Assign,
                        value: JavaExpr::NewArray {
                            element_type: JavaType::source_class("java.lang.Long"),
                            dimensions: vec![JavaExpr::Literal(JavaLiteral::Integer(2))],
                            initializer: Vec::new(),
                        },
                    },
                    JavaStmt::Assign {
                        target: JavaExpr::ArrayAccess {
                            array: Box::new(JavaExpr::Name(array.clone())),
                            index: Box::new(JavaExpr::Literal(JavaLiteral::Integer(0))),
                        },
                        op: JavaAssignOp::Assign,
                        value: JavaExpr::Literal(JavaLiteral::Long(1000)),
                    },
                    JavaStmt::Assign {
                        target: JavaExpr::ArrayAccess {
                            array: Box::new(JavaExpr::Name(array.clone())),
                            index: Box::new(JavaExpr::Literal(JavaLiteral::Integer(1))),
                        },
                        op: JavaAssignOp::Assign,
                        value: JavaExpr::Literal(JavaLiteral::Long(15000)),
                    },
                ])),
                else_stmt: None,
            },
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::This,
                args: vec![JavaExpr::Conditional {
                    condition: Box::new(condition),
                    when_true: Box::new(JavaExpr::Name(array)),
                    when_false: Box::new(JavaExpr::Name(fallback)),
                }],
            },
        ];

        ConstructorSyntaxRecovery::schedule_arguments(&mut statements);

        assert!(matches!(
            statements.as_slice(),
            [JavaStmt::ConstructorInvocation { args, .. }]
                if matches!(
                    args.as_slice(),
                    [JavaExpr::Conditional { when_true, .. }]
                        if matches!(when_true.as_ref(), JavaExpr::NewArray {
                            dimensions,
                            initializer,
                            ..
                        } if dimensions.is_empty() && initializer.len() == 2)
                )
        ));
    }

    #[test]
    fn one_use_branch_local_inlines_into_a_constructor_argument() {
        let condition = JavaExpr::Name(JavaIdentifier::from_dex("useDefault"));
        let defaults = JavaIdentifier::from_dex("defaults");
        let temporary = JavaIdentifier::from_dex("temporary");
        let fallback = JavaIdentifier::from_dex("fallback");
        let temporary_value = JavaExpr::NewArray {
            element_type: JavaType::source_class("kotlin.Pair"),
            dimensions: Vec::new(),
            initializer: vec![JavaExpr::Literal(JavaLiteral::Integer(1))],
        };
        let map_of = JavaIdentifier::from_dex("mapOf");
        let mut statements = vec![
            JavaStmt::Variable {
                ty: JavaType::source_class("java.util.Map"),
                name: defaults.clone(),
                value: Some(JavaExpr::Literal(JavaLiteral::Null)),
            },
            JavaStmt::If {
                condition: condition.clone(),
                then_stmt: Box::new(JavaStmt::Block(vec![
                    JavaStmt::Variable {
                        ty: JavaType::array(JavaType::source_class("kotlin.Pair")),
                        name: temporary.clone(),
                        value: Some(temporary_value.clone()),
                    },
                    JavaStmt::Assign {
                        target: JavaExpr::Name(defaults.clone()),
                        op: JavaAssignOp::Assign,
                        value: JavaExpr::Call {
                            receiver: None,
                            owner: Some(JavaType::source_class("kotlin.collections.MapsKt")),
                            type_arguments: Vec::new(),
                            method: map_of.clone(),
                            args: vec![JavaExpr::Name(temporary)],
                        },
                    },
                ])),
                else_stmt: None,
            },
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::This,
                args: vec![JavaExpr::Conditional {
                    condition: Box::new(condition),
                    when_true: Box::new(JavaExpr::Name(defaults)),
                    when_false: Box::new(JavaExpr::Name(fallback)),
                }],
            },
        ];

        ConstructorSyntaxRecovery::schedule_arguments(&mut statements);

        assert!(matches!(
            statements.as_slice(),
            [JavaStmt::ConstructorInvocation { args, .. }]
                if matches!(
                    args.as_slice(),
                    [JavaExpr::Conditional { when_true, .. }]
                        if matches!(when_true.as_ref(), JavaExpr::Call { method, args, .. }
                            if method == &map_of && args == &vec![temporary_value])
                )
        ));
    }

    #[test]
    fn duplicated_branch_local_is_not_inlined() {
        let condition = JavaExpr::Name(JavaIdentifier::from_dex("useDefault"));
        let output = JavaIdentifier::from_dex("output");
        let temporary = JavaIdentifier::from_dex("temporary");
        let mut dataflow = ConstructorDataflow::default();

        let result = dataflow.evaluate(&[
            JavaStmt::Variable {
                ty: JavaType::source_class("java.lang.Object"),
                name: output.clone(),
                value: Some(JavaExpr::Literal(JavaLiteral::Null)),
            },
            JavaStmt::If {
                condition,
                then_stmt: Box::new(JavaStmt::Block(vec![
                    JavaStmt::Variable {
                        ty: JavaType::source_class("java.lang.Object"),
                        name: temporary.clone(),
                        value: Some(JavaExpr::New {
                            enclosing: None,
                            ty: JavaType::source_class("java.lang.Object"),
                            target_type: None,
                            args: Vec::new(),
                            anonymous_body: None,
                        }),
                    },
                    JavaStmt::Assign {
                        target: JavaExpr::Name(output),
                        op: JavaAssignOp::Assign,
                        value: JavaExpr::Call {
                            receiver: None,
                            owner: Some(JavaType::source_class("example.Factory")),
                            type_arguments: Vec::new(),
                            method: JavaIdentifier::from_dex("combine"),
                            args: vec![
                                JavaExpr::Name(temporary.clone()),
                                JavaExpr::Name(temporary),
                            ],
                        },
                    },
                ])),
                else_stmt: None,
            },
        ]);

        assert!(result.is_none());
    }

    #[test]
    fn interleaved_branch_local_evaluations_are_not_reordered() {
        let condition = JavaExpr::Name(JavaIdentifier::from_dex("useDefault"));
        let output = JavaIdentifier::from_dex("output");
        let marker = JavaIdentifier::from_dex("marker");
        let temporary = JavaIdentifier::from_dex("temporary");
        let call = |method: &str, args: Vec<JavaExpr>| JavaExpr::Call {
            receiver: None,
            owner: Some(JavaType::source_class("example.Factory")),
            type_arguments: Vec::new(),
            method: JavaIdentifier::from_dex(method),
            args,
        };
        let mut dataflow = ConstructorDataflow::default();

        let result = dataflow.evaluate(&[
            JavaStmt::Variable {
                ty: JavaType::source_class("java.lang.Object"),
                name: output.clone(),
                value: Some(JavaExpr::Literal(JavaLiteral::Null)),
            },
            JavaStmt::Variable {
                ty: JavaType::source_class("java.lang.Object"),
                name: marker.clone(),
                value: Some(JavaExpr::Literal(JavaLiteral::Null)),
            },
            JavaStmt::If {
                condition,
                then_stmt: Box::new(JavaStmt::Block(vec![
                    JavaStmt::Variable {
                        ty: JavaType::source_class("java.lang.Object"),
                        name: temporary.clone(),
                        value: Some(call("first", Vec::new())),
                    },
                    JavaStmt::Assign {
                        target: JavaExpr::Name(marker),
                        op: JavaAssignOp::Assign,
                        value: call("second", Vec::new()),
                    },
                    JavaStmt::Assign {
                        target: JavaExpr::Name(output),
                        op: JavaAssignOp::Assign,
                        value: call("wrap", vec![JavaExpr::Name(temporary)]),
                    },
                ])),
                else_stmt: None,
            },
        ]);

        assert!(result.is_none());
    }

    #[test]
    fn deferred_branch_local_capture_is_not_inlined() {
        let condition = JavaExpr::Name(JavaIdentifier::from_dex("useDefault"));
        let output = JavaIdentifier::from_dex("output");
        let temporary = JavaIdentifier::from_dex("temporary");
        let mut dataflow = ConstructorDataflow::default();

        let result = dataflow.evaluate(&[
            JavaStmt::Variable {
                ty: JavaType::source_class("java.lang.Object"),
                name: output.clone(),
                value: Some(JavaExpr::Literal(JavaLiteral::Null)),
            },
            JavaStmt::If {
                condition,
                then_stmt: Box::new(JavaStmt::Block(vec![
                    JavaStmt::Variable {
                        ty: JavaType::source_class("java.lang.Object"),
                        name: temporary.clone(),
                        value: Some(JavaExpr::New {
                            enclosing: None,
                            ty: JavaType::source_class("java.lang.Object"),
                            target_type: None,
                            args: Vec::new(),
                            anonymous_body: None,
                        }),
                    },
                    JavaStmt::Assign {
                        target: JavaExpr::Name(output),
                        op: JavaAssignOp::Assign,
                        value: JavaExpr::Lambda {
                            parameters: Vec::new(),
                            body: Box::new(JavaExpr::Name(temporary)),
                        },
                    },
                ])),
                else_stmt: None,
            },
        ]);

        assert!(result.is_none());
    }

    #[test]
    fn array_write_aggregation_preserves_casted_constructions() {
        let array = JavaIdentifier::from_dex("pairs");
        let mut dataflow = ConstructorDataflow::default();
        dataflow
            .evaluate(&[
                JavaStmt::Variable {
                    ty: JavaType::array(JavaType::source_class("kotlin.Pair")),
                    name: array.clone(),
                    value: Some(JavaExpr::Cast {
                        ty: JavaType::array(JavaType::source_class("kotlin.Pair")),
                        value: Box::new(JavaExpr::NewArray {
                            element_type: JavaType::source_class("kotlin.Pair"),
                            dimensions: vec![JavaExpr::Literal(JavaLiteral::Integer(1))],
                            initializer: Vec::new(),
                        }),
                    }),
                },
                JavaStmt::Assign {
                    target: JavaExpr::ArrayAccess {
                        array: Box::new(JavaExpr::Name(array.clone())),
                        index: Box::new(JavaExpr::Literal(JavaLiteral::Integer(0))),
                    },
                    op: JavaAssignOp::Assign,
                    value: JavaExpr::Name(JavaIdentifier::from_dex("pair")),
                },
            ])
            .expect("casted array dataflow");

        dataflow.finalize_arrays().expect("array initializer");

        assert!(matches!(
            &dataflow.values[&array],
            JavaExpr::Cast { value, .. }
                if matches!(value.as_ref(), JavaExpr::NewArray {
                    dimensions,
                    initializer,
                    ..
                } if dimensions.is_empty() && initializer.len() == 1)
        ));
    }

    #[test]
    fn string_builder_append_chain_inlines_into_super_argument() {
        let builder = JavaIdentifier::from_dex("builder");
        let append = JavaIdentifier::from_dex("append");
        let mut statements = vec![
            JavaStmt::Variable {
                ty: JavaType::source_class("java.lang.StringBuilder"),
                name: builder.clone(),
                value: Some(JavaExpr::New {
                    enclosing: None,
                    ty: JavaType::source_class("java.lang.StringBuilder"),
                    target_type: None,
                    args: vec![JavaExpr::Literal(JavaLiteral::String(
                        crate::ir::Utf16String::from("status: "),
                    ))],
                    anonymous_body: None,
                }),
            },
            JavaStmt::Expression(JavaExpr::Call {
                receiver: Some(Box::new(JavaExpr::Name(builder.clone()))),
                owner: None,
                type_arguments: Vec::new(),
                method: append.clone(),
                args: vec![JavaExpr::Literal(JavaLiteral::Integer(500))],
            }),
            JavaStmt::Expression(JavaExpr::Call {
                receiver: Some(Box::new(JavaExpr::Name(builder.clone()))),
                owner: None,
                type_arguments: Vec::new(),
                method: append,
                args: vec![JavaExpr::Literal(JavaLiteral::String(
                    crate::ir::Utf16String::from(" failed"),
                ))],
            }),
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                args: vec![JavaExpr::Call {
                    receiver: Some(Box::new(JavaExpr::Name(builder))),
                    owner: None,
                    type_arguments: Vec::new(),
                    method: JavaIdentifier::from_dex("toString"),
                    args: Vec::new(),
                }],
            },
        ];

        ConstructorSyntaxRecovery::schedule_arguments(&mut statements);

        let [JavaStmt::ConstructorInvocation { args, .. }] = statements.as_slice() else {
            panic!("builder prelude should be folded into the invocation");
        };
        let [JavaExpr::Call {
            receiver: Some(receiver),
            method,
            ..
        }] = args.as_slice()
        else {
            panic!("super argument should remain a toString call");
        };
        assert_eq!(method.as_str(), "toString");
        assert!(matches!(
            receiver.as_ref(),
            JavaExpr::Call {
                receiver: Some(inner),
                method,
                ..
            } if method.as_str() == "append"
                && matches!(
                    inner.as_ref(),
                    JavaExpr::Call { method, .. } if method.as_str() == "append"
                )
        ));
    }

    #[test]
    fn string_builder_self_append_is_not_duplicated() {
        let builder = JavaIdentifier::from_dex("builder");
        let mut statements = vec![
            JavaStmt::Variable {
                ty: JavaType::source_class("java.lang.StringBuilder"),
                name: builder.clone(),
                value: Some(JavaExpr::New {
                    enclosing: None,
                    ty: JavaType::source_class("java.lang.StringBuilder"),
                    target_type: None,
                    args: Vec::new(),
                    anonymous_body: None,
                }),
            },
            JavaStmt::Expression(JavaExpr::Call {
                receiver: Some(Box::new(JavaExpr::Name(builder.clone()))),
                owner: None,
                type_arguments: Vec::new(),
                method: JavaIdentifier::from_dex("append"),
                args: vec![JavaExpr::Name(builder.clone())],
            }),
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                args: vec![JavaExpr::Call {
                    receiver: Some(Box::new(JavaExpr::Name(builder))),
                    owner: None,
                    type_arguments: Vec::new(),
                    method: JavaIdentifier::from_dex("toString"),
                    args: Vec::new(),
                }],
            },
        ];

        ConstructorSyntaxRecovery::schedule_arguments(&mut statements);

        assert_eq!(statements.len(), 3);
    }

    #[test]
    fn non_jdk_string_builder_is_not_assumed_to_return_its_receiver() {
        let builder = JavaIdentifier::from_dex("builder");
        let mut statements = vec![
            JavaStmt::Variable {
                ty: JavaType::source_class("com.example.StringBuilder"),
                name: builder.clone(),
                value: Some(JavaExpr::New {
                    enclosing: None,
                    ty: JavaType::source_class("com.example.StringBuilder"),
                    target_type: None,
                    args: Vec::new(),
                    anonymous_body: None,
                }),
            },
            JavaStmt::Expression(JavaExpr::Call {
                receiver: Some(Box::new(JavaExpr::Name(builder.clone()))),
                owner: None,
                type_arguments: Vec::new(),
                method: JavaIdentifier::from_dex("append"),
                args: vec![JavaExpr::Literal(JavaLiteral::Integer(1))],
            }),
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                args: vec![JavaExpr::Name(builder)],
            },
        ];

        ConstructorSyntaxRecovery::schedule_arguments(&mut statements);

        assert_eq!(statements.len(), 3);
    }

    #[test]
    fn direct_object_super_after_a_prelude_is_implicit() {
        let prelude = JavaStmt::Expression(JavaExpr::Call {
            receiver: None,
            owner: Some(JavaType::source_class("java.lang.System")),
            type_arguments: Vec::new(),
            method: JavaIdentifier::from_dex("currentTimeMillis"),
            args: Vec::new(),
        });
        let invocation = JavaStmt::ConstructorInvocation {
            target: JavaConstructorTarget::Super,
            args: Vec::new(),
        };
        let mut direct_object = vec![prelude.clone(), invocation.clone()];
        let mut custom_superclass = vec![prelude, invocation];

        ConstructorSyntaxRecovery::remove_implicit_super(&mut direct_object, true);
        ConstructorSyntaxRecovery::remove_implicit_super(&mut custom_superclass, false);

        assert_eq!(direct_object.len(), 1);
        assert_eq!(custom_superclass.len(), 2);
    }
}
