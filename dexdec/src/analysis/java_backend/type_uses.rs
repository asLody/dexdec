use crate::frontend::{AnnotationNode, DexValue};
use crate::ir::generic_types::JvmTypeSignature;
use crate::ir::ty::ArgType;

use super::java_model::JavaClassModel;

pub(super) struct ClassTypeUses;

impl ClassTypeUses {
    pub(super) fn collect(class: &JavaClassModel) -> Vec<ArgType> {
        let mut types = Vec::new();
        let mut pending = vec![class];
        while let Some(class) = pending.pop() {
            pending.extend(class.nested.iter().rev());
            Self::collect_class(class, &mut types);
        }
        types
    }

    fn collect_class(class: &JavaClassModel, types: &mut Vec<ArgType>) {
        if let Some(extends) = &class.declaration.extends {
            types.push(extends.clone());
        }
        AnnotationTypeUses::collect(&class.declaration.annotations, types);
        types.extend(class.declaration.implements.iter().cloned());
        if let Some(signature) = &class.declaration.signature {
            GenericTypeUses::class(&signature.super_class, types);
            for interface in &signature.super_interfaces {
                GenericTypeUses::class(interface, types);
            }
            Self::collect_type_parameter_bounds(&signature.type_parameters, types);
        }
        for field in &class.fields {
            AnnotationTypeUses::collect(&field.annotations, types);
            types.push(field.field_type.clone());
            if let Some(initializer) = &field.initializer {
                DexValueTypeUses::collect(initializer, types);
            }
            if let Some(signature) = &field.signature {
                GenericTypeUses::ty(signature, types);
            }
        }
        for method in &class.methods {
            JavaMethodTypeUses::collect_into(method, types);
        }
    }

    fn collect_type_parameter_bounds(
        parameters: &[crate::ir::generic_types::TypeParameter],
        types: &mut Vec<ArgType>,
    ) {
        for parameter in parameters {
            if let Some(bound) = &parameter.class_bound {
                GenericTypeUses::ty(bound, types);
            }
            for bound in &parameter.interface_bounds {
                GenericTypeUses::ty(bound, types);
            }
        }
    }
}

pub(super) struct JavaMethodTypeUses;

impl JavaMethodTypeUses {
    pub(super) fn collect(method: &super::java_model::JavaMethodModel) -> Vec<ArgType> {
        let mut types = Vec::new();
        Self::collect_into(method, &mut types);
        types
    }

    fn collect_into(method: &super::java_model::JavaMethodModel, types: &mut Vec<ArgType>) {
        AnnotationTypeUses::collect(&method.declaration.annotations, types);
        if method.declaration.override_semantics.is_some() {
            types.push(ArgType::object("java/lang/Override"));
        }
        if let Some(return_type) = &method.declaration.return_type {
            types.push(return_type.clone());
        }
        if let Some(return_type) = &method.declaration.source_return_type {
            types.push(return_type.clone());
        }
        if let Some(interface) = &method.declaration.function_interface {
            GenericTypeUses::ty(interface, types);
        }
        for parameter in &method.declaration.parameters {
            types.push(parameter.ty.clone());
            AnnotationTypeUses::collect(&parameter.annotations, types);
        }
        types.extend(
            method
                .declaration
                .source_parameter_types
                .iter()
                .flatten()
                .cloned(),
        );
        types.extend(method.declaration.throws.iter().cloned());
        if let Some(signature) = &method.declaration.signature {
            GenericTypeUses::ty(&signature.return_type, types);
            for parameter in &signature.parameter_types {
                GenericTypeUses::ty(parameter, types);
            }
            for exception in &signature.throws {
                GenericTypeUses::ty(exception, types);
            }
            ClassTypeUses::collect_type_parameter_bounds(&signature.type_parameters, types);
        }
        if let Some(body) = &method.body {
            types.extend(body.type_uses().cloned());
        }
    }
}

pub(super) struct GenericTypeUses;

impl GenericTypeUses {
    pub(super) fn field_contract(
        contract: &crate::ir::generic_types::GenericFieldContract,
        types: &mut Vec<ArgType>,
    ) {
        Self::class(&contract.owner, types);
        Self::ty(&contract.signature, types);
    }

    pub(super) fn method_contract(
        contract: &crate::ir::generic_types::GenericMethodContract,
        types: &mut Vec<ArgType>,
    ) {
        Self::class(&contract.owner, types);
        for parameter in &contract.signature.parameter_types {
            Self::ty(parameter, types);
        }
        Self::ty(&contract.signature.return_type, types);
        for exception in &contract.signature.throws {
            Self::ty(exception, types);
        }
        ClassTypeUses::collect_type_parameter_bounds(&contract.signature.type_parameters, types);
    }

    pub(super) fn ty(signature: &JvmTypeSignature, types: &mut Vec<ArgType>) {
        let mut pending = vec![GenericTypeTask::Type(signature)];
        while let Some(task) = pending.pop() {
            match task {
                GenericTypeTask::Type(JvmTypeSignature::Array(element)) => {
                    pending.push(GenericTypeTask::Type(element));
                }
                GenericTypeTask::Type(JvmTypeSignature::ClassType(class))
                | GenericTypeTask::Class(class) => {
                    types.push(ArgType::object(&class.erased_name()));
                    pending.extend(
                        class
                            .inner_segments
                            .iter()
                            .rev()
                            .flat_map(|segment| segment.type_arguments.iter().rev())
                            .map(GenericTypeTask::Argument),
                    );
                    pending.extend(
                        class
                            .type_arguments
                            .iter()
                            .rev()
                            .map(GenericTypeTask::Argument),
                    );
                }
                GenericTypeTask::Argument(argument) => match argument {
                    crate::ir::generic_types::TypeArgument::Unbounded => {}
                    crate::ir::generic_types::TypeArgument::Extends(ty)
                    | crate::ir::generic_types::TypeArgument::Super(ty)
                    | crate::ir::generic_types::TypeArgument::Exact(ty) => {
                        pending.push(GenericTypeTask::Type(ty));
                    }
                },
                GenericTypeTask::Type(JvmTypeSignature::TypeVariable(_))
                | GenericTypeTask::Type(JvmTypeSignature::BaseType(_)) => {}
            }
        }
    }

    pub(super) fn class(
        class: &crate::ir::generic_types::ClassTypeSignature,
        types: &mut Vec<ArgType>,
    ) {
        let mut pending = vec![GenericTypeTask::Class(class)];
        while let Some(task) = pending.pop() {
            match task {
                GenericTypeTask::Class(class) => {
                    types.push(ArgType::object(&class.erased_name()));
                    pending.extend(
                        class
                            .inner_segments
                            .iter()
                            .rev()
                            .flat_map(|segment| segment.type_arguments.iter().rev())
                            .map(GenericTypeTask::Argument),
                    );
                    pending.extend(
                        class
                            .type_arguments
                            .iter()
                            .rev()
                            .map(GenericTypeTask::Argument),
                    );
                }
                GenericTypeTask::Type(ty) => Self::ty(ty, types),
                GenericTypeTask::Argument(argument) => match argument {
                    crate::ir::generic_types::TypeArgument::Unbounded => {}
                    crate::ir::generic_types::TypeArgument::Extends(ty)
                    | crate::ir::generic_types::TypeArgument::Super(ty)
                    | crate::ir::generic_types::TypeArgument::Exact(ty) => {
                        pending.push(GenericTypeTask::Type(ty));
                    }
                },
            }
        }
    }
}

enum GenericTypeTask<'a> {
    Type(&'a JvmTypeSignature),
    Class(&'a crate::ir::generic_types::ClassTypeSignature),
    Argument(&'a crate::ir::generic_types::TypeArgument),
}

pub(super) struct AnnotationTypeUses;

impl AnnotationTypeUses {
    pub(super) fn collect(annotations: &[AnnotationNode], types: &mut Vec<ArgType>) {
        for annotation in annotations {
            types.push(annotation.annotation_type.clone());
            for element in &annotation.elements {
                DexValueTypeUses::collect(&element.value, types);
            }
        }
    }
}

pub(super) struct DexValueTypeUses;

impl DexValueTypeUses {
    pub(super) fn collect(value: &DexValue, types: &mut Vec<ArgType>) {
        let mut pending = vec![value];
        while let Some(value) = pending.pop() {
            match value {
                DexValue::Type(ty) => types.push(ty.clone()),
                DexValue::Field(reference) | DexValue::Enum(reference) => {
                    types.push(reference.owner.clone());
                    types.push(reference.field_type.clone());
                }
                DexValue::Method(reference) => {
                    types.push(reference.owner.clone());
                    types.extend(reference.descriptor.parameters.iter().cloned());
                    types.push(reference.descriptor.return_type.clone());
                }
                DexValue::MethodType(descriptor) => {
                    types.extend(descriptor.parameters.iter().cloned());
                    types.push(descriptor.return_type.clone());
                }
                DexValue::Array(values) => pending.extend(values.iter().rev()),
                DexValue::Annotation(annotation) => {
                    types.push(annotation.annotation_type.clone());
                    pending.extend(
                        annotation
                            .elements
                            .iter()
                            .rev()
                            .map(|element| &element.value),
                    );
                }
                DexValue::Null
                | DexValue::Boolean(_)
                | DexValue::Byte(_)
                | DexValue::Short(_)
                | DexValue::Char(_)
                | DexValue::Int(_)
                | DexValue::Long(_)
                | DexValue::Float(_)
                | DexValue::Double(_)
                | DexValue::String(_)
                | DexValue::Unsupported { .. } => {}
            }
        }
    }
}
