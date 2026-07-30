use std::collections::{BTreeMap, BTreeSet};

use crate::ir::generic_types::{ClassTypeSignature, JvmTypeSignature, TypeSubstitution};
use crate::ir::{ArgType, MethodReference};

#[derive(Default)]
struct TypeBindings {
    values: BTreeMap<String, ArgType>,
    conflicts: BTreeSet<String>,
}

impl TypeBindings {
    fn bind(&mut self, name: &str, value: &ArgType) {
        if self.conflicts.contains(name) {
            return;
        }
        match self.values.get(name) {
            Some(current) if current != value => {
                self.values.remove(name);
                self.conflicts.insert(name.to_string());
            }
            Some(_) => {}
            None => {
                self.values.insert(name.to_string(), value.clone());
            }
        }
    }

    fn get(&self, name: &str) -> Option<&ArgType> {
        self.values.get(name)
    }
}

/// A source-level SAM instantiation proven atomically with the specialized
/// implementation parameters that make the method a valid override.
pub(super) struct FunctionObjectMethodTypes {
    parameters: Vec<Option<ArgType>>,
    interface: JvmTypeSignature,
}

impl FunctionObjectMethodTypes {
    pub(super) fn parameters(&self) -> &[Option<ArgType>] {
        &self.parameters
    }

    pub(super) fn interface(&self) -> &JvmTypeSignature {
        &self.interface
    }
}

pub(super) struct FunctionObjectMethodInference;

impl FunctionObjectMethodInference {
    pub(super) fn infer(
        method: &crate::frontend::MethodNode,
        declared_interfaces: &[ArgType],
        body_parameters: &[Option<ArgType>],
        return_type: Option<&ArgType>,
        source_abi: &super::JavaSourceAbi,
    ) -> Option<FunctionObjectMethodTypes> {
        Self::infer_specialized(method, body_parameters, return_type, source_abi)
            .filter(|types| {
                let interface = types.interface.erased();
                declared_interfaces
                    .iter()
                    .any(|declared| declared == &interface)
            })
            .or_else(|| {
                Self::infer_erased(method, declared_interfaces, body_parameters, source_abi)
            })
    }

    fn infer_specialized(
        method: &crate::frontend::MethodNode,
        body_parameters: &[Option<ArgType>],
        return_type: Option<&ArgType>,
        source_abi: &super::JavaSourceAbi,
    ) -> Option<FunctionObjectMethodTypes> {
        let (reference, contract) = method
            .override_semantics
            .as_ref()?
            .base_methods
            .iter()
            .find_map(|reference| {
                let reference = Self::method_reference(reference)?;
                source_abi
                    .generic_method(&reference)
                    .filter(|contract| contract.owner_is_generic())
                    .map(|contract| (reference, contract))
            })?;
        let owner_parameters = contract.owner_type_parameters().collect::<BTreeSet<_>>();
        let mut erased_bindings = TypeBindings::default();
        for (formal, erased) in contract
            .signature
            .parameter_types
            .iter()
            .zip(&reference.descriptor.parameters)
        {
            Self::constrain(formal, erased, &owner_parameters, &mut erased_bindings);
        }
        Self::constrain(
            &contract.signature.return_type,
            &reference.descriptor.return_type,
            &owner_parameters,
            &mut erased_bindings,
        );
        let mut bindings = TypeBindings::default();
        for ((formal, actual), erased) in contract
            .signature
            .parameter_types
            .iter()
            .zip(body_parameters)
            .zip(&reference.descriptor.parameters)
        {
            if let Some(actual) = actual.as_ref().filter(|actual| *actual != erased) {
                Self::constrain(formal, actual, &owner_parameters, &mut bindings);
            }
        }
        if let Some(actual) =
            return_type.filter(|actual| *actual != &reference.descriptor.return_type)
        {
            Self::constrain(
                &contract.signature.return_type,
                actual,
                &owner_parameters,
                &mut bindings,
            );
        }
        let substitutions = contract
            .owner_type_parameters()
            .map(|parameter| {
                bindings
                    .get(parameter)
                    .or_else(|| erased_bindings.get(parameter))
                    .and_then(Self::signature)
                    .map(|signature| {
                        (
                            parameter.to_string(),
                            crate::ir::generic_types::TypeArgument::Exact(signature),
                        )
                    })
            })
            .collect::<Option<TypeSubstitution>>()?;
        Some(FunctionObjectMethodTypes {
            parameters: body_parameters.to_vec(),
            interface: JvmTypeSignature::ClassType(contract.owner.substitute(&substitutions).ok()?),
        })
    }

    fn infer_erased(
        method: &crate::frontend::MethodNode,
        declared_interfaces: &[ArgType],
        body_parameters: &[Option<ArgType>],
        source_abi: &super::JavaSourceAbi,
    ) -> Option<FunctionObjectMethodTypes> {
        let interface = source_abi.functional_interface(
            declared_interfaces,
            method.name(),
            method.param_types(),
        )?;
        Some(FunctionObjectMethodTypes {
            parameters: body_parameters.to_vec(),
            interface: Self::signature(&interface)?,
        })
    }

    fn constrain(
        formal: &JvmTypeSignature,
        actual: &ArgType,
        owner_parameters: &BTreeSet<&str>,
        bindings: &mut TypeBindings,
    ) {
        match (formal, actual) {
            (JvmTypeSignature::TypeVariable(name), actual)
                if owner_parameters.contains(name.as_str()) =>
            {
                bindings.bind(name, actual);
            }
            (JvmTypeSignature::Array(formal), ArgType::Array(actual)) => {
                Self::constrain(formal, actual, owner_parameters, bindings);
            }
            _ => {}
        }
    }

    fn signature(ty: &ArgType) -> Option<JvmTypeSignature> {
        match ty {
            ArgType::Object(name) => Some(JvmTypeSignature::ClassType(ClassTypeSignature {
                raw_name: name.clone(),
                type_arguments: Vec::new(),
                inner_segments: Vec::new(),
            })),
            ArgType::Array(element) => {
                Some(JvmTypeSignature::Array(Box::new(Self::signature(element)?)))
            }
            ArgType::Primitive(_) | ArgType::Unknown(_) => None,
        }
    }

    fn method_reference(reference: &crate::frontend::MethodReference) -> Option<MethodReference> {
        format!("{}->{}", reference.declaring_class, reference.short_id)
            .parse()
            .ok()
    }
}

pub(super) struct FunctionObjectTypeCatalog;

impl FunctionObjectTypeCatalog {
    pub(super) fn collect(
        root: &super::java_model::JavaClassModel,
    ) -> BTreeMap<ArgType, JvmTypeSignature> {
        let mut types = BTreeMap::new();
        let mut pending = vec![root];
        while let Some(class) = pending.pop() {
            pending.extend(class.nested.iter().rev());
            if !class.function_object && !class.declaration.is_anonymous {
                continue;
            }
            let Some(identity) = class.declaration.current_type() else {
                continue;
            };
            let interface = class.function_interface().cloned().or_else(|| {
                let [declared] = class.declaration.implements.as_slice() else {
                    return None;
                };
                class
                    .declaration
                    .signature
                    .as_ref()?
                    .super_interfaces
                    .iter()
                    .find(|interface| {
                        &JvmTypeSignature::ClassType((*interface).clone()).erased() == declared
                    })
                    .cloned()
                    .map(JvmTypeSignature::ClassType)
            });
            let Some(interface) = interface else {
                continue;
            };
            types.insert(identity, interface);
        }
        types
    }
}
