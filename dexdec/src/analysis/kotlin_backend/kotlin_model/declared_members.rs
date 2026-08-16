//! Source-level member facts recovered from `@kotlin.Metadata`.
//!
//! Bytecode has no `internal`: the compiler lowers it to a public member whose
//! name gains a module suffix. Nothing in the DEX distinguishes that from a
//! genuinely public member with an unusual name, so a decompiler that only reads
//! access flags declares it `public` — which is not what the class said.

use std::collections::BTreeMap;
use std::str::FromStr;

use super::metadata_members::{backing_field_references, MetadataCallable};
use crate::frontend::kotlin_metadata::{KotlinMetadata, TypeReference, Visibility};
use crate::frontend::{ClassNode, MethodNode};
use crate::ir::generic_types::{GenericSignatures, JvmTypeSignature, TypeArgument};
use crate::ir::{ArgType, FieldReference, MethodDescriptor, MethodReference};
use crate::language::kotlin::{KotlinDefaultCallContract, KotlinDefaultMask, KotlinIdentifier};
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::analysis::kotlin_backend) struct KotlinSuspendDeclaration {
    pub(in crate::analysis::kotlin_backend) continuation_parameter: usize,
    pub(in crate::analysis::kotlin_backend) return_type: crate::ir::ArgType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::analysis::kotlin_backend) struct KotlinDefaultParameter {
    pub(in crate::analysis::kotlin_backend) parameter: usize,
    pub(in crate::analysis::kotlin_backend) mask: usize,
    pub(in crate::analysis::kotlin_backend) bit: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::analysis::kotlin_backend) struct KotlinDefaultArgumentLayout {
    pub(in crate::analysis::kotlin_backend) mask_count: usize,
    pub(in crate::analysis::kotlin_backend) parameters: Vec<KotlinDefaultParameter>,
    pub(in crate::analysis::kotlin_backend) exact: bool,
}

struct DefaultDispatcherAbi {
    dispatcher: MethodReference,
    target: MethodReference,
    target_static: bool,
    extension_receiver: Option<usize>,
    mask_count: usize,
    masks: Vec<KotlinDefaultMask>,
    exact_masks: bool,
}

impl DefaultDispatcherAbi {
    fn analyze(
        class: &ClassNode,
        dispatcher: &crate::frontend::MethodNode,
        extension_receivers: &BTreeMap<MethodReference, usize>,
        resolve_method: &impl Fn(&ClassNode, u32) -> Option<MethodReference>,
    ) -> Option<Self> {
        if dispatcher.is_constructor() {
            return Self::constructor(class, dispatcher, resolve_method);
        }
        Self::function(class, dispatcher, extension_receivers, resolve_method)
    }

    fn function(
        class: &ClassNode,
        dispatcher: &crate::frontend::MethodNode,
        extension_receivers: &BTreeMap<MethodReference, usize>,
        resolve_method: &impl Fn(&ClassNode, u32) -> Option<MethodReference>,
    ) -> Option<Self> {
        if !dispatcher.access_flags.is_static() {
            return None;
        }
        let target_name = dispatcher.name().strip_suffix("$default")?;
        let parameters = dispatcher.param_types();
        if parameters.last() != Some(&crate::ir::ArgType::object("java/lang/Object")) {
            return None;
        }
        let candidates = class
            .methods()
            .iter()
            .filter(|target| {
                target.name() == target_name
                    && target.return_type() == dispatcher.return_type()
                    && !target.is_constructor()
            })
            .filter_map(|target| {
                let target_reference = Self::reference(class, target);
                let extension_receiver = extension_receivers.get(&target_reference).copied();
                let dispatch_parameters = usize::from(!target.access_flags.is_static());
                let mask_start = dispatch_parameters + target.param_types().len();
                let mask_count = parameters.len().checked_sub(mask_start + 1)?;
                if mask_count == 0 {
                    return None;
                }
                let mut expected = Vec::new();
                if !target.access_flags.is_static() {
                    expected.push(class.class_type().clone());
                }
                expected.extend(target.param_types().iter().cloned());
                expected.extend(std::iter::repeat_n(crate::ir::ArgType::INT, mask_count));
                expected.push(crate::ir::ArgType::object("java/lang/Object"));
                (expected == parameters).then_some((
                    target_reference,
                    target.access_flags.is_static(),
                    extension_receiver,
                    mask_count,
                ))
            })
            .collect::<Vec<_>>();
        let proven = candidates
            .iter()
            .filter_map(|(target, target_static, extension_receiver, mask_count)| {
                let masks = super::default_mask_flow::DefaultMaskFlow::function(
                    class,
                    dispatcher,
                    target,
                    *target_static,
                    *mask_count,
                    resolve_method,
                )?;
                Some((
                    target.clone(),
                    *target_static,
                    *extension_receiver,
                    *mask_count,
                    masks,
                ))
            })
            .collect::<Vec<_>>();
        let (target, target_static, extension_receiver, mask_count, masks, exact_masks) =
            match proven.as_slice() {
                [(target, target_static, extension_receiver, mask_count, masks)] => (
                    target.clone(),
                    *target_static,
                    *extension_receiver,
                    *mask_count,
                    masks.clone(),
                    true,
                ),
                [] => {
                    let [(target, target_static, extension_receiver, mask_count)] =
                        candidates.as_slice()
                    else {
                        return None;
                    };
                    (
                        target.clone(),
                        *target_static,
                        *extension_receiver,
                        *mask_count,
                        Self::ordered_masks(target, *extension_receiver),
                        false,
                    )
                }
                _ => return None,
            };
        Some(Self {
            dispatcher: Self::reference(class, dispatcher),
            target,
            target_static,
            extension_receiver,
            mask_count,
            masks,
            exact_masks,
        })
    }

    fn constructor(
        class: &ClassNode,
        dispatcher: &crate::frontend::MethodNode,
        resolve_method: &impl Fn(&ClassNode, u32) -> Option<MethodReference>,
    ) -> Option<Self> {
        let parameters = dispatcher.param_types();
        if parameters.last()
            != Some(&crate::ir::ArgType::object(
                "kotlin/jvm/internal/DefaultConstructorMarker",
            ))
        {
            return None;
        }
        let dispatcher_reference = Self::reference(class, dispatcher);
        let candidates = class
            .methods()
            .iter()
            .filter(|target| target.is_constructor())
            .filter_map(|target| {
                let target_reference = Self::reference(class, target);
                if target_reference == dispatcher_reference {
                    return None;
                }
                let mask_start = target.param_types().len();
                let mask_count = parameters.len().checked_sub(mask_start + 1)?;
                if mask_count == 0 {
                    return None;
                }
                let mut expected = target.param_types().to_vec();
                expected.extend(std::iter::repeat_n(crate::ir::ArgType::INT, mask_count));
                expected.push(crate::ir::ArgType::object(
                    "kotlin/jvm/internal/DefaultConstructorMarker",
                ));
                (expected == parameters).then_some((target_reference, mask_count))
            })
            .collect::<Vec<_>>();
        let proven = candidates
            .iter()
            .filter_map(|(target, mask_count)| {
                let masks = super::default_mask_flow::DefaultMaskFlow::constructor(
                    class,
                    dispatcher,
                    target,
                    *mask_count,
                    resolve_method,
                )?;
                Some((target.clone(), *mask_count, masks))
            })
            .collect::<Vec<_>>();
        let (target, mask_count, masks, exact_masks) = match proven.as_slice() {
            [(target, mask_count, masks)] => (target.clone(), *mask_count, masks.clone(), true),
            [] => {
                let [(target, mask_count)] = candidates.as_slice() else {
                    return None;
                };
                (
                    target.clone(),
                    *mask_count,
                    Self::ordered_masks(target, None),
                    false,
                )
            }
            _ => return None,
        };
        Some(Self {
            dispatcher: dispatcher_reference,
            target,
            target_static: false,
            extension_receiver: None,
            mask_count,
            masks,
            exact_masks,
        })
    }

    fn reference(class: &ClassNode, method: &crate::frontend::MethodNode) -> MethodReference {
        MethodReference {
            owner: class.class_type().clone(),
            name: method.name().to_string(),
            descriptor: MethodDescriptor {
                parameters: method.param_types().to_vec(),
                return_type: method.return_type().clone(),
            },
        }
    }

    fn masks(&self) -> Vec<KotlinDefaultMask> {
        self.masks.clone()
    }

    fn ordered_masks(
        target: &MethodReference,
        extension_receiver: Option<usize>,
    ) -> Vec<KotlinDefaultMask> {
        target
            .descriptor
            .parameters
            .iter()
            .enumerate()
            .filter(|(parameter, _)| Some(*parameter) != extension_receiver)
            .enumerate()
            .map(|(source, (parameter, _))| {
                KotlinDefaultMask::new(parameter, source / 32, 1 << (source % 32))
            })
            .collect()
    }

    fn default_parameters(&self) -> Vec<KotlinDefaultParameter> {
        self.masks()
            .into_iter()
            .map(|mask| KotlinDefaultParameter {
                parameter: mask.parameter(),
                mask: mask.word(),
                bit: mask.bit(),
            })
            .collect()
    }
}

/// What a Kotlin class declares about the visibility of its own members.
#[derive(Debug, Clone, Default)]
pub(crate) struct KotlinDeclaredMembers {
    methods: BTreeMap<MethodReference, Visibility>,
    fields: BTreeMap<FieldReference, Visibility>,
    /// Fields backing a `lateinit` property, which the source declares non-null
    /// even though the JVM leaves them unset until the first assignment.
    lateinit_fields: std::collections::BTreeSet<FieldReference>,
    /// Source parameter names, positioned against the parameters the DEX method
    /// takes. A slot is empty where the source named nothing.
    parameter_names: BTreeMap<MethodReference, Vec<Option<String>>>,
    /// Source type trees, aligned to the DEX parameter list. Unlike the JVM
    /// descriptor, these retain nullability at every represented nesting level.
    parameter_types: BTreeMap<MethodReference, Vec<Option<TypeReference>>>,
    /// Source return type trees for methods whose metadata resolves to one
    /// exact JVM declaration.
    return_types: BTreeMap<MethodReference, TypeReference>,
    /// Source element nullability for metadata-declared `vararg` parameters.
    /// Presence also proves that the corresponding JVM array is a vararg.
    vararg_elements: BTreeMap<MethodReference, BTreeMap<usize, bool>>,
    vararg_parameters: Arc<BTreeMap<MethodReference, std::collections::BTreeSet<usize>>>,
    /// The DEX parameter occupied by a Kotlin extension receiver.
    extension_receivers: BTreeMap<MethodReference, usize>,
    default_arguments: BTreeMap<MethodReference, KotlinDefaultArgumentLayout>,
    default_calls: Arc<BTreeMap<MethodReference, KotlinDefaultCallContract>>,
    suspend_functions: BTreeMap<MethodReference, KotlinSuspendDeclaration>,
    computed_properties: BTreeMap<MethodReference, KotlinIdentifier>,
    default_property_getters: BTreeMap<MethodReference, KotlinIdentifier>,
    default_property_setters: BTreeMap<MethodReference, KotlinIdentifier>,
    /// Members to declare under the source name instead of the mangled one.
    /// Shared so that every class resolves a reference the same way.
    source_names: Arc<BTreeMap<MethodReference, KotlinIdentifier>>,
    classes: BTreeMap<crate::ir::ArgType, Visibility>,
    class_kinds: BTreeMap<crate::ir::ArgType, crate::frontend::kotlin_metadata::ClassKind>,
    /// Classes with exactly one instance, whose singleton field is never null.
    singletons: Arc<std::collections::BTreeSet<crate::ir::ArgType>>,
    singleton_instances: Arc<std::collections::BTreeSet<FieldReference>>,
    sealed: std::collections::BTreeSet<crate::ir::ArgType>,
    /// Fields backing a compile-time constant property.
    constants: std::collections::BTreeSet<FieldReference>,
    mutable_fields: std::collections::BTreeSet<FieldReference>,
}

impl KotlinDeclaredMembers {
    pub(crate) fn analyze(
        classes: &[&ClassNode],
        resolve_method: &impl Fn(&ClassNode, u32) -> Option<MethodReference>,
    ) -> Self {
        let mut declared = Self::default();
        let mut source_names = BTreeMap::new();
        let mut singletons = std::collections::BTreeSet::new();
        for class in classes {
            declared.collect(class, &mut source_names, &mut singletons);
        }
        let mut vararg_parameters = declared
            .vararg_elements
            .iter()
            .map(|(method, parameters)| (method.clone(), parameters.keys().copied().collect()))
            .collect::<BTreeMap<_, std::collections::BTreeSet<_>>>();
        for class in classes {
            for method in class
                .methods()
                .iter()
                .filter(|method| method.access_flags.is_varargs())
            {
                let Some(parameter) = method.param_types().len().checked_sub(1) else {
                    continue;
                };
                let reference = MethodReference {
                    owner: class.class_type().clone(),
                    name: method.name().to_string(),
                    descriptor: MethodDescriptor {
                        parameters: method.param_types().to_vec(),
                        return_type: method.return_type().clone(),
                    },
                };
                vararg_parameters
                    .entry(reference)
                    .or_default()
                    .insert(parameter);
            }
        }
        declared.vararg_parameters = Arc::new(vararg_parameters);
        declared.index_singleton_instances(classes, &singletons);
        declared.index_default_calls(classes, resolve_method);
        declared.source_names = Arc::new(source_names);
        declared.singletons = Arc::new(singletons);
        declared
    }

    pub(super) fn merge_external_abi(
        &mut self,
        symbols: &crate::platform_symbols::PlatformSymbolSet,
    ) {
        let external = super::external_abi::ExternalKotlinAbi::cached(symbols);
        let mut calls = external.default_calls().as_ref().clone();
        // The input DEX is authoritative when it contains the declaration.
        calls.extend(
            self.default_calls
                .iter()
                .map(|(call, contract)| (call.clone(), contract.clone())),
        );
        self.default_calls = Arc::new(calls);

        let mut extension_receivers = external.extension_receivers().as_ref().clone();
        extension_receivers.extend(self.extension_receivers.clone());
        self.extension_receivers = extension_receivers;

        let mut source_names = external.source_names().as_ref().clone();
        source_names.extend(
            self.source_names
                .iter()
                .map(|(method, name)| (method.clone(), name.clone())),
        );
        self.source_names = Arc::new(source_names);

        let mut property_getters = external.property_getters().as_ref().clone();
        property_getters.extend(self.default_property_getters.clone());
        property_getters.extend(self.computed_properties.clone());
        self.default_property_getters = property_getters;

        let mut property_setters = external.property_setters().as_ref().clone();
        property_setters.extend(self.default_property_setters.clone());
        self.default_property_setters = property_setters;

        let mut singletons = external.singletons().as_ref().clone();
        singletons.extend(self.singletons.iter().cloned());
        self.singletons = Arc::new(singletons);

        let mut singleton_instances = external.singleton_instances().as_ref().clone();
        singleton_instances.extend(self.singleton_instances.iter().cloned());
        self.singleton_instances = Arc::new(singleton_instances);
    }

    /// Every member that declares itself under a name other than its JVM one.
    pub(crate) fn source_names(&self) -> Arc<BTreeMap<MethodReference, KotlinIdentifier>> {
        Arc::clone(&self.source_names)
    }

    pub(crate) fn computed_property(&self, method: &MethodReference) -> Option<&KotlinIdentifier> {
        self.computed_properties.get(method)
    }

    pub(crate) fn property_getters(&self) -> Arc<BTreeMap<MethodReference, KotlinIdentifier>> {
        let mut getters = self.default_property_getters.clone();
        getters.extend(self.computed_properties.clone());
        Arc::new(getters)
    }

    pub(crate) fn property_setters(&self) -> Arc<BTreeMap<MethodReference, KotlinIdentifier>> {
        Arc::new(self.default_property_setters.clone())
    }

    pub(crate) fn is_default_property_accessor(&self, method: &MethodReference) -> bool {
        self.default_property_getters.contains_key(method)
            || self.default_property_setters.contains_key(method)
    }

    pub(crate) fn singletons(&self) -> Arc<std::collections::BTreeSet<crate::ir::ArgType>> {
        Arc::clone(&self.singletons)
    }

    pub(crate) fn singleton_instances(&self) -> Arc<std::collections::BTreeSet<FieldReference>> {
        Arc::clone(&self.singleton_instances)
    }

    pub(crate) fn is_singleton_instance(&self, field: &FieldReference) -> bool {
        self.singleton_instances.contains(field)
    }

    pub(crate) fn is_sealed(&self, class: &crate::ir::ArgType) -> bool {
        self.sealed.contains(class)
    }

    pub(crate) fn is_constant(&self, field: &FieldReference) -> bool {
        self.constants.contains(field)
    }

    pub(crate) fn class_visibility(&self, class: &crate::ir::ArgType) -> Option<Visibility> {
        self.classes.get(class).copied()
    }

    pub(crate) fn class_kind(
        &self,
        class: &crate::ir::ArgType,
    ) -> Option<crate::frontend::kotlin_metadata::ClassKind> {
        self.class_kinds.get(class).copied()
    }

    pub(crate) fn method_visibility(&self, method: &MethodReference) -> Option<Visibility> {
        self.methods.get(method).copied()
    }

    pub(crate) fn field_visibility(&self, field: &FieldReference) -> Option<Visibility> {
        self.fields.get(field).copied()
    }

    pub(crate) fn field_is_lateinit(&self, field: &FieldReference) -> bool {
        self.lateinit_fields.contains(field)
    }

    pub(crate) fn field_is_mutable(&self, field: &FieldReference) -> bool {
        self.mutable_fields.contains(field)
    }

    /// The name the source gave one parameter of a method.
    pub(crate) fn parameter_name(
        &self,
        method: &MethodReference,
        parameter: usize,
    ) -> Option<&str> {
        self.parameter_names.get(method)?.get(parameter)?.as_deref()
    }

    pub(crate) fn parameter_type(
        &self,
        method: &MethodReference,
        parameter: usize,
    ) -> Option<&TypeReference> {
        self.parameter_types.get(method)?.get(parameter)?.as_ref()
    }

    pub(crate) fn return_type(&self, method: &MethodReference) -> Option<&TypeReference> {
        self.return_types.get(method)
    }

    pub(crate) fn vararg_element_nullable(
        &self,
        method: &MethodReference,
        parameter: usize,
    ) -> Option<bool> {
        self.vararg_elements.get(method)?.get(&parameter).copied()
    }

    pub(crate) fn vararg_parameters(
        &self,
    ) -> Arc<BTreeMap<MethodReference, std::collections::BTreeSet<usize>>> {
        Arc::clone(&self.vararg_parameters)
    }

    pub(crate) fn extension_receiver(&self, method: &MethodReference) -> Option<usize> {
        self.extension_receivers.get(method).copied()
    }

    pub(crate) fn extension_receivers(&self) -> Arc<BTreeMap<MethodReference, usize>> {
        Arc::new(self.extension_receivers.clone())
    }

    pub(crate) fn default_calls(
        &self,
    ) -> Arc<BTreeMap<MethodReference, KotlinDefaultCallContract>> {
        Arc::clone(&self.default_calls)
    }

    pub(crate) fn is_default_dispatcher(&self, method: &MethodReference) -> bool {
        self.default_calls.contains_key(method)
    }

    pub(super) fn default_arguments(
        &self,
        method: &MethodReference,
    ) -> Option<&KotlinDefaultArgumentLayout> {
        self.default_arguments.get(method)
    }

    pub(crate) fn suspend_declaration(
        &self,
        method: &MethodReference,
    ) -> Option<&KotlinSuspendDeclaration> {
        self.suspend_functions.get(method)
    }

    pub(crate) fn source_types_for(
        &self,
        owner: &crate::ir::ArgType,
    ) -> impl Iterator<Item = crate::ir::ArgType> + '_ {
        let owner = owner.clone();
        self.suspend_functions
            .iter()
            .filter(move |(method, _)| method.owner == owner)
            .map(|(_, declaration)| declaration.return_type.clone())
    }

    fn collect(
        &mut self,
        class: &ClassNode,
        source_names: &mut BTreeMap<MethodReference, KotlinIdentifier>,
        singletons: &mut std::collections::BTreeSet<crate::ir::ArgType>,
    ) {
        let Some(Ok(metadata)) = KotlinMetadata::of(&class.annotations) else {
            self.collect_suspend_abi(class);
            return;
        };
        let declarations = metadata.declarations();
        self.classes
            .insert(class.class_type().clone(), declarations.flags.visibility());
        self.class_kinds
            .insert(class.class_type().clone(), declarations.flags.class_kind());
        if declarations.flags.class_kind().is_singleton() {
            singletons.insert(class.class_type().clone());
        }
        if declarations.flags.is_sealed() {
            self.sealed.insert(class.class_type().clone());
        }
        let callables = MetadataCallable::of(declarations);
        for method in class.methods() {
            let Some(callable) = MetadataCallable::resolve(&callables, class, method) else {
                continue;
            };
            let reference = MethodReference {
                owner: class.class_type().clone(),
                name: method.name().to_string(),
                descriptor: MethodDescriptor {
                    parameters: method.param_types().to_vec(),
                    return_type: method.return_type().clone(),
                },
            };
            self.methods.insert(reference.clone(), callable.visibility);
            if let Some(name) = callable.unmangled_name() {
                source_names.insert(reference.clone(), KotlinIdentifier::from_dex(name));
            }
            let Some(offset) = callable.parameter_offset(method) else {
                continue;
            };
            if callable.receiver_type.is_some() {
                self.extension_receivers.insert(reference.clone(), 0);
            }
            if callable.is_suspend {
                let return_type = callable
                    .return_type
                    .and_then(|ty| ty.erased_return_descriptor())
                    .and_then(|descriptor| crate::ir::ArgType::from_str(&descriptor).ok());
                if let Some(return_type) = return_type {
                    self.suspend_functions.insert(
                        reference.clone(),
                        KotlinSuspendDeclaration {
                            continuation_parameter: offset + callable.parameters.len(),
                            return_type,
                        },
                    );
                }
            }
            let mut names = vec![None; method.param_types().len()];
            let mut types = vec![None; method.param_types().len()];
            if let (Some(receiver), Some(slot)) = (callable.receiver_type, types.first_mut()) {
                *slot = Some(receiver.clone());
            }
            let mut vararg_elements = BTreeMap::new();
            let mut default_parameters = Vec::new();
            for (index, parameter) in callable.parameters.iter().enumerate() {
                if let Some(slot) = names.get_mut(offset + index) {
                    *slot = parameter.name.map(str::to_string);
                }
                if let Some(slot) = types.get_mut(offset + index) {
                    *slot = parameter.ty.cloned();
                }
                if let Some(element) = parameter.vararg_element_type {
                    vararg_elements.insert(offset + index, element.nullable);
                }
                if parameter.has_default {
                    default_parameters.push(KotlinDefaultParameter {
                        parameter: offset + index,
                        mask: index / 32,
                        bit: 1u32 << (index % 32),
                    });
                }
            }
            if names.iter().any(Option::is_some) {
                self.parameter_names.insert(reference.clone(), names);
            }
            if types.iter().any(Option::is_some) {
                self.parameter_types.insert(reference.clone(), types);
            }
            if let Some(return_type) = callable.return_type {
                self.return_types
                    .insert(reference.clone(), return_type.clone());
            }
            if !vararg_elements.is_empty() {
                self.vararg_elements
                    .insert(reference.clone(), vararg_elements);
            }
            if !default_parameters.is_empty() {
                self.default_arguments.insert(
                    reference,
                    KotlinDefaultArgumentLayout {
                        mask_count: callable.parameters.len().div_ceil(32),
                        parameters: default_parameters,
                        exact: true,
                    },
                );
            }
        }
        for property in &declarations.properties {
            let backing_fields = backing_field_references(class, declarations, property);
            if backing_fields.is_empty() && !property.is_variable() {
                if let Some(getter) = &property.getter {
                    if let Ok(descriptor) = MethodDescriptor::from_str(&getter.descriptor) {
                        if descriptor.parameters.is_empty() {
                            self.computed_properties.insert(
                                MethodReference {
                                    owner: class.class_type().clone(),
                                    name: getter.name.clone(),
                                    descriptor,
                                },
                                KotlinIdentifier::from_dex(&property.name),
                            );
                        }
                    }
                }
            }
            if !backing_fields.is_empty() {
                let property_name = KotlinIdentifier::from_dex(&property.name);
                if property.getter_is_default {
                    if let Some(reference) = property
                        .getter
                        .as_ref()
                        .and_then(|getter| property_accessor_reference(class, getter))
                    {
                        self.default_property_getters
                            .insert(reference, property_name.clone());
                    }
                }
                if property.setter_is_default {
                    if let Some(reference) = property
                        .setter
                        .as_ref()
                        .and_then(|setter| property_accessor_reference(class, setter))
                    {
                        self.default_property_setters
                            .insert(reference, property_name);
                    }
                }
            }
            for reference in backing_fields {
                if property.is_variable() {
                    self.mutable_fields.insert(reference.clone());
                }
                if property.flags.is_lateinit() {
                    self.lateinit_fields.insert(reference.clone());
                }
                if property.flags.is_const() {
                    self.constants.insert(reference.clone());
                }
                self.fields.insert(reference, property.flags.visibility());
            }
        }
        self.collect_suspend_abi(class);
    }

    fn collect_suspend_abi(&mut self, class: &ClassNode) {
        let continuation_impl = class
            .methods()
            .iter()
            .any(|method| method.name() == "invokeSuspend");
        for method in class.methods() {
            if method.is_constructor() || method.name() == "<clinit>" {
                continue;
            }
            if method.name() == "create" || method.name() == "invokeSuspend" {
                continue;
            }
            if continuation_impl && method.name() == "invoke" {
                continue;
            }
            let Some(declaration) = suspend_abi_declaration(method) else {
                continue;
            };
            let reference = method_reference(class, method);
            self.suspend_functions
                .entry(reference)
                .or_insert(declaration);
        }
    }

    fn index_default_calls(
        &mut self,
        classes: &[&ClassNode],
        resolve_method: &impl Fn(&ClassNode, u32) -> Option<MethodReference>,
    ) {
        let mut calls = BTreeMap::new();
        for (target, layout) in &self.default_arguments {
            let Some(class) = classes
                .iter()
                .copied()
                .find(|class| class.class_type() == &target.owner)
            else {
                continue;
            };
            let Some(primary) = class.methods().iter().find(|method| {
                method.name() == target.name
                    && method.param_types() == target.descriptor.parameters
                    && method.return_type() == &target.descriptor.return_type
            }) else {
                continue;
            };
            let constructor = target.name == "<init>";
            let mut parameters = Vec::new();
            if !constructor && !primary.access_flags.is_static() {
                parameters.push(target.owner.clone());
            }
            parameters.extend(target.descriptor.parameters.iter().cloned());
            parameters.extend(std::iter::repeat_n(
                crate::ir::ArgType::INT,
                layout.mask_count,
            ));
            parameters.push(crate::ir::ArgType::object(if constructor {
                "kotlin/jvm/internal/DefaultConstructorMarker"
            } else {
                "java/lang/Object"
            }));
            let descriptor = MethodDescriptor {
                parameters,
                return_type: target.descriptor.return_type.clone(),
            };
            let name = if constructor {
                "<init>".to_string()
            } else {
                format!("{}$default", target.name)
            };
            let mut dispatchers = class.methods().iter().filter(|method| {
                method.name() == name
                    && method.param_types() == descriptor.parameters
                    && method.return_type() == &descriptor.return_type
                    && method.access_flags.is_static() == !constructor
                    && method.access_flags.is_synthetic()
            });
            let Some(dispatcher) = dispatchers.next() else {
                continue;
            };
            if dispatchers.next().is_some() {
                continue;
            }
            let reference = MethodReference {
                owner: class.class_type().clone(),
                name: dispatcher.name().to_string(),
                descriptor,
            };
            let masks = layout
                .parameters
                .iter()
                .map(|parameter| {
                    KotlinDefaultMask::new(parameter.parameter, parameter.mask, parameter.bit)
                })
                .collect();
            let parameter_names = self
                .parameter_names
                .get(target)
                .into_iter()
                .flatten()
                .enumerate()
                .filter_map(|(parameter, name)| {
                    name.as_deref()
                        .map(KotlinIdentifier::from_dex)
                        .map(|name| (parameter, name))
                })
                .collect();
            let varargs = self
                .vararg_elements
                .get(target)
                .into_iter()
                .flat_map(|parameters| parameters.keys().copied())
                .collect();
            let contract = if constructor {
                KotlinDefaultCallContract::constructor(
                    target.clone(),
                    masks,
                    layout.mask_count,
                    parameter_names,
                    varargs,
                )
            } else {
                KotlinDefaultCallContract::function(
                    target.clone(),
                    masks,
                    layout.mask_count,
                    primary.access_flags.is_static(),
                    self.extension_receivers.get(target).copied(),
                    parameter_names,
                    varargs,
                )
            };
            calls.insert(reference, contract);
        }
        for class in classes {
            for dispatcher in class.methods() {
                let Some(abi) = DefaultDispatcherAbi::analyze(
                    class,
                    dispatcher,
                    &self.extension_receivers,
                    resolve_method,
                ) else {
                    continue;
                };
                let parameter_names = self
                    .parameter_names
                    .get(&abi.target)
                    .into_iter()
                    .flatten()
                    .enumerate()
                    .filter_map(|(parameter, name)| {
                        name.as_deref()
                            .map(KotlinIdentifier::from_dex)
                            .map(|name| (parameter, name))
                    })
                    .collect();
                let varargs = self
                    .vararg_elements
                    .get(&abi.target)
                    .into_iter()
                    .flat_map(|parameters| parameters.keys().copied())
                    .collect();
                self.default_arguments
                    .entry(abi.target.clone())
                    .or_insert_with(|| KotlinDefaultArgumentLayout {
                        mask_count: abi.mask_count,
                        parameters: abi.default_parameters(),
                        exact: abi.exact_masks,
                    });
                let masks = abi.masks();
                let target = abi.target.clone();
                let contract = if target.is_constructor() {
                    KotlinDefaultCallContract::constructor(
                        target,
                        masks,
                        abi.mask_count,
                        parameter_names,
                        varargs,
                    )
                } else {
                    KotlinDefaultCallContract::function(
                        target,
                        masks,
                        abi.mask_count,
                        abi.target_static,
                        abi.extension_receiver,
                        parameter_names,
                        varargs,
                    )
                };
                calls.entry(abi.dispatcher).or_insert(contract);
            }
        }
        self.default_calls = Arc::new(calls);
    }

    fn index_singleton_instances(
        &mut self,
        classes: &[&ClassNode],
        singletons: &std::collections::BTreeSet<crate::ir::ArgType>,
    ) {
        let mut candidates = BTreeMap::<crate::ir::ArgType, Vec<FieldReference>>::new();
        for class in classes {
            for field in class.fields().iter().filter(|field| {
                field.is_static() && field.is_final() && singletons.contains(field.field_type())
            }) {
                candidates
                    .entry(field.field_type().clone())
                    .or_default()
                    .push(FieldReference {
                        owner: class.class_type().clone(),
                        name: field.name().to_string(),
                        field_type: field.field_type().clone(),
                    });
            }
        }
        self.singleton_instances = Arc::new(
            candidates
                .into_values()
                .filter_map(|instances| match instances.as_slice() {
                    [instance] => Some(instance.clone()),
                    _ => None,
                })
                .collect(),
        );
    }
}

fn method_reference(class: &ClassNode, method: &MethodNode) -> MethodReference {
    MethodReference {
        owner: class.class_type().clone(),
        name: method.name().to_string(),
        descriptor: MethodDescriptor {
            parameters: method.param_types().to_vec(),
            return_type: method.return_type().clone(),
        },
    }
}

fn suspend_abi_declaration(method: &MethodNode) -> Option<KotlinSuspendDeclaration> {
    if method.return_type() != &ArgType::object("java/lang/Object") {
        return None;
    }
    let continuation_parameter = method.param_types().len().checked_sub(1)?;
    if !is_continuation_type(&method.param_types()[continuation_parameter]) {
        return None;
    }
    Some(KotlinSuspendDeclaration {
        continuation_parameter,
        return_type: suspend_abi_return_type(method),
    })
}

fn suspend_abi_return_type(method: &MethodNode) -> ArgType {
    continuation_result_type(method).unwrap_or_else(|| ArgType::object("java/lang/Object"))
}

fn continuation_result_type(method: &MethodNode) -> Option<ArgType> {
    let signature = method
        .signature
        .as_deref()
        .and_then(|signature| GenericSignatures::method(signature).ok())
        .or_else(|| {
            method
                .override_semantics
                .as_ref()
                .and_then(|semantics| semantics.inherited_signature.clone())
        })?;
    let last = signature.parameter_types.last()?;
    continuation_type_argument(last).map(|ty| ty.erased())
}

fn continuation_type_argument(ty: &JvmTypeSignature) -> Option<&JvmTypeSignature> {
    let JvmTypeSignature::ClassType(class) = ty else {
        return None;
    };
    if !is_continuation_class_name(&class.erased_name()) {
        return None;
    }
    match class.type_arguments.first()? {
        TypeArgument::Super(inner) | TypeArgument::Exact(inner) | TypeArgument::Extends(inner) => {
            Some(inner)
        }
        TypeArgument::Unbounded => None,
    }
}

fn is_continuation_type(ty: &ArgType) -> bool {
    ty.as_object().is_some_and(is_continuation_class_name)
}

fn is_continuation_class_name(name: &str) -> bool {
    name == "kotlin/coroutines/Continuation" || name.ends_with("/Continuation")
}

fn property_accessor_reference(
    class: &ClassNode,
    signature: &crate::frontend::kotlin_metadata::JvmSignature,
) -> Option<MethodReference> {
    Some(MethodReference {
        owner: class.class_type().clone(),
        name: signature.name.clone(),
        descriptor: MethodDescriptor::from_str(&signature.descriptor).ok()?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::{AccessInfo, ClassInfo, MethodInfo};

    fn class_with_methods(name: &str, methods: Vec<MethodNode>) -> ClassNode {
        let mut class = ClassNode::new(
            0,
            ClassInfo::from_type_descriptor(&format!("L{name};")).expect("class descriptor"),
            AccessInfo::for_class(0x1),
        );
        for method in methods {
            class.add_method(method);
        }
        class
    }

    fn method(name: &str, parameters: Vec<ArgType>, return_type: ArgType) -> MethodNode {
        MethodNode::new(
            0,
            MethodInfo::new(
                "Lsample/Host;".to_string(),
                name.to_string(),
                parameters,
                return_type,
            ),
            AccessInfo::for_method(0x9),
        )
    }

    #[test]
    fn continuation_type_accepts_obfuscated_package() {
        assert!(is_continuation_type(&ArgType::object(
            "kotlin/coroutines/Continuation"
        )));
        assert!(is_continuation_type(&ArgType::object("ef1/Continuation")));
        assert!(!is_continuation_type(&ArgType::object("java/lang/Object")));
        assert!(!is_continuation_type(&ArgType::INT));
    }

    #[test]
    fn suspend_abi_reads_continuation_result_type() {
        let method = method(
            "await",
            vec![
                ArgType::object("java/lang/String"),
                ArgType::object("kotlin/coroutines/Continuation"),
            ],
            ArgType::object("java/lang/Object"),
        )
        .with_signature(Some(
            "(Ljava/lang/String;Lkotlin/coroutines/Continuation<-Ljava/lang/Integer;>;)Ljava/lang/Object;"
                .into(),
        ));
        let declaration = suspend_abi_declaration(&method).expect("suspend ABI");
        assert_eq!(declaration.continuation_parameter, 1);
        assert_eq!(
            declaration.return_type,
            ArgType::object("java/lang/Integer")
        );
    }

    #[test]
    fn collect_suspend_abi_skips_continuation_impl_invoke() {
        let class = class_with_methods(
            "sample/StateMachine",
            vec![
                method(
                    "invokeSuspend",
                    vec![ArgType::object("java/lang/Object")],
                    ArgType::object("java/lang/Object"),
                ),
                method(
                    "invoke",
                    vec![
                        ArgType::object("java/lang/String"),
                        ArgType::object("kotlin/coroutines/Continuation"),
                    ],
                    ArgType::object("java/lang/Object"),
                ),
                method(
                    "await",
                    vec![ArgType::object("kotlin/coroutines/Continuation")],
                    ArgType::object("java/lang/Object"),
                ),
            ],
        );
        let declared = KotlinDeclaredMembers::analyze(&[&class], &|_, _| None);
        let invoke = method_reference(
            &class,
            class
                .methods()
                .iter()
                .find(|method| method.name() == "invoke")
                .expect("invoke"),
        );
        let await_method = method_reference(
            &class,
            class
                .methods()
                .iter()
                .find(|method| method.name() == "await")
                .expect("await"),
        );
        assert!(declared.suspend_declaration(&invoke).is_none());
        assert!(declared.suspend_declaration(&await_method).is_some());
    }
}
