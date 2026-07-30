//! Kotlin source contracts recovered from metadata in external symbol archives.
//!
//! These facts use exact owner/name/descriptor identity. They make source ABI
//! available when a referenced library class is absent from the input DEX,
//! without embedding library-specific method knowledge in the decompiler.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::str::FromStr;
use std::sync::{Arc, OnceLock};

use crate::frontend::kotlin_metadata::{Function, JvmSignature, KotlinMetadata, ValueParameter};
use crate::frontend::{AnnotationElement, AnnotationNode, AnnotationVisibility, DexValue};
use crate::ir::{ArgType, FieldReference, MethodDescriptor, MethodReference};
use crate::language::kotlin::{KotlinDefaultCallContract, KotlinDefaultMask, KotlinIdentifier};
use crate::platform_symbols::{
    PlatformAnnotation, PlatformAnnotationValue, PlatformClass, PlatformMethod, PlatformSymbolSet,
};

const ACC_STATIC: u32 = 0x0008;
const ACC_FINAL: u32 = 0x0010;
const ACC_SYNTHETIC: u32 = 0x1000;

/// Immutable index of source-level call contracts supplied by dependency ABI.
pub(super) struct ExternalKotlinAbi {
    default_calls: Arc<BTreeMap<MethodReference, KotlinDefaultCallContract>>,
    extension_receivers: Arc<BTreeMap<MethodReference, usize>>,
    source_names: Arc<BTreeMap<MethodReference, KotlinIdentifier>>,
    property_getters: Arc<BTreeMap<MethodReference, KotlinIdentifier>>,
    property_setters: Arc<BTreeMap<MethodReference, KotlinIdentifier>>,
    singletons: Arc<BTreeSet<ArgType>>,
    singleton_instances: Arc<BTreeSet<FieldReference>>,
}

impl ExternalKotlinAbi {
    pub(super) fn cached(symbols: &PlatformSymbolSet) -> Arc<Self> {
        static ABI: OnceLock<Arc<ExternalKotlinAbi>> = OnceLock::new();
        Arc::clone(ABI.get_or_init(|| Arc::new(Self::analyze(symbols))))
    }

    fn analyze(symbols: &PlatformSymbolSet) -> Self {
        let mut default_calls = BTreeMap::new();
        let mut extension_receivers = BTreeMap::new();
        let mut source_names = BTreeMap::new();
        let mut property_getters = BTreeMap::new();
        let mut property_setters = BTreeMap::new();
        let mut singletons = BTreeSet::new();
        for class in symbols.classes() {
            let Some(metadata) = PlatformMetadata::decode(class) else {
                continue;
            };
            let owner = match ArgType::from_str(&class.descriptor) {
                Ok(owner) => owner,
                Err(_) => continue,
            };
            if metadata.declarations().flags.class_kind().is_singleton() {
                singletons.insert(owner.clone());
            }
            for function in &metadata.declarations().functions {
                let Some(function) = ExternalFunctionAbi::resolve(class, &owner, function) else {
                    continue;
                };
                if function.declaration.has_receiver {
                    extension_receivers.insert(function.target.clone(), 0);
                }
                if function.declaration.name != function.target.name {
                    source_names.insert(
                        function.target.clone(),
                        KotlinIdentifier::from_dex(&function.declaration.name),
                    );
                }
                if let Some((dispatcher, contract)) = function.default_contract() {
                    default_calls.insert(dispatcher, contract);
                }
            }
            for constructor in &metadata.declarations().constructors {
                if let Some((dispatcher, contract)) =
                    DefaultConstructorAbi::new(class, &owner, constructor).contract()
                {
                    default_calls.insert(dispatcher, contract);
                }
            }
            for property in &metadata.declarations().properties {
                let name = KotlinIdentifier::from_dex(&property.name);
                if let Some(getter) =
                    ExternalPropertyAccessor::resolve(class, &owner, property.getter.as_ref())
                {
                    if property.has_receiver {
                        extension_receivers.insert(getter.clone(), 0);
                    }
                    property_getters.insert(getter, name.clone());
                }
                if let Some(setter) =
                    ExternalPropertyAccessor::resolve(class, &owner, property.setter.as_ref())
                {
                    if property.has_receiver {
                        extension_receivers.insert(setter.clone(), 0);
                    }
                    property_setters.insert(setter, name);
                }
            }
        }
        let singleton_instances = SingletonInstances::analyze(symbols, &singletons);
        let aliases = MethodResolutionAliases::new(symbols);
        Self {
            default_calls: Arc::new(aliases.expand(default_calls)),
            extension_receivers: Arc::new(aliases.expand(extension_receivers)),
            source_names: Arc::new(aliases.expand(source_names)),
            property_getters: Arc::new(aliases.expand(property_getters)),
            property_setters: Arc::new(aliases.expand(property_setters)),
            singletons: Arc::new(singletons),
            singleton_instances: Arc::new(singleton_instances),
        }
    }

    pub(super) fn default_calls(
        &self,
    ) -> Arc<BTreeMap<MethodReference, KotlinDefaultCallContract>> {
        Arc::clone(&self.default_calls)
    }

    pub(super) fn extension_receivers(&self) -> Arc<BTreeMap<MethodReference, usize>> {
        Arc::clone(&self.extension_receivers)
    }

    pub(super) fn source_names(&self) -> Arc<BTreeMap<MethodReference, KotlinIdentifier>> {
        Arc::clone(&self.source_names)
    }

    pub(super) fn property_getters(&self) -> Arc<BTreeMap<MethodReference, KotlinIdentifier>> {
        Arc::clone(&self.property_getters)
    }

    pub(super) fn property_setters(&self) -> Arc<BTreeMap<MethodReference, KotlinIdentifier>> {
        Arc::clone(&self.property_setters)
    }

    pub(super) fn singletons(&self) -> Arc<BTreeSet<ArgType>> {
        Arc::clone(&self.singletons)
    }

    pub(super) fn singleton_instances(&self) -> Arc<BTreeSet<FieldReference>> {
        Arc::clone(&self.singleton_instances)
    }
}

struct SingletonInstances;

impl SingletonInstances {
    fn analyze(
        symbols: &PlatformSymbolSet,
        singletons: &BTreeSet<ArgType>,
    ) -> BTreeSet<FieldReference> {
        let mut candidates = BTreeMap::<ArgType, Vec<FieldReference>>::new();
        for class in symbols.classes() {
            let Ok(owner) = ArgType::from_str(&class.descriptor) else {
                continue;
            };
            for field in &class.fields {
                if field.access_flags & (ACC_STATIC | ACC_FINAL) != (ACC_STATIC | ACC_FINAL) {
                    continue;
                }
                let Ok(field_type) = ArgType::from_str(&field.descriptor) else {
                    continue;
                };
                if !singletons.contains(&field_type) {
                    continue;
                }
                candidates
                    .entry(field_type.clone())
                    .or_default()
                    .push(FieldReference {
                        owner: owner.clone(),
                        name: field.name.clone(),
                        field_type,
                    });
            }
        }
        candidates
            .into_values()
            .filter_map(|fields| {
                let [field] = fields.as_slice() else {
                    return None;
                };
                Some(field.clone())
            })
            .collect()
    }
}

struct ExternalPropertyAccessor;

impl ExternalPropertyAccessor {
    fn resolve(
        class: &PlatformClass,
        owner: &ArgType,
        signature: Option<&JvmSignature>,
    ) -> Option<MethodReference> {
        let signature = signature?;
        class.method(&signature.name, &signature.descriptor)?;
        Some(MethodReference {
            owner: owner.clone(),
            name: signature.name.clone(),
            descriptor: MethodDescriptor::from_str(&signature.descriptor).ok()?,
        })
    }
}

struct ExternalFunctionAbi<'a> {
    class: &'a PlatformClass,
    owner: &'a ArgType,
    declaration: &'a Function,
    target: MethodReference,
    target_static: bool,
}

impl<'a> ExternalFunctionAbi<'a> {
    fn resolve(
        class: &'a PlatformClass,
        owner: &'a ArgType,
        declaration: &'a Function,
    ) -> Option<Self> {
        let signature = declaration
            .signature
            .clone()
            .or_else(|| declaration.default_jvm_signature())?;
        let descriptor = MethodDescriptor::from_str(&signature.descriptor).ok()?;
        let primary = class.method(&signature.name, &signature.descriptor)?;
        Some(Self {
            class,
            owner,
            declaration,
            target: MethodReference {
                owner: owner.clone(),
                name: signature.name,
                descriptor,
            },
            target_static: primary.access_flags & ACC_STATIC != 0,
        })
    }

    fn default_contract(&self) -> Option<(MethodReference, KotlinDefaultCallContract)> {
        let defaults = DefaultParameters::of(
            &self.declaration.parameters,
            usize::from(self.declaration.has_receiver),
        )?;
        let dispatcher = self.dispatcher(defaults.mask_count)?;
        let contract = KotlinDefaultCallContract::function(
            self.target.clone(),
            defaults.masks,
            defaults.mask_count,
            self.target_static,
            self.declaration.has_receiver.then_some(0),
            defaults.names,
            defaults.varargs,
        );
        Some((dispatcher, contract))
    }

    fn dispatcher(&self, mask_count: usize) -> Option<MethodReference> {
        let mut parameters = Vec::new();
        if !self.target_static {
            parameters.push(self.owner.clone());
        }
        parameters.extend(self.target.descriptor.parameters.iter().cloned());
        parameters.extend(std::iter::repeat_n(ArgType::INT, mask_count));
        parameters.push(ArgType::object("java/lang/Object"));
        let descriptor = MethodDescriptor {
            parameters,
            return_type: self.target.descriptor.return_type.clone(),
        };
        let name = format!("{}$default", self.target.name);
        self.class.synthetic_static_method(&name, &descriptor)?;
        Some(MethodReference {
            owner: self.owner.clone(),
            name,
            descriptor,
        })
    }
}

struct DefaultConstructorAbi<'a> {
    class: &'a PlatformClass,
    owner: &'a ArgType,
    constructor: &'a crate::frontend::kotlin_metadata::Constructor,
}

impl<'a> DefaultConstructorAbi<'a> {
    fn new(
        class: &'a PlatformClass,
        owner: &'a ArgType,
        constructor: &'a crate::frontend::kotlin_metadata::Constructor,
    ) -> Self {
        Self {
            class,
            owner,
            constructor,
        }
    }

    fn contract(&self) -> Option<(MethodReference, KotlinDefaultCallContract)> {
        let defaults = DefaultParameters::of(&self.constructor.parameters, 0)?;
        let signature = self
            .constructor
            .signature
            .clone()
            .or_else(|| self.constructor.default_jvm_signature())?;
        let descriptor = MethodDescriptor::from_str(&signature.descriptor).ok()?;
        self.class.method("<init>", &signature.descriptor)?;
        let target = MethodReference {
            owner: self.owner.clone(),
            name: "<init>".to_string(),
            descriptor: descriptor.clone(),
        };
        let mut parameters = descriptor.parameters.clone();
        parameters.extend(std::iter::repeat_n(ArgType::INT, defaults.mask_count));
        parameters.push(ArgType::object(
            "kotlin/jvm/internal/DefaultConstructorMarker",
        ));
        let dispatcher_descriptor = MethodDescriptor {
            parameters,
            return_type: descriptor.return_type.clone(),
        };
        self.class
            .synthetic_instance_method("<init>", &dispatcher_descriptor)?;
        let dispatcher = MethodReference {
            owner: self.owner.clone(),
            name: "<init>".to_string(),
            descriptor: dispatcher_descriptor,
        };
        let contract = KotlinDefaultCallContract::constructor(
            target,
            defaults.masks,
            defaults.mask_count,
            defaults.names,
            defaults.varargs,
        );
        Some((dispatcher, contract))
    }
}

struct DefaultParameters {
    masks: Vec<KotlinDefaultMask>,
    mask_count: usize,
    names: BTreeMap<usize, KotlinIdentifier>,
    varargs: BTreeSet<usize>,
}

impl DefaultParameters {
    fn of(parameters: &[ValueParameter], jvm_offset: usize) -> Option<Self> {
        let masks = parameters
            .iter()
            .enumerate()
            .filter(|(_, parameter)| parameter.has_default)
            .map(|(index, _)| {
                KotlinDefaultMask::new(jvm_offset + index, index / 32, 1 << (index % 32))
            })
            .collect::<Vec<_>>();
        if masks.is_empty() {
            return None;
        }
        let names = parameters
            .iter()
            .enumerate()
            .map(|(index, parameter)| {
                (
                    jvm_offset + index,
                    KotlinIdentifier::from_dex(&parameter.name),
                )
            })
            .collect();
        let varargs = parameters
            .iter()
            .enumerate()
            .filter(|(_, parameter)| parameter.vararg_element_type.is_some())
            .map(|(index, _)| jvm_offset + index)
            .collect();
        Some(Self {
            masks,
            mask_count: parameters.len().div_ceil(32),
            names,
            varargs,
        })
    }
}

/// Expands exact method facts to alternate legal owners according to JVM
/// superclass resolution. Each alias is retained only when resolution points
/// back to the same declaration, so hidden methods cannot inherit stale facts.
struct MethodResolutionAliases<'a> {
    symbols: &'a PlatformSymbolSet,
    children: BTreeMap<&'a str, Vec<&'a PlatformClass>>,
}

impl<'a> MethodResolutionAliases<'a> {
    fn new(symbols: &'a PlatformSymbolSet) -> Self {
        let mut children = BTreeMap::<&str, Vec<&PlatformClass>>::new();
        for class in symbols.classes() {
            if let Some(parent) = class.super_class.as_deref() {
                children.entry(parent).or_default().push(class);
            }
        }
        Self { symbols, children }
    }

    fn expand<T: Clone>(
        &self,
        declarations: BTreeMap<MethodReference, T>,
    ) -> BTreeMap<MethodReference, T> {
        let mut expanded = declarations.clone();
        for (method, fact) in declarations {
            let owner = method.owner.to_descriptor();
            let descriptor = method.descriptor.to_string();
            let mut pending = VecDeque::from([owner.as_str()]);
            let mut seen = BTreeSet::new();
            while let Some(parent) = pending.pop_front() {
                for child in self.children.get(parent).into_iter().flatten().copied() {
                    if !seen.insert(child.descriptor.as_str()) {
                        continue;
                    }
                    pending.push_back(&child.descriptor);
                    let Some((declaration, _)) =
                        self.symbols
                            .resolve_method(&child.descriptor, &method.name, &descriptor)
                    else {
                        continue;
                    };
                    if declaration.descriptor != owner {
                        continue;
                    }
                    let Ok(alias_owner) = ArgType::from_str(&child.descriptor) else {
                        continue;
                    };
                    expanded.insert(
                        MethodReference {
                            owner: alias_owner,
                            name: method.name.clone(),
                            descriptor: method.descriptor.clone(),
                        },
                        fact.clone(),
                    );
                }
            }
        }
        expanded
    }
}

trait PlatformClassMethods {
    fn method(&self, name: &str, descriptor: &str) -> Option<&PlatformMethod>;
    fn synthetic_static_method(
        &self,
        name: &str,
        descriptor: &MethodDescriptor,
    ) -> Option<&PlatformMethod>;
    fn synthetic_instance_method(
        &self,
        name: &str,
        descriptor: &MethodDescriptor,
    ) -> Option<&PlatformMethod>;
}

impl PlatformClassMethods for PlatformClass {
    fn method(&self, name: &str, descriptor: &str) -> Option<&PlatformMethod> {
        self.methods
            .iter()
            .find(|method| method.name == name && method.descriptor == descriptor)
    }

    fn synthetic_static_method(
        &self,
        name: &str,
        descriptor: &MethodDescriptor,
    ) -> Option<&PlatformMethod> {
        self.method(name, &descriptor.to_string()).filter(|method| {
            method.access_flags & (ACC_STATIC | ACC_SYNTHETIC) == (ACC_STATIC | ACC_SYNTHETIC)
        })
    }

    fn synthetic_instance_method(
        &self,
        name: &str,
        descriptor: &MethodDescriptor,
    ) -> Option<&PlatformMethod> {
        self.method(name, &descriptor.to_string()).filter(|method| {
            method.access_flags & ACC_STATIC == 0 && method.access_flags & ACC_SYNTHETIC != 0
        })
    }
}

struct PlatformMetadata;

impl PlatformMetadata {
    fn decode(class: &PlatformClass) -> Option<KotlinMetadata> {
        let annotations = class
            .annotations
            .iter()
            .filter_map(Self::annotation)
            .collect::<Vec<_>>();
        KotlinMetadata::of(&annotations)?.ok()
    }

    fn annotation(annotation: &PlatformAnnotation) -> Option<AnnotationNode> {
        Some(AnnotationNode {
            visibility: AnnotationVisibility::Runtime,
            annotation_type: ArgType::from_str(&annotation.descriptor).ok()?,
            elements: annotation
                .elements
                .iter()
                .filter_map(|(name, value)| {
                    Self::value(value).map(|value| AnnotationElement {
                        name: name.clone(),
                        value,
                    })
                })
                .collect(),
        })
    }

    fn value(value: &PlatformAnnotationValue) -> Option<DexValue> {
        match value {
            PlatformAnnotationValue::Boolean(value) => Some(DexValue::Boolean(*value)),
            PlatformAnnotationValue::Integer(value) => i32::try_from(*value)
                .map(DexValue::Int)
                .ok()
                .or_else(|| Some(DexValue::Long(*value))),
            PlatformAnnotationValue::Float(bits) => Some(DexValue::Float(f32::from_bits(*bits))),
            PlatformAnnotationValue::Double(bits) => Some(DexValue::Double(f64::from_bits(*bits))),
            PlatformAnnotationValue::String(value) => Some(DexValue::String(value.clone().into())),
            PlatformAnnotationValue::Type(value) => {
                ArgType::from_str(value).ok().map(DexValue::Type)
            }
            PlatformAnnotationValue::Array(values) => Some(DexValue::Array(
                values.iter().filter_map(Self::value).collect(),
            )),
            PlatformAnnotationValue::Annotation(annotation) => Self::annotation(annotation)
                .map(Box::new)
                .map(DexValue::Annotation),
            PlatformAnnotationValue::Enum { .. } | PlatformAnnotationValue::Field(_) => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn indexes_external_singleton_from_metadata_and_field_ownership() {
        let symbols =
            crate::platform_symbols::default_platform_symbols().expect("embedded platform symbols");
        let abi = ExternalKotlinAbi::cached(&symbols);
        let unit = ArgType::object("kotlin/Unit");
        assert!(abi.singletons().contains(&unit));
        assert!(abi.singleton_instances().contains(&FieldReference {
            owner: unit.clone(),
            name: "INSTANCE".to_string(),
            field_type: unit,
        }));
    }
}
