use crate::frontend::{AccessInfo, ClassNode, MethodNode};
use crate::ir::cfg::CFG;
use crate::ir::generic_types::{
    ClassTypeSignature, GenericFieldContract, GenericMethodContract, GenericSignatures,
    InnerClassTypeSignature, JvmTypeSignature, TypeArgument, TypeParameter,
};
use crate::ir::{ArgType, FieldReference, InsnType, MemberReference, MethodReference};
use crate::language::java::{JavaConstructorLayout, JavaIdentifier};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::super::function_object_types::FunctionObjectMethodInference;

/// Source-level enclosing-instance semantics recorded by the class file. This
/// is independent of whether the compiler needs to retain that instance in a
/// synthetic field after construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::analysis::java_backend) struct EnclosingInstanceAbi {
    pub(super) outer_type: ArgType,
}

impl EnclosingInstanceAbi {
    pub(super) fn analyze(class: &ClassNode) -> Option<Self> {
        if !class.is_inner() {
            return None;
        }
        let access = class
            .metadata
            .inner_class
            .as_ref()
            .map(|inner| AccessInfo::for_class(inner.access_flags_raw))
            .unwrap_or(class.access_flags);
        if access.is_static() {
            return None;
        }
        if class.metadata.enclosing.as_ref().is_some_and(|enclosing| {
            enclosing.method_reference.is_some() && enclosing.method_static == Some(true)
        }) {
            return None;
        }
        let outer_type = class.parent_class_name()?.parse().ok()?;
        if !class
            .constructors()
            .any(|constructor| constructor.param_types().first() == Some(&outer_type))
        {
            return None;
        }
        Some(Self { outer_type })
    }

    pub(super) fn constructor_parameter(&self, constructor: &MethodNode) -> Option<usize> {
        (constructor.is_constructor()
            && constructor.param_types().first() == Some(&self.outer_type))
        .then_some(0)
    }
}

/// Java source-level representation of the implicit enclosing instance carried
/// by a non-static nested class in DEX ABI.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::analysis::java_backend) struct OuterInstanceField {
    pub(super) reference: FieldReference,
    pub(super) outer_type: ArgType,
}

impl OuterInstanceField {
    /// Proves the enclosing-instance field from constructor def-use rather
    /// than field names or type uniqueness. This is required for local and
    /// anonymous classes, where another captured value can have the same type
    /// as the lexical enclosing instance.
    pub(in crate::analysis::java_backend) fn analyze_cfgs<'a>(
        class: &ClassNode,
        methods: impl IntoIterator<Item = (&'a MethodNode, &'a CFG)>,
    ) -> Option<Self> {
        let enclosing = EnclosingInstanceAbi::analyze(class)?;
        let candidates = class
            .instance_fields()
            .filter(|field| {
                field.is_final()
                    && field.is_synthetic()
                    && field.field_type() == &enclosing.outer_type
            })
            .map(|field| FieldReference {
                owner: class.class_type().clone(),
                name: field.name().to_string(),
                field_type: field.field_type().clone(),
            })
            .collect::<BTreeSet<_>>();
        if candidates.is_empty() {
            return None;
        }

        let mut stores = BTreeSet::new();
        for (constructor, cfg) in methods {
            let Some(parameter) = enclosing.constructor_parameter(constructor) else {
                continue;
            };
            let first_input = cfg.registers.checked_sub(cfg.ins)?;
            let this_register = (!constructor.is_static()).then_some(first_input)?;
            let parameter_register = first_input
                + u32::from(!constructor.is_static())
                + constructor.param_types()[..parameter]
                    .iter()
                    .map(|ty| if ty.is_wide() { 2 } else { 1 })
                    .sum::<u32>();
            stores.extend(
                ConstructorOriginFlow::new(cfg, this_register, parameter_register)
                    .enclosing_field_stores(&candidates),
            );
        }

        if stores.len() != 1 {
            return None;
        }
        let reference = stores.into_iter().next()?;
        Some(Self {
            reference,
            outer_type: enclosing.outer_type,
        })
    }

    pub(in crate::analysis::java_backend) fn analyze(class: &ClassNode) -> Option<Self> {
        // A local or anonymous class has an enclosing-method constructor
        // parameter, but fields of the enclosing type may instead be ordinary
        // captured locals. Type equality cannot distinguish those fields.
        // Their def-use relation is recovered by anonymous/capture lowering;
        // only member classes have a metadata-owned outer-instance field here.
        if class
            .metadata
            .enclosing
            .as_ref()
            .is_some_and(|enclosing| enclosing.method_reference.is_some())
        {
            return None;
        }
        let enclosing = EnclosingInstanceAbi::analyze(class)?;
        let mut candidates = class.instance_fields().filter(|field| {
            field.is_final() && field.is_synthetic() && field.field_type() == &enclosing.outer_type
        });
        let field = candidates.next()?;
        if candidates.next().is_some() {
            return None;
        }
        Some(Self {
            reference: FieldReference {
                owner: class.class_type().clone(),
                name: field.name().to_string(),
                field_type: field.field_type().clone(),
            },
            outer_type: enclosing.outer_type,
        })
    }

    pub(super) fn matches(&self, field: &crate::frontend::FieldNode) -> bool {
        field.declaring_class() == self.reference.owner.to_descriptor()
            && field.name() == self.reference.name
            && field.field_type() == &self.reference.field_type
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstructorOrigin {
    This,
    Enclosing,
}

/// Forward must-analysis over raw DEX registers. A register retains an origin
/// at a join only when every discovered predecessor agrees on that origin.
struct ConstructorOriginFlow<'a> {
    cfg: &'a CFG,
    entry: BTreeMap<u32, ConstructorOrigin>,
}

impl<'a> ConstructorOriginFlow<'a> {
    fn new(cfg: &'a CFG, this_register: u32, enclosing_register: u32) -> Self {
        Self {
            cfg,
            entry: BTreeMap::from([
                (this_register, ConstructorOrigin::This),
                (enclosing_register, ConstructorOrigin::Enclosing),
            ]),
        }
    }

    fn enclosing_field_stores(
        &self,
        candidates: &BTreeSet<FieldReference>,
    ) -> BTreeSet<FieldReference> {
        let entries = self.solve();
        let mut stores = BTreeSet::new();
        for (block_id, block) in &self.cfg.blocks {
            let Some(mut state) = entries.get(block_id).cloned() else {
                continue;
            };
            for instruction in &block.insns {
                if instruction.insn_type == InsnType::Iput
                    && instruction
                        .args
                        .first()
                        .and_then(|arg| arg.as_register())
                        .and_then(|register| state.get(&register.reg_num))
                        == Some(&ConstructorOrigin::Enclosing)
                    && instruction
                        .args
                        .get(1)
                        .and_then(|arg| arg.as_register())
                        .and_then(|register| state.get(&register.reg_num))
                        == Some(&ConstructorOrigin::This)
                {
                    if let Some(MemberReference::Field(field)) =
                        instruction.payload.reference.as_ref()
                    {
                        if candidates.contains(field) {
                            stores.insert(field.clone());
                        }
                    }
                }
                Self::transfer_instruction(&mut state, instruction);
            }
        }
        stores
    }

    fn solve(&self) -> BTreeMap<crate::ir::BlockId, BTreeMap<u32, ConstructorOrigin>> {
        let mut entries = BTreeMap::from([(self.cfg.entry, self.entry.clone())]);
        let mut worklist = VecDeque::from([self.cfg.entry]);
        while let Some(block_id) = worklist.pop_front() {
            let Some(block) = self.cfg.blocks.get(&block_id) else {
                continue;
            };
            let mut exit = entries.get(&block_id).cloned().unwrap_or_default();
            for instruction in &block.insns {
                Self::transfer_instruction(&mut exit, instruction);
            }
            for successor in self.cfg.successors(block_id) {
                let changed = match entries.get_mut(&successor) {
                    Some(entry) => {
                        let before = entry.len();
                        entry.retain(|register, origin| exit.get(register) == Some(origin));
                        entry.len() != before
                    }
                    None => {
                        entries.insert(successor, exit.clone());
                        true
                    }
                };
                if changed {
                    worklist.push_back(successor);
                }
            }
        }
        entries
    }

    fn transfer_instruction(
        state: &mut BTreeMap<u32, ConstructorOrigin>,
        instruction: &crate::ir::InsnNode,
    ) {
        let Some(result) = instruction.result.as_ref() else {
            return;
        };
        let origin = matches!(instruction.insn_type, InsnType::Move | InsnType::CheckCast)
            .then(|| {
                instruction
                    .args
                    .first()
                    .and_then(|arg| arg.as_register())
                    .and_then(|source| state.get(&source.reg_num))
                    .copied()
            })
            .flatten();
        if let Some(origin) = origin {
            state.insert(result.reg_num, origin);
        } else {
            state.remove(&result.reg_num);
        }
    }
}

/// A synthetic constructor added by the Java compiler to bridge source-level
/// constructor access. Its trailing marker parameter does not exist in Java
/// source and the bridge declaration itself is not a source member.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::analysis::java_backend) struct SyntheticConstructorBridge {
    marker_parameter: usize,
}

impl SyntheticConstructorBridge {
    pub(super) fn analyze(class: &ClassNode, constructor: &MethodNode) -> Option<Self> {
        if !constructor.is_constructor() || !constructor.access_flags.is_synthetic() {
            return None;
        }
        let parameters = constructor.param_types();
        let marker_parameter = parameters.len().checked_sub(1)?;
        if !parameters[marker_parameter].is_reference() {
            return None;
        }
        let source_parameters = &parameters[..marker_parameter];
        class
            .constructors()
            .any(|candidate| {
                candidate.id != constructor.id && candidate.param_types() == source_parameters
            })
            .then_some(Self { marker_parameter })
    }

    pub(super) fn marker_parameter(self) -> usize {
        self.marker_parameter
    }
}

#[derive(Debug, Clone)]
struct ConstructorSourceAbi {
    hidden_parameters: std::collections::BTreeMap<usize, JvmTypeSignature>,
    enclosing_parameter: Option<usize>,
}

impl ConstructorSourceAbi {
    fn analyze(
        class: &ClassNode,
        constructor: &MethodNode,
        owner_types: &std::collections::BTreeMap<ArgType, ClassTypeSignature>,
    ) -> Option<Self> {
        if !constructor.is_constructor() {
            return None;
        }
        let parameters = constructor.param_types();
        let mut hidden_parameters = std::collections::BTreeMap::new();
        if let Some(bridge) = SyntheticConstructorBridge::analyze(class, constructor) {
            let index = bridge.marker_parameter();
            hidden_parameters.insert(index, Self::signature(parameters.get(index)?)?);
        }
        if class.is_enum()
            && parameters.first() == Some(&ArgType::string())
            && parameters.get(1) == Some(&ArgType::INT)
        {
            hidden_parameters.insert(0, Self::signature(&parameters[0])?);
            hidden_parameters.insert(1, Self::signature(&parameters[1])?);
        }
        let enclosing = EnclosingInstanceAbi::analyze(class);
        let enclosing_parameter = enclosing
            .as_ref()
            .and_then(|enclosing| enclosing.constructor_parameter(constructor));
        if let (Some(index), Some(enclosing)) = (enclosing_parameter, enclosing) {
            let signature = owner_types
                .get(&enclosing.outer_type)
                .cloned()
                .map(JvmTypeSignature::ClassType)
                .or_else(|| Self::signature(&enclosing.outer_type))?;
            hidden_parameters.insert(index, signature);
        }
        Some(Self {
            hidden_parameters,
            enclosing_parameter,
        })
    }

    fn align(
        &self,
        mut signature: crate::ir::generic_types::MethodSignature,
        arity: usize,
    ) -> crate::ir::generic_types::MethodSignature {
        if signature.parameter_types.len() + self.hidden_parameters.len() != arity {
            return signature;
        }
        let mut visible = std::mem::take(&mut signature.parameter_types).into_iter();
        signature.parameter_types = (0..arity)
            .filter_map(|index| {
                self.hidden_parameters
                    .get(&index)
                    .cloned()
                    .or_else(|| visible.next())
            })
            .collect();
        signature
    }

    fn layout(&self, class: &ClassNode, constructor: &MethodNode) -> Option<JavaConstructorLayout> {
        if self.hidden_parameters.is_empty() {
            return None;
        }
        let mut layout = JavaConstructorLayout::new(
            class.class_type().clone(),
            crate::ir::MethodDescriptor {
                parameters: constructor.param_types().to_vec(),
                return_type: ArgType::VOID,
            },
            self.hidden_parameters.keys().copied(),
        );
        if let Some(parameter) = self.enclosing_parameter {
            layout = layout.with_enclosing_parameter(parameter);
        }
        Some(layout)
    }

    fn signature(ty: &ArgType) -> Option<JvmTypeSignature> {
        match ty {
            ArgType::Primitive(primitive) => Some(JvmTypeSignature::BaseType(*primitive)),
            ArgType::Object(name) => Some(JvmTypeSignature::ClassType(ClassTypeSignature {
                raw_name: name.clone(),
                type_arguments: Vec::new(),
                inner_segments: Vec::new(),
            })),
            ArgType::Array(element) => {
                Self::signature(element).map(|element| JvmTypeSignature::Array(Box::new(element)))
            }
            ArgType::Unknown(_) => None,
        }
    }
}

/// Identifies compiler-generated implementations of a single functional
/// interface from class semantics rather than generated naming conventions.
pub(crate) struct FunctionObjectClass;

impl FunctionObjectClass {
    pub(crate) fn analyze(class: &ClassNode) -> bool {
        class.access_flags.is_synthetic()
            && class.access_flags.is_final()
            && !class.interfaces.is_empty()
            && class
                .super_class
                .as_ref()
                .is_none_or(|ty| ty == &ArgType::object("java/lang/Object"))
            && class
                .fields()
                .iter()
                .all(|field| !field.is_static() && field.is_final())
            && class
                .methods()
                .iter()
                .filter(|method| {
                    !method.is_constructor() && !method.is_class_init() && !method.is_static()
                })
                .count()
                == 1
    }
}

/// Source contract of a compiler bridge recovered through ordinary inherited
/// member lookup. The bridge stays callable in DEX but is absent from source.
struct InheritedMethodAbi;

impl InheritedMethodAbi {
    fn contract(
        reference: &MethodReference,
        owner: &ClassTypeSignature,
        owner_parameters: &[TypeParameter],
        methods: &std::collections::BTreeMap<MethodReference, GenericMethodContract>,
        hierarchy: &crate::analysis::method_override::GenericTypeHierarchy,
    ) -> Option<GenericMethodContract> {
        let mut nearest: Option<(&MethodReference, &GenericMethodContract)> = None;
        for (candidate, contract) in methods.iter().filter(|(candidate, _)| {
            candidate.owner != reference.owner
                && candidate.name == reference.name
                && candidate.descriptor == reference.descriptor
                && hierarchy.is_subtype(&reference.owner, &candidate.owner)
        }) {
            nearest = match nearest {
                None => Some((candidate, contract)),
                Some((current, _)) if hierarchy.is_subtype(&candidate.owner, &current.owner) => {
                    Some((candidate, contract))
                }
                Some((current, current_contract))
                    if hierarchy.is_subtype(&current.owner, &candidate.owner) =>
                {
                    Some((current, current_contract))
                }
                Some(_) => return None,
            };
        }
        let (_, inherited) = nearest?;
        let signature = hierarchy.project_method_signature(
            &JvmTypeSignature::ClassType(owner.clone()),
            &inherited.owner,
            &inherited.signature,
        )?;
        Some(GenericMethodContract {
            signature,
            owner: owner.clone(),
            owner_parameters: owner_parameters.to_vec(),
        })
    }
}

/// Computes the generic variables visible at each class declaration. Java's
/// lexical scope follows both non-static enclosing classes and EnclosingMethod;
/// DEX stores those relations independently from the synthetic capture ABI.
struct LexicalTypeEnvironment<'a> {
    classes: std::collections::BTreeMap<ArgType, &'a ClassNode>,
    scopes: std::collections::BTreeMap<ArgType, Vec<TypeParameter>>,
}

impl<'a> LexicalTypeEnvironment<'a> {
    fn analyze(
        classes: &[&'a ClassNode],
    ) -> std::collections::BTreeMap<ArgType, Vec<TypeParameter>> {
        let mut environment = Self {
            classes: classes
                .iter()
                .map(|class| (class.class_type().clone(), *class))
                .collect(),
            scopes: classes
                .iter()
                .map(|class| {
                    (
                        class.class_type().clone(),
                        JavaSourceAbi::declared_type_parameters(class),
                    )
                })
                .collect(),
        };
        environment.converge();
        environment.scopes
    }

    fn converge(&mut self) {
        loop {
            let updates = self
                .classes
                .values()
                .filter_map(|class| {
                    let scope = self.scope(class);
                    (self.scopes.get(class.class_type()) != Some(&scope))
                        .then(|| (class.class_type().clone(), scope))
                })
                .collect::<Vec<_>>();
            if updates.is_empty() {
                break;
            }
            self.scopes.extend(updates);
        }
    }

    fn scope(&self, class: &ClassNode) -> Vec<TypeParameter> {
        let mut scope = class
            .metadata
            .enclosing
            .as_ref()
            .and_then(|enclosing| enclosing.method_reference.as_deref())
            .and_then(|reference| reference.parse::<MethodReference>().ok())
            .and_then(|reference| self.enclosing_method(&reference))
            .map(|(owner, method)| {
                let mut scope = if method.is_static() {
                    Vec::new()
                } else {
                    self.scopes
                        .get(owner.class_type())
                        .cloned()
                        .unwrap_or_default()
                };
                scope.extend(Self::method_type_parameters(method));
                scope
            })
            .or_else(|| {
                EnclosingInstanceAbi::analyze(class).and_then(|_| {
                    class
                        .parent_class_name()
                        .and_then(|parent| parent.parse::<ArgType>().ok())
                        .and_then(|parent| self.scopes.get(&parent).cloned())
                })
            })
            .unwrap_or_default();
        scope.extend(JavaSourceAbi::declared_type_parameters(class));
        scope
    }

    fn enclosing_method(
        &self,
        reference: &MethodReference,
    ) -> Option<(&'a ClassNode, &'a MethodNode)> {
        let owner = self.classes.get(&reference.owner)?;
        let method = owner.methods().iter().find(|method| {
            method.name() == reference.name
                && method.param_types() == reference.descriptor.parameters
                && method.return_type() == &reference.descriptor.return_type
        })?;
        Some((*owner, method))
    }

    fn method_type_parameters(method: &MethodNode) -> Vec<TypeParameter> {
        method
            .signature
            .as_deref()
            .and_then(|signature| GenericSignatures::method(signature).ok())
            .map(|signature| signature.type_parameters)
            .unwrap_or_default()
    }
}

/// Source-level constructor layouts recovered from DEX class metadata.
#[derive(Debug, Clone, Default)]
pub(crate) struct JavaSourceAbi {
    constructors: Vec<JavaConstructorLayout>,
    methods: Vec<MethodReference>,
    owner_types: std::collections::BTreeMap<ArgType, ClassTypeSignature>,
    lexical_type_parameters: std::collections::BTreeMap<ArgType, Vec<TypeParameter>>,
    inherited_member_types: BTreeMap<ArgType, BTreeSet<(JavaIdentifier, ArgType)>>,
    outer_instances: std::collections::BTreeMap<FieldReference, ArgType>,
    field_types: std::collections::BTreeMap<FieldReference, GenericFieldContract>,
    method_exceptions: std::collections::BTreeMap<MethodReference, Vec<ArgType>>,
    platform_exceptions: std::sync::Arc<std::collections::BTreeMap<MethodReference, Vec<ArgType>>>,
    generic_methods: std::collections::BTreeMap<MethodReference, GenericMethodContract>,
    generic_method_declarations: std::collections::BTreeMap<
        (String, crate::ir::MethodDescriptor),
        Vec<(ArgType, GenericMethodContract)>,
    >,
    function_object_types: std::collections::BTreeMap<ArgType, JvmTypeSignature>,
    externally_referenced_nested_types: BTreeSet<ArgType>,
    inaccessible_top_level_imports: BTreeSet<String>,
    generic_hierarchy: Option<crate::analysis::method_override::GenericTypeHierarchy>,
    platform_generic_hierarchy: Option<crate::analysis::method_override::GenericTypeHierarchy>,
    platform_symbols: Option<std::sync::Arc<crate::platform_symbols::PlatformSymbolSet>>,
}

impl JavaSourceAbi {
    pub(crate) fn analyze<'a>(
        classes: impl IntoIterator<Item = &'a ClassNode>,
        mut function_signature: impl FnMut(&MethodReference) -> (Vec<Option<ArgType>>, Option<ArgType>),
    ) -> Self {
        let classes = classes.into_iter().collect::<Vec<_>>();
        let open_owners = Self::open_owner_types(&classes);
        let lexical_type_parameters = LexicalTypeEnvironment::analyze(&classes);
        let inherited_member_types = Self::build_inherited_member_types(&classes);
        let outer_instances = classes
            .iter()
            .filter_map(|class| OuterInstanceField::analyze(class))
            .map(|outer| (outer.reference, outer.outer_type))
            .collect();
        let constructor_owner_types = &open_owners;
        let constructors = classes
            .iter()
            .copied()
            .flat_map(|class| {
                class.constructors().filter_map(move |constructor| {
                    ConstructorSourceAbi::analyze(class, constructor, constructor_owner_types)
                        .and_then(|abi| abi.layout(class, constructor))
                })
            })
            .collect();
        let methods = Self::method_overloads(&classes);
        let field_types = classes
            .iter()
            .copied()
            .flat_map(|class| {
                let owner = open_owners
                    .get(class.class_type())
                    .cloned()
                    .unwrap_or_else(|| Self::direct_owner_type(class));
                class.fields().iter().filter_map(move |field| {
                    let signature = field
                        .signature
                        .as_deref()
                        .and_then(|value| GenericSignatures::field(value).ok())?;
                    Some((
                        FieldReference {
                            owner: class.class_type().clone(),
                            name: field.name().to_string(),
                            field_type: field.field_type().clone(),
                        },
                        GenericFieldContract {
                            signature,
                            owner: owner.clone(),
                        },
                    ))
                })
            })
            .collect();
        let method_exceptions = classes
            .iter()
            .copied()
            .flat_map(|class| {
                class.methods().iter().filter_map(move |method| {
                    let exceptions = method.throws().to_vec();
                    (!exceptions.is_empty()).then(|| {
                        (
                            MethodReference {
                                owner: class.class_type().clone(),
                                name: method.name().to_string(),
                                descriptor: crate::ir::MethodDescriptor {
                                    parameters: method.param_types().to_vec(),
                                    return_type: method.return_type().clone(),
                                },
                            },
                            exceptions,
                        )
                    })
                })
            })
            .collect();
        let platform_exceptions =
            crate::analysis::method_override::platform_exception_contracts().unwrap_or_default();
        let generic_hierarchy =
            crate::analysis::method_override::GenericTypeHierarchy::from_classes(
                classes.iter().copied(),
            )
            .ok();
        let generic_owner_types = &open_owners;
        let mut generic_methods = classes
            .iter()
            .copied()
            .flat_map(|class| {
                let owner = open_owners
                    .get(class.class_type())
                    .cloned()
                    .unwrap_or_else(|| Self::direct_owner_type(class));
                class.methods().iter().filter_map(move |method| {
                    let declared_parameters = Self::declared_type_parameters(class);
                    let parsed_signature = method
                        .signature
                        .as_deref()
                        .and_then(|signature| GenericSignatures::method(signature).ok());
                    let contract = parsed_signature
                        .map(|signature| {
                            let signature =
                                ConstructorSourceAbi::analyze(class, method, generic_owner_types)
                                    .map(|abi| {
                                        abi.align(signature.clone(), method.param_types().len())
                                    })
                                    .unwrap_or(signature);
                            GenericMethodContract {
                                signature,
                                owner: owner.clone(),
                                owner_parameters: declared_parameters.clone(),
                            }
                        })
                        .or_else(|| {
                            method.is_constructor().then(|| {
                                GenericMethodContract::erased_constructor(
                                    owner.clone(),
                                    declared_parameters,
                                    method.param_types(),
                                    method.throws(),
                                )
                            })?
                        })?;
                    Some((
                        MethodReference {
                            owner: class.class_type().clone(),
                            name: method.name().to_string(),
                            descriptor: crate::ir::MethodDescriptor {
                                parameters: method.param_types().to_vec(),
                                return_type: method.return_type().clone(),
                            },
                        },
                        contract,
                    ))
                })
            })
            .collect::<std::collections::BTreeMap<_, _>>();
        if let Some(hierarchy) = generic_hierarchy.as_ref() {
            for class in &classes {
                let owner = open_owners
                    .get(class.class_type())
                    .cloned()
                    .unwrap_or_else(|| Self::direct_owner_type(class));
                let owner_parameters = Self::declared_type_parameters(class);
                for method in class
                    .methods()
                    .iter()
                    .filter(|method| method.access_flags.is_bridge())
                {
                    let reference = MethodReference {
                        owner: class.class_type().clone(),
                        name: method.name().to_string(),
                        descriptor: crate::ir::MethodDescriptor {
                            parameters: method.param_types().to_vec(),
                            return_type: method.return_type().clone(),
                        },
                    };
                    if generic_methods.contains_key(&reference) {
                        continue;
                    }
                    if let Some(contract) = InheritedMethodAbi::contract(
                        &reference,
                        &owner,
                        &owner_parameters,
                        &generic_methods,
                        hierarchy,
                    ) {
                        generic_methods.insert(reference, contract);
                    }
                }
            }
        }
        let platform_generic_hierarchy =
            crate::analysis::method_override::GenericTypeHierarchy::from_classes(
                std::iter::empty::<&ClassNode>(),
            )
            .ok();
        let platform_symbols = crate::platform_symbols::default_platform_symbols().ok();
        let inaccessible_top_level_imports = classes
            .iter()
            .filter(|class| !class.is_public())
            .filter_map(|class| class.class_type().as_object())
            .filter(|name| {
                !name
                    .rsplit('/')
                    .next()
                    .is_some_and(|name| name.contains('$'))
            })
            .map(|name| name.replace('/', "."))
            .collect();
        let externally_referenced_nested_types = Self::externally_referenced_nested_types(&classes);
        let mut generic_method_declarations = std::collections::BTreeMap::new();
        for (method, contract) in &generic_methods {
            generic_method_declarations
                .entry((method.name.clone(), method.descriptor.clone()))
                .or_insert_with(Vec::new)
                .push((method.owner.clone(), contract.clone()));
        }
        let mut abi = Self {
            constructors,
            methods,
            owner_types: open_owners,
            lexical_type_parameters,
            inherited_member_types,
            outer_instances,
            field_types,
            method_exceptions,
            platform_exceptions,
            generic_methods,
            generic_method_declarations,
            function_object_types: std::collections::BTreeMap::new(),
            externally_referenced_nested_types,
            inaccessible_top_level_imports,
            generic_hierarchy,
            platform_generic_hierarchy,
            platform_symbols,
        };
        abi.function_object_types = classes
            .iter()
            .copied()
            .filter(|class| FunctionObjectClass::analyze(class))
            .filter_map(|class| {
                let method = class.methods().iter().find(|method| {
                    !method.is_constructor() && !method.is_class_init() && !method.is_static()
                })?;
                let reference = MethodReference {
                    owner: class.class_type().clone(),
                    name: method.name().to_string(),
                    descriptor: crate::ir::MethodDescriptor {
                        parameters: method.param_types().to_vec(),
                        return_type: method.return_type().clone(),
                    },
                };
                let (mut parameters, return_type) = function_signature(&reference);
                parameters.resize(method.param_types().len(), None);
                let inferred = FunctionObjectMethodInference::infer(
                    method,
                    &class.interfaces,
                    &parameters,
                    return_type.as_ref(),
                    &abi,
                )?;
                Some((class.class_type().clone(), inferred.interface().clone()))
            })
            .collect();
        abi
    }

    pub(crate) fn constructors(&self) -> impl Iterator<Item = JavaConstructorLayout> + '_ {
        self.constructors.iter().cloned()
    }

    pub(crate) fn referenced_constructors<'a>(
        &self,
        methods: impl IntoIterator<Item = &'a MethodReference>,
    ) -> Vec<JavaConstructorLayout> {
        let references = methods.into_iter().collect::<Vec<_>>();
        self.constructors
            .iter()
            .filter(|layout| references.iter().any(|reference| layout.matches(reference)))
            .cloned()
            .collect()
    }

    pub(crate) fn methods(&self) -> impl Iterator<Item = MethodReference> + '_ {
        self.methods.iter().cloned()
    }

    pub(crate) fn import_is_accessible(
        &self,
        import: &crate::language::java::JavaClassName,
    ) -> bool {
        !self
            .inaccessible_top_level_imports
            .contains(&import.to_string())
    }

    fn method_overloads(classes: &[&ClassNode]) -> Vec<MethodReference> {
        let classes_by_type = classes
            .iter()
            .map(|class| (class.class_type().clone(), *class))
            .collect::<std::collections::BTreeMap<_, _>>();
        let mut methods = std::collections::BTreeSet::new();
        for target in classes {
            let mut pending = vec![(*target, true)];
            let mut visited = std::collections::BTreeSet::new();
            while let Some((owner, declared_here)) = pending.pop() {
                if !visited.insert(owner.class_type().clone()) {
                    continue;
                }
                methods.extend(
                    owner
                        .methods()
                        .iter()
                        .filter(|method| !method.is_class_init())
                        .filter(|method| {
                            declared_here
                                || (!method.is_constructor() && !method.access_flags.is_private())
                        })
                        .map(|method| MethodReference {
                            owner: target.class_type().clone(),
                            name: method.name().to_string(),
                            descriptor: crate::ir::MethodDescriptor {
                                parameters: method.param_types().to_vec(),
                                return_type: method.return_type().clone(),
                            },
                        }),
                );
                pending.extend(
                    owner
                        .super_class
                        .iter()
                        .chain(&owner.interfaces)
                        .filter_map(|parent| classes_by_type.get(parent).copied())
                        .map(|parent| (parent, false)),
                );
            }
        }
        methods.into_iter().collect()
    }

    pub(crate) fn owner_type(&self, owner: &ArgType) -> Option<&ClassTypeSignature> {
        self.owner_types.get(owner)
    }

    pub(crate) fn inherited_member_type_names<'a>(
        &'a self,
        owner: &'a ArgType,
    ) -> impl Iterator<Item = &'a JavaIdentifier> {
        self.inherited_member_types
            .get(owner)
            .into_iter()
            .flatten()
            .filter_map(move |(name, declaration)| (declaration != owner).then_some(name))
    }

    pub(crate) fn lexical_type_erasures(
        &self,
        owner: &ArgType,
    ) -> impl Iterator<Item = (&str, ArgType)> {
        self.lexical_type_parameters
            .get(owner)
            .into_iter()
            .flatten()
            .map(|parameter| {
                let erased = parameter
                    .class_bound
                    .as_ref()
                    .or_else(|| parameter.interface_bounds.first())
                    .map(JvmTypeSignature::erased)
                    .unwrap_or_else(|| ArgType::object("java/lang/Object"));
                (parameter.name.as_str(), erased)
            })
    }

    pub(crate) fn lexical_type_variables(&self, owner: &ArgType) -> impl Iterator<Item = &str> {
        self.lexical_type_parameters
            .get(owner)
            .into_iter()
            .flatten()
            .map(|parameter| parameter.name.as_str())
    }

    pub(crate) fn lexical_type_bounds(
        &self,
        owner: &ArgType,
    ) -> impl Iterator<Item = (&str, &JvmTypeSignature)> {
        self.lexical_type_parameters
            .get(owner)
            .into_iter()
            .flatten()
            .filter_map(|parameter| {
                parameter
                    .class_bound
                    .as_ref()
                    .or_else(|| parameter.interface_bounds.first())
                    .map(|bound| (parameter.name.as_str(), bound))
            })
    }

    pub(crate) fn outer_instances(&self) -> impl Iterator<Item = (&FieldReference, &ArgType)> {
        self.outer_instances.iter()
    }

    pub(crate) fn field_types(
        &self,
    ) -> impl Iterator<Item = (&FieldReference, &GenericFieldContract)> {
        self.field_types.iter()
    }

    pub(crate) fn generic_field(&self, field: &FieldReference) -> Option<GenericFieldContract> {
        if let Some(contract) = self.field_types.get(field) {
            return Some(contract.clone());
        }
        let hierarchy = self.generic_hierarchy.as_ref()?;
        let mut nearest: Option<(&FieldReference, &GenericFieldContract)> = None;
        for (candidate, contract) in self.field_types.iter().filter(|(candidate, _)| {
            candidate.name == field.name
                && candidate.field_type == field.field_type
                && hierarchy.is_subtype(&field.owner, &candidate.owner)
        }) {
            nearest = match nearest {
                None => Some((candidate, contract)),
                Some((current, _)) if hierarchy.is_subtype(&candidate.owner, &current.owner) => {
                    Some((candidate, contract))
                }
                Some((current, current_contract))
                    if hierarchy.is_subtype(&current.owner, &candidate.owner) =>
                {
                    Some((current, current_contract))
                }
                Some(_) => return None,
            };
        }
        let (declaring_field, contract) = nearest?;
        if declaring_field.owner == field.owner {
            return Some(contract.clone());
        }
        let Some(instantiated_owner) = self.owner_types.get(&field.owner) else {
            return Some(contract.clone());
        };
        let Some(signature) = hierarchy.project_member_type(
            &JvmTypeSignature::ClassType(instantiated_owner.clone()),
            &contract.owner,
            &contract.signature,
        ) else {
            return Some(contract.clone());
        };
        Some(GenericFieldContract {
            signature,
            owner: instantiated_owner.clone(),
        })
    }

    pub(crate) fn generic_fields<'a>(
        &self,
        fields: impl IntoIterator<Item = &'a FieldReference>,
    ) -> std::collections::BTreeMap<FieldReference, GenericFieldContract> {
        fields
            .into_iter()
            .filter_map(|field| {
                self.generic_field(field)
                    .map(|contract| (field.clone(), contract))
            })
            .collect()
    }

    pub(crate) fn method_exceptions(&self, method: &MethodReference) -> &[ArgType] {
        self.method_exceptions
            .get(method)
            .or_else(|| self.platform_exceptions.get(method))
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    pub(crate) fn generic_method(&self, method: &MethodReference) -> Option<GenericMethodContract> {
        if let Some(contract) = self.generic_methods.get(method) {
            return Some(contract.clone());
        }
        self.generic_hierarchy
            .as_ref()
            .and_then(|hierarchy| hierarchy.method_contract(method))
            .or_else(|| {
                self.platform_generic_hierarchy
                    .as_ref()
                    .and_then(|hierarchy| hierarchy.method_contract(method))
            })
            .or_else(|| {
                if method.is_constructor() {
                    None
                } else {
                    self.inherited_generic_method(method)
                }
            })
    }

    fn inherited_generic_method(&self, method: &MethodReference) -> Option<GenericMethodContract> {
        let candidates = self
            .generic_method_declarations
            .get(&(method.name.clone(), method.descriptor.clone()))?;
        let mut best: Option<(&ArgType, &GenericMethodContract)> = None;
        for (candidate_owner, contract) in candidates
            .iter()
            .filter(|(owner, _)| self.is_subtype(&method.owner, owner))
        {
            let Some((current_owner, _)) = best else {
                best = Some((candidate_owner, contract));
                continue;
            };
            if self.is_subtype(candidate_owner, current_owner) {
                best = Some((candidate_owner, contract));
            } else if !self.is_subtype(current_owner, candidate_owner) {
                return None;
            }
        }
        best.map(|(_, contract)| contract.clone())
    }

    pub(crate) fn generic_methods<'a>(
        &self,
        methods: impl IntoIterator<Item = &'a MethodReference>,
    ) -> std::collections::BTreeMap<MethodReference, GenericMethodContract> {
        methods
            .into_iter()
            .filter_map(|method| {
                self.generic_method(method)
                    .map(|contract| (method.clone(), contract))
            })
            .collect()
    }

    pub(crate) fn function_object_types(
        &self,
    ) -> impl Iterator<Item = (&ArgType, &JvmTypeSignature)> {
        self.function_object_types.iter()
    }

    pub(crate) fn nested_type_requires_external_access(&self, ty: &ArgType) -> bool {
        self.externally_referenced_nested_types.contains(ty)
    }

    pub(crate) fn referenced_overloads<'a>(
        &self,
        methods: impl IntoIterator<Item = &'a MethodReference>,
    ) -> BTreeSet<MethodReference> {
        let mut overloads = BTreeSet::new();
        for method in methods {
            overloads.insert(method.clone());
            if let Some(hierarchy) = &self.generic_hierarchy {
                overloads.extend(hierarchy.method_overloads(method));
            }
            if let Some(hierarchy) = &self.platform_generic_hierarchy {
                overloads.extend(hierarchy.method_overloads(method));
            }
        }
        overloads
    }

    pub(crate) fn inherited_method_signature(
        &self,
        instantiated_type: &JvmTypeSignature,
        method: &MethodReference,
    ) -> Option<crate::ir::generic_types::MethodSignature> {
        self.generic_hierarchy
            .as_ref()
            .and_then(|hierarchy| hierarchy.inherited_method_signature(instantiated_type, method))
            .or_else(|| {
                self.platform_generic_hierarchy
                    .as_ref()
                    .and_then(|hierarchy| {
                        hierarchy.inherited_method_signature(instantiated_type, method)
                    })
            })
    }

    /// Recovers a declaration signature from an immediate superclass or
    /// interface when the method's own generic metadata is unusable. Distinct
    /// inherited contracts remain unresolved instead of being guessed.
    pub(crate) fn inherited_declaration_signature(
        &self,
        class: &ClassNode,
        method: &MethodNode,
    ) -> Option<crate::ir::generic_types::MethodSignature> {
        let instantiated_type =
            JvmTypeSignature::ClassType(self.owner_type(class.class_type())?.clone());
        let mut recovered = None;
        for parent in class.super_class.iter().chain(&class.interfaces) {
            let reference = MethodReference {
                owner: parent.clone(),
                name: method.name().to_string(),
                descriptor: crate::ir::MethodDescriptor {
                    parameters: method.param_types().to_vec(),
                    return_type: method.return_type().clone(),
                },
            };
            let Some(candidate) = self.inherited_method_signature(&instantiated_type, &reference)
            else {
                continue;
            };
            if recovered
                .as_ref()
                .is_some_and(|existing| existing != &candidate)
            {
                return None;
            }
            recovered = Some(candidate);
        }
        recovered
    }

    pub(crate) fn class_type_parameters(&self, ty: &ArgType) -> Option<Vec<TypeParameter>> {
        self.generic_hierarchy
            .as_ref()
            .and_then(|hierarchy| hierarchy.declared_type_parameters(ty))
            .or_else(|| {
                self.platform_generic_hierarchy
                    .as_ref()
                    .and_then(|hierarchy| hierarchy.declared_type_parameters(ty))
            })
    }

    pub(crate) fn is_subtype(&self, subtype: &ArgType, supertype: &ArgType) -> bool {
        subtype == supertype
            || self
                .generic_hierarchy
                .as_ref()
                .is_some_and(|hierarchy| hierarchy.is_subtype(subtype, supertype))
            || self
                .platform_generic_hierarchy
                .as_ref()
                .is_some_and(|hierarchy| hierarchy.is_subtype(subtype, supertype))
            || self.platform_symbols.as_deref().is_some_and(|symbols| {
                symbols.is_subtype(&subtype.to_descriptor(), &supertype.to_descriptor())
            })
    }

    pub(crate) fn specialize_subtype(
        &self,
        subtype: &ArgType,
        expected_supertype: &JvmTypeSignature,
    ) -> Option<JvmTypeSignature> {
        self.generic_hierarchy
            .as_ref()
            .and_then(|hierarchy| hierarchy.specialize_subtype(subtype, expected_supertype))
            .or_else(|| {
                self.platform_generic_hierarchy
                    .as_ref()
                    .and_then(|hierarchy| hierarchy.specialize_subtype(subtype, expected_supertype))
            })
    }

    pub(crate) fn infer_subtype(
        &self,
        subtype: &ArgType,
        expected_supertype: &JvmTypeSignature,
    ) -> Option<JvmTypeSignature> {
        self.generic_hierarchy
            .as_ref()
            .and_then(|hierarchy| hierarchy.infer_subtype(subtype, expected_supertype))
            .or_else(|| {
                self.platform_generic_hierarchy
                    .as_ref()
                    .and_then(|hierarchy| hierarchy.infer_subtype(subtype, expected_supertype))
            })
    }

    pub(crate) fn project_supertype(
        &self,
        subtype: &JvmTypeSignature,
        expected_supertype: &ArgType,
    ) -> Option<JvmTypeSignature> {
        self.generic_hierarchy
            .as_ref()
            .and_then(|hierarchy| hierarchy.project_supertype(subtype, expected_supertype))
            .or_else(|| {
                self.platform_generic_hierarchy
                    .as_ref()
                    .and_then(|hierarchy| hierarchy.project_supertype(subtype, expected_supertype))
            })
    }

    pub(crate) fn functional_interface(
        &self,
        interfaces: &[ArgType],
        implementation_name: &str,
        implementation_parameters: &[ArgType],
    ) -> Option<ArgType> {
        self.generic_hierarchy
            .as_ref()
            .and_then(|hierarchy| {
                hierarchy.functional_interface(
                    interfaces,
                    implementation_name,
                    implementation_parameters,
                )
            })
            .or_else(|| {
                self.platform_generic_hierarchy
                    .as_ref()
                    .and_then(|hierarchy| {
                        hierarchy.functional_interface(
                            interfaces,
                            implementation_name,
                            implementation_parameters,
                        )
                    })
            })
    }

    fn open_owner_types(
        classes: &[&ClassNode],
    ) -> std::collections::BTreeMap<ArgType, ClassTypeSignature> {
        let by_type = classes
            .iter()
            .map(|class| (class.class_type().clone(), *class))
            .collect::<std::collections::BTreeMap<_, _>>();
        classes
            .iter()
            .map(|class| {
                (
                    class.class_type().clone(),
                    Self::open_owner_type(class, &by_type),
                )
            })
            .collect()
    }

    fn externally_referenced_nested_types(classes: &[&ClassNode]) -> BTreeSet<ArgType> {
        let by_type = classes
            .iter()
            .map(|class| (class.class_type().clone(), *class))
            .collect::<BTreeMap<_, _>>();
        let roots = classes
            .iter()
            .map(|class| {
                (
                    class.class_type().clone(),
                    Self::source_unit_root(class, &by_type),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let mut widened = BTreeSet::new();
        for class in classes {
            let Some(referencing_root) = roots.get(class.class_type()) else {
                continue;
            };
            let references = class
                .fields()
                .iter()
                .flat_map(|field| std::iter::once(field.field_type()))
                .chain(class.methods().iter().flat_map(|method| {
                    method
                        .param_types()
                        .iter()
                        .chain(std::iter::once(method.return_type()))
                }))
                .chain(class.super_class.iter())
                .chain(&class.interfaces);
            for reference in references {
                let Some(reference) = Self::referenced_object_type(reference) else {
                    continue;
                };
                let Some(target) = by_type.get(reference) else {
                    continue;
                };
                let target_access = target
                    .metadata
                    .inner_class
                    .as_ref()
                    .map(|inner| AccessInfo::for_class(inner.access_flags_raw))
                    .unwrap_or(target.access_flags);
                if target.is_inner()
                    && target_access.is_private()
                    && roots
                        .get(reference)
                        .is_some_and(|root| root != referencing_root)
                {
                    widened.insert(reference.clone());
                }
            }
        }
        widened
    }

    fn source_unit_root(class: &ClassNode, classes: &BTreeMap<ArgType, &ClassNode>) -> ArgType {
        let mut current = class;
        let mut visited = BTreeSet::new();
        while current.is_inner() && visited.insert(current.class_type().clone()) {
            let Some(parent) = current
                .parent_class_name()
                .and_then(|parent| parent.parse::<ArgType>().ok())
                .and_then(|parent| classes.get(&parent).copied())
            else {
                break;
            };
            current = parent;
        }
        current.class_type().clone()
    }

    fn referenced_object_type(ty: &ArgType) -> Option<&ArgType> {
        match ty {
            ArgType::Object(_) => Some(ty),
            ArgType::Array(element) => Self::referenced_object_type(element),
            ArgType::Primitive(_) | ArgType::Unknown(_) => None,
        }
    }

    fn build_inherited_member_types(
        classes: &[&ClassNode],
    ) -> BTreeMap<ArgType, BTreeSet<(JavaIdentifier, ArgType)>> {
        let by_type = classes
            .iter()
            .map(|class| (class.class_type().clone(), *class))
            .collect::<BTreeMap<_, _>>();
        let mut direct_members = BTreeMap::<ArgType, BTreeSet<(JavaIdentifier, ArgType)>>::new();
        for class in classes.iter().copied().filter(|class| class.is_inner()) {
            let Some(owner) = class
                .parent_class_name()
                .and_then(|owner| owner.parse::<ArgType>().ok())
            else {
                continue;
            };
            direct_members.entry(owner).or_default().insert((
                super::class::simple_inner_class_name(class),
                class.class_type().clone(),
            ));
        }

        classes
            .iter()
            .copied()
            .map(|class| {
                let mut names = BTreeSet::new();
                let mut visited = BTreeSet::new();
                let mut pending = class
                    .super_class
                    .iter()
                    .chain(&class.interfaces)
                    .cloned()
                    .collect::<Vec<_>>();
                while let Some(parent) = pending.pop() {
                    if !visited.insert(parent.clone()) {
                        continue;
                    }
                    names.extend(direct_members.get(&parent).into_iter().flatten().cloned());
                    if let Some(parent_class) = by_type.get(&parent) {
                        pending.extend(
                            parent_class
                                .super_class
                                .iter()
                                .chain(&parent_class.interfaces)
                                .cloned(),
                        );
                    }
                }
                (class.class_type().clone(), names)
            })
            .collect()
    }

    fn declared_type_parameters(class: &ClassNode) -> Vec<TypeParameter> {
        class
            .signature
            .as_deref()
            .and_then(|signature| GenericSignatures::class(signature).ok())
            .into_iter()
            .flat_map(|signature| signature.type_parameters)
            .collect()
    }

    fn open_owner_type(
        class: &ClassNode,
        classes: &std::collections::BTreeMap<ArgType, &ClassNode>,
    ) -> ClassTypeSignature {
        let mut chain = vec![class];
        let mut seen = std::collections::BTreeSet::from([class.class_type().clone()]);
        let mut current = class;
        while let Some(parent) = current
            .parent_class_name()
            .and_then(|descriptor| descriptor.parse::<ArgType>().ok())
            .filter(|parent| seen.insert(parent.clone()))
            .and_then(|parent| classes.get(&parent).copied())
        {
            chain.push(parent);
            current = parent;
        }
        chain.reverse();

        let mut arguments = vec![Vec::new(); chain.len()];
        let mut captures_parent = true;
        for index in (0..chain.len()).rev() {
            if captures_parent {
                arguments[index] = Self::declared_type_arguments(chain[index]);
            }
            if index != 0 {
                captures_parent &= EnclosingInstanceAbi::analyze(chain[index]).is_some();
            }
        }

        let Some(raw_name) = chain
            .first()
            .and_then(|class| class.class_type().as_object())
        else {
            return Self::direct_owner_type(class);
        };
        let inner_segments = chain
            .windows(2)
            .enumerate()
            .filter_map(|(index, pair)| {
                let parent = pair[0].class_type().as_object()?;
                let child = pair[1].class_type().as_object()?;
                let simple_name = child
                    .strip_prefix(parent)
                    .and_then(|suffix| suffix.strip_prefix('$'))
                    .or_else(|| child.rsplit('$').next())?;
                Some(InnerClassTypeSignature {
                    simple_name: simple_name.to_string(),
                    type_arguments: arguments[index + 1].clone(),
                })
            })
            .collect::<Vec<_>>();
        if inner_segments.len() + 1 != chain.len() {
            return Self::direct_owner_type(class);
        }
        ClassTypeSignature {
            raw_name: raw_name.to_string(),
            type_arguments: arguments.into_iter().next().unwrap_or_default(),
            inner_segments,
        }
    }

    fn direct_owner_type(class: &ClassNode) -> ClassTypeSignature {
        ClassTypeSignature {
            raw_name: class
                .class_type()
                .as_object()
                .unwrap_or("java/lang/Object")
                .to_string(),
            type_arguments: Self::declared_type_arguments(class),
            inner_segments: Vec::new(),
        }
    }

    fn declared_type_arguments(class: &ClassNode) -> Vec<TypeArgument> {
        class
            .signature
            .as_deref()
            .and_then(|signature| GenericSignatures::class(signature).ok())
            .into_iter()
            .flat_map(|signature| signature.type_parameters)
            .map(|parameter| TypeArgument::Exact(JvmTypeSignature::TypeVariable(parameter.name)))
            .collect()
    }
}
