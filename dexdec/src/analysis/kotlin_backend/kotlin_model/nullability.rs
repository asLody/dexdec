use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::metadata_members::{backing_field_references, MetadataCallable};
use crate::decoder::method_decoder::MethodDecoder;
use crate::frontend::kotlin_metadata::KotlinMetadata;
use crate::frontend::{AnnotationNode, ClassNode, DexValue, MethodNode};
use crate::ir::{
    BlockId, EdgeKind, IfOp, InsnArg, InsnNode, InsnType, InvokeType, MemberReference,
    MethodContext, MethodDescriptor, MethodReference, Splitter, CFG,
};

#[derive(Debug, Clone, Default)]
pub(super) struct DexNullabilityContracts {
    methods: BTreeMap<MethodReference, crate::language::kotlin::KotlinMethodNullability>,
    non_null_fields: std::sync::Arc<BTreeSet<crate::ir::FieldReference>>,
    dependencies: BTreeSet<crate::ir::ArgType>,
}

impl DexNullabilityContracts {
    pub(super) fn analyze(
        classes: &[&ClassNode],
        contract_roots: &BTreeSet<MethodReference>,
        resolve_method: &impl Fn(&ClassNode, u32) -> Option<MethodReference>,
        resolve_field: &impl Fn(&ClassNode, u32) -> Option<crate::ir::FieldReference>,
    ) -> Self {
        let metadata = NullabilityMetadata::analyze(classes);
        let cfgs = MethodCfgCatalog::analyze(classes, resolve_method, resolve_field);
        let mut non_null_fields = metadata.non_null_fields.clone();
        non_null_fields.extend(StaticFieldNullability::analyze(classes, &cfgs));
        let fixed_non_null_fields = non_null_fields.clone();
        let instance_fields = InstanceFieldEvidence::analyze(classes, &cfgs);
        let summaries = classes
            .iter()
            .flat_map(|class| {
                let cfgs = &cfgs;
                class
                    .methods()
                    .iter()
                    .filter(|method| !method.is_class_init())
                    .map(move |method| {
                        let reference = Self::reference(class, method);
                        let evidence = cfgs.get(&reference).map_or_else(
                            || MethodNullabilityEvidence {
                                parameters: vec![
                                    ParameterEvidence::default();
                                    method.param_types().len()
                                ],
                                ..Default::default()
                            },
                            |cfg| MethodParameterNullability::analyze(method, cfg),
                        );
                        (reference, evidence)
                    })
            })
            .collect::<BTreeMap<_, _>>();
        let relevant = Self::relevant_methods(contract_roots, &summaries);
        let mut dependencies = contract_roots
            .iter()
            .filter(|method| !summaries.contains_key(*method))
            .map(|method| method.owner.clone())
            .collect::<BTreeSet<_>>();
        dependencies.extend(cfgs.unresolved_termination_owners(&relevant));
        for method in &relevant {
            let Some(evidence) = summaries.get(method) else {
                continue;
            };
            dependencies.extend(
                evidence
                    .parameters
                    .iter()
                    .flat_map(|parameter| &parameter.dependencies)
                    .filter(|dependency| !summaries.contains_key(&dependency.method))
                    .map(|dependency| dependency.method.owner.clone()),
            );
            dependencies.extend(evidence.returns.call_dependencies().filter_map(|method| {
                (!summaries.contains_key(method)).then(|| method.owner.clone())
            }));
        }
        let mut non_null = metadata.non_null_parameters;
        loop {
            let before = non_null.len();
            for (method, parameters) in &summaries {
                for (parameter, evidence) in parameters.parameters.iter().enumerate() {
                    let id = ParameterId {
                        method: method.clone(),
                        parameter,
                    };
                    if metadata.nullable_parameters.contains(&id) {
                        continue;
                    }
                    if evidence.required_on_all_returns {
                        non_null.insert(id);
                        continue;
                    }
                    if evidence.uses == 0
                        || evidence.uses != evidence.required + evidence.dependencies.len()
                    {
                        continue;
                    }
                    let dependencies_hold = evidence.dependencies.iter().all(|dependency| {
                        non_null.contains(&ParameterId {
                            method: dependency.method.clone(),
                            parameter: dependency.parameter,
                        })
                    });
                    if (evidence.required != 0 || !evidence.dependencies.is_empty())
                        && dependencies_hold
                    {
                        non_null.insert(id);
                    }
                }
            }
            if non_null.len() == before {
                break;
            }
        }
        let fixed_non_null_returns = metadata.non_null_returns.clone();
        let mut non_null_returns = fixed_non_null_returns.clone();
        non_null_returns.extend(
            summaries
                .keys()
                .filter(|method| {
                    method.descriptor.return_type.is_reference()
                        && !metadata.nullable_returns.contains(*method)
                })
                .cloned(),
        );
        non_null_fields.extend(
            instance_fields
                .writes
                .keys()
                .filter(|field| !metadata.nullable_fields.contains(*field))
                .cloned(),
        );
        loop {
            let previous_returns = non_null_returns.clone();
            let previous_fields = non_null_fields.clone();
            non_null_returns.retain(|method| {
                fixed_non_null_returns.contains(method)
                    || summaries.get(method).is_some_and(|evidence| {
                        evidence.returns.all_non_null(
                            method,
                            &non_null,
                            &previous_returns,
                            &previous_fields,
                        )
                    })
            });
            instance_fields.retain_proven(
                &mut non_null_fields,
                &non_null,
                &previous_returns,
                &fixed_non_null_fields,
            );
            if non_null_returns == previous_returns && non_null_fields == previous_fields {
                break;
            }
        }
        let methods = summaries
            .into_iter()
            .filter_map(|(method, evidence)| {
                let parameters = evidence
                    .parameters
                    .iter()
                    .enumerate()
                    .map(|(parameter, _)| {
                        non_null.contains(&ParameterId {
                            method: method.clone(),
                            parameter,
                        })
                    })
                    .collect::<Vec<_>>();
                let return_non_null = non_null_returns.contains(&method)
                    && !metadata.nullable_returns.contains(&method);
                (parameters.iter().any(|required| *required) || return_non_null).then_some((
                    method,
                    crate::language::kotlin::KotlinMethodNullability::new(
                        parameters,
                        return_non_null,
                    ),
                ))
            })
            .collect();
        Self {
            methods,
            non_null_fields: std::sync::Arc::new(non_null_fields),
            dependencies,
        }
    }

    fn relevant_methods(
        roots: &BTreeSet<MethodReference>,
        summaries: &BTreeMap<MethodReference, MethodNullabilityEvidence>,
    ) -> BTreeSet<MethodReference> {
        let mut relevant = roots.clone();
        let mut pending = roots.iter().cloned().collect::<VecDeque<_>>();
        while let Some(method) = pending.pop_front() {
            let Some(evidence) = summaries.get(&method) else {
                continue;
            };
            let dependencies = evidence
                .parameters
                .iter()
                .flat_map(|parameter| &parameter.dependencies)
                .map(|dependency| &dependency.method)
                .chain(evidence.returns.call_dependencies());
            for dependency in dependencies {
                if relevant.insert(dependency.clone()) {
                    pending.push_back(dependency.clone());
                }
            }
        }
        relevant
    }

    pub(super) fn get(
        &self,
        method: &MethodReference,
    ) -> Option<&crate::language::kotlin::KotlinMethodNullability> {
        self.methods.get(method)
    }

    pub(super) fn field_is_non_null(&self, field: &crate::ir::FieldReference) -> bool {
        self.non_null_fields.contains(field)
    }

    pub(super) fn non_null_fields(&self) -> std::sync::Arc<BTreeSet<crate::ir::FieldReference>> {
        std::sync::Arc::clone(&self.non_null_fields)
    }

    pub(super) fn dependencies(&self) -> impl Iterator<Item = &crate::ir::ArgType> {
        self.dependencies.iter()
    }

    pub(super) fn select<'a>(
        &'a self,
        methods: impl IntoIterator<Item = &'a MethodReference>,
    ) -> BTreeMap<MethodReference, crate::language::kotlin::KotlinMethodNullability> {
        methods
            .into_iter()
            .filter_map(|method| {
                self.methods
                    .get(method)
                    .cloned()
                    .map(|contract| (method.clone(), contract))
            })
            .collect()
    }

    fn reference(class: &ClassNode, method: &MethodNode) -> MethodReference {
        MethodReference {
            owner: class.class_type().clone(),
            name: method.name().to_string(),
            descriptor: MethodDescriptor {
                parameters: method.param_types().to_vec(),
                return_type: method.return_type().clone(),
            },
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct DefaultTargets {
    parameters: bool,
    methods: bool,
}

#[derive(Debug, Default)]
struct NullabilityMetadata {
    non_null_parameters: BTreeSet<ParameterId>,
    nullable_parameters: BTreeSet<ParameterId>,
    non_null_returns: BTreeSet<MethodReference>,
    nullable_returns: BTreeSet<MethodReference>,
    /// Fields a Kotlin class declares as a non-null property.
    non_null_fields: BTreeSet<crate::ir::FieldReference>,
    nullable_fields: BTreeSet<crate::ir::FieldReference>,
}

impl NullabilityMetadata {
    fn analyze(classes: &[&ClassNode]) -> Self {
        let defaults = classes
            .iter()
            .filter_map(|class| {
                let non_null = Self::has_non_null(&class.annotations);
                let targets = class
                    .annotations
                    .iter()
                    .find(|annotation| {
                        Self::descriptor(annotation)
                            == "Ljavax/annotation/meta/TypeQualifierDefault;"
                    })
                    .map(Self::default_targets)?;
                (non_null && targets.parameters).then(|| (class.class_type().clone(), targets))
            })
            .collect::<BTreeMap<_, _>>();
        let mut metadata = Self::default();
        for class in classes {
            let class_default = class.annotations.iter().any(|annotation| {
                Self::is_null_marked(Self::descriptor(annotation))
                    || defaults
                        .get(&annotation.annotation_type)
                        .is_some_and(|targets| targets.parameters)
            });
            let return_default = class.annotations.iter().any(|annotation| {
                Self::is_null_marked(Self::descriptor(annotation))
                    || defaults
                        .get(&annotation.annotation_type)
                        .is_some_and(|targets| targets.methods)
            });
            for method in class.methods() {
                let reference = DexNullabilityContracts::reference(class, method);
                if method.return_type().is_reference() {
                    if Self::has_nullable(&method.annotations) {
                        metadata.nullable_returns.insert(reference.clone());
                    } else if return_default || Self::has_non_null(&method.annotations) {
                        metadata.non_null_returns.insert(reference.clone());
                    }
                }
                for (parameter, ty) in method.param_types().iter().enumerate() {
                    if !ty.is_reference() {
                        continue;
                    }
                    let annotations = method
                        .parameter_annotations
                        .get(parameter)
                        .map(Vec::as_slice)
                        .unwrap_or_default();
                    let id = ParameterId {
                        method: reference.clone(),
                        parameter,
                    };
                    if Self::has_nullable(annotations) {
                        metadata.nullable_parameters.insert(id);
                    } else if class_default || Self::has_non_null(annotations) {
                        metadata.non_null_parameters.insert(id);
                    }
                }
            }
            metadata.declare(class);
        }
        metadata
    }

    /// Records what a Kotlin-compiled class states about its own declarations.
    ///
    /// Bytecode cannot express nullability, so the Kotlin compiler restates
    /// every declaration in `@kotlin.Metadata`. Where a class carries it the
    /// annotation is the source rather than an inference, so it settles members
    /// that the Java annotations left open.
    fn declare(&mut self, class: &ClassNode) {
        let Some(Ok(metadata)) = KotlinMetadata::of(&class.annotations) else {
            return;
        };
        let declarations = metadata.declarations();
        let callables = MetadataCallable::of(declarations);
        for method in class.methods() {
            let Some(callable) = MetadataCallable::resolve(&callables, class, method) else {
                continue;
            };
            let reference = DexNullabilityContracts::reference(class, method);
            if method.return_type().is_reference() {
                match callable.return_type.map(|ty| ty.nullable) {
                    Some(true) => {
                        self.non_null_returns.remove(&reference);
                        self.nullable_returns.insert(reference.clone());
                    }
                    Some(false) => {
                        self.nullable_returns.remove(&reference);
                        self.non_null_returns.insert(reference.clone());
                    }
                    None => {}
                }
            }
            let Some(offset) = callable.parameter_offset(method) else {
                continue;
            };
            if let Some(receiver) = callable.receiver_type {
                if method
                    .param_types()
                    .first()
                    .is_some_and(crate::ir::ArgType::is_reference)
                {
                    let id = ParameterId {
                        method: reference.clone(),
                        parameter: 0,
                    };
                    if receiver.nullable {
                        self.non_null_parameters.remove(&id);
                        self.nullable_parameters.insert(id);
                    } else {
                        self.nullable_parameters.remove(&id);
                        self.non_null_parameters.insert(id);
                    }
                }
            }
            for (index, parameter) in callable.parameters.iter().enumerate() {
                let Some(ty) = method.param_types().get(offset + index) else {
                    continue;
                };
                if !ty.is_reference() {
                    continue;
                }
                let id = ParameterId {
                    method: reference.clone(),
                    parameter: offset + index,
                };
                match parameter.ty.map(|ty| ty.nullable) {
                    Some(true) => {
                        self.non_null_parameters.remove(&id);
                        self.nullable_parameters.insert(id);
                    }
                    Some(false) => {
                        self.nullable_parameters.remove(&id);
                        self.non_null_parameters.insert(id);
                    }
                    None => {}
                }
            }
        }
        for property in &declarations.properties {
            if let Some(ty) = property.ty.as_ref() {
                for field in backing_field_references(class, declarations, property) {
                    if !field.field_type.is_reference() {
                        continue;
                    }
                    if ty.nullable {
                        self.nullable_fields.insert(field);
                    } else {
                        self.non_null_fields.insert(field);
                    }
                }
            }
        }
    }

    fn default_targets(annotation: &AnnotationNode) -> DefaultTargets {
        let parameters = annotation
            .elements
            .iter()
            .find(|element| element.name == "value")
            .into_iter()
            .flat_map(|element| match &element.value {
                DexValue::Array(values) => values.as_slice(),
                value => std::slice::from_ref(value),
            })
            .any(|value| {
                matches!(
                    value,
                    DexValue::Enum(field) if field.name == "PARAMETER"
                )
            });
        let methods = annotation
            .elements
            .iter()
            .find(|element| element.name == "value")
            .into_iter()
            .flat_map(|element| match &element.value {
                DexValue::Array(values) => values.as_slice(),
                value => std::slice::from_ref(value),
            })
            .any(|value| {
                matches!(
                    value,
                    DexValue::Enum(field) if field.name == "METHOD"
                )
            });
        DefaultTargets {
            parameters,
            methods,
        }
    }

    fn has_non_null(annotations: &[AnnotationNode]) -> bool {
        annotations
            .iter()
            .any(|annotation| Self::is_non_null(Self::descriptor(annotation)))
    }

    fn has_nullable(annotations: &[AnnotationNode]) -> bool {
        annotations
            .iter()
            .any(|annotation| Self::is_nullable(Self::descriptor(annotation)))
    }

    fn descriptor(annotation: &AnnotationNode) -> String {
        annotation.annotation_type.to_descriptor()
    }

    fn is_non_null(descriptor: String) -> bool {
        matches!(
            descriptor.as_str(),
            "Ljavax/annotation/Nonnull;"
                | "Ljakarta/annotation/Nonnull;"
                | "Lorg/jetbrains/annotations/NotNull;"
                | "Landroidx/annotation/NonNull;"
                | "Landroid/annotation/NonNull;"
                | "Lorg/jspecify/annotations/NonNull;"
        )
    }

    fn is_nullable(descriptor: String) -> bool {
        matches!(
            descriptor.as_str(),
            "Ljavax/annotation/Nullable;"
                | "Ljakarta/annotation/Nullable;"
                | "Lorg/jetbrains/annotations/Nullable;"
                | "Landroidx/annotation/Nullable;"
                | "Landroid/annotation/Nullable;"
                | "Lorg/jspecify/annotations/Nullable;"
        )
    }

    fn is_null_marked(descriptor: String) -> bool {
        descriptor == "Lorg/jspecify/annotations/NullMarked;"
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ParameterId {
    method: MethodReference,
    parameter: usize,
}

/// One resolved raw CFG per loaded method. Nullability analyses share this
/// catalog so termination, return flow, and field flow observe identical
/// control-flow and member identities.
#[derive(Debug, Default)]
struct MethodCfgCatalog {
    methods: BTreeMap<MethodReference, CFG>,
}

impl MethodCfgCatalog {
    fn analyze(
        classes: &[&ClassNode],
        resolve_method: &impl Fn(&ClassNode, u32) -> Option<MethodReference>,
        resolve_field: &impl Fn(&ClassNode, u32) -> Option<crate::ir::FieldReference>,
    ) -> Self {
        let mut methods = BTreeMap::new();
        for class in classes {
            for method in class.methods() {
                let Some(code) = method.code() else {
                    continue;
                };
                let decoded = MethodDecoder::from_code(code).decode();
                let mut cfg = Splitter::new(method.name())
                    .instructions(decoded.insns)
                    .handlers(decoded.handlers)
                    .registers(decoded.registers)
                    .ins(decoded.ins)
                    .build();
                cfg.set_method(MethodContext::new(
                    class.class_type().clone(),
                    method.name(),
                    MethodDescriptor {
                        parameters: method.param_types().to_vec(),
                        return_type: method.return_type().clone(),
                    },
                    method.is_static(),
                ));
                for instruction in cfg.blocks.values_mut().flat_map(|block| &mut block.insns) {
                    if let Some(reference) = instruction
                        .payload
                        .method_index
                        .and_then(|index| resolve_method(class, index))
                    {
                        instruction.payload.reference = Some(MemberReference::Method(reference));
                    } else if let Some(reference) = instruction
                        .payload
                        .field_index
                        .and_then(|index| resolve_field(class, index))
                    {
                        instruction.payload.reference = Some(MemberReference::Field(reference));
                    }
                }
                methods.insert(DexNullabilityContracts::reference(class, method), cfg);
            }
        }
        let termination = crate::ir::analysis::MethodTermination::analyze(methods.values());
        for cfg in methods.values_mut() {
            termination.apply(cfg);
        }
        Self { methods }
    }

    fn get(&self, method: &MethodReference) -> Option<&CFG> {
        self.methods.get(method)
    }

    fn unresolved_termination_owners(
        &self,
        relevant: &BTreeSet<MethodReference>,
    ) -> BTreeSet<crate::ir::ArgType> {
        relevant
            .iter()
            .filter_map(|method| self.methods.get(method))
            .flat_map(|cfg| cfg.blocks.values())
            .flat_map(|block| &block.insns)
            .filter(|instruction| {
                instruction.insn_type == InsnType::Invoke
                    && matches!(
                        instruction.payload.invoke_type,
                        Some(InvokeType::Static | InvokeType::Direct | InvokeType::Super)
                    )
            })
            .filter_map(|instruction| match instruction.payload.reference.as_ref() {
                Some(MemberReference::Method(method)) if !self.methods.contains_key(method) => {
                    Some(method.owner.clone())
                }
                _ => None,
            })
            .collect()
    }
}

#[derive(Debug, Clone)]
struct ParameterDependency {
    method: MethodReference,
    parameter: usize,
}

#[derive(Debug, Clone, Default)]
struct ParameterEvidence {
    uses: usize,
    required: usize,
    required_on_all_returns: bool,
    dependencies: Vec<ParameterDependency>,
}

#[derive(Debug, Clone, Default)]
struct MethodNullabilityEvidence {
    parameters: Vec<ParameterEvidence>,
    returns: ReturnEvidence,
}

#[derive(Debug, Clone, Default)]
struct ReturnEvidence {
    values: Vec<ReturnOrigin>,
}

impl ReturnEvidence {
    fn call_dependencies(&self) -> impl Iterator<Item = &MethodReference> {
        self.values
            .iter()
            .flat_map(|origin| match origin {
                ReturnOrigin::Proven(requirements) => requirements.as_slice(),
                ReturnOrigin::Unknown | ReturnOrigin::Null => &[],
            })
            .filter_map(|requirement| match requirement {
                ReturnRequirement::Call(method) => Some(method),
                ReturnRequirement::Parameter(_) | ReturnRequirement::Field(_) => None,
            })
    }

    fn all_non_null(
        &self,
        method: &MethodReference,
        parameters: &BTreeSet<ParameterId>,
        inferred: &BTreeSet<MethodReference>,
        fields: &BTreeSet<crate::ir::FieldReference>,
    ) -> bool {
        !self.values.is_empty()
            && self.values.iter().all(|value| match value {
                ReturnOrigin::Proven(requirements) => {
                    requirements.iter().all(|requirement| match requirement {
                        ReturnRequirement::Parameter(parameter) => {
                            parameters.contains(&ParameterId {
                                method: method.clone(),
                                parameter: *parameter,
                            })
                        }
                        ReturnRequirement::Call(method) => inferred.contains(method),
                        ReturnRequirement::Field(field) => fields.contains(field),
                    })
                }
                ReturnOrigin::Unknown | ReturnOrigin::Null => false,
            })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ReturnOrigin {
    Unknown,
    Null,
    Proven(Vec<ReturnRequirement>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ReturnRequirement {
    Parameter(usize),
    Call(MethodReference),
    Field(crate::ir::FieldReference),
}

struct MethodParameterNullability;

impl MethodParameterNullability {
    fn analyze(method: &MethodNode, cfg: &CFG) -> MethodNullabilityEvidence {
        let mut parameters = vec![ParameterEvidence::default(); method.param_types().len()];
        let Some(code) = method.code() else {
            return MethodNullabilityEvidence {
                parameters,
                ..Default::default()
            };
        };
        let mut entry = vec![None; usize::from(code.registers_size)];
        let mut register = usize::from(code.args_start_reg()) + usize::from(!method.is_static());
        for (parameter, ty) in method.param_types().iter().enumerate() {
            if ty.is_reference() {
                if let Some(origin) = entry.get_mut(register) {
                    *origin = Some(parameter);
                }
            }
            register += if ty.is_wide() { 2 } else { 1 };
        }

        if !cfg.handlers.is_empty() {
            return MethodNullabilityEvidence {
                parameters,
                ..Default::default()
            };
        }
        let Some(entry_block) = cfg.entry_block().map(|block| block.id) else {
            return MethodNullabilityEvidence {
                parameters,
                ..Default::default()
            };
        };
        let incoming = Self::solve_origins(cfg, entry_block, entry);
        let mut required_blocks = vec![BTreeSet::new(); parameters.len()];
        for block in cfg.blocks_iter() {
            let Some(mut origins) = incoming.get(&block.id).cloned() else {
                continue;
            };
            for instruction in &block.insns {
                let invoked = match instruction.payload.reference.as_ref() {
                    Some(MemberReference::Method(method)) => Some(method),
                    _ => None,
                };
                Self::observe(
                    block.id,
                    instruction,
                    invoked,
                    &origins,
                    &mut parameters,
                    &mut required_blocks,
                );
                Self::transfer(instruction, &mut origins);
            }
        }
        Self::mark_required_on_all_returns(cfg, &required_blocks, &mut parameters);
        let returns = if method.return_type().is_reference() {
            MethodReturnNullability::analyze(method, cfg, entry_block)
        } else {
            ReturnEvidence::default()
        };
        MethodNullabilityEvidence {
            parameters,
            returns,
        }
    }

    fn solve_origins(
        cfg: &crate::ir::CFG,
        entry: BlockId,
        state: Vec<Option<usize>>,
    ) -> BTreeMap<BlockId, Vec<Option<usize>>> {
        let mut incoming = BTreeMap::from([(entry, state)]);
        let mut pending = VecDeque::from([entry]);
        while let Some(block_id) = pending.pop_front() {
            let Some(block) = cfg.block(block_id) else {
                continue;
            };
            let mut outgoing = incoming[&block_id].clone();
            for instruction in &block.insns {
                Self::transfer(instruction, &mut outgoing);
            }
            for successor in cfg.normal_successors(block_id) {
                let changed = match incoming.get_mut(&successor) {
                    None => {
                        incoming.insert(successor, outgoing.clone());
                        true
                    }
                    Some(current) => Self::join(current, &outgoing),
                };
                if changed {
                    pending.push_back(successor);
                }
            }
        }
        incoming
    }

    fn join(current: &mut [Option<usize>], incoming: &[Option<usize>]) -> bool {
        let mut changed = false;
        for (current, incoming) in current.iter_mut().zip(incoming) {
            if *current != *incoming && current.take().is_some() {
                changed = true;
            }
        }
        changed
    }

    fn transfer(instruction: &InsnNode, origins: &mut [Option<usize>]) {
        if instruction.insn_type == InsnType::Move {
            let origin = instruction
                .args
                .first()
                .and_then(|argument| argument.reg_num())
                .and_then(|register| origins.get(register as usize))
                .copied()
                .flatten();
            if let Some(result) = &instruction.result {
                if let Some(target) = origins.get_mut(result.reg_num as usize) {
                    *target = origin;
                }
            }
            return;
        }
        if let Some(result) = &instruction.result {
            if let Some(target) = origins.get_mut(result.reg_num as usize) {
                *target = None;
            }
        }
    }

    fn observe(
        block: BlockId,
        instruction: &InsnNode,
        invoked: Option<&MethodReference>,
        origins: &[Option<usize>],
        evidence: &mut [ParameterEvidence],
        required_blocks: &mut [BTreeSet<BlockId>],
    ) {
        if instruction.insn_type == InsnType::CheckCast {
            return;
        }
        for (index, argument) in instruction.args.iter().enumerate() {
            let Some(parameter) = argument
                .reg_num()
                .and_then(|register| origins.get(register as usize))
                .copied()
                .flatten()
            else {
                continue;
            };
            evidence[parameter].uses += 1;
            if Self::requires_non_null(instruction, index) {
                evidence[parameter].required += 1;
                required_blocks[parameter].insert(block);
            } else if instruction.insn_type == InsnType::Invoke {
                if let Some(method) = invoked {
                    if let Some(target_parameter) =
                        Self::invoke_parameter(method, instruction.payload.invoke_type, index)
                    {
                        evidence[parameter].dependencies.push(ParameterDependency {
                            method: method.clone(),
                            parameter: target_parameter,
                        });
                    }
                }
            }
        }
    }

    fn mark_required_on_all_returns(
        cfg: &crate::ir::CFG,
        required_blocks: &[BTreeSet<BlockId>],
        evidence: &mut [ParameterEvidence],
    ) {
        let returns = cfg
            .blocks_iter()
            .filter(|block| {
                block
                    .insns
                    .iter()
                    .any(|instruction| instruction.insn_type == InsnType::Return)
            })
            .map(|block| block.id)
            .collect::<Vec<_>>();
        if returns.is_empty() {
            return;
        }
        let Ok(dominators) = crate::ir::analysis::DominatorTree::compute(cfg) else {
            return;
        };
        for (parameter, required) in required_blocks.iter().enumerate() {
            evidence[parameter].required_on_all_returns = returns.iter().all(|exit| {
                required
                    .iter()
                    .any(|block| dominators.dominates(*block, *exit))
            });
        }
    }

    fn invoke_parameter(
        method: &MethodReference,
        invoke_type: Option<InvokeType>,
        register_word: usize,
    ) -> Option<usize> {
        let mut cursor = usize::from(invoke_type != Some(InvokeType::Static));
        for (parameter, ty) in method.descriptor.parameters.iter().enumerate() {
            if register_word == cursor {
                return Some(parameter);
            }
            cursor += if ty.is_wide() { 2 } else { 1 };
        }
        None
    }

    fn requires_non_null(instruction: &InsnNode, argument: usize) -> bool {
        match instruction.insn_type {
            InsnType::ArrayLength | InsnType::Aget => argument == 0,
            InsnType::Aput => argument == 1,
            InsnType::Iget => argument == 0,
            InsnType::Iput => argument == 1,
            InsnType::MonitorEnter | InsnType::MonitorExit | InsnType::Throw => argument == 0,
            InsnType::Invoke => {
                argument == 0 && instruction.payload.invoke_type != Some(InvokeType::Static)
            }
            _ => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ReturnFlowState {
    registers: Vec<ReturnOrigin>,
    pending_result: ReturnOrigin,
}

#[derive(Debug, Clone, Copy)]
enum NullnessFact {
    Null,
    NonNull,
}

/// Edge transfer for reference equality tests in the raw CFG.
///
/// The value analyses deliberately share this transfer so a branch fact is
/// preserved before return, constructor-field, and static-field proofs diverge.
struct NullnessEdgeTransfer {
    register: usize,
    when_true: NullnessFact,
    when_false: NullnessFact,
}

impl NullnessEdgeTransfer {
    fn analyze(terminator: &InsnNode) -> Option<Self> {
        if terminator.insn_type != InsnType::If {
            return None;
        }
        let register = match terminator.args.as_slice() {
            [InsnArg::Reg(register), InsnArg::Lit(literal)]
            | [InsnArg::Lit(literal), InsnArg::Reg(register)]
                if literal.value == 0 =>
            {
                register.reg_num as usize
            }
            _ => return None,
        };
        let (when_true, when_false) = match terminator.payload.if_op? {
            IfOp::Eq => (NullnessFact::Null, NullnessFact::NonNull),
            IfOp::Ne => (NullnessFact::NonNull, NullnessFact::Null),
            IfOp::Lt | IfOp::Ge | IfOp::Gt | IfOp::Le => return None,
        };
        Some(Self {
            register,
            when_true,
            when_false,
        })
    }

    fn apply(&self, edge: EdgeKind, state: &mut ReturnFlowState) -> bool {
        let fact = match edge {
            EdgeKind::True => self.when_true,
            EdgeKind::False => self.when_false,
            EdgeKind::Normal | EdgeKind::SwitchCase(_) | EdgeKind::SwitchDefault => return true,
            EdgeKind::Exception => return false,
        };
        let Some(origin) = state.registers.get_mut(self.register) else {
            return true;
        };

        // Null and Proven are reference-domain values. Unknown may also be an
        // integer, so refining it here would manufacture type information.
        match (fact, &*origin) {
            (NullnessFact::NonNull, ReturnOrigin::Null) => false,
            (NullnessFact::Null, ReturnOrigin::Proven(requirements)) if requirements.is_empty() => {
                false
            }
            (NullnessFact::NonNull, ReturnOrigin::Proven(_)) => {
                *origin = ReturnOrigin::Proven(Vec::new());
                true
            }
            (NullnessFact::Null, ReturnOrigin::Proven(_) | ReturnOrigin::Null) => {
                *origin = ReturnOrigin::Null;
                true
            }
            (_, ReturnOrigin::Unknown) => true,
        }
    }
}

struct MethodReturnNullability;

impl MethodReturnNullability {
    fn analyze(method: &MethodNode, cfg: &crate::ir::CFG, entry: BlockId) -> ReturnEvidence {
        let Some(state) = Self::entry_state(method, cfg) else {
            return ReturnEvidence::default();
        };
        let incoming = Self::solve(cfg, entry, state);
        let mut values = Vec::new();
        for block in cfg.blocks_iter() {
            let Some(mut state) = incoming.get(&block.id).cloned() else {
                continue;
            };
            for instruction in &block.insns {
                if instruction.insn_type == InsnType::Return {
                    if let Some(value) = instruction.args.first() {
                        values.push(Self::argument(value, &state.registers));
                    }
                }
                Self::transfer(instruction, &mut state);
            }
        }
        ReturnEvidence { values }
    }

    fn entry_state(method: &MethodNode, cfg: &CFG) -> Option<ReturnFlowState> {
        method.code()?;
        Some(Self::entry_state_from_cfg(cfg))
    }

    fn entry_state_from_cfg(cfg: &CFG) -> ReturnFlowState {
        let mut registers = vec![ReturnOrigin::Unknown; cfg.registers as usize];
        let mut register = (cfg.registers - cfg.ins) as usize;
        if !cfg.method().is_static() {
            if let Some(this) = registers.get_mut(register) {
                *this = ReturnOrigin::Proven(Vec::new());
            }
            register += 1;
        }
        for (parameter, ty) in cfg.method().descriptor().parameters.iter().enumerate() {
            if ty.is_reference() {
                if let Some(origin) = registers.get_mut(register) {
                    *origin = ReturnOrigin::Proven(vec![ReturnRequirement::Parameter(parameter)]);
                }
            }
            register += if ty.is_wide() { 2 } else { 1 };
        }
        ReturnFlowState {
            registers,
            pending_result: ReturnOrigin::Unknown,
        }
    }

    fn solve(
        cfg: &crate::ir::CFG,
        entry: BlockId,
        state: ReturnFlowState,
    ) -> BTreeMap<BlockId, ReturnFlowState> {
        let mut incoming = BTreeMap::from([(entry, state)]);
        let mut pending = VecDeque::from([entry]);
        while let Some(block_id) = pending.pop_front() {
            let Some(block) = cfg.block(block_id) else {
                continue;
            };
            let mut outgoing = incoming[&block_id].clone();
            for instruction in &block.insns {
                Self::transfer(instruction, &mut outgoing);
            }
            let nullness = block.terminator().and_then(NullnessEdgeTransfer::analyze);
            for &(successor, edge) in cfg.successors_with_kind(block_id) {
                if edge.is_exception() {
                    continue;
                }
                let mut successor_state = outgoing.clone();
                if nullness
                    .as_ref()
                    .is_some_and(|transfer| !transfer.apply(edge, &mut successor_state))
                {
                    continue;
                }
                let changed = match incoming.get_mut(&successor) {
                    None => {
                        incoming.insert(successor, successor_state);
                        true
                    }
                    Some(current) => Self::join(current, &successor_state),
                };
                if changed {
                    pending.push_back(successor);
                }
            }
        }
        incoming
    }

    fn join(current: &mut ReturnFlowState, incoming: &ReturnFlowState) -> bool {
        let mut changed = false;
        for (current, incoming) in current.registers.iter_mut().zip(&incoming.registers) {
            let joined = Self::join_origin(current, incoming);
            if *current != joined {
                *current = joined;
                changed = true;
            }
        }
        let pending = Self::join_origin(&current.pending_result, &incoming.pending_result);
        if current.pending_result != pending {
            current.pending_result = pending;
            changed = true;
        }
        changed
    }

    fn join_origin(current: &ReturnOrigin, incoming: &ReturnOrigin) -> ReturnOrigin {
        if current == incoming {
            return current.clone();
        }
        let (ReturnOrigin::Proven(current), ReturnOrigin::Proven(incoming)) = (current, incoming)
        else {
            return ReturnOrigin::Unknown;
        };
        let mut requirements = current.clone();
        for requirement in incoming {
            if !requirements.contains(requirement) {
                requirements.push(requirement.clone());
            }
        }
        ReturnOrigin::Proven(requirements)
    }

    fn transfer(instruction: &InsnNode, state: &mut ReturnFlowState) {
        let pending = std::mem::replace(&mut state.pending_result, ReturnOrigin::Unknown);
        let value = match instruction.insn_type {
            InsnType::Move => instruction
                .args
                .first()
                .map(|argument| Self::argument(argument, &state.registers))
                .unwrap_or(ReturnOrigin::Unknown),
            InsnType::MoveResult => pending,
            InsnType::Const => instruction
                .args
                .first()
                .and_then(|argument| argument.literal_value())
                .filter(|value| *value == 0)
                .map(|_| ReturnOrigin::Null)
                .unwrap_or(ReturnOrigin::Unknown),
            InsnType::ConstStr
            | InsnType::ConstClass
            | InsnType::NewInstance
            | InsnType::NewArray
            | InsnType::Constructor
            | InsnType::StringConcat
            | InsnType::MoveException => ReturnOrigin::Proven(Vec::new()),
            InsnType::Cast => instruction
                .args
                .first()
                .map(|argument| Self::argument(argument, &state.registers))
                .unwrap_or(ReturnOrigin::Unknown),
            InsnType::Iget | InsnType::Sget => instruction
                .payload
                .reference
                .as_ref()
                .and_then(|reference| match reference {
                    MemberReference::Field(field) if field.field_type.is_reference() => Some(
                        ReturnOrigin::Proven(vec![ReturnRequirement::Field(field.clone())]),
                    ),
                    _ => None,
                })
                .unwrap_or(ReturnOrigin::Unknown),
            _ => ReturnOrigin::Unknown,
        };
        if let Some(result) = &instruction.result {
            if let Some(target) = state.registers.get_mut(result.reg_num as usize) {
                *target = value;
            }
        }
        match instruction.insn_type {
            InsnType::Invoke => {
                state.pending_result = instruction
                    .payload
                    .reference
                    .as_ref()
                    .and_then(|reference| match reference {
                        MemberReference::Method(method) => Some(method.clone()),
                        MemberReference::Field(_) => None,
                    })
                    .filter(|method| method.descriptor.return_type.is_reference())
                    .map(|method| ReturnOrigin::Proven(vec![ReturnRequirement::Call(method)]))
                    .unwrap_or(ReturnOrigin::Unknown);
            }
            InsnType::FilledNewArray => state.pending_result = ReturnOrigin::Proven(Vec::new()),
            _ => {}
        }
    }

    fn argument(argument: &crate::ir::InsnArg, registers: &[ReturnOrigin]) -> ReturnOrigin {
        if let Some(register) = argument.reg_num() {
            return registers
                .get(register as usize)
                .cloned()
                .unwrap_or(ReturnOrigin::Unknown);
        }
        if argument.literal_value() == Some(0) {
            ReturnOrigin::Null
        } else {
            ReturnOrigin::Unknown
        }
    }
}

#[derive(Debug, Clone)]
struct FieldWriteEvidence {
    method: MethodReference,
    value: ReturnOrigin,
}

#[derive(Debug, Default)]
struct InstanceFieldEvidence {
    writes: BTreeMap<crate::ir::FieldReference, Vec<FieldWriteEvidence>>,
}

impl InstanceFieldEvidence {
    fn analyze(classes: &[&ClassNode], cfgs: &MethodCfgCatalog) -> Self {
        let mut evidence = Self::default();
        for class in classes {
            evidence.analyze_class(class, cfgs);
        }
        evidence.scan_writes(cfgs);
        evidence
    }

    fn analyze_class(&mut self, class: &ClassNode, cfgs: &MethodCfgCatalog) {
        let candidates = class
            .fields()
            .iter()
            .filter(|field| field.is_instance() && field.field_type().is_reference())
            .map(|field| crate::ir::FieldReference {
                owner: class.class_type().clone(),
                name: field.name().to_string(),
                field_type: field.field_type().clone(),
            })
            .collect::<BTreeSet<_>>();
        if candidates.is_empty() {
            return;
        }
        let constructors = class
            .constructors()
            .map(|method| (DexNullabilityContracts::reference(class, method), method))
            .collect::<Vec<_>>();
        if constructors.is_empty() {
            return;
        }

        let mut summaries =
            BTreeMap::<MethodReference, BTreeMap<crate::ir::FieldReference, ReturnOrigin>>::new();
        loop {
            let mut changed = false;
            for (reference, method) in &constructors {
                let Some(cfg) = cfgs.get(reference) else {
                    continue;
                };
                let summary = ConstructorFieldFlow::analyze(
                    method,
                    cfg,
                    class.class_type(),
                    &candidates,
                    &summaries,
                );
                if summaries.get(reference) != Some(&summary) {
                    summaries.insert(reference.clone(), summary);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        for field in &candidates {
            for (constructor, _) in &constructors {
                let value = summaries
                    .get(constructor)
                    .and_then(|summary| summary.get(field))
                    .cloned()
                    .unwrap_or(ReturnOrigin::Unknown);
                self.writes
                    .entry(field.clone())
                    .or_default()
                    .push(FieldWriteEvidence {
                        method: constructor.clone(),
                        value,
                    });
            }
        }
    }

    fn scan_writes(&mut self, cfgs: &MethodCfgCatalog) {
        for (reference, cfg) in &cfgs.methods {
            if reference.is_constructor() {
                continue;
            }
            let Some(entry) = cfg.entry_block().map(|block| block.id) else {
                continue;
            };
            let state = MethodReturnNullability::entry_state_from_cfg(cfg);
            let incoming = MethodReturnNullability::solve(cfg, entry, state);
            for block in cfg.blocks_iter() {
                let Some(mut state) = incoming.get(&block.id).cloned() else {
                    continue;
                };
                for instruction in &block.insns {
                    if instruction.insn_type == InsnType::Iput {
                        if let Some(field) = Self::field_reference(instruction)
                            .filter(|field| self.writes.contains_key(field))
                        {
                            let value = instruction
                                .args
                                .first()
                                .map(|value| {
                                    MethodReturnNullability::argument(value, &state.registers)
                                })
                                .unwrap_or(ReturnOrigin::Unknown);
                            self.writes
                                .entry(field)
                                .or_default()
                                .push(FieldWriteEvidence {
                                    method: reference.clone(),
                                    value,
                                });
                        }
                    }
                    MethodReturnNullability::transfer(instruction, &mut state);
                }
            }
        }
    }

    fn retain_proven(
        &self,
        fields: &mut BTreeSet<crate::ir::FieldReference>,
        parameters: &BTreeSet<ParameterId>,
        methods: &BTreeSet<MethodReference>,
        declared: &BTreeSet<crate::ir::FieldReference>,
    ) {
        let assumed = fields.clone();
        fields.retain(|field| {
            declared.contains(field)
                || self.writes.get(field).is_some_and(|writes| {
                    !writes.is_empty()
                        && writes.iter().all(|write| {
                            Self::origin_is_non_null(
                                &write.value,
                                &write.method,
                                parameters,
                                methods,
                                &assumed,
                            )
                        })
                })
        });
    }

    fn origin_is_non_null(
        origin: &ReturnOrigin,
        method: &MethodReference,
        parameters: &BTreeSet<ParameterId>,
        methods: &BTreeSet<MethodReference>,
        fields: &BTreeSet<crate::ir::FieldReference>,
    ) -> bool {
        let ReturnOrigin::Proven(requirements) = origin else {
            return false;
        };
        requirements.iter().all(|requirement| match requirement {
            ReturnRequirement::Parameter(parameter) => parameters.contains(&ParameterId {
                method: method.clone(),
                parameter: *parameter,
            }),
            ReturnRequirement::Call(method) => methods.contains(method),
            ReturnRequirement::Field(field) => fields.contains(field),
        })
    }

    fn field_reference(instruction: &InsnNode) -> Option<crate::ir::FieldReference> {
        match instruction.payload.reference.as_ref()? {
            MemberReference::Field(field) => Some(field.clone()),
            MemberReference::Method(_) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ConstructorFieldState {
    values: ReturnFlowState,
    this_aliases: Vec<bool>,
    fields: BTreeMap<crate::ir::FieldReference, Option<ReturnOrigin>>,
}

struct ConstructorFieldFlow;

impl ConstructorFieldFlow {
    fn analyze(
        method: &MethodNode,
        cfg: &CFG,
        owner: &crate::ir::ArgType,
        candidates: &BTreeSet<crate::ir::FieldReference>,
        summaries: &BTreeMap<MethodReference, BTreeMap<crate::ir::FieldReference, ReturnOrigin>>,
    ) -> BTreeMap<crate::ir::FieldReference, ReturnOrigin> {
        if !cfg.handlers.is_empty() {
            return BTreeMap::new();
        }
        let Some(entry) = cfg.entry_block().map(|block| block.id) else {
            return BTreeMap::new();
        };
        let Some(values) = MethodReturnNullability::entry_state(method, cfg) else {
            return BTreeMap::new();
        };
        let mut this_aliases = vec![false; cfg.registers as usize];
        let this_register = method.code().map(|code| code.args_start_reg());
        if let Some(alias) =
            this_register.and_then(|register| this_aliases.get_mut(register as usize))
        {
            *alias = true;
        }
        let initial = ConstructorFieldState {
            values,
            this_aliases,
            fields: candidates
                .iter()
                .cloned()
                .map(|field| (field, None))
                .collect(),
        };
        let incoming = Self::solve(cfg, entry, initial, owner, candidates, summaries);
        let mut exits = cfg.blocks_iter().filter_map(|block| {
            let mut state = incoming.get(&block.id)?.clone();
            let mut returns = false;
            for instruction in &block.insns {
                returns |= instruction.insn_type == InsnType::Return;
                Self::transfer(instruction, &mut state, owner, candidates, summaries);
            }
            returns.then_some(state.fields)
        });
        let Some(mut result) = exits.next() else {
            return BTreeMap::new();
        };
        for incoming in exits {
            Self::join_fields(&mut result, &incoming);
        }
        result
            .into_iter()
            .filter_map(|(field, value)| value.map(|value| (field, value)))
            .collect()
    }

    fn solve(
        cfg: &CFG,
        entry: BlockId,
        state: ConstructorFieldState,
        owner: &crate::ir::ArgType,
        candidates: &BTreeSet<crate::ir::FieldReference>,
        summaries: &BTreeMap<MethodReference, BTreeMap<crate::ir::FieldReference, ReturnOrigin>>,
    ) -> BTreeMap<BlockId, ConstructorFieldState> {
        let mut incoming = BTreeMap::from([(entry, state)]);
        let mut pending = VecDeque::from([entry]);
        while let Some(block_id) = pending.pop_front() {
            let Some(block) = cfg.block(block_id) else {
                continue;
            };
            let mut outgoing = incoming[&block_id].clone();
            for instruction in &block.insns {
                Self::transfer(instruction, &mut outgoing, owner, candidates, summaries);
            }
            let nullness = block.terminator().and_then(NullnessEdgeTransfer::analyze);
            for &(successor, edge) in cfg.successors_with_kind(block_id) {
                if edge.is_exception() {
                    continue;
                }
                let mut successor_state = outgoing.clone();
                if nullness
                    .as_ref()
                    .is_some_and(|transfer| !transfer.apply(edge, &mut successor_state.values))
                {
                    continue;
                }
                let changed = match incoming.get_mut(&successor) {
                    None => {
                        incoming.insert(successor, successor_state);
                        true
                    }
                    Some(current) => Self::join(current, &successor_state),
                };
                if changed {
                    pending.push_back(successor);
                }
            }
        }
        incoming
    }

    fn transfer(
        instruction: &InsnNode,
        state: &mut ConstructorFieldState,
        owner: &crate::ir::ArgType,
        candidates: &BTreeSet<crate::ir::FieldReference>,
        summaries: &BTreeMap<MethodReference, BTreeMap<crate::ir::FieldReference, ReturnOrigin>>,
    ) {
        if instruction.insn_type == InsnType::Iput
            && instruction
                .args
                .get(1)
                .and_then(|argument| argument.reg_num())
                .and_then(|register| state.this_aliases.get(register as usize))
                .copied()
                .unwrap_or(false)
        {
            if let Some(field) = InstanceFieldEvidence::field_reference(instruction)
                .filter(|field| candidates.contains(field))
            {
                let value = instruction
                    .args
                    .first()
                    .map(|value| MethodReturnNullability::argument(value, &state.values.registers))
                    .unwrap_or(ReturnOrigin::Unknown);
                state.fields.insert(field, Some(value));
            }
        }
        if let Some(MemberReference::Method(target)) = instruction.payload.reference.as_ref() {
            let receiver_is_this = instruction
                .args
                .first()
                .and_then(|argument| argument.reg_num())
                .and_then(|register| state.this_aliases.get(register as usize))
                .copied()
                .unwrap_or(false);
            if instruction.insn_type == InsnType::Invoke
                && instruction.payload.invoke_type == Some(InvokeType::Direct)
                && target.is_constructor()
                && &target.owner == owner
                && receiver_is_this
            {
                if let Some(summary) = summaries.get(target) {
                    for (field, value) in summary {
                        state.fields.insert(
                            field.clone(),
                            Some(Self::instantiate(value, target, instruction, &state.values)),
                        );
                    }
                }
            }
        }

        let alias = if instruction.insn_type == InsnType::Move {
            instruction
                .args
                .first()
                .and_then(|argument| argument.reg_num())
                .and_then(|register| state.this_aliases.get(register as usize))
                .copied()
                .unwrap_or(false)
        } else {
            false
        };
        if let Some(result) = &instruction.result {
            if let Some(target) = state.this_aliases.get_mut(result.reg_num as usize) {
                *target = alias;
            }
        }
        MethodReturnNullability::transfer(instruction, &mut state.values);
    }

    fn instantiate(
        origin: &ReturnOrigin,
        target: &MethodReference,
        invocation: &InsnNode,
        caller: &ReturnFlowState,
    ) -> ReturnOrigin {
        let ReturnOrigin::Proven(requirements) = origin else {
            return origin.clone();
        };
        let mut instantiated = Vec::new();
        for requirement in requirements {
            match requirement {
                ReturnRequirement::Parameter(parameter) => {
                    let Some(argument) = Self::invocation_argument(target, invocation, *parameter)
                    else {
                        return ReturnOrigin::Unknown;
                    };
                    let ReturnOrigin::Proven(arguments) =
                        MethodReturnNullability::argument(argument, &caller.registers)
                    else {
                        return ReturnOrigin::Unknown;
                    };
                    for argument in arguments {
                        if !instantiated.contains(&argument) {
                            instantiated.push(argument);
                        }
                    }
                }
                requirement => {
                    if !instantiated.contains(requirement) {
                        instantiated.push(requirement.clone());
                    }
                }
            }
        }
        ReturnOrigin::Proven(instantiated)
    }

    fn invocation_argument<'a>(
        target: &MethodReference,
        invocation: &'a InsnNode,
        parameter: usize,
    ) -> Option<&'a crate::ir::InsnArg> {
        let mut cursor = 1usize;
        for (index, ty) in target.descriptor.parameters.iter().enumerate() {
            if index == parameter {
                return invocation.args.get(cursor);
            }
            cursor += if ty.is_wide() { 2 } else { 1 };
        }
        None
    }

    fn join(current: &mut ConstructorFieldState, incoming: &ConstructorFieldState) -> bool {
        let mut changed = MethodReturnNullability::join(&mut current.values, &incoming.values);
        for (current, incoming) in current.this_aliases.iter_mut().zip(&incoming.this_aliases) {
            let joined = *current && *incoming;
            changed |= *current != joined;
            *current = joined;
        }
        changed | Self::join_fields(&mut current.fields, &incoming.fields)
    }

    fn join_fields(
        current: &mut BTreeMap<crate::ir::FieldReference, Option<ReturnOrigin>>,
        incoming: &BTreeMap<crate::ir::FieldReference, Option<ReturnOrigin>>,
    ) -> bool {
        let mut changed = false;
        for (field, current) in current {
            let joined = match (
                current.as_ref(),
                incoming.get(field).and_then(Option::as_ref),
            ) {
                (Some(current), Some(incoming)) => {
                    Some(MethodReturnNullability::join_origin(current, incoming))
                }
                _ => None,
            };
            changed |= *current != joined;
            *current = joined;
        }
        changed
    }
}

/// Proves non-null static final fields from their class-initializer data flow.
///
/// A field is accepted only when every reachable normal return has observed a
/// definitely non-null write. The join is intersection, so a missing or
/// unknown write on any predecessor invalidates the proof.
struct StaticFieldNullability;

impl StaticFieldNullability {
    fn analyze(
        classes: &[&ClassNode],
        cfgs: &MethodCfgCatalog,
    ) -> BTreeSet<crate::ir::FieldReference> {
        classes
            .iter()
            .flat_map(|class| {
                let candidates = class
                    .fields()
                    .iter()
                    .filter(|field| {
                        field.is_static() && field.is_final() && field.field_type().is_reference()
                    })
                    .map(|field| crate::ir::FieldReference {
                        owner: class.class_type().clone(),
                        name: field.name().to_string(),
                        field_type: field.field_type().clone(),
                    })
                    .collect::<BTreeSet<_>>();
                class
                    .methods()
                    .iter()
                    .find(|method| method.is_class_init())
                    .and_then(|method| {
                        let reference = DexNullabilityContracts::reference(class, method);
                        cfgs.get(&reference)
                            .map(|cfg| Self::class_initializer(cfg, candidates))
                    })
                    .unwrap_or_default()
            })
            .collect()
    }

    fn class_initializer(
        cfg: &CFG,
        candidates: BTreeSet<crate::ir::FieldReference>,
    ) -> BTreeSet<crate::ir::FieldReference> {
        if candidates.is_empty() {
            return BTreeSet::new();
        }
        if !cfg.handlers.is_empty() {
            return BTreeSet::new();
        }
        let Some(entry) = cfg.entry_block().map(|block| block.id) else {
            return BTreeSet::new();
        };
        let initial = StaticFieldState {
            values: ReturnFlowState {
                registers: vec![ReturnOrigin::Unknown; cfg.registers as usize],
                pending_result: ReturnOrigin::Unknown,
            },
            initialized: candidates
                .iter()
                .cloned()
                .map(|field| (field, false))
                .collect(),
        };
        let incoming = Self::solve(cfg, entry, initial, &candidates);
        let exits = cfg
            .blocks_iter()
            .filter_map(|block| {
                let mut state = incoming.get(&block.id)?.clone();
                let mut returns = false;
                for instruction in &block.insns {
                    if instruction.insn_type == InsnType::Return {
                        returns = true;
                    }
                    Self::transfer(instruction, &mut state, &candidates);
                }
                returns.then_some(state.initialized)
            })
            .collect::<Vec<_>>();
        if exits.is_empty() {
            return BTreeSet::new();
        }
        candidates
            .into_iter()
            .filter(|field| {
                exits
                    .iter()
                    .all(|state| state.get(field).copied().unwrap_or(false))
            })
            .collect()
    }

    fn solve(
        cfg: &crate::ir::CFG,
        entry: BlockId,
        state: StaticFieldState,
        candidates: &BTreeSet<crate::ir::FieldReference>,
    ) -> BTreeMap<BlockId, StaticFieldState> {
        let mut incoming = BTreeMap::from([(entry, state)]);
        let mut pending = VecDeque::from([entry]);
        let mut queued = BTreeSet::from([entry]);
        while let Some(block_id) = pending.pop_front() {
            queued.remove(&block_id);
            let Some(block) = cfg.block(block_id) else {
                continue;
            };
            let mut outgoing = incoming[&block_id].clone();
            for instruction in &block.insns {
                Self::transfer(instruction, &mut outgoing, candidates);
            }
            let nullness = block.terminator().and_then(NullnessEdgeTransfer::analyze);
            for &(successor, edge) in cfg.successors_with_kind(block_id) {
                if edge.is_exception() {
                    continue;
                }
                let mut successor_state = outgoing.clone();
                if nullness
                    .as_ref()
                    .is_some_and(|transfer| !transfer.apply(edge, &mut successor_state.values))
                {
                    continue;
                }
                let changed = match incoming.get_mut(&successor) {
                    None => {
                        incoming.insert(successor, successor_state);
                        true
                    }
                    Some(current) => Self::join(current, &successor_state),
                };
                if changed && queued.insert(successor) {
                    pending.push_back(successor);
                }
            }
        }
        incoming
    }

    fn transfer(
        instruction: &InsnNode,
        state: &mut StaticFieldState,
        candidates: &BTreeSet<crate::ir::FieldReference>,
    ) {
        if instruction.insn_type == InsnType::Sput {
            if let Some(field) = instruction
                .payload
                .reference
                .as_ref()
                .and_then(|reference| match reference {
                    MemberReference::Field(field) => Some(field.clone()),
                    MemberReference::Method(_) => None,
                })
                .filter(|field| candidates.contains(field))
            {
                let non_null = instruction
                    .args
                    .first()
                    .map(|value| {
                        MethodReturnNullability::argument(value, &state.values.registers)
                    })
                    .is_some_and(|origin| {
                        matches!(origin, ReturnOrigin::Proven(requirements) if requirements.is_empty())
                    });
                state.initialized.insert(field, non_null);
            }
        }
        MethodReturnNullability::transfer(instruction, &mut state.values);
    }

    fn join(current: &mut StaticFieldState, incoming: &StaticFieldState) -> bool {
        let mut changed = MethodReturnNullability::join(&mut current.values, &incoming.values);
        for (field, initialized) in &mut current.initialized {
            let joined = *initialized && incoming.initialized.get(field).copied().unwrap_or(false);
            if *initialized != joined {
                *initialized = joined;
                changed = true;
            }
        }
        changed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct StaticFieldState {
    values: ReturnFlowState,
    initialized: BTreeMap<crate::ir::FieldReference, bool>,
}
