use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::ir::analysis::{SubtypeRelation, TypeHierarchy};
use crate::ir::{
    ArgType, BlockId, InsnArg, InsnNode, InsnType, InvokeType, MemberReference, MethodReference,
    CFG,
};

use crate::analysis::{ClassMethodInput, NestedClassInput};

#[derive(Debug, Clone)]
enum TypeConstraint {
    Unseen,
    Exact(ArgType),
    Conflict,
}

/// Recovers source-level method signatures erased by DEX lowering. Parameter
/// evidence comes from represented call sites; return evidence comes from
/// every normal return in the method CFG.
pub(crate) struct SourceSignatureInference<'a> {
    hierarchy: &'a dyn TypeHierarchy,
    parameters: BTreeMap<MethodReference, Vec<TypeConstraint>>,
    body_parameters: BTreeMap<MethodReference, Vec<TypeConstraint>>,
    returns: BTreeMap<MethodReference, TypeConstraint>,
}

impl<'a> SourceSignatureInference<'a> {
    pub(crate) fn analyze(
        hierarchy: &'a dyn TypeHierarchy,
        methods: &[ClassMethodInput],
        nested: &[NestedClassInput],
    ) -> Self {
        let mut analysis = Self {
            hierarchy,
            parameters: BTreeMap::new(),
            body_parameters: BTreeMap::new(),
            returns: BTreeMap::new(),
        };
        analysis.cfgs(methods);
        for input in nested {
            analysis.nested(input);
        }
        analysis
    }

    pub(crate) fn parameter_types(&self, method: &MethodReference) -> Vec<Option<ArgType>> {
        self.parameters
            .get(method)
            .map(|constraints| {
                constraints
                    .iter()
                    .map(|constraint| match constraint {
                        TypeConstraint::Exact(ty) => Some(ty.clone()),
                        TypeConstraint::Unseen | TypeConstraint::Conflict => None,
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    pub(crate) fn return_type(&self, method: &MethodReference) -> Option<ArgType> {
        match self.returns.get(method) {
            Some(TypeConstraint::Exact(ty)) => Some(ty.clone()),
            Some(TypeConstraint::Unseen | TypeConstraint::Conflict) | None => None,
        }
    }

    pub(crate) fn body_parameter_types(&self, method: &MethodReference) -> Vec<Option<ArgType>> {
        self.body_parameters
            .get(method)
            .map(|constraints| {
                constraints
                    .iter()
                    .map(|constraint| match constraint {
                        TypeConstraint::Exact(ty) => Some(ty.clone()),
                        TypeConstraint::Unseen | TypeConstraint::Conflict => None,
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    fn nested(&mut self, input: &NestedClassInput) {
        self.cfgs(&input.methods);
        for nested in &input.nested {
            self.nested(nested);
        }
    }

    fn cfgs(&mut self, methods: &[ClassMethodInput]) {
        for cfg in methods.iter().filter_map(ClassMethodInput::cfg) {
            self.cfg(cfg);
        }
    }

    fn cfg(&mut self, cfg: &CFG) {
        let incoming = ReachingCastTypes::analyze(cfg);
        let current_method = MethodReference {
            owner: cfg.method().owner().clone(),
            name: cfg.method().name().to_string(),
            descriptor: cfg.method().descriptor().clone(),
        };
        let parameter_registers = Self::parameter_registers(cfg);
        for (block_id, block) in &cfg.blocks {
            let Some(mut types) = incoming.get(block_id).cloned() else {
                continue;
            };
            let mut pending_result = None;
            for instruction in &block.insns {
                if instruction.insn_type == InsnType::CheckCast {
                    if let (Some(register), Some(actual)) = (
                        instruction.args.first().and_then(InsnArg::as_register),
                        instruction.conversion_type(),
                    ) {
                        if let Some(index) = parameter_registers.get(&register.reg_num).copied() {
                            let constraints = self
                                .body_parameters
                                .entry(current_method.clone())
                                .or_insert_with(|| {
                                    vec![
                                        TypeConstraint::Unseen;
                                        current_method.descriptor.parameters.len()
                                    ]
                                });
                            if let (Some(constraint), Some(erased)) = (
                                constraints.get_mut(index),
                                current_method.descriptor.parameters.get(index),
                            ) {
                                *constraint =
                                    Self::join(self.hierarchy, constraint, Some(actual), erased);
                            }
                        }
                    }
                }
                if instruction.insn_type == InsnType::Return {
                    let actual = instruction
                        .args
                        .first()
                        .and_then(|argument| ReachingCastTypes::argument_type(argument, &types));
                    let current = self
                        .returns
                        .entry(current_method.clone())
                        .or_insert(TypeConstraint::Unseen);
                    *current = Self::join(
                        self.hierarchy,
                        current,
                        actual,
                        &current_method.descriptor.return_type,
                    );
                }

                if instruction.insn_type == InsnType::Invoke {
                    if let Some(MemberReference::Method(method)) =
                        instruction.payload.reference.as_ref()
                    {
                        let skip_receiver = usize::from(
                            instruction.payload.invoke_type != Some(InvokeType::Static),
                        );
                        let arguments = instruction.args.iter().skip(skip_receiver);
                        let hierarchy = self.hierarchy;
                        let constraints =
                            self.parameters.entry(method.clone()).or_insert_with(|| {
                                vec![TypeConstraint::Unseen; method.descriptor.parameters.len()]
                            });
                        for ((constraint, expected), argument) in constraints
                            .iter_mut()
                            .zip(&method.descriptor.parameters)
                            .zip(arguments)
                        {
                            let actual = ReachingCastTypes::argument_type(argument, &types);
                            *constraint = Self::join(hierarchy, constraint, actual, expected);
                        }
                    }
                }
                ReachingCastTypes::transfer(instruction, &mut types, &mut pending_result);
            }
        }
    }

    fn parameter_registers(cfg: &CFG) -> BTreeMap<u32, usize> {
        let mut register = cfg.registers.saturating_sub(cfg.ins);
        if !cfg.method().is_static() {
            register = register.saturating_add(1);
        }
        let mut result = BTreeMap::new();
        for (index, ty) in cfg.method().descriptor().parameters.iter().enumerate() {
            result.insert(register, index);
            register = register.saturating_add(if ty.is_wide() { 2 } else { 1 });
        }
        result
    }

    fn join(
        hierarchy: &dyn TypeHierarchy,
        current: &TypeConstraint,
        actual: Option<&ArgType>,
        erased: &ArgType,
    ) -> TypeConstraint {
        let Some(actual) = actual.filter(|actual| Self::refines(hierarchy, actual, erased)) else {
            return TypeConstraint::Conflict;
        };
        match current {
            TypeConstraint::Unseen => TypeConstraint::Exact(actual.clone()),
            TypeConstraint::Exact(current) if current == actual => {
                TypeConstraint::Exact(current.clone())
            }
            TypeConstraint::Exact(current) => Self::common_type(hierarchy, current, actual)
                .filter(|common| Self::refines(hierarchy, common, erased))
                .map(TypeConstraint::Exact)
                .unwrap_or(TypeConstraint::Conflict),
            TypeConstraint::Conflict => TypeConstraint::Conflict,
        }
    }

    fn refines(hierarchy: &dyn TypeHierarchy, actual: &ArgType, erased: &ArgType) -> bool {
        if actual == erased || !actual.is_reference() || !erased.is_reference() {
            return false;
        }
        match (actual, erased) {
            (_, ArgType::Object(expected)) if expected == "java/lang/Object" => true,
            (ArgType::Object(actual), ArgType::Object(expected)) => {
                hierarchy.subtype_relation(actual, expected) == SubtypeRelation::Yes
            }
            (ArgType::Array(_), ArgType::Object(expected)) => expected == "java/lang/Object",
            _ => false,
        }
    }

    fn common_type(
        hierarchy: &dyn TypeHierarchy,
        left: &ArgType,
        right: &ArgType,
    ) -> Option<ArgType> {
        match (left, right) {
            (ArgType::Object(left), ArgType::Object(right)) => hierarchy
                .least_common_supertype(left, right)
                .map(|name| ArgType::object(&name)),
            (left, right) if left == right => Some(left.clone()),
            _ => None,
        }
    }
}

type RegisterTypes = BTreeMap<u32, ArgType>;

struct ReachingCastTypes;

impl ReachingCastTypes {
    fn analyze(cfg: &CFG) -> BTreeMap<BlockId, RegisterTypes> {
        let mut incoming = BTreeMap::from([(cfg.entry, RegisterTypes::new())]);
        let mut pending = VecDeque::from([cfg.entry]);
        let mut queued = BTreeSet::from([cfg.entry]);
        while let Some(block) = pending.pop_front() {
            queued.remove(&block);
            let Some(mut outgoing) = incoming.get(&block).cloned() else {
                continue;
            };
            if let Some(body) = cfg.block(block) {
                let mut pending_result = None;
                for instruction in &body.insns {
                    Self::transfer(instruction, &mut outgoing, &mut pending_result);
                }
            }
            for successor in cfg.normal_successors(block) {
                let changed = match incoming.get_mut(&successor) {
                    Some(current) => Self::intersect(current, &outgoing),
                    None => {
                        incoming.insert(successor, outgoing.clone());
                        true
                    }
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
        types: &mut RegisterTypes,
        pending_result: &mut Option<ArgType>,
    ) {
        if instruction.insn_type == InsnType::Invoke {
            *pending_result = match instruction.payload.reference.as_ref() {
                Some(MemberReference::Method(method))
                    if method.descriptor.return_type != ArgType::VOID =>
                {
                    Some(method.descriptor.return_type.clone())
                }
                _ => None,
            };
            return;
        }
        if instruction.insn_type == InsnType::FilledNewArray {
            *pending_result = instruction.payload.class_type.clone();
            return;
        }
        if instruction.insn_type == InsnType::MoveResult {
            let Some(result) = instruction.result.as_ref() else {
                pending_result.take();
                return;
            };
            let ty = pending_result
                .take()
                .or_else(|| result.ty.is_known().then(|| result.ty.clone()));
            match ty {
                Some(ty) => {
                    types.insert(result.reg_num, ty);
                }
                None => {
                    types.remove(&result.reg_num);
                }
            }
            return;
        }
        pending_result.take();
        if instruction.insn_type == InsnType::CheckCast {
            if let (Some(register), Some(ty)) = (
                instruction.args.first().and_then(InsnArg::as_register),
                instruction.conversion_type(),
            ) {
                types.insert(register.reg_num, ty.clone());
            }
            return;
        }
        let Some(result) = instruction.result.as_ref() else {
            return;
        };
        let ty = if instruction.insn_type == InsnType::Move {
            instruction
                .args
                .first()
                .and_then(|argument| Self::argument_type(argument, types))
                .cloned()
        } else {
            result.ty.is_known().then(|| result.ty.clone())
        };
        match ty {
            Some(ty) => {
                types.insert(result.reg_num, ty);
            }
            None => {
                types.remove(&result.reg_num);
            }
        }
    }

    fn argument_type<'a>(argument: &'a InsnArg, types: &'a RegisterTypes) -> Option<&'a ArgType> {
        argument
            .as_register()
            .and_then(|register| types.get(&register.reg_num))
            .or_else(|| argument.declared_type().filter(|ty| ty.is_known()))
    }

    fn intersect(current: &mut RegisterTypes, incoming: &RegisterTypes) -> bool {
        let before = current.len();
        current.retain(|register, ty| incoming.get(register) == Some(ty));
        current.len() != before
    }
}
