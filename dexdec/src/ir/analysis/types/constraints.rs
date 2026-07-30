use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    analysis::{SsaClasses, SsaValueGraph, SsaVar},
    ArgType, ArithOp, IfOp, InsnArg, InsnNode, InsnType, InstructionTree, InstructionVisitor,
    InvokeType, MemberReference, RegisterArg, CFG,
};

use super::TypeConstraintError;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum BoundKind {
    Domain,
    Fallback,
    Upper,
    Lower,
    Exact,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct TypeBound {
    pub(super) kind: BoundKind,
    pub(super) ty: ArgType,
}

impl TypeBound {
    pub(super) fn new(kind: BoundKind, ty: ArgType) -> Self {
        Self { kind, ty }
    }
}

pub(super) struct TypeConstraintGraph {
    classes: SsaClasses,
    values: BTreeSet<SsaVar>,
    bounds: BTreeMap<SsaVar, BTreeSet<TypeBound>>,
    flows: BTreeSet<(SsaVar, SsaVar)>,
    upper_flows: BTreeSet<(SsaVar, SsaVar)>,
    arrays: BTreeSet<ArrayConstraint>,
}

pub(super) struct NormalizedTypeConstraints {
    pub(super) members: BTreeMap<SsaVar, BTreeSet<SsaVar>>,
    pub(super) bounds: BTreeMap<SsaVar, BTreeSet<TypeBound>>,
    pub(super) flows: BTreeSet<(SsaVar, SsaVar)>,
    pub(super) upper_flows: BTreeSet<(SsaVar, SsaVar)>,
    pub(super) arrays: BTreeSet<ArrayConstraint>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum ArrayConstraint {
    Read { array: SsaVar, result: SsaVar },
    Write { array: SsaVar, value: SsaVar },
}

impl TypeConstraintGraph {
    pub(super) fn collect(
        cfg: &CFG,
        values: &SsaValueGraph,
        constants: &BTreeMap<SsaVar, InsnArg>,
    ) -> Result<Self, TypeConstraintError> {
        let all_values = values
            .values()
            .map(|value| value.variable)
            .collect::<BTreeSet<_>>();
        let mut graph = Self {
            classes: SsaClasses::new(all_values.iter().copied()),
            values: all_values,
            bounds: BTreeMap::new(),
            flows: BTreeSet::new(),
            upper_flows: BTreeSet::new(),
            arrays: BTreeSet::new(),
        };
        for copy in values.copies() {
            if !constants.contains_key(&copy.source) {
                graph.classes.union(copy.result, copy.source);
            }
        }
        for (&value, constant) in constants {
            if let Some(ty) = Self::constant_fallback(constant) {
                graph.add_value_bound(value, BoundKind::Fallback, ty);
            }
        }
        for phi in values.phis() {
            for input in &phi.inputs {
                if let Some(ty) = constants
                    .get(&input.value)
                    .and_then(Self::constant_fallback)
                {
                    graph.add_value_bound(phi.result, BoundKind::Fallback, ty);
                    graph.upper_flows.insert((input.value, phi.result));
                } else {
                    graph.flows.insert((input.value, phi.result));
                }
            }
        }
        graph.collect_method_inputs(cfg)?;
        for block in cfg.blocks.values() {
            for instruction in &block.insns {
                graph.constrain_instruction(instruction, cfg)?;
            }
        }
        Ok(graph)
    }

    pub(super) fn normalize(mut self) -> NormalizedTypeConstraints {
        let mut roots = BTreeMap::new();
        let mut members = BTreeMap::<SsaVar, BTreeSet<SsaVar>>::new();
        for value in self.values {
            let root = self.classes.root(value);
            roots.insert(value, root);
            members.entry(root).or_default().insert(value);
        }
        let mut bounds = BTreeMap::<SsaVar, BTreeSet<TypeBound>>::new();
        for (value, value_bounds) in self.bounds {
            let root = roots.get(&value).copied().unwrap_or(value);
            bounds.entry(root).or_default().extend(value_bounds);
            members.entry(root).or_default().insert(value);
        }
        let flows = self
            .flows
            .into_iter()
            .filter_map(|(source, target)| {
                let source = roots.get(&source).copied().unwrap_or(source);
                let target = roots.get(&target).copied().unwrap_or(target);
                (source != target).then_some((source, target))
            })
            .collect();
        let upper_flows = self
            .upper_flows
            .into_iter()
            .filter_map(|(source, target)| {
                let source = roots.get(&source).copied().unwrap_or(source);
                let target = roots.get(&target).copied().unwrap_or(target);
                (source != target).then_some((source, target))
            })
            .collect();
        let arrays = self
            .arrays
            .into_iter()
            .map(|constraint| match constraint {
                ArrayConstraint::Read { array, result } => ArrayConstraint::Read {
                    array: roots.get(&array).copied().unwrap_or(array),
                    result: roots.get(&result).copied().unwrap_or(result),
                },
                ArrayConstraint::Write { array, value } => ArrayConstraint::Write {
                    array: roots.get(&array).copied().unwrap_or(array),
                    value: roots.get(&value).copied().unwrap_or(value),
                },
            })
            .collect();
        NormalizedTypeConstraints {
            members,
            bounds,
            flows,
            upper_flows,
            arrays,
        }
    }

    fn collect_method_inputs(&mut self, cfg: &CFG) -> Result<(), TypeConstraintError> {
        let mut register = cfg.registers.saturating_sub(cfg.ins);
        if !cfg.method().is_static() {
            self.add_value_bound(
                SsaVar::new(register, 0),
                BoundKind::Exact,
                cfg.method().owner().clone(),
            );
            register += 1;
        }
        for ty in &cfg.method().descriptor().parameters {
            self.add_value_bound(SsaVar::new(register, 0), BoundKind::Exact, ty.clone());
            register += if ty.is_wide() { 2 } else { 1 };
        }
        Ok(())
    }

    fn constrain_instruction(
        &mut self,
        instruction: &InsnNode,
        cfg: &CFG,
    ) -> Result<(), TypeConstraintError> {
        if let Some(result) = &instruction.result {
            self.observe_register_type(result);
        }
        self.observe_arguments(instruction);

        match instruction.insn_type {
            InsnType::Invoke | InsnType::Constructor => self.constrain_invoke(instruction)?,
            InsnType::Iget | InsnType::Iput | InsnType::Sget | InsnType::Sput => {
                self.constrain_field(instruction)?
            }
            InsnType::Return => {
                if let Some(value) = instruction.args.first() {
                    let ty = cfg.method().descriptor().return_type.clone();
                    let kind = if ty.is_primitive() {
                        BoundKind::Exact
                    } else {
                        BoundKind::Upper
                    };
                    self.add_argument_bound(value, kind, ty);
                }
            }
            InsnType::Throw => {
                if let Some(value) = instruction.args.first() {
                    self.add_argument_bound(value, BoundKind::Upper, ArgType::throwable());
                }
            }
            InsnType::CheckCast | InsnType::Cast => {
                if let (Some(result), Some(ty)) =
                    (&instruction.result, instruction.conversion_type())
                {
                    self.add_register_bound(result, BoundKind::Exact, ty.clone());
                }
                if instruction.insn_type == InsnType::CheckCast {
                    if let Some(value) = instruction.args.first() {
                        self.add_argument_bound(value, BoundKind::Upper, ArgType::unknown_object());
                    }
                }
            }
            InsnType::MoveException => {
                if let Some(result) = &instruction.result {
                    self.add_register_bound(result, BoundKind::Upper, ArgType::throwable());
                }
            }
            InsnType::NewInstance => {
                if let (Some(result), Some(ty)) =
                    (&instruction.result, instruction.payload.class_type.as_ref())
                {
                    self.add_register_bound(result, BoundKind::Exact, ty.clone());
                }
            }
            InsnType::ConstClass => {
                if let Some(result) = &instruction.result {
                    self.add_register_bound(
                        result,
                        BoundKind::Exact,
                        ArgType::object("java/lang/Class"),
                    );
                }
            }
            InsnType::InstanceOf => {
                if let Some(result) = &instruction.result {
                    self.add_register_bound(result, BoundKind::Exact, ArgType::BOOLEAN);
                }
                if let Some(value) = instruction.args.first() {
                    self.add_argument_bound(value, BoundKind::Upper, ArgType::unknown_object());
                }
            }
            InsnType::ArrayLength => {
                if let Some(result) = &instruction.result {
                    self.add_register_bound(result, BoundKind::Exact, ArgType::INT);
                }
                if let Some(array) = instruction.args.first() {
                    self.add_argument_bound(array, BoundKind::Upper, ArgType::unknown_object());
                }
            }
            InsnType::Aget => self.constrain_array_get(instruction),
            InsnType::Aput => self.constrain_array_put(instruction),
            InsnType::NewArray | InsnType::FilledNewArray => {
                if let Some(result) = &instruction.result {
                    if let Some(array_type) = instruction.payload.class_type.as_ref() {
                        self.add_register_bound(result, BoundKind::Exact, array_type.clone());
                    }
                }
                if instruction.insn_type == InsnType::NewArray {
                    if let Some(size) = instruction.args.first() {
                        self.add_argument_bound(size, BoundKind::Upper, ArgType::INT);
                    }
                } else if let Some(array) = instruction.result.as_ref().and_then(SsaVar::from_reg) {
                    for value in &instruction.args {
                        if let Some(value) = Self::argument_value(value) {
                            self.arrays.insert(ArrayConstraint::Write { array, value });
                        }
                    }
                }
            }
            InsnType::Cmp => {
                if let Some(result) = &instruction.result {
                    self.add_register_bound(result, BoundKind::Exact, ArgType::INT);
                }
                self.constrain_peer_arguments(instruction);
            }
            InsnType::If => self.constrain_peer_arguments(instruction),
            InsnType::Switch => {
                if let Some(selector) = instruction.args.first() {
                    self.add_argument_bound(selector, BoundKind::Upper, ArgType::INT);
                }
            }
            InsnType::Arith | InsnType::CompoundAssign => self.constrain_arithmetic(instruction),
            InsnType::Neg | InsnType::Not => self.constrain_unary(instruction),
            InsnType::MonitorEnter | InsnType::MonitorExit => {
                if let Some(lock) = instruction.args.first() {
                    self.add_argument_bound(lock, BoundKind::Upper, ArgType::unknown_object());
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn constrain_invoke(&mut self, instruction: &InsnNode) -> Result<(), TypeConstraintError> {
        let reference = instruction.payload.reference.as_ref().ok_or(
            TypeConstraintError::MissingReference {
                offset: instruction.offset,
                instruction: instruction.insn_type,
            },
        )?;
        let MemberReference::Method(method) = reference else {
            return Err(TypeConstraintError::InvalidReferenceKind {
                offset: instruction.offset,
                instruction: instruction.insn_type,
            });
        };
        let invoke_type = instruction
            .payload
            .invoke_type
            .ok_or(TypeConstraintError::MissingInvokeType(instruction.offset))?;
        let is_static = invoke_type == InvokeType::Static;
        let expected = method.descriptor.parameters.len() + usize::from(!is_static);
        if instruction.args.len() != expected {
            return Err(TypeConstraintError::InvokeArity {
                offset: instruction.offset,
                expected,
                actual: instruction.args.len(),
            });
        }
        let mut arguments = instruction.args.iter();
        if !is_static {
            if let Some(receiver) = arguments.next() {
                self.add_argument_bound(receiver, BoundKind::Upper, method.owner.clone());
            }
        }
        for (argument, parameter) in arguments.zip(&method.descriptor.parameters) {
            self.add_argument_bound(argument, BoundKind::Upper, parameter.clone());
        }
        if let Some(result) = &instruction.result {
            let ty = if instruction.insn_type == InsnType::Constructor {
                if result.ty.is_known() {
                    result.ty.clone()
                } else {
                    method.owner.clone()
                }
            } else {
                method.descriptor.return_type.clone()
            };
            self.add_register_bound(result, BoundKind::Exact, ty);
        }
        Ok(())
    }

    fn constrain_field(&mut self, instruction: &InsnNode) -> Result<(), TypeConstraintError> {
        let reference = instruction.payload.reference.as_ref().ok_or(
            TypeConstraintError::MissingReference {
                offset: instruction.offset,
                instruction: instruction.insn_type,
            },
        )?;
        let MemberReference::Field(field) = reference else {
            return Err(TypeConstraintError::InvalidReferenceKind {
                offset: instruction.offset,
                instruction: instruction.insn_type,
            });
        };
        let field_type = field.field_type.clone();
        match instruction.insn_type {
            InsnType::Iget => {
                if let Some(result) = &instruction.result {
                    self.add_register_bound(result, BoundKind::Exact, field_type);
                }
                if let Some(owner) = instruction.args.first() {
                    self.add_argument_bound(owner, BoundKind::Upper, field.owner.clone());
                }
            }
            InsnType::Iput => {
                if let Some(value) = instruction.args.first() {
                    self.add_argument_bound(value, BoundKind::Upper, field_type);
                }
                if let Some(owner) = instruction.args.get(1) {
                    self.add_argument_bound(owner, BoundKind::Upper, field.owner.clone());
                }
            }
            InsnType::Sget => {
                if let Some(result) = &instruction.result {
                    self.add_register_bound(result, BoundKind::Exact, field_type);
                }
            }
            InsnType::Sput => {
                if let Some(value) = instruction.args.first() {
                    self.add_argument_bound(value, BoundKind::Upper, field_type);
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn constrain_array_get(&mut self, instruction: &InsnNode) {
        let Some(result) = &instruction.result else {
            return;
        };
        if result.ty.is_known() {
            if let Some(array) = instruction.args.first() {
                self.add_argument_bound(
                    array,
                    BoundKind::Fallback,
                    ArgType::array(result.ty.clone()),
                );
            }
        }
        if let Some(index) = instruction.args.get(1) {
            self.add_argument_bound(index, BoundKind::Upper, ArgType::INT);
        }
        if let (Some(array), Some(result)) = (
            instruction.args.first().and_then(Self::argument_value),
            SsaVar::from_reg(result),
        ) {
            self.arrays.insert(ArrayConstraint::Read { array, result });
        }
    }

    fn constrain_array_put(&mut self, instruction: &InsnNode) {
        let Some(value) = instruction.args.first() else {
            return;
        };
        if let Some(ty) = value.declared_type().filter(|ty| ty.is_known()) {
            if let Some(array) = instruction.args.get(1) {
                self.add_argument_bound(array, BoundKind::Fallback, ArgType::array(ty.clone()));
            }
        }
        if let Some(index) = instruction.args.get(2) {
            self.add_argument_bound(index, BoundKind::Upper, ArgType::INT);
        }
        if let (Some(array), Some(value)) = (
            instruction.args.get(1).and_then(Self::argument_value),
            Self::argument_value(value),
        ) {
            self.arrays.insert(ArrayConstraint::Write { array, value });
        }
    }

    fn constrain_peer_arguments(&mut self, instruction: &InsnNode) {
        let Some(left) = instruction.args.first() else {
            return;
        };
        let Some(right) = instruction.args.get(1) else {
            return;
        };
        let reference_equality = matches!(instruction.payload.if_op, Some(IfOp::Eq | IfOp::Ne));
        if let Some(ty) = left.declared_type().filter(|ty| ty.is_known()) {
            self.add_peer_bound(right, ty, reference_equality);
        }
        if let Some(ty) = right.declared_type().filter(|ty| ty.is_known()) {
            self.add_peer_bound(left, ty, reference_equality);
        }
    }

    fn add_peer_bound(&mut self, argument: &InsnArg, peer: &ArgType, reference_equality: bool) {
        if reference_equality {
            let domain = if peer.is_reference() {
                ArgType::unknown_object()
            } else {
                peer.clone()
            };
            self.add_argument_bound(argument, BoundKind::Domain, domain);
        } else {
            self.add_argument_bound(argument, BoundKind::Upper, peer.clone());
        }
    }

    fn constrain_arithmetic(&mut self, instruction: &InsnNode) {
        let result_type = instruction
            .result
            .as_ref()
            .map(|result| result.ty.clone())
            .filter(ArgType::is_known)
            .or_else(|| {
                instruction
                    .args
                    .iter()
                    .filter_map(InsnArg::declared_type)
                    .find(|ty| ty.is_known())
                    .cloned()
            });
        let Some(result_type) = result_type else {
            return;
        };
        if result_type == ArgType::INT
            && matches!(
                instruction.payload.arith_op,
                Some(ArithOp::And | ArithOp::Or | ArithOp::Xor)
            )
        {
            self.constrain_narrow_bitwise(instruction);
            return;
        }
        if let Some(result) = &instruction.result {
            self.add_register_bound(result, BoundKind::Lower, result_type.clone());
        }
        for (index, argument) in instruction.args.iter().enumerate() {
            let expected = if index == 1
                && matches!(
                    instruction.payload.arith_op,
                    Some(ArithOp::Shl | ArithOp::Shr | ArithOp::Ushr)
                ) {
                ArgType::INT
            } else {
                result_type.clone()
            };
            self.add_argument_bound(argument, BoundKind::Upper, expected);
        }
    }

    fn constrain_narrow_bitwise(&mut self, instruction: &InsnNode) {
        let Some(result) = instruction.result.as_ref().and_then(SsaVar::from_reg) else {
            return;
        };
        let mut has_value_source = false;
        for argument in &instruction.args {
            if let Some(source) = Self::argument_value(argument) {
                self.flows.insert((source, result));
                has_value_source = true;
                continue;
            }
            if matches!(argument, InsnArg::Lit(literal) if !matches!(literal.value, 0 | 1)) {
                self.add_value_bound(result, BoundKind::Lower, ArgType::INT);
            }
        }
        if !has_value_source {
            self.add_value_bound(result, BoundKind::Lower, ArgType::INT);
        }
    }

    fn constrain_unary(&mut self, instruction: &InsnNode) {
        let Some(result) = &instruction.result else {
            return;
        };
        self.add_register_bound(result, BoundKind::Lower, result.ty.clone());
        if let Some(source) = instruction.args.first() {
            self.add_argument_bound(source, BoundKind::Upper, result.ty.clone());
        }
    }

    fn observe_arguments(&mut self, instruction: &InsnNode) {
        InstructionTree::visit_args(instruction, &mut TypeObservation { graph: self });
    }

    fn add_argument_bound(&mut self, argument: &InsnArg, kind: BoundKind, ty: ArgType) {
        if let Some(register) = argument.as_register() {
            self.add_register_bound(register, kind, ty);
        }
    }

    fn add_register_bound(&mut self, register: &RegisterArg, kind: BoundKind, ty: ArgType) {
        if let Some(value) = SsaVar::from_reg(register) {
            self.add_value_bound(value, kind, ty);
        }
    }

    fn observe_register_type(&mut self, register: &RegisterArg) {
        self.add_register_bound(register, BoundKind::Domain, register.ty.clone());
        if register.ty.is_known() {
            self.add_register_bound(register, BoundKind::Fallback, register.ty.clone());
        }
    }

    fn add_value_bound(&mut self, value: SsaVar, kind: BoundKind, ty: ArgType) {
        self.values.insert(value);
        self.bounds
            .entry(value)
            .or_default()
            .insert(TypeBound::new(kind, ty));
    }

    fn argument_value(argument: &InsnArg) -> Option<SsaVar> {
        match argument {
            InsnArg::Reg(register) => SsaVar::from_reg(register),
            InsnArg::Wrapped(instruction) => instruction.result.as_ref().and_then(SsaVar::from_reg),
            InsnArg::Lit(_) => None,
        }
    }

    fn constant_fallback(value: &InsnArg) -> Option<ArgType> {
        let ty = match value {
            InsnArg::Lit(literal) => &literal.ty,
            InsnArg::Wrapped(instruction) if instruction.insn_type == InsnType::Const => {
                &instruction.result.as_ref()?.ty
            }
            InsnArg::Wrapped(instruction) if instruction.insn_type == InsnType::ConstStr => {
                return Some(ArgType::string());
            }
            InsnArg::Reg(_) | InsnArg::Wrapped(_) => return None,
        };
        if ty.is_known() {
            return Some(ty.clone());
        }
        match ty {
            ArgType::Unknown(categories)
                if categories.iter().any(|category| {
                    matches!(
                        category,
                        crate::ir::PrimitiveType::Boolean
                            | crate::ir::PrimitiveType::Byte
                            | crate::ir::PrimitiveType::Short
                            | crate::ir::PrimitiveType::Char
                            | crate::ir::PrimitiveType::Int
                            | crate::ir::PrimitiveType::Float
                    )
                }) =>
            {
                Some(ArgType::INT)
            }
            ArgType::Unknown(categories)
                if categories.iter().any(|category| {
                    matches!(
                        category,
                        crate::ir::PrimitiveType::Long | crate::ir::PrimitiveType::Double
                    )
                }) =>
            {
                Some(ArgType::LONG)
            }
            ArgType::Unknown(categories)
                if categories.iter().any(|category| {
                    matches!(
                        category,
                        crate::ir::PrimitiveType::Object | crate::ir::PrimitiveType::Array
                    )
                }) =>
            {
                Some(ArgType::object("java/lang/Object"))
            }
            _ => None,
        }
    }
}

struct TypeObservation<'a> {
    graph: &'a mut TypeConstraintGraph,
}

impl InstructionVisitor for TypeObservation<'_> {
    fn visit_register(&mut self, register: &RegisterArg) {
        self.graph.observe_register_type(register);
    }

    fn visit_instruction(&mut self, instruction: &InsnNode) {
        if let Some(result) = &instruction.result {
            self.graph.observe_register_type(result);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn concrete_register_observations_are_weak_type_evidence() {
        let value = SsaVar::new(2, 1);
        let mut graph = TypeConstraintGraph {
            classes: SsaClasses::new([value]),
            values: BTreeSet::from([value]),
            bounds: BTreeMap::new(),
            flows: BTreeSet::new(),
            upper_flows: BTreeSet::new(),
            arrays: BTreeSet::new(),
        };
        let register = RegisterArg::new_ssa(2, 1, ArgType::INT);

        graph.observe_register_type(&register);

        let bounds = graph.bounds.get(&value).expect("observed value bounds");
        assert!(bounds.contains(&TypeBound::new(BoundKind::Domain, ArgType::INT)));
        assert!(bounds.contains(&TypeBound::new(BoundKind::Fallback, ArgType::INT)));
    }

    #[test]
    fn narrow_bitwise_operations_preserve_boolean_type_flow() {
        let left = SsaVar::new(0, 1);
        let right = SsaVar::new(1, 1);
        let result = SsaVar::new(2, 1);
        let mut graph = TypeConstraintGraph {
            classes: SsaClasses::new([left, right, result]),
            values: BTreeSet::from([left, right, result]),
            bounds: BTreeMap::new(),
            flows: BTreeSet::new(),
            upper_flows: BTreeSet::new(),
            arrays: BTreeSet::new(),
        };
        let instruction = InsnNode::arith(
            ArithOp::Or,
            RegisterArg::new_ssa(2, 1, ArgType::INT),
            InsnArg::reg_ssa(0, 1, ArgType::BOOLEAN),
            InsnArg::reg_ssa(1, 1, ArgType::BOOLEAN),
            ArgType::INT,
        );

        graph.constrain_arithmetic(&instruction);

        assert!(graph.flows.contains(&(left, result)));
        assert!(graph.flows.contains(&(right, result)));
        assert!(!graph.bounds.get(&result).is_some_and(|bounds| {
            bounds.contains(&TypeBound::new(BoundKind::Lower, ArgType::INT))
        }));
    }

    #[test]
    fn physical_array_write_type_is_fallback_evidence() {
        let array = SsaVar::new(4, 1);
        let value_type = ArgType::object("android/content/pm/ActivityInfo");
        let mut graph = TypeConstraintGraph {
            classes: SsaClasses::new([array]),
            values: BTreeSet::from([array]),
            bounds: BTreeMap::new(),
            flows: BTreeSet::new(),
            upper_flows: BTreeSet::new(),
            arrays: BTreeSet::new(),
        };
        let instruction = InsnNode::aput(
            InsnArg::reg_ssa(1, 0, value_type.clone()),
            InsnArg::reg_ssa(4, 1, ArgType::unknown_object()),
            InsnArg::lit(0, ArgType::INT),
        );

        graph.constrain_array_put(&instruction);

        let bounds = graph.bounds.get(&array).expect("array bounds");
        assert!(bounds.contains(&TypeBound::new(
            BoundKind::Fallback,
            ArgType::array(value_type.clone()),
        )));
        assert!(!bounds.contains(&TypeBound::new(
            BoundKind::Upper,
            ArgType::array(value_type),
        )));
    }

    #[test]
    fn move_exception_is_constrained_to_throwable() {
        let value = SsaVar::new(3, 14);
        let mut graph = TypeConstraintGraph {
            classes: SsaClasses::new([value]),
            values: BTreeSet::from([value]),
            bounds: BTreeMap::new(),
            flows: BTreeSet::new(),
            upper_flows: BTreeSet::new(),
            arrays: BTreeSet::new(),
        };
        let instruction = InsnNode::move_exception(RegisterArg::new_ssa(
            value.reg_num,
            value.version,
            ArgType::unknown(),
        ));

        graph
            .constrain_instruction(&instruction, &CFG::new("handler"))
            .expect("move-exception constraint");

        assert!(graph.bounds.get(&value).is_some_and(|bounds| {
            bounds.contains(&TypeBound::new(BoundKind::Upper, ArgType::throwable()))
        }));
    }
}
