use std::collections::{BTreeMap, BTreeSet};

use crate::decoder::method_decoder::MethodDecoder;
use crate::frontend::{ClassNode, MethodNode};
use crate::ir::analysis::{ClassHierarchyIndex, SsaValueGraph, SsaVar};
use crate::ir::passes::CfgPipeline;
use crate::ir::{
    ArithOp, BlockId, EdgeKind, IfOp, InsnArg, InsnNode, InsnType, MemberReference, MethodContext,
    MethodDescriptor, MethodReference, Splitter, CFG,
};
use crate::language::kotlin::KotlinDefaultMask;

/// Recovers Kotlin default-argument masks from SSA value and control flow.
///
/// A proof starts at each argument of the dispatcher's unique target call. The
/// argument must be a phi joining the original parameter with a default value,
/// and every default input must be controlled by the same `mask & bit != 0`
/// edge. This also discovers extension-receiver offsets when metadata was
/// stripped because the receiver never participates in the mask.
pub(super) struct DefaultMaskFlow;

impl DefaultMaskFlow {
    pub(super) fn function(
        class: &ClassNode,
        dispatcher: &MethodNode,
        target: &MethodReference,
        target_static: bool,
        mask_count: usize,
        resolve_method: &impl Fn(&ClassNode, u32) -> Option<MethodReference>,
    ) -> Option<Vec<KotlinDefaultMask>> {
        Self::analyze(
            class,
            dispatcher,
            target,
            target_static,
            usize::from(!target_static),
            mask_count,
            resolve_method,
        )
    }

    pub(super) fn constructor(
        class: &ClassNode,
        dispatcher: &MethodNode,
        target: &MethodReference,
        mask_count: usize,
        resolve_method: &impl Fn(&ClassNode, u32) -> Option<MethodReference>,
    ) -> Option<Vec<KotlinDefaultMask>> {
        Self::analyze(
            class,
            dispatcher,
            target,
            false,
            0,
            mask_count,
            resolve_method,
        )
    }

    fn analyze(
        class: &ClassNode,
        dispatcher: &MethodNode,
        target: &MethodReference,
        target_static: bool,
        parameter_input_offset: usize,
        mask_count: usize,
        resolve_method: &impl Fn(&ClassNode, u32) -> Option<MethodReference>,
    ) -> Option<Vec<KotlinDefaultMask>> {
        let mut cfg = Self::cfg(class, dispatcher, resolve_method)?;
        let hierarchy = ClassHierarchyIndex::default();
        let values = CfgPipeline::new(&hierarchy).analyze(&mut cfg).ok()?.values;
        let invocation = Self::target_invocation(&cfg, target)?;
        let arguments = Self::target_arguments(invocation, target_static, target)?;
        let inputs = Self::input_registers(dispatcher)?;
        let mask_start = dispatcher.param_types().len().checked_sub(mask_count + 1)?;
        let mask_registers = inputs
            .get(mask_start..mask_start + mask_count)?
            .iter()
            .copied()
            .enumerate()
            .map(|(word, register)| (register, word))
            .collect::<BTreeMap<_, _>>();

        let mut masks = Vec::new();
        let mut occupied = BTreeSet::new();
        for (parameter, argument) in arguments.into_iter().enumerate() {
            let expected = *inputs.get(parameter_input_offset + parameter)?;
            if Self::is_input(&cfg, &values, argument, expected) {
                continue;
            }
            let (word, bit) =
                Self::argument_mask(&cfg, &values, argument, expected, &mask_registers)?;
            if !occupied.insert((word, bit)) {
                return None;
            }
            masks.push(KotlinDefaultMask::new(parameter, word, bit));
        }
        (!masks.is_empty()).then_some(masks)
    }

    fn cfg(
        class: &ClassNode,
        dispatcher: &MethodNode,
        resolve_method: &impl Fn(&ClassNode, u32) -> Option<MethodReference>,
    ) -> Option<CFG> {
        let code = dispatcher.code()?;
        let decoded = MethodDecoder::from_code(code).decode();
        let mut cfg = Splitter::new(dispatcher.name())
            .instructions(decoded.insns)
            .handlers(decoded.handlers)
            .registers(decoded.registers)
            .ins(decoded.ins)
            .build();
        cfg.set_method(MethodContext::new(
            class.class_type().clone(),
            dispatcher.name(),
            MethodDescriptor {
                parameters: dispatcher.param_types().to_vec(),
                return_type: dispatcher.return_type().clone(),
            },
            dispatcher.access_flags.is_static(),
        ));
        for instruction in cfg.blocks.values_mut().flat_map(|block| &mut block.insns) {
            let Some(reference) = instruction
                .payload
                .method_index
                .and_then(|index| resolve_method(class, index))
            else {
                continue;
            };
            instruction.payload.reference = Some(MemberReference::Method(reference));
        }
        Some(cfg)
    }

    fn target_invocation<'a>(cfg: &'a CFG, target: &MethodReference) -> Option<&'a InsnNode> {
        let candidates = cfg
            .blocks_iter()
            .flat_map(|block| &block.insns)
            .filter(|instruction| {
                instruction.insn_type == InsnType::Invoke
                    && matches!(
                        instruction.payload.reference.as_ref(),
                        Some(MemberReference::Method(method)) if method == target
                    )
            })
            .collect::<Vec<_>>();
        match candidates.as_slice() {
            [invocation] => Some(*invocation),
            _ => None,
        }
    }

    fn target_arguments(
        invocation: &InsnNode,
        target_static: bool,
        target: &MethodReference,
    ) -> Option<Vec<SsaVar>> {
        let mut cursor = usize::from(!target_static);
        let mut arguments = Vec::with_capacity(target.descriptor.parameters.len());
        for ty in &target.descriptor.parameters {
            let register = invocation.args.get(cursor)?.as_register()?;
            arguments.push(SsaVar::from_reg(register)?);
            cursor += if ty.is_wide() { 2 } else { 1 };
        }
        Some(arguments)
    }

    fn input_registers(method: &MethodNode) -> Option<Vec<u32>> {
        let code = method.code()?;
        let mut register =
            u32::from(code.args_start_reg()) + u32::from(!method.access_flags.is_static());
        let mut inputs = Vec::with_capacity(method.param_types().len());
        for ty in method.param_types() {
            inputs.push(register);
            register += if ty.is_wide() { 2 } else { 1 };
        }
        Some(inputs)
    }

    fn argument_mask(
        cfg: &CFG,
        values: &SsaValueGraph,
        argument: SsaVar,
        expected_parameter: u32,
        mask_registers: &BTreeMap<u32, usize>,
    ) -> Option<(usize, u32)> {
        let phi = values.phis().iter().find(|phi| phi.result == argument)?;
        let mut forwarded = false;
        let mut mask = None;
        for input in &phi.inputs {
            if Self::is_input(cfg, values, input.value, expected_parameter) {
                forwarded = true;
                continue;
            }
            let edge = Self::decision_edge(cfg, input.predecessor, input.edge_kind)?;
            let candidate = Self::mask_test(cfg, values, edge, mask_registers)?;
            if mask
                .replace(candidate)
                .is_some_and(|current| current != candidate)
            {
                return None;
            }
        }
        forwarded
            .then_some(mask?)
            .filter(|(_, bit)| bit.is_power_of_two())
    }

    fn is_input(cfg: &CFG, values: &SsaValueGraph, value: SsaVar, register: u32) -> bool {
        let value = Self::copy_root(cfg, values, value);
        value.reg_num == register
            && values
                .value(value)
                .is_some_and(|value| value.definition.is_none())
    }

    fn copy_root(cfg: &CFG, values: &SsaValueGraph, mut value: SsaVar) -> SsaVar {
        let mut visited = BTreeSet::new();
        while visited.insert(value) {
            let Some(definition) = Self::definition(cfg, values, value) else {
                break;
            };
            if definition.insn_type != InsnType::Move {
                break;
            }
            let Some(source) = definition
                .args
                .first()
                .and_then(InsnArg::as_register)
                .and_then(SsaVar::from_reg)
            else {
                break;
            };
            value = source;
        }
        value
    }

    fn decision_edge(
        cfg: &CFG,
        predecessor: BlockId,
        edge: EdgeKind,
    ) -> Option<(BlockId, EdgeKind)> {
        if matches!(edge, EdgeKind::True | EdgeKind::False) {
            return Some((predecessor, edge));
        }
        let mut current = predecessor;
        let mut visited = BTreeSet::new();
        while visited.insert(current) {
            let incoming = cfg
                .incoming_edges(current)
                .into_iter()
                .filter(|(_, edge)| !edge.is_exception())
                .collect::<Vec<_>>();
            let [(source, edge)] = incoming.as_slice() else {
                return None;
            };
            if matches!(edge, EdgeKind::True | EdgeKind::False) {
                return Some((*source, *edge));
            }
            current = *source;
        }
        None
    }

    fn mask_test(
        cfg: &CFG,
        values: &SsaValueGraph,
        (block, edge): (BlockId, EdgeKind),
        mask_registers: &BTreeMap<u32, usize>,
    ) -> Option<(usize, u32)> {
        let condition = cfg.block(block)?.terminator()?;
        let (register, zero) = match condition.args.as_slice() {
            [InsnArg::Reg(register), InsnArg::Lit(zero)]
            | [InsnArg::Lit(zero), InsnArg::Reg(register)] => (register, zero),
            _ => return None,
        };
        if zero.value != 0 {
            return None;
        }
        let non_zero = matches!(
            (condition.payload.if_op?, edge),
            (IfOp::Eq, EdgeKind::False) | (IfOp::Ne, EdgeKind::True)
        );
        if !non_zero {
            return None;
        }
        let value = Self::copy_root(cfg, values, SsaVar::from_reg(register)?);
        let operation = Self::definition(cfg, values, value)?;
        if operation.insn_type != InsnType::Arith
            || operation.payload.arith_op != Some(ArithOp::And)
        {
            return None;
        }
        let (mask, bit) = match operation.args.as_slice() {
            [InsnArg::Reg(mask), InsnArg::Lit(bit)] | [InsnArg::Lit(bit), InsnArg::Reg(mask)] => {
                (mask, bit)
            }
            _ => return None,
        };
        let mask = Self::copy_root(cfg, values, SsaVar::from_reg(mask)?);
        let word = *mask_registers.get(&mask.reg_num)?;
        u32::try_from(bit.value).ok().map(|bit| (word, bit))
    }

    fn definition<'a>(cfg: &'a CFG, values: &SsaValueGraph, value: SsaVar) -> Option<&'a InsnNode> {
        let position = values.value(value)?.definition?;
        cfg.block(position.block)?.insns.get(position.index)
    }
}
