//! Recovery facts for DEX uninitialized-object values.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{EdgeKind, InsnArg, InsnType, MemberReference, MethodReference, CFG};

use super::{
    DominanceError, DominatorTree, InsnPosition, SsaValueGraph, SsaVar, TypeHierarchy, UsePosition,
};

#[derive(Debug, Clone)]
pub struct ObjectInitialization {
    pub allocation: InsnPosition,
    pub constructors: Vec<InsnPosition>,
    pub aliases: BTreeSet<SsaVar>,
    pub value: SsaVar,
    pub ty: crate::ir::ArgType,
    pub allocation_exception_handlers: Vec<crate::ir::BlockId>,
}

#[derive(Debug, Clone, Default)]
pub struct ObjectInitializations {
    entries: Vec<ObjectInitialization>,
    discarded_allocations: BTreeSet<InsnPosition>,
}

struct ObjectAliases {
    classes: BTreeMap<SsaVar, SsaVar>,
    groups: BTreeMap<SsaVar, BTreeSet<SsaVar>>,
    phi_uses: BTreeSet<UsePosition>,
}

impl ObjectAliases {
    fn analyze(cfg: &CFG, values: &SsaValueGraph) -> Self {
        let mut classes = values.copy_classes();
        Self::close_phi_equations(cfg, values, &mut classes);

        let groups = classes.groups();
        let classes = groups
            .iter()
            .flat_map(|(class, members)| members.iter().map(|member| (*member, *class)))
            .collect::<BTreeMap<_, _>>();
        let mut phi_uses = BTreeSet::new();
        for phi in values.phis() {
            let Some(class) = classes.get(&phi.result) else {
                continue;
            };
            for (argument, input) in phi.inputs.iter().enumerate() {
                if classes.get(&input.value) != Some(class) {
                    continue;
                }
                let Some(predecessor) = cfg.block(input.predecessor) else {
                    continue;
                };
                phi_uses.insert(UsePosition::phi(
                    InsnPosition {
                        block: input.predecessor,
                        index: predecessor.insns.len(),
                    },
                    argument,
                    phi.result,
                ));
            }
        }
        Self {
            classes,
            groups,
            phi_uses,
        }
    }

    fn close_phi_equations(cfg: &CFG, values: &SsaValueGraph, classes: &mut super::SsaClasses) {
        loop {
            let mut dependencies = values
                .phis()
                .iter()
                .map(|phi| classes.root(phi.result))
                .map(|class| (class, BTreeSet::new()))
                .collect::<BTreeMap<_, _>>();
            let mut origins = BTreeMap::<SsaVar, BTreeSet<SsaVar>>::new();
            for value in values.values() {
                let class = classes.root(value.variable);
                let transport = value.definition.is_some_and(|position| {
                    cfg.block(position.block)
                        .and_then(|block| block.insns.get(position.index))
                        .is_some_and(|instruction| {
                            matches!(instruction.insn_type, InsnType::Move | InsnType::Phi)
                        })
                });
                if !transport {
                    origins.entry(class).or_default().insert(class);
                }
            }
            for phi in values.phis() {
                let result = classes.root(phi.result);
                for input in &phi.inputs {
                    let input = classes.root(input.value);
                    dependencies.entry(result).or_default().insert(input);
                    origins.entry(input).or_default();
                }
            }

            loop {
                let mut changed = false;
                for (class, inputs) in &dependencies {
                    let inherited = inputs
                        .iter()
                        .flat_map(|input| origins.get(input).into_iter().flatten().copied())
                        .collect::<Vec<_>>();
                    let target = origins.entry(*class).or_default();
                    let before = target.len();
                    target.extend(inherited);
                    changed |= target.len() != before;
                }
                if !changed {
                    break;
                }
            }

            let merges = origins
                .into_iter()
                .filter_map(|(class, origins)| {
                    let mut origins = origins.into_iter();
                    let origin = origins.next()?;
                    if origins.next().is_some() {
                        return None;
                    }
                    (class != origin).then_some((class, origin))
                })
                .collect::<Vec<_>>();
            if merges.is_empty() {
                break;
            }
            for (class, origin) in merges {
                classes.union(class, origin);
            }
        }
    }

    fn class_of(&self, value: SsaVar) -> SsaVar {
        self.classes.get(&value).copied().unwrap_or(value)
    }

    fn group(&self, class: SsaVar) -> Option<&BTreeSet<SsaVar>> {
        self.groups.get(&class)
    }

    fn transports(&self, usage: UsePosition) -> bool {
        self.phi_uses.contains(&usage)
    }
}

impl ObjectInitializations {
    pub fn analyze(
        cfg: &CFG,
        values: &SsaValueGraph,
        hierarchy: &dyn TypeHierarchy,
    ) -> Result<Self, ObjectInitializationError> {
        let aliases = ObjectAliases::analyze(cfg, values);

        let mut allocations = BTreeMap::<SsaVar, Vec<(InsnPosition, SsaVar)>>::new();
        let mut constructors =
            BTreeMap::<SsaVar, Vec<(InsnPosition, SsaVar, MethodReference)>>::new();
        for (&block, body) in &cfg.blocks {
            for (index, instruction) in body.insns.iter().enumerate() {
                let position = InsnPosition { block, index };
                if instruction.insn_type == InsnType::NewInstance {
                    let value = instruction
                        .result
                        .as_ref()
                        .and_then(SsaVar::from_reg)
                        .ok_or(ObjectInitializationError::MissingAllocationValue(position))?;
                    allocations
                        .entry(aliases.class_of(value))
                        .or_default()
                        .push((position, value));
                    continue;
                }
                let Some((receiver, method)) = Self::constructor_receiver(instruction, position)?
                else {
                    continue;
                };
                constructors
                    .entry(aliases.class_of(receiver))
                    .or_default()
                    .push((position, receiver, method));
            }
        }

        let dominators =
            DominatorTree::compute(cfg).map_err(ObjectInitializationError::Dominance)?;
        let mut entries = Vec::new();
        let mut discarded_allocations = BTreeSet::new();
        for (class, allocation) in allocations {
            let [(allocation, allocation_value)] = allocation.as_slice() else {
                return Err(ObjectInitializationError::MultipleAllocations {
                    class,
                    allocations: allocation
                        .into_iter()
                        .map(|(position, _)| position)
                        .collect(),
                });
            };
            let Some(constructors) = constructors.get(&class) else {
                if Self::is_unobserved_allocation(cfg, values, &aliases, class, *allocation) {
                    discarded_allocations.insert(*allocation);
                    continue;
                }
                return Err(ObjectInitializationError::MissingConstructor(*allocation));
            };
            let constructor_positions = constructors
                .iter()
                .map(|(position, _, _)| *position)
                .collect::<Vec<_>>();
            let allocation_type = cfg
                .block(allocation.block)
                .and_then(|block| block.insns.get(allocation.index))
                .and_then(|instruction| instruction.payload.class_type.as_ref())
                .ok_or(ObjectInitializationError::MissingAllocationType(
                    *allocation,
                ))?;
            for (_, _, method) in constructors {
                let compatible_owner = match (allocation_type.as_object(), method.owner.as_object())
                {
                    (Some(allocated), Some(constructed)) => {
                        hierarchy.is_subtype(allocated, constructed)
                    }
                    _ => allocation_type == &method.owner,
                };
                if !compatible_owner {
                    return Err(ObjectInitializationError::ConstructorTypeMismatch {
                        allocation: *allocation,
                        allocated: allocation_type.clone(),
                        constructed: method.owner.clone(),
                    });
                }
            }
            let object_aliases = aliases
                .group(class)
                .cloned()
                .ok_or(ObjectInitializationError::MissingAliasClass(class))?;
            for constructor in &constructor_positions {
                if !Self::position_dominates(*allocation, *constructor, &dominators) {
                    return Err(ObjectInitializationError::ConstructorNotDominated {
                        allocation: *allocation,
                        constructor: *constructor,
                    });
                }
            }
            if let [(constructor, _, _)] = constructors.as_slice() {
                if let Some(usage) = Self::invalid_initialization_use(
                    cfg,
                    values,
                    &aliases,
                    &object_aliases,
                    *constructor,
                    &dominators,
                ) {
                    return Err(ObjectInitializationError::UseBeforeInitialization {
                        allocation: *allocation,
                        constructor: *constructor,
                        usage,
                    });
                }
            }
            let allocation_exception_handlers =
                Self::allocation_exception_handlers(cfg, *allocation, &constructor_positions);
            entries.push(ObjectInitialization {
                allocation: *allocation,
                constructors: constructor_positions,
                aliases: object_aliases,
                value: constructors
                    .first()
                    .map(|(_, value, _)| *value)
                    .unwrap_or(*allocation_value),
                ty: allocation_type.clone(),
                allocation_exception_handlers,
            });
        }
        Ok(Self {
            entries,
            discarded_allocations,
        })
    }

    pub fn entries(&self) -> &[ObjectInitialization] {
        &self.entries
    }

    pub fn discarded_allocations(&self) -> &BTreeSet<InsnPosition> {
        &self.discarded_allocations
    }

    fn is_unobserved_allocation(
        cfg: &CFG,
        values: &SsaValueGraph,
        aliases: &ObjectAliases,
        class: SsaVar,
        allocation: InsnPosition,
    ) -> bool {
        if !Self::has_stable_exception_scope(cfg, allocation.block) {
            return false;
        }
        aliases.group(class).is_some_and(|members| {
            members.iter().all(|member| {
                values.value(*member).is_none_or(|value| {
                    value.uses.iter().all(|usage| {
                        if aliases.transports(*usage) {
                            return true;
                        }
                        cfg.block(usage.instruction.block)
                            .and_then(|block| block.insns.get(usage.instruction.index))
                            .is_some_and(|instruction| instruction.insn_type == InsnType::Move)
                    })
                })
            })
        })
    }

    /// Kotlin has no expression for allocating an uninitialized instance and
    /// then abandoning it. Such a value is removable when it has no data-flow
    /// uses and the following source operation is protected by the identical
    /// exception domain. The latter condition keeps handler ownership stable;
    /// only the VM resource-exhaustion effect, which has no faithful Kotlin
    /// source representation here, is abstracted away.
    fn has_stable_exception_scope(cfg: &CFG, block: crate::ir::BlockId) -> bool {
        let successors = cfg.successors_with_kind(block);
        let exceptional = successors
            .iter()
            .filter_map(|(target, kind)| (*kind == EdgeKind::Exception).then_some(*target))
            .collect::<BTreeSet<_>>();
        if exceptional.is_empty() {
            return true;
        }
        let normal = successors
            .iter()
            .filter_map(|(target, kind)| (*kind != EdgeKind::Exception).then_some(*target))
            .collect::<BTreeSet<_>>();
        if normal.len() != 1 {
            return false;
        }
        let Some(continuation) = normal.first().copied() else {
            return false;
        };
        cfg.successors_with_kind(continuation)
            .iter()
            .filter_map(|(target, kind)| (*kind == EdgeKind::Exception).then_some(*target))
            .collect::<BTreeSet<_>>()
            == exceptional
    }

    fn constructor_receiver(
        instruction: &crate::ir::InsnNode,
        position: InsnPosition,
    ) -> Result<Option<(SsaVar, MethodReference)>, ObjectInitializationError> {
        if instruction.insn_type != InsnType::Invoke
            || instruction.payload.invoke_type != Some(crate::ir::InvokeType::Direct)
        {
            return Ok(None);
        }
        let reference = instruction
            .payload
            .reference
            .as_ref()
            .ok_or(ObjectInitializationError::MissingReference(position))?;
        let MemberReference::Method(method) = reference else {
            return Err(ObjectInitializationError::InvalidReferenceKind(position));
        };
        if !method.is_constructor() {
            return Ok(None);
        }
        let receiver = instruction
            .args
            .first()
            .and_then(InsnArg::as_register)
            .and_then(SsaVar::from_reg)
            .ok_or(ObjectInitializationError::MissingConstructorReceiver(
                position,
            ))?;
        Ok(Some((receiver, method.clone())))
    }

    fn invalid_initialization_use(
        cfg: &CFG,
        values: &SsaValueGraph,
        alias_analysis: &ObjectAliases,
        object_aliases: &BTreeSet<SsaVar>,
        constructor: InsnPosition,
        dominators: &DominatorTree,
    ) -> Option<UsePosition> {
        object_aliases.iter().find_map(|alias| {
            values.value(*alias).and_then(|value| {
                value.uses.iter().find_map(|usage| {
                    let position = usage.instruction;
                    let Some(instruction) = cfg
                        .block(position.block)
                        .and_then(|block| block.insns.get(position.index))
                    else {
                        if alias_analysis.transports(*usage) {
                            return None;
                        }
                        return (!Self::position_dominates(constructor, position, dominators))
                            .then_some(*usage);
                    };
                    if instruction.insn_type == InsnType::Move {
                        return None;
                    }
                    if position == constructor {
                        return (usage.argument != 0).then_some(*usage);
                    }
                    (!Self::position_dominates(constructor, position, dominators)).then_some(*usage)
                })
            })
        })
    }

    fn position_dominates(
        definition: InsnPosition,
        usage: InsnPosition,
        dominators: &DominatorTree,
    ) -> bool {
        if definition.block == usage.block {
            definition.index < usage.index
        } else {
            dominators.dominates(definition.block, usage.block)
        }
    }

    fn allocation_exception_handlers(
        cfg: &CFG,
        allocation: InsnPosition,
        constructors: &[InsnPosition],
    ) -> Vec<crate::ir::BlockId> {
        if constructors
            .iter()
            .any(|constructor| allocation.block == constructor.block)
        {
            return Vec::new();
        }

        cfg.successors_with_kind(allocation.block)
            .iter()
            .filter_map(|(target, kind)| (*kind == EdgeKind::Exception).then_some(*target))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }
}

#[derive(Debug)]
pub enum ObjectInitializationError {
    Dominance(DominanceError),
    MissingAllocationValue(InsnPosition),
    MultipleAllocations {
        class: SsaVar,
        allocations: Vec<InsnPosition>,
    },
    MissingConstructor(InsnPosition),
    MissingAllocationType(InsnPosition),
    ConstructorTypeMismatch {
        allocation: InsnPosition,
        allocated: crate::ir::ArgType,
        constructed: crate::ir::ArgType,
    },
    ConstructorNotDominated {
        allocation: InsnPosition,
        constructor: InsnPosition,
    },
    UseBeforeInitialization {
        allocation: InsnPosition,
        constructor: InsnPosition,
        usage: UsePosition,
    },
    MissingReference(InsnPosition),
    InvalidReferenceKind(InsnPosition),
    MissingConstructorReceiver(InsnPosition),
    MissingAliasClass(SsaVar),
}

impl std::fmt::Display for ObjectInitializationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Dominance(source) => write!(formatter, "object dominance failed: {source}"),
            Self::MissingAllocationValue(position) => {
                write!(formatter, "allocation at {position:?} has no SSA value")
            }
            Self::MultipleAllocations { class, allocations } => write!(
                formatter,
                "uninitialized class {class:?} contains multiple allocations {allocations:?}"
            ),
            Self::MissingConstructor(allocation) => {
                write!(formatter, "allocation at {allocation:?} has no constructor")
            }
            Self::MissingAllocationType(position) => {
                write!(formatter, "allocation at {position:?} has no class type")
            }
            Self::ConstructorTypeMismatch {
                allocation,
                allocated,
                constructed,
            } => write!(
                formatter,
                "allocation at {allocation:?} creates {allocated}, constructor initializes {constructed}"
            ),
            Self::ConstructorNotDominated {
                allocation,
                constructor,
            } => write!(
                formatter,
                "allocation at {allocation:?} does not dominate constructor {constructor:?}"
            ),
            Self::UseBeforeInitialization {
                allocation,
                constructor,
                usage,
            } => write!(
                formatter,
                "allocation at {allocation:?} is used at {usage:?} outside initialized scope of {constructor:?}"
            ),
            Self::MissingReference(position) => {
                write!(formatter, "direct invoke at {position:?} has no reference")
            }
            Self::InvalidReferenceKind(position) => {
                write!(
                    formatter,
                    "direct invoke at {position:?} has a non-method reference"
                )
            }
            Self::MissingConstructorReceiver(position) => {
                write!(formatter, "constructor at {position:?} has no SSA receiver")
            }
            Self::MissingAliasClass(value) => {
                write!(
                    formatter,
                    "allocation value {value:?} has no SSA alias class"
                )
            }
        }
    }
}

impl std::error::Error for ObjectInitializationError {}
