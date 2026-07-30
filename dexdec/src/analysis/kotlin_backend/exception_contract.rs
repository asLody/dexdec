use std::collections::{BTreeMap, BTreeSet};

use crate::frontend::{ClassNode, MethodNode};
use crate::ir::analysis::{SubtypeRelation, TypeHierarchy};
use crate::ir::generic_types::{JvmTypeSignature, MethodSignature, TypeArgument};
use crate::ir::{ArgType, InsnType, MemberReference, MethodDescriptor, MethodReference, CFG};

use super::KotlinSourceAbi;

/// Recovers checked-exception contracts absent from DEX method metadata.
///
/// The analysis is a forward may-effect fixed point over the class-local call
/// graph. Declared source and platform contracts are seeds; protected invokes
/// whose exception is accepted by a handler do not escape the method. This is
/// required for Kotlin legalization because DEX itself does not enforce checked
/// exceptions, regardless of which frontend produced the bytecode.
pub(super) struct DeclaredExceptionAnalysis<'a> {
    abi: &'a KotlinSourceAbi,
    hierarchy: &'a dyn TypeHierarchy,
}

impl<'a> DeclaredExceptionAnalysis<'a> {
    pub(super) fn new(abi: &'a KotlinSourceAbi, hierarchy: &'a dyn TypeHierarchy) -> Self {
        Self { abi, hierarchy }
    }

    pub(super) fn solve<'b>(
        &self,
        class: &ClassNode,
        methods: impl IntoIterator<Item = (&'b MethodNode, &'b CFG)>,
    ) -> BTreeMap<MethodReference, Vec<ArgType>> {
        let methods = methods.into_iter().collect::<Vec<_>>();
        let mut contracts = class
            .methods()
            .iter()
            .filter_map(|method| {
                let exceptions = Self::declared(class, method);
                (!exceptions.is_empty()).then(|| (Self::reference(class, method), exceptions))
            })
            .collect::<BTreeMap<_, _>>();
        let candidates = methods
            .into_iter()
            .filter(|(method, _)| {
                !method.is_class_init() && Self::declared(class, method).is_empty()
            })
            .collect::<Vec<_>>();

        loop {
            let mut changed = false;
            for (method, cfg) in &candidates {
                let reference = Self::reference(class, method);
                let inferred = self.escaping_invocation_exceptions(cfg, &contracts);
                let current = contracts.entry(reference).or_default();
                let before = current.len();
                current.extend(inferred);
                current.sort();
                current.dedup();
                changed |= current.len() != before;
            }
            if !changed {
                break;
            }
        }

        candidates
            .into_iter()
            .filter_map(|(method, _)| {
                let reference = Self::reference(class, method);
                contracts
                    .remove(&reference)
                    .filter(|exceptions| !exceptions.is_empty())
                    .map(|exceptions| (reference, exceptions))
            })
            .collect()
    }

    fn escaping_invocation_exceptions(
        &self,
        cfg: &CFG,
        local: &BTreeMap<MethodReference, Vec<ArgType>>,
    ) -> BTreeSet<ArgType> {
        cfg.blocks
            .values()
            .flat_map(|block| &block.insns)
            .filter(|instruction| instruction.insn_type == InsnType::Invoke)
            .filter_map(|instruction| {
                let Some(MemberReference::Method(method)) = instruction.payload.reference.as_ref()
                else {
                    return None;
                };
                let exceptions = self.invocation_exceptions(method, local);
                Some(
                    exceptions
                        .into_iter()
                        .filter(|exception| self.is_checked(exception))
                        .filter(|exception| !self.handled(cfg, instruction.offset, exception))
                        .collect::<Vec<_>>(),
                )
            })
            .flatten()
            .collect()
    }

    fn invocation_exceptions(
        &self,
        method: &MethodReference,
        local: &BTreeMap<MethodReference, Vec<ArgType>>,
    ) -> Vec<ArgType> {
        let generic = self.abi.generic_method(method);
        let Some(signature) = generic
            .as_ref()
            .map(|contract| &contract.signature)
            .filter(|signature| !signature.throws.is_empty())
        else {
            return local
                .get(method)
                .map(Vec::as_slice)
                .unwrap_or_else(|| self.abi.method_exceptions(method))
                .to_vec();
        };
        signature
            .throws
            .iter()
            .filter(|exception| !Self::is_unconstrained_throws_variable(signature, exception))
            .map(JvmTypeSignature::erased)
            .collect()
    }

    /// JLS 18.4 instantiates an inference variable used only in a throws
    /// bound as `RuntimeException` when no proper lower bound constrains it.
    /// Such a variable therefore contributes no checked effect at the call
    /// site even though its declaration erases to `Throwable`.
    fn is_unconstrained_throws_variable(
        signature: &MethodSignature,
        exception: &JvmTypeSignature,
    ) -> bool {
        let JvmTypeSignature::TypeVariable(name) = exception else {
            return false;
        };
        signature
            .type_parameters
            .iter()
            .any(|parameter| parameter.name == *name)
            && !signature
                .parameter_types
                .iter()
                .any(|parameter| Self::references_variable(parameter, name))
            && !Self::references_variable(&signature.return_type, name)
    }

    fn references_variable(ty: &JvmTypeSignature, name: &str) -> bool {
        match ty {
            JvmTypeSignature::TypeVariable(variable) => variable == name,
            JvmTypeSignature::Array(element) => Self::references_variable(element, name),
            JvmTypeSignature::ClassType(class) => class
                .type_arguments
                .iter()
                .chain(
                    class
                        .inner_segments
                        .iter()
                        .flat_map(|segment| &segment.type_arguments),
                )
                .any(|argument| match argument {
                    TypeArgument::Unbounded => false,
                    TypeArgument::Exact(ty)
                    | TypeArgument::Extends(ty)
                    | TypeArgument::Super(ty) => Self::references_variable(ty, name),
                }),
            JvmTypeSignature::BaseType(_) => false,
        }
    }

    fn handled(&self, cfg: &CFG, offset: u32, exception: &ArgType) -> bool {
        cfg.handlers.iter().any(|handler| {
            handler.covers(offset)
                && handler
                    .catch_type
                    .as_ref()
                    .is_none_or(|caught| self.is_subtype(exception, caught))
        })
    }

    fn is_checked(&self, exception: &ArgType) -> bool {
        self.is_subtype(exception, &ArgType::object("java/lang/Throwable"))
            && !self.is_subtype(exception, &ArgType::object("java/lang/RuntimeException"))
            && !self.is_subtype(exception, &ArgType::object("java/lang/Error"))
    }

    fn is_subtype(&self, value: &ArgType, expected: &ArgType) -> bool {
        match (value.as_object(), expected.as_object()) {
            (Some(value), Some(expected)) => {
                self.hierarchy.subtype_relation(value, expected) == SubtypeRelation::Yes
            }
            _ => false,
        }
    }

    fn declared(class: &ClassNode, method: &MethodNode) -> Vec<ArgType> {
        if !method.throws().is_empty() {
            return method.throws().to_vec();
        }
        (method.access_flags.is_synthetic() || super::FunctionObjectClass::analyze(class))
            .then(|| {
                method
                    .override_semantics
                    .as_ref()
                    .map(|semantics| semantics.inherited_throws.clone())
            })
            .flatten()
            .unwrap_or_default()
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
