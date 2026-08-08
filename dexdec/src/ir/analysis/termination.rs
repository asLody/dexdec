//! Interprocedural normal-completion analysis.
//!
//! DEX has no `noreturn` call opcode. The property is recovered as a least
//! fixed point over normal-return reachability: a statically resolved call
//! contributes a normal continuation only after its target is known to have
//! one. Exception dispatch remains reachable independently.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{EdgeKind, InsnNode, InsnType, InvokeType, MemberReference, MethodReference, CFG};

#[derive(Debug, Clone, Default)]
pub struct MethodTermination {
    members: BTreeSet<MethodReference>,
    no_return: BTreeSet<MethodReference>,
}

impl MethodTermination {
    pub fn analyze<'a>(methods: impl IntoIterator<Item = &'a CFG>) -> Self {
        let methods = methods
            .into_iter()
            .map(|cfg| (Self::method_reference(cfg), cfg))
            .collect::<BTreeMap<_, _>>();
        let members = methods.keys().cloned().collect::<BTreeSet<_>>();
        let mut may_return = BTreeSet::new();

        loop {
            let discovered = methods
                .iter()
                .filter_map(|(method, cfg)| {
                    (!may_return.contains(method)
                        && ReturnReachability::new(&members, &may_return).analyze(cfg))
                    .then_some(method.clone())
                })
                .collect::<Vec<_>>();
            if discovered.is_empty() {
                break;
            }
            may_return.extend(discovered);
        }

        let no_return = members.difference(&may_return).cloned().collect();
        Self { members, no_return }
    }

    pub fn apply(&self, cfg: &mut CFG) -> bool {
        if cfg.is_analysis_prepared() {
            return false;
        }
        let blocks = cfg.block_ids();
        let mut changed = false;
        for block in blocks {
            let no_return = cfg.block(block).and_then(|body| {
                body.insns
                    .iter()
                    .position(|instruction| self.is_no_return_call(instruction))
            });
            let Some(index) = no_return else {
                continue;
            };
            if let Some(body) = cfg.block_mut(block) {
                body.insns[index].payload.no_return = true;
                if body.insns.len() > index + 1 {
                    body.insns.truncate(index + 1);
                }
            }
            cfg.remove_normal_edges_from(block);
            changed = true;
        }
        changed
    }

    fn method_reference(cfg: &CFG) -> MethodReference {
        MethodReference {
            owner: cfg.method().owner().clone(),
            name: cfg.method().name().to_string(),
            descriptor: cfg.method().descriptor().clone(),
        }
    }

    fn is_no_return_call(&self, instruction: &InsnNode) -> bool {
        self.exact_internal_target(instruction)
            .is_some_and(|target| {
                self.no_return.contains(target) && !preserves_source_continuation(target)
            })
    }

    fn exact_internal_target<'a>(
        &'a self,
        instruction: &'a InsnNode,
    ) -> Option<&'a MethodReference> {
        let exact = matches!(
            instruction.payload.invoke_type,
            Some(InvokeType::Static | InvokeType::Direct | InvokeType::Super)
        );
        if instruction.insn_type != InsnType::Invoke || !exact {
            return None;
        }
        let MemberReference::Method(target) = instruction.payload.reference.as_ref()? else {
            return None;
        };
        self.members.contains(target).then_some(target)
    }
}

struct ReturnReachability<'a> {
    members: &'a BTreeSet<MethodReference>,
    may_return: &'a BTreeSet<MethodReference>,
}

impl<'a> ReturnReachability<'a> {
    fn new(
        members: &'a BTreeSet<MethodReference>,
        may_return: &'a BTreeSet<MethodReference>,
    ) -> Self {
        Self {
            members,
            may_return,
        }
    }

    fn analyze(&self, cfg: &CFG) -> bool {
        let mut pending = vec![cfg.entry];
        let mut reached = BTreeSet::new();
        while let Some(block) = pending.pop() {
            if !reached.insert(block) {
                continue;
            }
            let Some(body) = cfg.block(block) else {
                continue;
            };
            let mut normal = true;
            for instruction in &body.insns {
                if instruction.insn_type == InsnType::Return {
                    return true;
                }
                if self.blocks_normal_completion(instruction) {
                    normal = false;
                    break;
                }
            }
            pending.extend(
                cfg.successors_with_kind(block)
                    .iter()
                    .filter_map(|(target, kind)| {
                        (normal || *kind == EdgeKind::Exception).then_some(*target)
                    }),
            );
        }
        false
    }

    fn blocks_normal_completion(&self, instruction: &InsnNode) -> bool {
        if instruction.insn_type != InsnType::Invoke
            || !matches!(
                instruction.payload.invoke_type,
                Some(InvokeType::Static | InvokeType::Direct | InvokeType::Super)
            )
        {
            return false;
        }
        let Some(MemberReference::Method(target)) = instruction.payload.reference.as_ref() else {
            return false;
        };
        self.members.contains(target)
            && !self.may_return.contains(target)
            && !preserves_source_continuation(target)
    }
}

/// Kotlin emits these calls as compiler markers around code that is expected
/// to be inlined. Their runtime implementations deliberately throw, but the
/// bytecode following the marker is still the source-level continuation that
/// a decompiler must preserve.
fn preserves_source_continuation(target: &MethodReference) -> bool {
    target.owner.as_object() == Some("kotlin/jvm/internal/Intrinsics")
        && matches!(
            target.name.as_str(),
            "reifiedOperationMarker" | "needClassReification"
        )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{ArgType, Block, BlockId, MethodContext, MethodDescriptor};

    fn reference(name: &str) -> MethodReference {
        MethodReference {
            owner: ArgType::object("example/Test"),
            name: name.to_string(),
            descriptor: MethodDescriptor {
                parameters: Vec::new(),
                return_type: ArgType::VOID,
            },
        }
    }

    fn graph(name: &str) -> CFG {
        CFG::with_method(MethodContext::new(
            ArgType::object("example/Test"),
            name,
            MethodDescriptor {
                parameters: Vec::new(),
                return_type: ArgType::VOID,
            },
            true,
        ))
    }

    fn call(target: &str) -> InsnNode {
        let mut invoke = InsnNode::invoke(InvokeType::Static, 0, Vec::new());
        invoke.payload.reference = Some(MemberReference::Method(reference(target)));
        invoke
    }

    #[test]
    fn no_return_call_removes_only_normal_continuation() {
        let mut helper = graph("fail");
        let mut helper_entry = Block::new(0);
        helper_entry.push(InsnNode::throw(crate::ir::InsnArg::lit(
            0,
            ArgType::object("java/lang/Throwable"),
        )));
        helper.add_block(helper_entry);

        let mut caller = graph("caller");
        let mut entry = Block::new(0);
        entry.push(call("fail"));
        entry.push(InsnNode::goto(1));
        caller.add_block(entry);
        let mut normal = Block::new(1);
        normal.push(InsnNode::return_void());
        caller.add_block(normal);
        let mut caught = Block::new(2);
        caught.push(InsnNode::return_void());
        caller.add_block(caught);
        caller.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);
        caller.add_edge(BlockId::new(0), BlockId::new(2), EdgeKind::Exception);

        let summary = MethodTermination::analyze([&helper, &caller]);
        assert!(summary.apply(&mut caller));
        let entry = caller.block(BlockId::new(0)).expect("entry");
        assert_eq!(entry.insns.len(), 1);
        assert!(entry.insns[0].payload.no_return);
        assert_eq!(
            caller.successors_with_kind(BlockId::new(0)),
            &[(BlockId::new(2), EdgeKind::Exception)]
        );
    }

    #[test]
    fn mutually_recursive_calls_have_no_normal_completion() {
        let mut left = graph("left");
        let mut left_entry = Block::new(0);
        left_entry.push(call("right"));
        left_entry.push(InsnNode::goto(1));
        left.add_block(left_entry);
        let mut left_return = Block::new(1);
        left_return.push(InsnNode::return_void());
        left.add_block(left_return);
        left.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);

        let mut right = graph("right");
        let mut right_entry = Block::new(0);
        right_entry.push(call("left"));
        right_entry.push(InsnNode::goto(1));
        right.add_block(right_entry);
        let mut right_return = Block::new(1);
        right_return.push(InsnNode::return_void());
        right.add_block(right_return);
        right.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);

        let summary = MethodTermination::analyze([&left, &right]);
        assert!(summary.apply(&mut left));
        assert!(summary.apply(&mut right));
    }

    #[test]
    fn kotlin_reification_markers_preserve_source_continuation() {
        let marker = MethodReference {
            owner: ArgType::object("kotlin/jvm/internal/Intrinsics"),
            name: "reifiedOperationMarker".to_string(),
            descriptor: MethodDescriptor {
                parameters: vec![ArgType::INT, ArgType::object("java/lang/String")],
                return_type: ArgType::VOID,
            },
        };
        assert!(preserves_source_continuation(&marker));
        let mut class_reification = marker.clone();
        class_reification.name = "needClassReification".to_string();
        assert!(preserves_source_continuation(&class_reification));
        let mut explicit_throw = marker.clone();
        explicit_throw.name = "throwUndefinedForReified".to_string();
        assert!(!preserves_source_continuation(&explicit_throw));

        let mut marker_body = CFG::with_method(MethodContext::new(
            marker.owner.clone(),
            marker.name.clone(),
            marker.descriptor.clone(),
            true,
        ));
        let mut marker_entry = Block::new(0);
        marker_entry.push(InsnNode::throw(crate::ir::InsnArg::lit(
            0,
            ArgType::object("java/lang/Throwable"),
        )));
        marker_body.add_block(marker_entry);

        let mut caller = graph("caller");
        let mut entry = Block::new(0);
        let mut invoke = InsnNode::invoke(InvokeType::Static, 0, Vec::new());
        invoke.payload.reference = Some(MemberReference::Method(marker));
        entry.push(invoke);
        entry.push(InsnNode::goto(1));
        caller.add_block(entry);
        let mut normal = Block::new(1);
        normal.push(InsnNode::return_void());
        caller.add_block(normal);
        caller.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);

        let summary = MethodTermination::analyze([&marker_body, &caller]);
        assert!(!summary.apply(&mut caller));
        assert_eq!(caller.block(BlockId::new(0)).expect("entry").insns.len(), 2);
        assert_eq!(
            caller.successors_with_kind(BlockId::new(0)),
            &[(BlockId::new(1), EdgeKind::Normal)]
        );
    }
}
