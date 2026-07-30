//! Block Splitter
//!
//! Splits instruction list into basic blocks and builds CFG.

use std::collections::{BTreeSet, HashMap};

use super::block::{Block, BlockId, ExceptionHandler};
use super::cfg::{EdgeKind, MethodContext, CFG};
use super::insn::{InsnNode, InsnType};

/// Block splitter - builds CFG from instruction list
pub struct Splitter {
    method: MethodContext,
    insns: Vec<InsnNode>,
    handlers: Vec<ExceptionHandler>,
    registers: u32,
    ins: u32,
}

impl Splitter {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            method: MethodContext::synthetic(name),
            insns: Vec::new(),
            handlers: Vec::new(),
            registers: 0,
            ins: 0,
        }
    }

    pub fn instructions(mut self, insns: Vec<InsnNode>) -> Self {
        self.insns = insns;
        self
    }

    pub fn handlers(mut self, handlers: Vec<ExceptionHandler>) -> Self {
        self.handlers = handlers;
        self
    }

    pub fn registers(mut self, count: u32) -> Self {
        self.registers = count;
        self
    }

    pub fn ins(mut self, count: u32) -> Self {
        self.ins = count;
        self
    }
    pub fn method(mut self, method: MethodContext) -> Self {
        self.method = method;
        self
    }
    /// Build CFG
    pub fn build(mut self) -> CFG {
        let mut cfg = CFG::with_method(self.method.clone());
        cfg.registers = self.registers;
        cfg.ins = self.ins;
        cfg.handlers = self.handlers.clone();
        if self.insns.is_empty() {
            return cfg;
        }
        self.annotate_dispatch_metadata();

        // Find leaders
        let leaders = self.find_leaders();

        // Create blocks
        let offset_to_block = self.create_blocks(&mut cfg, &leaders);

        // Build edges
        self.build_edges(&mut cfg, &offset_to_block);

        cfg
    }

    fn annotate_dispatch_metadata(&mut self) {
        for index in 0..self.insns.len() {
            if self.insns[index].insn_type != InsnType::Switch {
                continue;
            }
            let default = self
                .insns
                .get(index + 1)
                .and_then(|instruction| i32::try_from(instruction.offset).ok());
            self.insns[index].payload.switch_default = default;
        }
    }

    fn find_leaders(&self) -> BTreeSet<u32> {
        let mut leaders = BTreeSet::new();
        let insn_offsets: BTreeSet<u32> = self.insns.iter().map(|insn| insn.offset).collect();

        // First instruction
        if let Some(first) = self.insns.first() {
            leaders.insert(first.offset);
        }

        // Try region boundaries and handler entries.
        //
        // Exception ranges are defined over instruction offsets, not existing
        // block boundaries. If a try starts or ends in the middle of a block,
        // structuring later on needs the CFG to already reflect that boundary.
        for eh in &self.handlers {
            if insn_offsets.contains(&eh.start) {
                leaders.insert(eh.start);
            }
            if insn_offsets.contains(&eh.end) {
                leaders.insert(eh.end);
            }
            leaders.insert(eh.handler);
        }

        // Branch targets and instructions after branches
        // Note: target in InsnNode is stored as absolute address by decoder
        for (i, insn) in self.insns.iter().enumerate() {
            match insn.insn_type {
                InsnType::Goto => {
                    // Keep control ownership independent from the effects in
                    // the lexical prefix. Exception regions can then own a
                    // non-throwing dispatch without also claiming preceding
                    // calls that lie outside the protected DEX interval.
                    leaders.insert(insn.offset);
                    if let Some(target) = insn.get_target() {
                        // target is already absolute address
                        leaders.insert(target as u32);
                    }
                    if let Some(next) = self.insns.get(i + 1) {
                        leaders.insert(next.offset);
                    }
                }
                InsnType::If => {
                    leaders.insert(insn.offset);
                    if let Some(target) = insn.get_target() {
                        // target is already absolute address
                        leaders.insert(target as u32);
                    }
                    if let Some(next) = self.insns.get(i + 1) {
                        leaders.insert(next.offset);
                    }
                }
                InsnType::Switch => {
                    leaders.insert(insn.offset);
                    if let Some(cases) = insn.get_switch_cases() {
                        for &(_, target) in cases {
                            // target is already absolute address
                            leaders.insert(target as u32);
                        }
                    }
                    if let Some(next) = self.insns.get(i + 1) {
                        leaders.insert(next.offset);
                    }
                }
                InsnType::Return | InsnType::Throw => {
                    if let Some(next) = self.insns.get(i + 1) {
                        leaders.insert(next.offset);
                    }
                }
                _ => {
                    // Instructions that can throw in try region
                    if insn.can_throw() && self.handlers.iter().any(|h| h.covers(insn.offset)) {
                        if let Some(next) = self.insns.get(i + 1) {
                            leaders.insert(next.offset);
                        }
                    }
                }
            }
        }

        leaders
    }

    fn create_blocks(&self, cfg: &mut CFG, leaders: &BTreeSet<u32>) -> HashMap<u32, BlockId> {
        let mut offset_to_block = HashMap::new();
        let leader_vec: Vec<u32> = leaders.iter().copied().collect();

        for (idx, &leader) in leader_vec.iter().enumerate() {
            let block_id = BlockId::new(idx as u32);
            offset_to_block.insert(leader, block_id);

            let mut block = Block::with_offset(block_id, leader);
            let next_leader = leader_vec.get(idx + 1).copied().unwrap_or(u32::MAX);

            for insn in &self.insns {
                if insn.offset >= leader && insn.offset < next_leader {
                    block.push(insn.clone());
                }
            }

            cfg.add_block(block);
        }

        if let Some(&entry) = self
            .insns
            .first()
            .and_then(|i| offset_to_block.get(&i.offset))
        {
            cfg.entry = entry;
        }

        offset_to_block
    }

    fn build_edges(&self, cfg: &mut CFG, offset_to_block: &HashMap<u32, BlockId>) {
        // Build instruction offset map
        let offsets: Vec<u32> = self.insns.iter().map(|i| i.offset).collect();
        let next_offset = |off: u32| -> Option<u32> {
            offsets
                .iter()
                .position(|&o| o == off)
                .and_then(|i| offsets.get(i + 1).copied())
        };

        // Collect edges first to avoid borrow issues
        let mut edges: Vec<(BlockId, BlockId, EdgeKind)> = Vec::new();

        for block in cfg.blocks.values() {
            let Some(term) = block.terminator() else {
                continue;
            };
            let block_id = block.id;

            match term.insn_type {
                InsnType::Goto => {
                    if let Some(target) = term.get_target() {
                        // target is already absolute address
                        let abs = target as u32;
                        if let Some(&to) = offset_to_block.get(&abs) {
                            edges.push((block_id, to, EdgeKind::Normal));
                        }
                    }
                }
                InsnType::If => {
                    if let Some(target) = term.get_target() {
                        // target is already absolute address
                        let abs = target as u32;
                        if let Some(&to) = offset_to_block.get(&abs) {
                            edges.push((block_id, to, EdgeKind::True));
                        }
                    }
                    if let Some(next) = next_offset(term.offset) {
                        if let Some(&to) = offset_to_block.get(&next) {
                            edges.push((block_id, to, EdgeKind::False));
                        }
                    }
                }
                InsnType::Switch => {
                    if let Some(cases) = term.get_switch_cases() {
                        for &(value, target) in cases {
                            // target is already absolute address
                            let abs = target as u32;
                            if let Some(&to) = offset_to_block.get(&abs) {
                                edges.push((block_id, to, EdgeKind::SwitchCase(value)));
                            }
                        }
                    }
                    if let Some(next) = next_offset(term.offset) {
                        if let Some(&to) = offset_to_block.get(&next) {
                            edges.push((block_id, to, EdgeKind::SwitchDefault));
                        }
                    }
                }
                InsnType::Return | InsnType::Throw => {}
                _ => {
                    if let Some(next) = next_offset(term.offset) {
                        if let Some(&to) = offset_to_block.get(&next) {
                            edges.push((block_id, to, EdgeKind::Normal));
                        }
                    }
                }
            }
        }

        // Exception edges
        let handlers = cfg.handlers.clone();
        for eh in &handlers {
            if let Some(&handler_id) = offset_to_block.get(&eh.handler) {
                for block in cfg.blocks.values() {
                    for insn in &block.insns {
                        if insn.can_throw() && eh.covers(insn.offset) {
                            edges.push((block.id, handler_id, EdgeKind::Exception));
                            break;
                        }
                    }
                }
            }
        }

        // Edge identity includes its kind. This preserves degenerate branches
        // whose true and false edges intentionally share one target.
        for (from, to, kind) in edges {
            cfg.add_edge(from, to, kind);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::block::ExceptionHandler as RawHandler;

    fn make_insn(offset: u32, ty: InsnType) -> InsnNode {
        let mut insn = InsnNode::new(ty, 0);
        insn.offset = offset;
        insn
    }

    #[test]
    fn test_linear() {
        let insns = vec![
            make_insn(0, InsnType::Const),
            make_insn(2, InsnType::Const),
            make_insn(4, InsnType::Return),
        ];
        let cfg = Splitter::new("test").instructions(insns).build();
        assert_eq!(cfg.num_blocks(), 1);
    }

    #[test]
    fn test_branch() {
        let mut if_insn = InsnNode::new(InsnType::If, 0);
        if_insn.offset = 0;
        if_insn.payload.target = Some(4); // jump to offset 4

        let insns = vec![
            if_insn,
            make_insn(2, InsnType::Return),
            make_insn(4, InsnType::Return),
        ];
        let cfg = Splitter::new("test").instructions(insns).build();

        // Leaders: 0, 2, 4
        assert_eq!(cfg.num_blocks(), 3);

        let succs: Vec<_> = cfg.successors(0u32).collect();
        assert_eq!(succs.len(), 2);
    }

    #[test]
    fn test_exception_edges() {
        // Test: try { invoke() } catch { ... }
        // Layout:
        //   0: invoke  <- can throw, in try region
        //   2: return
        //   4: move-exception <- handler entry
        //   6: return
        let insns = vec![
            make_insn(0, InsnType::Invoke), // can_throw = true
            make_insn(2, InsnType::Return),
            make_insn(4, InsnType::MoveException),
            make_insn(6, InsnType::Return),
        ];

        let handlers = vec![RawHandler::new(
            0,
            4,
            4,
            Some("Ljava/lang/Exception;".parse().unwrap()),
        )];

        let cfg = Splitter::new("test")
            .instructions(insns)
            .handlers(handlers)
            .build();

        // Should have multiple blocks:
        // - Block 0: offset 0 (invoke)
        // - Block 1: offset 2 (return after invoke - because invoke can throw)
        // - Block 2: offset 4 (handler entry)
        assert!(
            cfg.num_blocks() >= 3,
            "should have at least 3 blocks, got {}",
            cfg.num_blocks()
        );

        // Find the block containing invoke instruction
        let invoke_block = cfg
            .blocks
            .values()
            .find(|b| {
                b.insns
                    .iter()
                    .any(|i| matches!(i.insn_type, InsnType::Invoke))
            })
            .expect("should have invoke block");

        // Find the handler block
        let handler_block = cfg
            .blocks
            .values()
            .find(|b| b.offset == 4)
            .expect("should have handler block");

        // Check that there's an exception edge from invoke block to handler
        let has_exception_edge = cfg
            .successors_with_kind(invoke_block.id)
            .iter()
            .any(|(to, kind)| *to == handler_block.id && *kind == EdgeKind::Exception);

        assert!(
            has_exception_edge,
            "should have exception edge from invoke block to handler block"
        );
    }

    #[test]
    fn test_exception_edge_kind() {
        // Verify that exception edges are marked as EdgeKind::Exception
        let insns = vec![
            make_insn(0, InsnType::Invoke),
            make_insn(2, InsnType::Return),
            make_insn(4, InsnType::MoveException),
            make_insn(6, InsnType::Return),
        ];

        let handlers = vec![
            RawHandler::new(0, 4, 4, None), // catch-all
        ];

        let cfg = Splitter::new("test")
            .instructions(insns)
            .handlers(handlers)
            .build();

        // Count exception edges
        let exception_edge_count: usize = cfg
            .blocks
            .values()
            .flat_map(|b| cfg.successors_with_kind(b.id))
            .filter(|(_, kind)| *kind == EdgeKind::Exception)
            .count();

        assert!(
            exception_edge_count >= 1,
            "should have at least one exception edge"
        );
    }

    #[test]
    fn test_handler_is_leader() {
        // Handler entry should always be a leader
        let insns = vec![
            make_insn(0, InsnType::Const),
            make_insn(2, InsnType::Return),
            make_insn(4, InsnType::MoveException),
            make_insn(6, InsnType::Return),
        ];

        let handlers = vec![RawHandler::new(0, 2, 4, None)];

        let cfg = Splitter::new("test")
            .instructions(insns)
            .handlers(handlers)
            .build();

        // Handler at offset 4 should be its own block
        let handler_block = cfg.blocks.values().find(|b| b.offset == 4);

        assert!(
            handler_block.is_some(),
            "handler entry should be a leader and have its own block"
        );
    }

    #[test]
    fn test_try_boundaries_split_mid_block() {
        let insns = vec![
            make_insn(0, InsnType::Sget),
            make_insn(2, InsnType::MonitorEnter),
            make_insn(4, InsnType::Arith),
            make_insn(6, InsnType::Return),
            make_insn(8, InsnType::MoveException),
            make_insn(10, InsnType::Return),
        ];

        let handlers = vec![RawHandler::new(4, 6, 8, None)];

        let cfg = Splitter::new("mid_block_try")
            .instructions(insns)
            .handlers(handlers)
            .build();

        assert!(
            cfg.blocks.values().any(|block| block.offset == 0),
            "expected pre-try prefix block at offset 0"
        );
        assert!(
            cfg.blocks.values().any(|block| block.offset == 4),
            "expected try body block starting at protected offset 4"
        );

        let prefix_block = cfg
            .blocks
            .values()
            .find(|block| block.offset == 0)
            .expect("missing prefix block");
        assert!(
            prefix_block.insns.iter().all(|insn| insn.offset < 4),
            "prefix block should not contain protected instructions: {:?}",
            prefix_block.insns
        );

        let try_block = cfg
            .blocks
            .values()
            .find(|block| block.offset == 4)
            .expect("missing try block");
        assert!(
            try_block.insns.iter().any(|insn| insn.offset == 4),
            "try block should contain protected throwing instruction"
        );
        assert!(
            try_block.insns.iter().all(|insn| insn.offset >= 4),
            "try block should not contain pre-try instructions: {:?}",
            try_block.insns
        );
    }
}
