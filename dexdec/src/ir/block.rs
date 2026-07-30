//! Basic Blocks
//!
//! Minimal block definition - only ID, offset, and instructions.

use super::insn::InsnNode;
use std::fmt;

/// Block identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct BlockId(pub u32);

impl BlockId {
    pub const fn new(id: u32) -> Self {
        Self(id)
    }
    pub const fn raw(self) -> u32 {
        self.0
    }
    pub const INVALID: BlockId = BlockId(u32::MAX);
}

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "B{}", self.0)
    }
}

impl From<u32> for BlockId {
    fn from(id: u32) -> Self {
        Self(id)
    }
}

impl From<BlockId> for u32 {
    fn from(id: BlockId) -> Self {
        id.0
    }
}

/// Basic block
#[derive(Debug, Clone)]
pub struct Block {
    pub id: BlockId,
    pub offset: u32,
    pub insns: Vec<InsnNode>,
    pub synthetic: bool,
}

impl Block {
    pub fn new(id: impl Into<BlockId>) -> Self {
        let id = id.into();
        Self {
            id,
            offset: id.raw(),
            insns: Vec::new(),
            synthetic: false,
        }
    }

    pub fn with_offset(id: impl Into<BlockId>, offset: u32) -> Self {
        Self {
            id: id.into(),
            offset,
            insns: Vec::new(),
            synthetic: false,
        }
    }

    pub fn synthetic(id: impl Into<BlockId>) -> Self {
        let id = id.into();
        Self {
            id,
            offset: u32::MAX,
            insns: Vec::new(),
            synthetic: true,
        }
    }

    pub fn push(&mut self, insn: InsnNode) {
        self.insns.push(insn);
    }

    pub fn terminator(&self) -> Option<&InsnNode> {
        self.insns.last()
    }
}

impl fmt::Display for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{:04x}", self.id, self.offset)
    }
}

/// Raw exception handler from DEX
#[derive(Debug, Clone)]
pub struct ExceptionHandler {
    pub start: u32,
    pub end: u32,
    pub handler: u32,
    pub catch_type: Option<crate::ir::ArgType>,
}

impl ExceptionHandler {
    pub fn new(start: u32, end: u32, handler: u32, catch_type: Option<crate::ir::ArgType>) -> Self {
        Self {
            start,
            end,
            handler,
            catch_type,
        }
    }

    pub fn is_catch_all(&self) -> bool {
        self.catch_type.is_none()
    }

    pub fn covers(&self, offset: u32) -> bool {
        offset >= self.start && offset < self.end
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_block_id() {
        let id: BlockId = 42.into();
        assert_eq!(id.raw(), 42);
        assert_eq!(format!("{}", id), "B42");
    }

    #[test]
    fn test_block() {
        let block = Block::new(0u32);
        assert!(block.insns.is_empty());
        assert_eq!(block.id, BlockId::new(0));
    }
}
