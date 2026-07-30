//! Instruction Decoder
//!
//! This module decodes Dalvik bytecode into IR instructions.
//! - `method_decoder`: Decodes our MethodCode format
//! - `insn_decoder`: Decodes rusty-dex CodeItem format

pub mod insn_decoder;
pub mod method_decoder;

pub use insn_decoder::{CodeDecodeResult, InsnDecoder};
pub use method_decoder::{DecodeResult, MethodDecoder};
