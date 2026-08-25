//! Instruction Decoder
//!
//! This module decodes Dalvik bytecode into IR instructions from the raw
//! `MethodCode` format.

pub mod method_decoder;

pub use method_decoder::{DecodeResult, MethodDecoder};
