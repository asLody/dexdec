//! DEX Frontend - Parse DEX structure into IR-ready format
//!
//! This module handles DEX file parsing and provides structures for
//! classes, methods, and fields similar to jadx's node design.
//!
//! ## Architecture
//!
//! ```text
//! DexFile (rusty-dex)
//!     │
//!     ▼
//! ┌─────────────────┐
//! │  DexFileReader  │  Load and cache DEX data
//! └─────────────────┘
//!     │
//!     ▼
//! ┌─────────────────┐
//! │    ClassNode    │  Class information + methods + fields
//! └─────────────────┘
//!     │
//!     ├──▶ MethodNode  (code, signatures, access flags)
//!     │
//!     └──▶ FieldNode   (type, access flags)
//! ```

mod access_info;
mod analysis_diagnostic;
mod class_node;
mod dex_reader;
mod field_node;
pub mod kotlin_metadata;
mod metadata;
mod method_node;

pub use access_info::*;
pub use analysis_diagnostic::*;
pub use class_node::*;
pub use dex_reader::*;
pub use field_node::*;
pub use metadata::*;
pub use method_node::*;
