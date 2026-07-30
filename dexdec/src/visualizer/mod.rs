//! Visualization module for dexdec
//!
//! This module provides visualization capabilities for various IR structures,
//! including CFG visualization in DOT format.

pub mod cfg_dot;

pub use cfg_dot::{method_to_dot, method_to_text};
