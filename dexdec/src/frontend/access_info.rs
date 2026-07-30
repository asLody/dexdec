//! Access flags and modifiers
//!
//! This module defines access flags for classes, methods, and fields,
//! following the DEX file format specification.

use std::fmt;

/// Access flag constants for DEX file format
/// Reference: https://source.android.com/devices/tech/dalvik/dex-format#access-flags
pub mod access_flags {
    pub const PUBLIC: u32 = 0x0001;
    pub const PRIVATE: u32 = 0x0002;
    pub const PROTECTED: u32 = 0x0004;
    pub const STATIC: u32 = 0x0008;
    pub const FINAL: u32 = 0x0010;
    pub const SYNCHRONIZED: u32 = 0x0020;
    pub const VOLATILE: u32 = 0x0040; // For fields
    pub const BRIDGE: u32 = 0x0040; // For methods
    pub const TRANSIENT: u32 = 0x0080; // For fields
    pub const VARARGS: u32 = 0x0080; // For methods
    pub const NATIVE: u32 = 0x0100;
    pub const INTERFACE: u32 = 0x0200;
    pub const ABSTRACT: u32 = 0x0400;
    pub const STRICT: u32 = 0x0800; // strictfp
    pub const SYNTHETIC: u32 = 0x1000;
    pub const ANNOTATION: u32 = 0x2000;
    pub const ENUM: u32 = 0x4000;
    pub const CONSTRUCTOR: u32 = 0x10000; // method only
    pub const DECLARED_SYNCHRONIZED: u32 = 0x20000; // method only
}

/// Access flag enum (unique values only, context-dependent meanings handled via flag_type)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccessFlag {
    Public,
    Private,
    Protected,
    Static,
    Final,
    Synchronized,
    Volatile,  // For fields (same bit as Bridge for methods)
    Bridge,    // For methods (same bit as Volatile for fields)
    Transient, // For fields (same bit as Varargs for methods)
    Varargs,   // For methods (same bit as Transient for fields)
    Native,
    Interface,
    Abstract,
    Strict,
    Synthetic,
    Annotation,
    Enum,
    Constructor,
    DeclaredSynchronized,
}

/// Access flag type (class, method, or field)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccessFlagType {
    Class,
    Method,
    Field,
}

/// Container for access flags with utility methods
#[derive(Clone, Copy, PartialEq, Eq, Default)]
pub struct AccessInfo {
    /// Raw access flags value
    flags: u32,
    /// Type of the access info (class, method, field)
    flag_type: AccessFlagType,
}

impl Default for AccessFlagType {
    fn default() -> Self {
        AccessFlagType::Class
    }
}

impl AccessInfo {
    /// Create new access info
    pub fn new(flags: u32, flag_type: AccessFlagType) -> Self {
        Self { flags, flag_type }
    }

    /// Create access info for a class
    pub fn for_class(flags: u32) -> Self {
        Self::new(flags, AccessFlagType::Class)
    }

    /// Create access info for a method
    pub fn for_method(flags: u32) -> Self {
        Self::new(flags, AccessFlagType::Method)
    }

    /// Create access info for a field
    pub fn for_field(flags: u32) -> Self {
        Self::new(flags, AccessFlagType::Field)
    }

    /// Get raw flags value
    #[inline]
    pub fn raw(&self) -> u32 {
        self.flags
    }

    /// Get flag type
    #[inline]
    pub fn flag_type(&self) -> AccessFlagType {
        self.flag_type
    }

    // ==================== Visibility ====================

    #[inline]
    pub fn is_public(&self) -> bool {
        self.has_flag(AccessFlag::Public)
    }

    #[inline]
    pub fn is_private(&self) -> bool {
        self.has_flag(AccessFlag::Private)
    }

    #[inline]
    pub fn is_protected(&self) -> bool {
        self.has_flag(AccessFlag::Protected)
    }

    /// Package-private (no visibility modifier)
    #[inline]
    pub fn is_package_private(&self) -> bool {
        !self.is_public() && !self.is_private() && !self.is_protected()
    }

    // ==================== Modifiers ====================

    #[inline]
    pub fn is_static(&self) -> bool {
        self.has_flag(AccessFlag::Static)
    }

    #[inline]
    pub fn is_final(&self) -> bool {
        self.has_flag(AccessFlag::Final)
    }

    #[inline]
    pub fn is_abstract(&self) -> bool {
        self.has_flag(AccessFlag::Abstract)
    }

    #[inline]
    pub fn is_native(&self) -> bool {
        self.has_flag(AccessFlag::Native)
    }

    #[inline]
    pub fn is_synthetic(&self) -> bool {
        self.has_flag(AccessFlag::Synthetic)
    }

    // ==================== Method-specific ====================

    #[inline]
    pub fn is_synchronized(&self) -> bool {
        self.has_flag(AccessFlag::Synchronized)
    }

    #[inline]
    pub fn is_bridge(&self) -> bool {
        self.flag_type == AccessFlagType::Method && self.has_flag(AccessFlag::Bridge)
    }

    #[inline]
    pub fn is_varargs(&self) -> bool {
        self.flag_type == AccessFlagType::Method && self.has_flag(AccessFlag::Varargs)
    }

    #[inline]
    pub fn is_strict(&self) -> bool {
        self.has_flag(AccessFlag::Strict)
    }

    #[inline]
    pub fn is_constructor(&self) -> bool {
        self.has_flag(AccessFlag::Constructor)
    }

    #[inline]
    pub fn is_declared_synchronized(&self) -> bool {
        self.has_flag(AccessFlag::DeclaredSynchronized)
    }

    // ==================== Field-specific ====================

    #[inline]
    pub fn is_volatile(&self) -> bool {
        self.flag_type == AccessFlagType::Field && self.has_flag(AccessFlag::Volatile)
    }

    #[inline]
    pub fn is_transient(&self) -> bool {
        self.flag_type == AccessFlagType::Field && self.has_flag(AccessFlag::Transient)
    }

    // ==================== Class-specific ====================

    #[inline]
    pub fn is_interface(&self) -> bool {
        self.has_flag(AccessFlag::Interface)
    }

    #[inline]
    pub fn is_annotation(&self) -> bool {
        self.has_flag(AccessFlag::Annotation)
    }

    #[inline]
    pub fn is_enum(&self) -> bool {
        self.has_flag(AccessFlag::Enum)
    }

    // ==================== Utility ====================

    /// Convert AccessFlag enum to its raw value based on context
    fn flag_to_raw(&self, flag: AccessFlag) -> u32 {
        use access_flags::*;
        match flag {
            AccessFlag::Public => PUBLIC,
            AccessFlag::Private => PRIVATE,
            AccessFlag::Protected => PROTECTED,
            AccessFlag::Static => STATIC,
            AccessFlag::Final => FINAL,
            AccessFlag::Synchronized => SYNCHRONIZED,
            AccessFlag::Volatile => VOLATILE,
            AccessFlag::Bridge => BRIDGE,
            AccessFlag::Transient => TRANSIENT,
            AccessFlag::Varargs => VARARGS,
            AccessFlag::Native => NATIVE,
            AccessFlag::Interface => INTERFACE,
            AccessFlag::Abstract => ABSTRACT,
            AccessFlag::Strict => STRICT,
            AccessFlag::Synthetic => SYNTHETIC,
            AccessFlag::Annotation => ANNOTATION,
            AccessFlag::Enum => ENUM,
            AccessFlag::Constructor => CONSTRUCTOR,
            AccessFlag::DeclaredSynchronized => DECLARED_SYNCHRONIZED,
        }
    }

    #[inline]
    fn has_flag(&self, flag: AccessFlag) -> bool {
        self.flags & self.flag_to_raw(flag) != 0
    }

    /// Set a flag
    pub fn set_flag(&mut self, flag: AccessFlag) {
        self.flags |= self.flag_to_raw(flag);
    }

    /// Clear a flag
    pub fn clear_flag(&mut self, flag: AccessFlag) {
        self.flags &= !self.flag_to_raw(flag);
    }

    /// Create a modified copy with different flags
    pub fn with_flags(&self, flags: u32) -> Self {
        Self::new(flags, self.flag_type)
    }

    /// Visibility level for comparison
    pub fn visibility_level(&self) -> u8 {
        if self.is_public() {
            3
        } else if self.is_protected() {
            2
        } else if self.is_package_private() {
            1
        } else {
            0 // private
        }
    }

    /// Build modifier string for Kotlin source code
    pub fn to_modifier_string(&self) -> String {
        let mut parts = Vec::new();

        // Visibility
        if self.is_public() {
            parts.push("public");
        } else if self.is_private() {
            parts.push("private");
        } else if self.is_protected() {
            parts.push("protected");
        }

        // Other modifiers
        if self.is_static() {
            parts.push("static");
        }
        if self.is_final() {
            parts.push("final");
        }
        if self.is_abstract() {
            parts.push("abstract");
        }
        if self.is_native() {
            parts.push("native");
        }
        if self.is_synchronized() && !self.is_declared_synchronized() {
            parts.push("synchronized");
        }
        if self.is_strict() {
            parts.push("strictfp");
        }
        if self.is_transient() {
            parts.push("transient");
        }
        if self.is_volatile() {
            parts.push("volatile");
        }

        parts.join(" ")
    }
}

impl fmt::Debug for AccessInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AccessInfo({:#06x}, {:?})", self.flags, self.flag_type)
    }
}

impl fmt::Display for AccessInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_modifier_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_access_flags() {
        let info = AccessInfo::for_method(0x0001 | 0x0008); // public static
        assert!(info.is_public());
        assert!(info.is_static());
        assert!(!info.is_private());
        assert!(!info.is_final());
    }

    #[test]
    fn test_modifier_string() {
        let info = AccessInfo::for_method(0x0001 | 0x0008 | 0x0010); // public static final
        assert_eq!(info.to_modifier_string(), "public static final");
    }

    #[test]
    fn test_visibility_level() {
        let public = AccessInfo::for_class(0x0001);
        let protected = AccessInfo::for_class(0x0004);
        let private = AccessInfo::for_class(0x0002);
        let package = AccessInfo::for_class(0x0000);

        assert_eq!(public.visibility_level(), 3);
        assert_eq!(protected.visibility_level(), 2);
        assert_eq!(package.visibility_level(), 1);
        assert_eq!(private.visibility_level(), 0);
    }
}
