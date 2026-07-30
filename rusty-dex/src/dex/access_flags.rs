#![allow(non_camel_case_types)]

//! Helper functions to manipulate access flags
//!
//! Access flags are stored as an unsigned 32 bits integer and can be used for classes, fields, or
//! methods. In this module we define structs to represent these flags and help methods to parse
//! and print them.
//!
//! # Example
//!
//! ```
//! use rusty_dex::dex::access_flags::{ AccessFlag, AccessFlagType };
//!
//! let flags = AccessFlag::parse(0x0001_0009, AccessFlagType::Method);
//!
//! assert_eq!(flags, vec![AccessFlag::ACC_PUBLIC,
//!                        AccessFlag::ACC_STATIC,
//!                        AccessFlag::ACC_CONSTRUCTOR]);
//! ```

use log::warn;
use std::fmt;

/// Representation of the different access flag types: for classes, fields, or methods
#[derive(Debug)]
pub enum AccessFlagType {
    /// Flag for a class
    Class,
    /// Flag for a class field
    Field,
    /// Flag for a method
    Method,
}

/// Implementation of the `Display` trait for access flag types
impl fmt::Display for AccessFlagType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AccessFlagType::Class => {
                write!(f, "class")
            }
            AccessFlagType::Field => {
                write!(f, "field")
            }
            AccessFlagType::Method => {
                write!(f, "method")
            }
        }
    }
}

/// Representation of the different access flag
///
/// Bitfields of these flags are used to indicate the accessibility and overall properties of
/// classes and class members.
#[derive(Debug, PartialEq)]
pub enum AccessFlag {
    /// Public: visible everywhere
    ACC_PUBLIC,
    /// Private: only visible to defining class
    ACC_PRIVATE,
    /// Protected: visible to package and subclasses
    ACC_PROTECTED,
    /// Static: meaning depends of where the flag is used
    ///   * for classes: is not constructed with an outer `this` reference
    ///   * for methods: does not take a `this` argument
    ///   * for fields: global to defining class
    ACC_STATIC,
    /// Final: meaning depends of where the flag is used
    ///   * for classes: not subclassable
    ///   * for methods: not overridable
    ///   * for fields: immutable after construction
    ACC_FINAL,
    /// Synchronized (only valid for methods): associated lock automatically
    /// acquired around call to this method.
    /// Note: only valid to set when `ACC_NATIVE` is also set.
    ACC_SYNCHRONIZED,
    /// Volatile (only valid for fields): special access rules to help with
    /// thread safety
    ACC_VOLATILE,
    /// Bridge (only valid for methods): method added automatically by the
    /// compiler as a type-safe bridge
    ACC_BRIDGE,
    /// Transient (only valid for fields): the field must not be saved by
    /// default serialization
    ACC_TRANSIENT,
    /// Varargs (only valid for methods): the last argument to this method
    /// should be treated as a "rest" argument by the compiler
    ACC_VARARGS,
    /// Native (only valid for methods): this method is implemented in
    /// native code
    ACC_NATIVE,
    /// Interface (only valid for classes): multiply-implementable abstract class
    ACC_INTERFACE,
    /// Abstract (only valid for classes and methods):
    ///   * for classes: not directly instantiable
    ///   * for methods: unimplemented by this class
    ACC_ABSTRACT,
    /// Strict floating-point (only valid for methods): strict rules for
    /// floating-point arithmetic
    ACC_STRICT,
    /// Synthetic: not directly defined in source code
    ACC_SYNTHETIC,
    /// Annotation (only valid for classes): declared as an annotation class
    ACC_ANNOTATION,
    /// Enum (only valid for classes and fields):
    ///   * for classes: declared as an enumerated type
    ///   * for fields: declared as an enumerated value
    ACC_ENUM,
    /// Constructor (only valid for methods): contructor method
    ACC_CONSTRUCTOR,
    /// Declared synchronized (only valid for methods): method declared
    /// as `synchronized`
    ACC_DECLARED_SYNCHRONIZED,
}

impl AccessFlag {
    /// Converts a raw flag (an unsigned 32 bits integer) into a vector for access flags
    ///
    /// The result values will be different depending on where the type is used (for a class, a
    /// method, or a field)
    pub fn parse(raw: u32, for_type: AccessFlagType) -> Vec<Self> {
        let mut flags = Vec::new();

        if raw & 0x01 != 0 {
            flags.push(AccessFlag::ACC_PUBLIC);
        }
        if raw & 0x02 != 0 {
            flags.push(AccessFlag::ACC_PRIVATE);
        }
        if raw & 0x04 != 0 {
            flags.push(AccessFlag::ACC_PROTECTED);
        }
        if raw & 0x08 != 0 {
            flags.push(AccessFlag::ACC_STATIC);
        }
        if raw & 0x10 != 0 {
            flags.push(AccessFlag::ACC_FINAL);
        }
        if raw & 0x20 != 0 {
            match for_type {
                AccessFlagType::Method => {
                    flags.push(AccessFlag::ACC_SYNCHRONIZED);
                }
                _ => {
                    warn!("Ignoring invalid flag for {for_type}: 0x20");
                }
            }
        }
        if raw & 0x40 != 0 {
            match for_type {
                AccessFlagType::Class => {
                    warn!("Ignoring invalid flag for {for_type}: 0x40");
                }
                AccessFlagType::Field => {
                    flags.push(AccessFlag::ACC_VOLATILE);
                }
                AccessFlagType::Method => {
                    flags.push(AccessFlag::ACC_BRIDGE);
                }
            }
        }
        if raw & 0x80 != 0 {
            match for_type {
                AccessFlagType::Class => {
                    warn!("Ignoring invalid flag for {for_type}: 0x80");
                }
                AccessFlagType::Field => {
                    flags.push(AccessFlag::ACC_TRANSIENT);
                }
                AccessFlagType::Method => {
                    flags.push(AccessFlag::ACC_VARARGS);
                }
            }
        }
        if raw & 0x100 != 0 {
            match for_type {
                AccessFlagType::Method => {
                    flags.push(AccessFlag::ACC_NATIVE);
                }
                _ => {
                    warn!("Ignoring invalid flag for {for_type}: 0x100");
                }
            }
        }
        if raw & 0x200 != 0 {
            match for_type {
                AccessFlagType::Class => {
                    flags.push(AccessFlag::ACC_INTERFACE);
                }
                _ => {
                    warn!("Ignoring invalid flag for {for_type}: 0x200");
                }
            }
        }
        if raw & 0x400 != 0 {
            match for_type {
                AccessFlagType::Field => {
                    warn!("Ignoring invalid flag for {for_type}: 0x400");
                }
                _ => {
                    flags.push(AccessFlag::ACC_ABSTRACT);
                }
            }
        }
        if raw & 0x800 != 0 {
            match for_type {
                AccessFlagType::Method => {
                    flags.push(AccessFlag::ACC_STRICT);
                }
                _ => {
                    warn!("Ignoring invalid flag for {for_type}: 0x800");
                }
            }
        }
        if raw & 0x1000 != 0 {
            flags.push(AccessFlag::ACC_SYNTHETIC);
        }
        if raw & 0x2000 != 0 {
            match for_type {
                AccessFlagType::Class => {
                    flags.push(AccessFlag::ACC_ANNOTATION);
                }
                _ => {
                    warn!("Ignoring invalid flag for {for_type}: 0x2000");
                }
            }
        }
        if raw & 0x4000 != 0 {
            match for_type {
                AccessFlagType::Method => {
                    warn!("Ignoring invalid flag for {for_type}: 0x4000");
                }
                _ => {
                    flags.push(AccessFlag::ACC_ENUM);
                }
            }
        }
        if raw & 0x8000 != 0 {
            warn!("Ignoring invalid (unused) flag: 0x8000");
        }
        if raw & 0x10000 != 0 {
            match for_type {
                AccessFlagType::Method => {
                    flags.push(AccessFlag::ACC_CONSTRUCTOR);
                }
                _ => {
                    warn!("Ignoring invalid flag for {for_type}: 0x10000");
                }
            }
        }
        if raw & 0x20000 != 0 {
            match for_type {
                AccessFlagType::Method => {
                    flags.push(AccessFlag::ACC_DECLARED_SYNCHRONIZED);
                }
                _ => {
                    warn!("Ignoring invalid flag for {for_type}: 0x20000");
                }
            }
        }

        flags
    }

    /// Pretty print a vector of access flags
    pub fn vec_to_string(flags: &[AccessFlag]) -> String {
        let mut output = String::new();
        let flags_len = flags.len();

        for (idx, flag) in flags.iter().enumerate() {
            output.push_str(&flag.to_string());
            if idx < flags_len - 1 {
                output.push('|');
            }
        }

        output
    }
}

/// Implementation of the `Display` trait for access flags
impl fmt::Display for AccessFlag {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AccessFlag::ACC_PUBLIC => write!(f, "public"),
            AccessFlag::ACC_PRIVATE => write!(f, "private"),
            AccessFlag::ACC_PROTECTED => write!(f, "protected"),
            AccessFlag::ACC_STATIC => write!(f, "static"),
            AccessFlag::ACC_FINAL => write!(f, "final"),
            AccessFlag::ACC_SYNCHRONIZED => write!(f, "synchronized"),
            AccessFlag::ACC_VOLATILE => write!(f, "volatile"),
            AccessFlag::ACC_BRIDGE => write!(f, "bridge"),
            AccessFlag::ACC_TRANSIENT => write!(f, "transient"),
            AccessFlag::ACC_VARARGS => write!(f, "varargs"),
            AccessFlag::ACC_NATIVE => write!(f, "native"),
            AccessFlag::ACC_INTERFACE => write!(f, "interface"),
            AccessFlag::ACC_ABSTRACT => write!(f, "abstract"),
            AccessFlag::ACC_STRICT => write!(f, "strict"),
            AccessFlag::ACC_SYNTHETIC => write!(f, "synthetic"),
            AccessFlag::ACC_ANNOTATION => write!(f, "annotation"),
            AccessFlag::ACC_ENUM => write!(f, "enum"),
            AccessFlag::ACC_CONSTRUCTOR => write!(f, "constructor"),
            AccessFlag::ACC_DECLARED_SYNCHRONIZED => write!(f, "synchronized"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_access_flag_type_display() {
        let class_flag = AccessFlagType::Class;
        let field_flag = AccessFlagType::Field;
        let method_flag = AccessFlagType::Method;

        assert_eq!(class_flag.to_string(), "class");
        assert_eq!(field_flag.to_string(), "field");
        assert_eq!(method_flag.to_string(), "method");
    }

    #[test]
    fn test_access_flag_class_parse() {
        // Test with valid flags
        // Testing all at once because there is no semantics at play here
        let flags = AccessFlag::parse(0x3ffff, AccessFlagType::Class);
        assert_eq!(
            flags,
            vec![
                AccessFlag::ACC_PUBLIC,
                AccessFlag::ACC_PRIVATE,
                AccessFlag::ACC_PROTECTED,
                AccessFlag::ACC_STATIC,
                AccessFlag::ACC_FINAL,
                AccessFlag::ACC_INTERFACE,
                AccessFlag::ACC_ABSTRACT,
                AccessFlag::ACC_SYNTHETIC,
                AccessFlag::ACC_ANNOTATION,
                AccessFlag::ACC_ENUM
            ]
        );
    }

    #[test]
    fn test_access_flag_field_parse() {
        // Test with valid flags
        // Testing all at once because there is no semantics at play here
        let flags = AccessFlag::parse(0x3ffff, AccessFlagType::Field);
        assert_eq!(
            flags,
            vec![
                AccessFlag::ACC_PUBLIC,
                AccessFlag::ACC_PRIVATE,
                AccessFlag::ACC_PROTECTED,
                AccessFlag::ACC_STATIC,
                AccessFlag::ACC_FINAL,
                AccessFlag::ACC_VOLATILE,
                AccessFlag::ACC_TRANSIENT,
                AccessFlag::ACC_SYNTHETIC,
                AccessFlag::ACC_ENUM
            ]
        );
    }

    #[test]
    fn test_access_flag_method_parse() {
        // Test with valid flags
        // Testing all at once because there is no semantics at play here
        let flags = AccessFlag::parse(0x3ffff, AccessFlagType::Method);
        assert_eq!(
            flags,
            vec![
                AccessFlag::ACC_PUBLIC,
                AccessFlag::ACC_PRIVATE,
                AccessFlag::ACC_PROTECTED,
                AccessFlag::ACC_STATIC,
                AccessFlag::ACC_FINAL,
                AccessFlag::ACC_SYNCHRONIZED,
                AccessFlag::ACC_BRIDGE,
                AccessFlag::ACC_VARARGS,
                AccessFlag::ACC_NATIVE,
                AccessFlag::ACC_ABSTRACT,
                AccessFlag::ACC_STRICT,
                AccessFlag::ACC_SYNTHETIC,
                AccessFlag::ACC_CONSTRUCTOR,
                AccessFlag::ACC_DECLARED_SYNCHRONIZED
            ]
        );
    }
}
