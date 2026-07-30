use super::{KotlinClassType, KotlinType};

/// Kotlin source contracts for JVM platform types.
///
/// A JVM class can have two distinct source roles: a value type alias used in
/// declarations and a namespace used to access static members. Keeping those
/// roles separate preserves the JVM member identity without leaking Java
/// wrapper names into Kotlin signatures.
pub(crate) struct KotlinJvmBuiltins;

impl KotlinJvmBuiltins {
    pub(crate) fn value_type_alias(binary_name: &str) -> Option<&'static str> {
        Some(match binary_name {
            "java.lang.Object" => "Any",
            "java.lang.Boolean" => "Boolean",
            "java.lang.Byte" => "Byte",
            "java.lang.Character" => "Char",
            "java.lang.Short" => "Short",
            "java.lang.Integer" => "Int",
            "java.lang.Long" => "Long",
            "java.lang.Float" => "Float",
            "java.lang.Double" => "Double",
            _ => return None,
        })
    }

    pub(crate) fn static_namespace(internal_name: &str) -> Option<KotlinType> {
        let source_name = match internal_name {
            "java/lang/Boolean" => "java.lang.Boolean",
            "java/lang/Byte" => "java.lang.Byte",
            "java/lang/Character" => "java.lang.Character",
            "java/lang/Short" => "java.lang.Short",
            "java/lang/Integer" => "java.lang.Integer",
            "java/lang/Long" => "java.lang.Long",
            "java/lang/Float" => "java.lang.Float",
            "java/lang/Double" => "java.lang.Double",
            _ => return None,
        };
        Some(KotlinType::Class(KotlinClassType::from_source(source_name)))
    }
}
