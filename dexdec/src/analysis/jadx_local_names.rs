//! Local names that follow JADX's `ApplyVariableNames` and
//! `ProcessKotlinInternals` rules.
//!
//! JADX never falls back to a DEX register (`v12`). It names a local from a
//! Kotlin `Intrinsics` check string when one exists, otherwise from the value's
//! type or defining call.

use std::collections::BTreeMap;

use crate::ir::{
    ArgType, InsnType, LiteralArg, MemberReference, PrimitiveType, SemanticExpression,
    SemanticNode, SemanticOperation, SemanticVisitor,
};

const OBJECT_ALIASES: &[(&str, &str)] = &[
    ("java.lang.String", "str"),
    ("kotlin.String", "str"),
    ("java.lang.Class", "cls"),
    ("java.lang.Throwable", "th"),
    ("java.lang.Object", "obj"),
    ("kotlin.Any", "obj"),
    ("java.util.Iterator", "it"),
    ("kotlin.collections.Iterator", "it"),
    ("java.util.HashMap", "map"),
    ("java.lang.Boolean", "bool"),
    ("java.lang.Short", "sh"),
    ("java.lang.Integer", "num"),
    ("java.lang.Character", "ch"),
    ("java.lang.Byte", "b"),
    ("java.lang.Float", "f"),
    ("java.lang.Long", "l"),
    ("java.lang.Double", "d"),
    ("java.lang.StringBuilder", "sb"),
    ("java.lang.Exception", "exc"),
];

const INVOKE_PREFIXES: &[&str] = &["get", "set", "to", "parse", "read", "format"];

pub(crate) fn primitive_local_name(primitive: PrimitiveType) -> Option<&'static str> {
    match primitive {
        PrimitiveType::Boolean => Some("z"),
        PrimitiveType::Byte => Some("b"),
        PrimitiveType::Short => Some("s"),
        PrimitiveType::Char => Some("c"),
        PrimitiveType::Int => Some("i"),
        PrimitiveType::Long => Some("j"),
        PrimitiveType::Float => Some("f"),
        PrimitiveType::Double => Some("d"),
        PrimitiveType::Void | PrimitiveType::Object | PrimitiveType::Array => None,
    }
}

pub(crate) fn object_alias(qualified: &str) -> Option<&'static str> {
    OBJECT_ALIASES
        .iter()
        .find(|(name, _)| *name == qualified)
        .map(|(_, alias)| *alias)
}

pub(crate) fn class_local_name(simple: &str) -> String {
    if simple.is_empty() {
        return "obj".to_string();
    }
    let alphabetic = simple
        .chars()
        .filter(|character| character.is_alphabetic())
        .collect::<Vec<_>>();
    if !alphabetic.is_empty() && alphabetic.iter().all(|character| character.is_uppercase()) {
        return simple.to_lowercase();
    }
    let mut characters = simple.chars();
    let Some(first) = characters.next() else {
        return "obj".to_string();
    };
    let mut lowered = first.to_lowercase().collect::<String>();
    lowered.extend(characters);
    if lowered != simple {
        return lowered;
    }
    format!("{simple}Var")
}

pub(crate) fn array_local_name(element: &str) -> String {
    format!("{element}Arr")
}

pub(crate) fn class_local_name_from_segments<'a>(
    segments: impl IntoIterator<Item = &'a str>,
) -> String {
    let segments = segments.into_iter().collect::<Vec<_>>();
    let qualified = segments.join(".");
    if let Some(alias) = object_alias(&qualified) {
        return alias.to_string();
    }
    class_local_name(segments.last().copied().unwrap_or(""))
}

pub(crate) fn trim_intrinsic_name(name: &str) -> &str {
    name.strip_prefix("$this$")
        .or_else(|| name.strip_prefix('$'))
        .unwrap_or(name)
}

pub(crate) fn invoke_local_name(method: &str) -> Option<String> {
    if method == "iterator" {
        return Some("it".to_string());
    }
    if method == "getInstance" {
        return None;
    }
    for prefix in INVOKE_PREFIXES {
        if let Some(rest) = method.strip_prefix(prefix) {
            if rest
                .chars()
                .next()
                .is_some_and(|character| character.is_ascii_uppercase())
            {
                return Some(class_local_name(rest));
            }
        }
    }
    None
}

pub(crate) fn intrinsic_local_names(root: &SemanticNode) -> BTreeMap<u32, String> {
    let mut collector = IntrinsicNameCollector::default();
    collector.visit_node(root);
    collector.names
}

#[derive(Default)]
struct IntrinsicNameCollector {
    names: BTreeMap<u32, String>,
}

impl SemanticVisitor for IntrinsicNameCollector {
    fn enter_operation(&mut self, operation: &SemanticOperation) {
        if let Some((variable, name)) = intrinsic_binding(operation) {
            self.names.entry(variable).or_insert(name);
        }
    }
}

fn intrinsic_binding(operation: &SemanticOperation) -> Option<(u32, String)> {
    if operation.insn_type != InsnType::Invoke {
        return None;
    }
    let MemberReference::Method(method) = operation.payload.reference.as_ref()? else {
        return None;
    };
    if !is_kotlin_varname_source(method) {
        return None;
    }
    let operands = operation.operands();
    if operands.len() < 2 {
        return None;
    }
    let variable = register_variable(&operands[0])?;
    let name = const_string(operands.last()?)?;
    let name = trim_intrinsic_name(&name);
    if name.is_empty() {
        return None;
    }
    Some((variable, name.to_string()))
}

fn is_kotlin_varname_source(method: &crate::ir::MethodReference) -> bool {
    let parameters = &method.descriptor.parameters;
    if method.descriptor.return_type != ArgType::VOID {
        return false;
    }
    let string = ArgType::object("java/lang/String");
    let object = ArgType::object("java/lang/Object");
    let signature_ok = matches!(
        parameters.as_slice(),
        [left, right] if left == &object && right == &string
    ) || matches!(
        parameters.as_slice(),
        [left, middle, right] if left == &object && middle == &string && right == &string
    );
    if !signature_ok {
        return false;
    }
    let owner = method.owner.as_object().unwrap_or("");
    owner == "kotlin/jvm/internal/Intrinsics"
        || owner.ends_with("/Intrinsics")
        || method.name.starts_with("checkNotNull")
        || method.name.starts_with("checkParameterIsNotNull")
        || method.name.starts_with("checkExpressionValueIsNotNull")
}

fn register_variable(expression: &SemanticExpression) -> Option<u32> {
    match expression {
        SemanticExpression::Register(register) => register.code_var,
        _ => None,
    }
}

fn const_string(expression: &SemanticExpression) -> Option<String> {
    match expression {
        SemanticExpression::Operation(operation) if operation.insn_type == InsnType::ConstStr => {
            Some(operation.payload.string_value.as_ref()?.to_string_lossy())
        }
        SemanticExpression::Literal(LiteralArg { .. }) => None,
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primitive_names_match_jadx_short_names() {
        assert_eq!(primitive_local_name(PrimitiveType::Int), Some("i"));
        assert_eq!(primitive_local_name(PrimitiveType::Boolean), Some("z"));
        assert_eq!(primitive_local_name(PrimitiveType::Long), Some("j"));
    }

    #[test]
    fn object_aliases_match_jadx() {
        assert_eq!(object_alias("java.lang.String"), Some("str"));
        assert_eq!(object_alias("java.lang.Object"), Some("obj"));
        assert_eq!(object_alias("kotlin.Any"), Some("obj"));
    }

    #[test]
    fn class_and_array_names_match_jadx() {
        assert_eq!(class_local_name("FooBar"), "fooBar");
        assert_eq!(class_local_name("HTML"), "html");
        assert_eq!(class_local_name("v0"), "v0Var");
        assert_eq!(array_local_name("i"), "iArr");
        assert_eq!(
            class_local_name_from_segments(["java", "lang", "String"]),
            "str"
        );
    }

    #[test]
    fn intrinsic_and_invoke_names_match_jadx() {
        assert_eq!(trim_intrinsic_name("$this$foo"), "foo");
        assert_eq!(trim_intrinsic_name("$view"), "view");
        assert_eq!(invoke_local_name("getView"), Some("view".to_string()));
        assert_eq!(invoke_local_name("iterator"), Some("it".to_string()));
    }
}
