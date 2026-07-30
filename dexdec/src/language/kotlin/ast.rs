#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum KotlinPrimitiveType {
    Void,
    Boolean,
    Byte,
    Short,
    Char,
    Int,
    Long,
    Float,
    Double,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct KotlinIdentifier(String);

impl KotlinIdentifier {
    /// The DEX name this identifier was built from, where it survives.
    ///
    /// Escaping only wraps the original in backticks, so removing them recovers
    /// it exactly. A name that could not be escaped was encoded instead and is
    /// not recoverable; it is returned as it stands rather than guessed at.
    pub fn dex_name(&self) -> &str {
        self.0
            .strip_prefix('`')
            .and_then(|name| name.strip_suffix('`'))
            .unwrap_or(&self.0)
    }

    pub fn from_dex(value: &str) -> Self {
        if Self::is_source_identifier(value) && !Self::is_reserved(value) {
            return Self(value.to_string());
        }
        if Self::can_escape(value) {
            return Self(format!("`{value}`"));
        }
        let mut encoded = String::from("_dex_");
        if value.is_empty() {
            encoded.push_str("empty");
        } else {
            for character in value.chars() {
                encoded.push_str(&format!("{:X}_", character as u32));
            }
        }
        Self(encoded)
    }

    pub fn from_hint(value: &str) -> Self {
        if Self::is_source_identifier(value) {
            if Self::is_reserved(value) {
                return Self(format!("{value}Value"));
            }
            return Self(value.to_string());
        }
        Self::from_dex(value)
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    fn is_reserved(value: &str) -> bool {
        matches!(
            value,
            "abstract"
                | "actual"
                | "as"
                | "break"
                | "by"
                | "catch"
                | "class"
                | "companion"
                | "const"
                | "constructor"
                | "continue"
                | "crossinline"
                | "data"
                | "delegate"
                | "do"
                | "dynamic"
                | "else"
                | "enum"
                | "expect"
                | "external"
                | "false"
                | "field"
                | "file"
                | "final"
                | "finally"
                | "for"
                | "fun"
                | "get"
                | "if"
                | "import"
                | "in"
                | "infix"
                | "init"
                | "inline"
                | "inner"
                | "interface"
                | "internal"
                | "is"
                | "lateinit"
                | "noinline"
                | "null"
                | "object"
                | "open"
                | "operator"
                | "out"
                | "override"
                | "package"
                | "param"
                | "private"
                | "property"
                | "protected"
                | "public"
                | "receiver"
                | "reified"
                | "return"
                | "sealed"
                | "set"
                | "setparam"
                | "super"
                | "suspend"
                | "tailrec"
                | "this"
                | "throw"
                | "true"
                | "try"
                | "typealias"
                | "typeof"
                | "val"
                | "var"
                | "vararg"
                | "when"
                | "where"
                | "while"
                | "_"
        )
    }

    fn can_escape(value: &str) -> bool {
        !value.is_empty()
            && !value.chars().any(|character| {
                matches!(
                    character,
                    '.' | ';' | '[' | ']' | '/' | '<' | '>' | ':' | '\\' | '`'
                )
            })
    }

    fn is_source_identifier(value: &str) -> bool {
        let mut characters = value.chars();
        let Some(first) = characters.next() else {
            return false;
        };
        (first == '_' || first.is_alphabetic())
            && characters.all(|character| character == '_' || character.is_alphanumeric())
    }
}

impl std::fmt::Display for KotlinIdentifier {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.0)
    }
}

#[derive(Debug, Clone, Default)]
pub struct KotlinNameScope {
    used: std::collections::BTreeSet<KotlinIdentifier>,
}

impl KotlinNameScope {
    pub fn reserve(&mut self, name: KotlinIdentifier) -> KotlinIdentifier {
        self.used.insert(name.clone());
        name
    }

    pub fn claim(&mut self, preferred: KotlinIdentifier) -> KotlinIdentifier {
        if self.used.insert(preferred.clone()) {
            return preferred;
        }
        let base = preferred.as_str();
        for suffix in 2u32.. {
            let candidate = KotlinIdentifier::from_hint(&format!("{base}{suffix}"));
            if self.used.insert(candidate.clone()) {
                return candidate;
            }
        }
        unreachable!()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KotlinClassName {
    components: Vec<KotlinIdentifier>,
}

impl KotlinClassName {
    pub fn from_source(name: &str) -> Self {
        Self::from_components(name.split('.'))
    }

    pub fn from_components<'a>(components: impl IntoIterator<Item = &'a str>) -> Self {
        let components = components
            .into_iter()
            .map(KotlinIdentifier::from_dex)
            .collect();
        Self { components }
    }

    pub fn from_identifiers(components: impl IntoIterator<Item = KotlinIdentifier>) -> Self {
        Self {
            components: components.into_iter().collect(),
        }
    }

    pub fn simple(name: KotlinIdentifier) -> Self {
        Self {
            components: vec![name],
        }
    }

    pub fn components(&self) -> &[KotlinIdentifier] {
        &self.components
    }
}

impl std::fmt::Display for KotlinClassName {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(
            &self
                .components
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("."),
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct KotlinClassTypeSegment {
    pub name: KotlinIdentifier,
    pub arguments: Vec<KotlinTypeArgument>,
}

impl std::fmt::Display for KotlinClassTypeSegment {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name.fmt(formatter)?;
        if !self.arguments.is_empty() {
            formatter.write_str("<")?;
            for (index, argument) in self.arguments.iter().enumerate() {
                if index != 0 {
                    formatter.write_str(", ")?;
                }
                argument.fmt(formatter)?;
            }
            formatter.write_str(">")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct KotlinClassType {
    pub segments: Vec<KotlinClassTypeSegment>,
}

impl KotlinClassType {
    pub fn raw(name: KotlinClassName) -> Self {
        Self {
            segments: name
                .components
                .into_iter()
                .map(|name| KotlinClassTypeSegment {
                    name,
                    arguments: Vec::new(),
                })
                .collect(),
        }
    }

    pub fn from_source(name: &str) -> Self {
        Self::raw(KotlinClassName::from_source(name))
    }

    pub fn name(&self) -> KotlinClassName {
        KotlinClassName {
            components: self
                .segments
                .iter()
                .map(|segment| segment.name.clone())
                .collect(),
        }
    }
}

impl std::fmt::Display for KotlinClassType {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (index, segment) in self.segments.iter().enumerate() {
            if index != 0 {
                formatter.write_str(".")?;
            }
            segment.fmt(formatter)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum KotlinTypeArgument {
    Any,
    Exact(KotlinType),
    Extends(KotlinType),
    Super(KotlinType),
}

impl std::fmt::Display for KotlinTypeArgument {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Any => formatter.write_str("*"),
            Self::Exact(ty) => KotlinType::fmt_platform_argument(ty, formatter),
            Self::Extends(ty) => {
                formatter.write_str("out ")?;
                KotlinType::fmt_platform_argument(ty, formatter)
            }
            Self::Super(ty) => {
                formatter.write_str("in ")?;
                KotlinType::fmt_platform_argument(ty, formatter)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum KotlinType {
    Primitive(KotlinPrimitiveType),
    Class(KotlinClassType),
    Variable(KotlinIdentifier),
    Array(Box<KotlinTypeUse>),
}

/// Nullability attached to one use of a Kotlin type.
///
/// `Unknown` preserves a JVM platform type until data flow or metadata proves
/// a source qualifier. It is deliberately distinct from explicit `Nullable`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum KotlinTypeNullability {
    Unknown,
    Nullable,
    NonNull,
}

/// A type together with the qualifier at this exact nesting position.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct KotlinTypeUse {
    ty: KotlinType,
    nullability: KotlinTypeNullability,
}

impl KotlinTypeUse {
    pub fn unknown(ty: KotlinType) -> Self {
        Self {
            ty,
            nullability: KotlinTypeNullability::Unknown,
        }
    }

    pub fn nullability(&self) -> KotlinTypeNullability {
        self.nullability
    }

    pub fn as_type(&self) -> &KotlinType {
        &self.ty
    }

    pub(crate) fn as_type_mut(&mut self) -> &mut KotlinType {
        &mut self.ty
    }

    pub(crate) fn set_declared_nullability(&mut self, nullable: bool) -> bool {
        let nullability = if nullable {
            KotlinTypeNullability::Nullable
        } else {
            KotlinTypeNullability::NonNull
        };
        if self.nullability == nullability {
            return false;
        }
        self.nullability = nullability;
        true
    }

    pub fn into_type(self) -> KotlinType {
        self.ty
    }

    pub(crate) fn map_type(self, map: impl FnOnce(KotlinType) -> KotlinType) -> Self {
        Self {
            ty: map(self.ty),
            nullability: self.nullability,
        }
    }
}

impl std::ops::Deref for KotlinTypeUse {
    type Target = KotlinType;

    fn deref(&self) -> &Self::Target {
        &self.ty
    }
}

impl std::ops::DerefMut for KotlinTypeUse {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.ty
    }
}

impl KotlinType {
    fn fmt_platform_argument(
        ty: &Self,
        formatter: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(formatter, "{ty}")?;
        if matches!(ty, Self::Class(_) | Self::Array(_)) {
            formatter.write_str("?")?;
        }
        Ok(())
    }

    pub fn source_class(source_name: &str) -> Self {
        Self::Class(KotlinClassType::from_source(source_name))
    }

    pub fn array(element: KotlinType) -> Self {
        Self::Array(Box::new(KotlinTypeUse::unknown(element)))
    }

    pub(crate) fn prove_array_elements_non_null(&mut self) -> bool {
        let Self::Array(element) = self else {
            return false;
        };
        if element.nullability == KotlinTypeNullability::NonNull {
            return false;
        }
        element.nullability = KotlinTypeNullability::NonNull;
        true
    }

    pub const fn int() -> Self {
        Self::Primitive(KotlinPrimitiveType::Int)
    }

    pub const fn boolean() -> Self {
        Self::Primitive(KotlinPrimitiveType::Boolean)
    }

    pub(crate) fn into_raw(mut self) -> Self {
        match &mut self {
            Self::Class(class) => {
                for segment in &mut class.segments {
                    segment.arguments.clear();
                }
            }
            Self::Array(element) => {
                element.ty = element.ty.clone().into_raw();
            }
            Self::Primitive(_) | Self::Variable(_) => {}
        }
        self
    }

    pub(crate) fn into_star_projection(mut self) -> Self {
        match &mut self {
            Self::Class(class) => {
                for segment in &mut class.segments {
                    for argument in &mut segment.arguments {
                        *argument = KotlinTypeArgument::Any;
                    }
                }
            }
            Self::Array(element) => {
                element.ty = element.ty.clone().into_star_projection();
            }
            Self::Primitive(_) | Self::Variable(_) => {}
        }
        self
    }

    pub(crate) fn array_shape(&self) -> (&Self, usize) {
        let mut element = self;
        let mut rank = 0usize;
        while let Self::Array(inner) = element {
            element = inner;
            rank += 1;
        }
        (element, rank)
    }
}

impl std::fmt::Display for KotlinType {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Primitive(primitive) => formatter.write_str(match primitive {
                KotlinPrimitiveType::Void => "Unit",
                KotlinPrimitiveType::Boolean => "Boolean",
                KotlinPrimitiveType::Byte => "Byte",
                KotlinPrimitiveType::Short => "Short",
                KotlinPrimitiveType::Char => "Char",
                KotlinPrimitiveType::Int => "Int",
                KotlinPrimitiveType::Long => "Long",
                KotlinPrimitiveType::Float => "Float",
                KotlinPrimitiveType::Double => "Double",
            }),
            Self::Class(class) => class.fmt(formatter),
            Self::Variable(variable) => variable.fmt(formatter),
            Self::Array(element) => match &element.ty {
                Self::Primitive(KotlinPrimitiveType::Boolean) => {
                    formatter.write_str("BooleanArray")
                }
                Self::Primitive(KotlinPrimitiveType::Byte) => formatter.write_str("ByteArray"),
                Self::Primitive(KotlinPrimitiveType::Short) => formatter.write_str("ShortArray"),
                Self::Primitive(KotlinPrimitiveType::Char) => formatter.write_str("CharArray"),
                Self::Primitive(KotlinPrimitiveType::Int) => formatter.write_str("IntArray"),
                Self::Primitive(KotlinPrimitiveType::Long) => formatter.write_str("LongArray"),
                Self::Primitive(KotlinPrimitiveType::Float) => formatter.write_str("FloatArray"),
                Self::Primitive(KotlinPrimitiveType::Double) => formatter.write_str("DoubleArray"),
                Self::Variable(_) => write!(formatter, "Array<{}>", element.ty),
                _ if element.nullability == KotlinTypeNullability::NonNull => {
                    write!(formatter, "Array<{}>", element.ty)
                }
                // JVM array components are platform types until metadata or
                // value flow proves a source qualifier.
                _ => write!(formatter, "Array<{}?>", element.ty),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KotlinTypeParameter {
    pub name: KotlinIdentifier,
    pub bounds: Vec<KotlinType>,
}

impl std::fmt::Display for KotlinTypeParameter {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name.fmt(formatter)?;
        if !self.bounds.is_empty() {
            formatter.write_str(" : ")?;
            for (index, bound) in self.bounds.iter().enumerate() {
                if index != 0 {
                    formatter.write_str(", ")?;
                }
                bound.fmt(formatter)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum KotlinLiteral {
    Null,
    Boolean(bool),
    Integer(i32),
    Long(i64),
    Float(f32),
    Double(f64),
    Character(u16),
    String(Utf16String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KotlinUnaryOp {
    Negate,
    LogicalNot,
    BitwiseNot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KotlinUpdateOp {
    Increment,
    Decrement,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KotlinBinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    BitAnd,
    BitOr,
    BitXor,
    ShiftLeft,
    ShiftRight,
    UnsignedShiftRight,
    LogicalAnd,
    LogicalOr,
    Equal,
    NotEqual,
    ReferentialEqual,
    ReferentialNotEqual,
    Less,
    GreaterEqual,
    Greater,
    LessEqual,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KotlinAssignOp {
    Assign,
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    BitAnd,
    BitOr,
    BitXor,
    ShiftLeft,
    ShiftRight,
    UnsignedShiftRight,
}

impl KotlinUnaryOp {
    pub(crate) fn token(self) -> &'static str {
        match self {
            Self::Negate => "-",
            Self::LogicalNot => "!",
            Self::BitwiseNot => "~",
        }
    }
}

impl KotlinUpdateOp {
    pub(crate) fn token(self) -> &'static str {
        match self {
            Self::Increment => "++",
            Self::Decrement => "--",
        }
    }
}

impl KotlinBinaryOp {
    pub(crate) fn token(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Subtract => "-",
            Self::Multiply => "*",
            Self::Divide => "/",
            Self::Remainder => "%",
            Self::BitAnd => "and",
            Self::BitOr => "or",
            Self::BitXor => "xor",
            Self::ShiftLeft => "shl",
            Self::ShiftRight => "shr",
            Self::UnsignedShiftRight => "ushr",
            Self::LogicalAnd => "&&",
            Self::LogicalOr => "||",
            Self::Equal => "==",
            Self::NotEqual => "!=",
            Self::ReferentialEqual => "===",
            Self::ReferentialNotEqual => "!==",
            Self::Less => "<",
            Self::GreaterEqual => ">=",
            Self::Greater => ">",
            Self::LessEqual => "<=",
        }
    }
}

impl KotlinAssignOp {
    pub(crate) fn token(self) -> &'static str {
        match self {
            Self::Assign => "=",
            Self::Add => "+=",
            Self::Subtract => "-=",
            Self::Multiply => "*=",
            Self::Divide => "/=",
            Self::Remainder => "%=",
            Self::BitAnd => "&=",
            Self::BitOr => "|=",
            Self::BitXor => "^=",
            Self::ShiftLeft => "<<=",
            Self::ShiftRight => ">>=",
            Self::UnsignedShiftRight => ">>>=",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KotlinJvmIntrinsic {
    ExpressionValueCheck,
    ParameterCheck,
    ReceiverNullCheck,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct KotlinCallArguments {
    values: Vec<KotlinExpr>,
    names: std::collections::BTreeMap<usize, KotlinIdentifier>,
    spreads: std::collections::BTreeSet<usize>,
}

impl KotlinCallArguments {
    pub fn from_parts(
        values: Vec<KotlinExpr>,
        names: impl IntoIterator<Item = (usize, KotlinIdentifier)>,
        spreads: impl IntoIterator<Item = usize>,
    ) -> Option<Self> {
        let names = names
            .into_iter()
            .collect::<std::collections::BTreeMap<_, _>>();
        let spreads = spreads
            .into_iter()
            .collect::<std::collections::BTreeSet<_>>();
        let length = values.len();
        if names
            .keys()
            .chain(spreads.iter())
            .any(|index| *index >= length)
        {
            return None;
        }
        Some(Self {
            values,
            names,
            spreads,
        })
    }

    pub fn name(&self, index: usize) -> Option<&KotlinIdentifier> {
        self.names.get(&index)
    }

    pub fn is_spread(&self, index: usize) -> bool {
        self.spreads.contains(&index)
    }

    pub fn as_slice(&self) -> &[KotlinExpr] {
        &self.values
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, KotlinExpr> {
        self.values.iter_mut()
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut KotlinExpr> {
        self.values.get_mut(index)
    }

    pub fn remove(&mut self, index: usize) -> KotlinExpr {
        let value = self.values.remove(index);
        self.names = std::mem::take(&mut self.names)
            .into_iter()
            .filter_map(|(position, name)| match position.cmp(&index) {
                std::cmp::Ordering::Less => Some((position, name)),
                std::cmp::Ordering::Equal => None,
                std::cmp::Ordering::Greater => Some((position - 1, name)),
            })
            .collect();
        self.spreads = std::mem::take(&mut self.spreads)
            .into_iter()
            .filter_map(|position| match position.cmp(&index) {
                std::cmp::Ordering::Less => Some(position),
                std::cmp::Ordering::Equal => None,
                std::cmp::Ordering::Greater => Some(position - 1),
            })
            .collect();
        value
    }

    pub fn map_values(mut self, mut map: impl FnMut(KotlinExpr) -> KotlinExpr) -> Self {
        self.values = self.values.into_iter().map(&mut map).collect();
        self
    }

    pub fn into_values(self) -> Vec<KotlinExpr> {
        self.values
    }
}

impl From<Vec<KotlinExpr>> for KotlinCallArguments {
    fn from(values: Vec<KotlinExpr>) -> Self {
        Self {
            values,
            names: Default::default(),
            spreads: Default::default(),
        }
    }
}

impl FromIterator<KotlinExpr> for KotlinCallArguments {
    fn from_iter<T: IntoIterator<Item = KotlinExpr>>(iter: T) -> Self {
        iter.into_iter().collect::<Vec<_>>().into()
    }
}

impl std::ops::Deref for KotlinCallArguments {
    type Target = [KotlinExpr];

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl IntoIterator for KotlinCallArguments {
    type Item = KotlinExpr;
    type IntoIter = std::vec::IntoIter<KotlinExpr>;

    fn into_iter(self) -> Self::IntoIter {
        self.values.into_iter()
    }
}

impl<'a> IntoIterator for &'a KotlinCallArguments {
    type Item = &'a KotlinExpr;
    type IntoIter = std::slice::Iter<'a, KotlinExpr>;

    fn into_iter(self) -> Self::IntoIter {
        self.values.iter()
    }
}

impl<'a> IntoIterator for &'a mut KotlinCallArguments {
    type Item = &'a mut KotlinExpr;
    type IntoIter = std::slice::IterMut<'a, KotlinExpr>;

    fn into_iter(self) -> Self::IntoIter {
        self.values.iter_mut()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum KotlinExpr {
    This,
    QualifiedThis(KotlinType),
    Super,
    Name(KotlinIdentifier),
    Literal(KotlinLiteral),
    ClassLiteral(KotlinType),
    /// A Kotlin `object` or companion value represented by a synthetic static
    /// field in JVM bytecode.
    ObjectReference(KotlinType),
    /// The enclosing path proves this value non-null and Kotlin can smart-cast
    /// it when it is used as a receiver.
    SmartCast(Box<KotlinExpr>),
    /// Kotlin's explicit non-null assertion at an ABI boundary.
    NonNullAssertion(Box<KotlinExpr>),
    /// A call emitted by the Kotlin/JVM compiler rather than the source
    /// program. The wrapped expression preserves executable semantics until a
    /// typed recovery proves that source-level Kotlin will recreate it.
    JvmIntrinsic {
        kind: KotlinJvmIntrinsic,
        expression: Box<KotlinExpr>,
    },
    Field {
        owner: Box<KotlinExpr>,
        name: KotlinIdentifier,
    },
    StaticField {
        owner: KotlinType,
        name: KotlinIdentifier,
    },
    ArrayAccess {
        array: Box<KotlinExpr>,
        index: Box<KotlinExpr>,
    },
    Call {
        receiver: Option<Box<KotlinExpr>>,
        owner: Option<KotlinType>,
        type_arguments: Vec<KotlinType>,
        method: KotlinIdentifier,
        args: KotlinCallArguments,
    },
    MethodReference {
        receiver: Box<KotlinExpr>,
        method: KotlinIdentifier,
    },
    Lambda {
        parameters: Vec<KotlinIdentifier>,
        body: Box<KotlinExpr>,
    },
    BlockLambda {
        parameters: Vec<KotlinIdentifier>,
        body: Box<KotlinStmt>,
    },
    New {
        enclosing: Option<Box<KotlinExpr>>,
        ty: KotlinType,
        target_type: Option<KotlinType>,
        args: Vec<KotlinExpr>,
        anonymous_body: Option<Box<super::KotlinAnonymousClassBody>>,
    },
    NewArray {
        element_type: KotlinType,
        dimensions: Vec<KotlinExpr>,
        initializer: Vec<KotlinExpr>,
    },
    Unary {
        op: KotlinUnaryOp,
        operand: Box<KotlinExpr>,
    },
    Update {
        op: KotlinUpdateOp,
        target: Box<KotlinExpr>,
        prefix: bool,
    },
    Binary {
        left: Box<KotlinExpr>,
        op: KotlinBinaryOp,
        right: Box<KotlinExpr>,
    },
    Cast {
        ty: KotlinType,
        value: Box<KotlinExpr>,
    },
    InstanceOf {
        value: Box<KotlinExpr>,
        ty: KotlinType,
    },
    Conditional {
        condition: Box<KotlinExpr>,
        when_true: Box<KotlinExpr>,
        when_false: Box<KotlinExpr>,
    },
    Assignment {
        target: Box<KotlinExpr>,
        op: KotlinAssignOp,
        value: Box<KotlinExpr>,
    },
}

impl KotlinExpr {
    pub(crate) fn negated(self) -> Self {
        Self::negated_form(self).0
    }

    fn negated_form(expression: Self) -> (Self, usize) {
        match expression {
            Self::Literal(KotlinLiteral::Boolean(value)) => {
                (Self::Literal(KotlinLiteral::Boolean(!value)), 0)
            }
            Self::Unary {
                op: KotlinUnaryOp::LogicalNot,
                operand,
            } => (*operand, 0),
            Self::Binary {
                left,
                op: KotlinBinaryOp::LogicalAnd,
                right,
            } => Self::negated_junction(*left, KotlinBinaryOp::LogicalAnd, *right),
            Self::Binary {
                left,
                op: KotlinBinaryOp::LogicalOr,
                right,
            } => Self::negated_junction(*left, KotlinBinaryOp::LogicalOr, *right),
            Self::Binary { left, op, right } => match Self::complementary_operator(op) {
                Some(op) => (Self::Binary { left, op, right }, 0),
                None => (
                    Self::Unary {
                        op: KotlinUnaryOp::LogicalNot,
                        operand: Box::new(Self::Binary { left, op, right }),
                    },
                    1,
                ),
            },
            expression => (
                Self::Unary {
                    op: KotlinUnaryOp::LogicalNot,
                    operand: Box::new(expression),
                },
                1,
            ),
        }
    }

    fn negated_junction(left: Self, operator: KotlinBinaryOp, right: Self) -> (Self, usize) {
        let original = Self::Binary {
            left: Box::new(left.clone()),
            op: operator,
            right: Box::new(right.clone()),
        };
        let (left, left_cost) = Self::negated_form(left);
        let (right, right_cost) = Self::negated_form(right);
        let transformed_cost = left_cost.saturating_add(right_cost);
        if transformed_cost <= 3 {
            return (
                Self::Binary {
                    left: Box::new(left),
                    op: match operator {
                        KotlinBinaryOp::LogicalAnd => KotlinBinaryOp::LogicalOr,
                        KotlinBinaryOp::LogicalOr => KotlinBinaryOp::LogicalAnd,
                        _ => unreachable!("boolean junction requires a logical operator"),
                    },
                    right: Box::new(right),
                },
                transformed_cost,
            );
        }
        (
            Self::Unary {
                op: KotlinUnaryOp::LogicalNot,
                operand: Box::new(original),
            },
            3,
        )
    }

    fn complementary_operator(operator: KotlinBinaryOp) -> Option<KotlinBinaryOp> {
        Some(match operator {
            KotlinBinaryOp::Equal => KotlinBinaryOp::NotEqual,
            KotlinBinaryOp::NotEqual => KotlinBinaryOp::Equal,
            KotlinBinaryOp::ReferentialEqual => KotlinBinaryOp::ReferentialNotEqual,
            KotlinBinaryOp::ReferentialNotEqual => KotlinBinaryOp::ReferentialEqual,
            KotlinBinaryOp::Less => KotlinBinaryOp::GreaterEqual,
            KotlinBinaryOp::GreaterEqual => KotlinBinaryOp::Less,
            KotlinBinaryOp::Greater => KotlinBinaryOp::LessEqual,
            KotlinBinaryOp::LessEqual => KotlinBinaryOp::Greater,
            KotlinBinaryOp::Add
            | KotlinBinaryOp::Subtract
            | KotlinBinaryOp::Multiply
            | KotlinBinaryOp::Divide
            | KotlinBinaryOp::Remainder
            | KotlinBinaryOp::BitAnd
            | KotlinBinaryOp::BitOr
            | KotlinBinaryOp::BitXor
            | KotlinBinaryOp::ShiftLeft
            | KotlinBinaryOp::ShiftRight
            | KotlinBinaryOp::UnsignedShiftRight
            | KotlinBinaryOp::LogicalAnd
            | KotlinBinaryOp::LogicalOr => return None,
        })
    }

    pub(crate) fn cost(&self) -> usize {
        let mut cost = 0usize;
        let mut pending = vec![self];
        while let Some(expression) = pending.pop() {
            cost += match expression {
                Self::Conditional { .. } => 16,
                Self::Call { .. } => 2,
                _ => 1,
            };
            match expression {
                Self::SmartCast(value)
                | Self::NonNullAssertion(value)
                | Self::JvmIntrinsic {
                    expression: value, ..
                } => pending.push(value),
                Self::Field { owner, .. } => pending.push(owner),
                Self::ArrayAccess { array, index } => {
                    pending.extend([array.as_ref(), index.as_ref()]);
                }
                Self::Call { receiver, args, .. } => {
                    pending.extend(args);
                    pending.extend(receiver.as_deref());
                }
                Self::MethodReference { receiver, .. } => pending.push(receiver),
                Self::Lambda { body, .. } => pending.push(body),
                Self::BlockLambda { .. } => {}
                Self::New {
                    enclosing, args, ..
                } => {
                    pending.extend(args);
                    pending.extend(enclosing.as_deref());
                }
                Self::NewArray {
                    dimensions,
                    initializer,
                    ..
                } => {
                    pending.extend(dimensions);
                    pending.extend(initializer);
                }
                Self::Unary { operand, .. }
                | Self::Update {
                    target: operand, ..
                }
                | Self::Cast { value: operand, .. }
                | Self::InstanceOf { value: operand, .. } => pending.push(operand),
                Self::Binary { left, right, .. }
                | Self::Assignment {
                    target: left,
                    value: right,
                    ..
                } => pending.extend([left.as_ref(), right.as_ref()]),
                Self::Conditional {
                    condition,
                    when_true,
                    when_false,
                } => pending.extend([condition.as_ref(), when_true.as_ref(), when_false.as_ref()]),
                Self::This
                | Self::QualifiedThis(_)
                | Self::Super
                | Self::Name(_)
                | Self::Literal(_)
                | Self::ClassLiteral(_)
                | Self::ObjectReference(_)
                | Self::StaticField { .. } => {}
            }
        }
        cost
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct KotlinField {
    pub owner: KotlinExpr,
    pub name: KotlinIdentifier,
}

#[derive(Debug, Clone, PartialEq)]
pub struct KotlinCatch {
    pub types: Vec<KotlinType>,
    pub variable: KotlinIdentifier,
    pub body: KotlinStmt,
}

#[derive(Debug, Clone, PartialEq)]
pub struct KotlinSwitchCase {
    pub labels: Vec<KotlinExpr>,
    pub body: Vec<KotlinStmt>,
    pub is_default: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KotlinLocalBinding {
    pub mutable: bool,
    pub nullable: bool,
}

impl KotlinLocalBinding {
    pub const MUTABLE_NULLABLE: Self = Self {
        mutable: true,
        nullable: true,
    };
}

impl Default for KotlinLocalBinding {
    fn default() -> Self {
        Self::MUTABLE_NULLABLE
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KotlinConstructorTarget {
    This,
    Super,
}

#[derive(Debug, Clone, PartialEq)]
pub enum KotlinStmt {
    Empty,
    Block(Vec<KotlinStmt>),
    Labeled {
        label: KotlinIdentifier,
        body: Box<KotlinStmt>,
    },
    Variable {
        binding: KotlinLocalBinding,
        ty: KotlinType,
        name: KotlinIdentifier,
        value: Option<KotlinExpr>,
    },
    Expression(KotlinExpr),
    ConstructorInvocation {
        target: KotlinConstructorTarget,
        args: Vec<KotlinExpr>,
    },
    Assign {
        target: KotlinExpr,
        op: KotlinAssignOp,
        value: KotlinExpr,
    },
    If {
        condition: KotlinExpr,
        then_stmt: Box<KotlinStmt>,
        else_stmt: Option<Box<KotlinStmt>>,
    },
    While {
        label: Option<KotlinIdentifier>,
        condition: KotlinExpr,
        body: Box<KotlinStmt>,
    },
    DoWhile {
        label: Option<KotlinIdentifier>,
        body: Box<KotlinStmt>,
        condition: KotlinExpr,
    },
    For {
        label: Option<KotlinIdentifier>,
        init: Vec<KotlinStmt>,
        condition: Option<KotlinExpr>,
        update: Vec<KotlinExpr>,
        body: Box<KotlinStmt>,
    },
    ForEach {
        label: Option<KotlinIdentifier>,
        ty: KotlinType,
        variable: KotlinIdentifier,
        iterable: KotlinExpr,
        body: Box<KotlinStmt>,
    },
    Switch {
        label: Option<KotlinIdentifier>,
        selector: KotlinExpr,
        cases: Vec<KotlinSwitchCase>,
    },
    Try {
        body: Box<KotlinStmt>,
        catches: Vec<KotlinCatch>,
        finally: Option<Box<KotlinStmt>>,
    },
    Synchronized {
        lock: KotlinExpr,
        body: Box<KotlinStmt>,
    },
    Return(Option<KotlinExpr>),
    Throw(KotlinExpr),
    Break(Option<KotlinIdentifier>),
    Continue(Option<KotlinIdentifier>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct KotlinMethodBody {
    pub root: KotlinStmt,
}
use crate::ir::Utf16String;
