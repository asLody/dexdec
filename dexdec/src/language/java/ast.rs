#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum JavaPrimitiveType {
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
pub struct JavaIdentifier(String);

impl JavaIdentifier {
    pub fn from_dex(value: &str) -> Self {
        if Self::is_source_identifier(value)
            && !Self::is_reserved(value)
            && !value.starts_with("$dex$")
        {
            return Self(value.to_string());
        }
        let mut encoded = String::from("$dex$");
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
                | "assert"
                | "boolean"
                | "break"
                | "byte"
                | "case"
                | "catch"
                | "char"
                | "class"
                | "const"
                | "continue"
                | "default"
                | "do"
                | "double"
                | "else"
                | "enum"
                | "extends"
                | "final"
                | "finally"
                | "float"
                | "for"
                | "goto"
                | "if"
                | "implements"
                | "import"
                | "instanceof"
                | "int"
                | "interface"
                | "long"
                | "native"
                | "new"
                | "package"
                | "private"
                | "protected"
                | "public"
                | "return"
                | "short"
                | "static"
                | "strictfp"
                | "super"
                | "switch"
                | "synchronized"
                | "this"
                | "throw"
                | "throws"
                | "transient"
                | "try"
                | "void"
                | "volatile"
                | "while"
                | "true"
                | "false"
                | "null"
                | "_"
        )
    }

    fn is_source_identifier(value: &str) -> bool {
        let mut characters = value.chars();
        let Some(first) = characters.next() else {
            return false;
        };
        (first == '_' || first == '$' || first.is_alphabetic())
            && characters.all(|character| {
                character == '_' || character == '$' || character.is_alphanumeric()
            })
    }
}

impl std::fmt::Display for JavaIdentifier {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.0)
    }
}

#[derive(Debug, Clone, Default)]
pub struct JavaNameScope {
    used: std::collections::BTreeSet<JavaIdentifier>,
}

impl JavaNameScope {
    pub fn reserve(&mut self, name: JavaIdentifier) -> JavaIdentifier {
        self.used.insert(name.clone());
        name
    }

    pub fn claim(&mut self, preferred: JavaIdentifier) -> JavaIdentifier {
        if self.used.insert(preferred.clone()) {
            return preferred;
        }
        let base = preferred.as_str();
        for suffix in 2u32.. {
            let candidate = JavaIdentifier::from_hint(&format!("{base}{suffix}"));
            if self.used.insert(candidate.clone()) {
                return candidate;
            }
        }
        unreachable!()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JavaClassName {
    components: Vec<JavaIdentifier>,
}

impl JavaClassName {
    pub fn from_source(name: &str) -> Self {
        Self::from_components(name.split('.'))
    }

    pub fn from_components<'a>(components: impl IntoIterator<Item = &'a str>) -> Self {
        let components = components
            .into_iter()
            .map(JavaIdentifier::from_dex)
            .collect();
        Self { components }
    }

    pub fn from_identifiers(components: impl IntoIterator<Item = JavaIdentifier>) -> Self {
        Self {
            components: components.into_iter().collect(),
        }
    }

    pub fn simple(name: JavaIdentifier) -> Self {
        Self {
            components: vec![name],
        }
    }

    pub fn components(&self) -> &[JavaIdentifier] {
        &self.components
    }
}

impl std::fmt::Display for JavaClassName {
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
pub struct JavaClassTypeSegment {
    pub name: JavaIdentifier,
    pub arguments: Vec<JavaTypeArgument>,
}

impl std::fmt::Display for JavaClassTypeSegment {
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
pub struct JavaClassType {
    pub segments: Vec<JavaClassTypeSegment>,
}

impl JavaClassType {
    pub fn raw(name: JavaClassName) -> Self {
        Self {
            segments: name
                .components
                .into_iter()
                .map(|name| JavaClassTypeSegment {
                    name,
                    arguments: Vec::new(),
                })
                .collect(),
        }
    }

    pub fn from_source(name: &str) -> Self {
        Self::raw(JavaClassName::from_source(name))
    }

    pub fn name(&self) -> JavaClassName {
        JavaClassName {
            components: self
                .segments
                .iter()
                .map(|segment| segment.name.clone())
                .collect(),
        }
    }
}

impl std::fmt::Display for JavaClassType {
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
pub enum JavaTypeArgument {
    Any,
    Exact(JavaType),
    Extends(JavaType),
    Super(JavaType),
}

impl std::fmt::Display for JavaTypeArgument {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Any => formatter.write_str("?"),
            Self::Exact(ty) => ty.fmt(formatter),
            Self::Extends(ty) => write!(formatter, "? extends {ty}"),
            Self::Super(ty) => write!(formatter, "? super {ty}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum JavaType {
    Primitive(JavaPrimitiveType),
    Class(JavaClassType),
    Variable(JavaIdentifier),
    Array(Box<JavaType>),
}

impl JavaType {
    pub fn source_class(source_name: &str) -> Self {
        Self::Class(JavaClassType::from_source(source_name))
    }

    pub fn array(element: JavaType) -> Self {
        Self::Array(Box::new(element))
    }

    pub const fn int() -> Self {
        Self::Primitive(JavaPrimitiveType::Int)
    }

    pub const fn boolean() -> Self {
        Self::Primitive(JavaPrimitiveType::Boolean)
    }

    pub(crate) fn into_raw(mut self) -> Self {
        match &mut self {
            Self::Class(class) => {
                for segment in &mut class.segments {
                    segment.arguments.clear();
                }
            }
            Self::Array(element) => {
                **element = (**element).clone().into_raw();
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

impl std::fmt::Display for JavaType {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Primitive(primitive) => formatter.write_str(match primitive {
                JavaPrimitiveType::Void => "void",
                JavaPrimitiveType::Boolean => "boolean",
                JavaPrimitiveType::Byte => "byte",
                JavaPrimitiveType::Short => "short",
                JavaPrimitiveType::Char => "char",
                JavaPrimitiveType::Int => "int",
                JavaPrimitiveType::Long => "long",
                JavaPrimitiveType::Float => "float",
                JavaPrimitiveType::Double => "double",
            }),
            Self::Class(class) => class.fmt(formatter),
            Self::Variable(variable) => variable.fmt(formatter),
            Self::Array(element) => write!(formatter, "{element}[]"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JavaTypeParameter {
    pub name: JavaIdentifier,
    pub bounds: Vec<JavaType>,
}

impl std::fmt::Display for JavaTypeParameter {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name.fmt(formatter)?;
        if !self.bounds.is_empty() {
            formatter.write_str(" extends ")?;
            for (index, bound) in self.bounds.iter().enumerate() {
                if index != 0 {
                    formatter.write_str(" & ")?;
                }
                bound.fmt(formatter)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum JavaLiteral {
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
pub enum JavaUnaryOp {
    Negate,
    LogicalNot,
    BitwiseNot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JavaUpdateOp {
    Increment,
    Decrement,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JavaBinaryOp {
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
    Less,
    GreaterEqual,
    Greater,
    LessEqual,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JavaAssignOp {
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

impl JavaUnaryOp {
    pub(crate) fn token(self) -> &'static str {
        match self {
            Self::Negate => "-",
            Self::LogicalNot => "!",
            Self::BitwiseNot => "~",
        }
    }
}

impl JavaUpdateOp {
    pub(crate) fn token(self) -> &'static str {
        match self {
            Self::Increment => "++",
            Self::Decrement => "--",
        }
    }
}

impl JavaBinaryOp {
    pub(crate) fn token(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Subtract => "-",
            Self::Multiply => "*",
            Self::Divide => "/",
            Self::Remainder => "%",
            Self::BitAnd => "&",
            Self::BitOr => "|",
            Self::BitXor => "^",
            Self::ShiftLeft => "<<",
            Self::ShiftRight => ">>",
            Self::UnsignedShiftRight => ">>>",
            Self::LogicalAnd => "&&",
            Self::LogicalOr => "||",
            Self::Equal => "==",
            Self::NotEqual => "!=",
            Self::Less => "<",
            Self::GreaterEqual => ">=",
            Self::Greater => ">",
            Self::LessEqual => "<=",
        }
    }
}

impl JavaAssignOp {
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

#[derive(Debug, Clone, PartialEq)]
pub enum JavaExpr {
    This,
    QualifiedThis(JavaType),
    Super,
    Name(JavaIdentifier),
    Literal(JavaLiteral),
    ClassLiteral(JavaType),
    Field {
        owner: Box<JavaExpr>,
        name: JavaIdentifier,
    },
    StaticField {
        owner: JavaType,
        name: JavaIdentifier,
    },
    ArrayAccess {
        array: Box<JavaExpr>,
        index: Box<JavaExpr>,
    },
    Call {
        receiver: Option<Box<JavaExpr>>,
        owner: Option<JavaType>,
        type_arguments: Vec<JavaType>,
        method: JavaIdentifier,
        args: Vec<JavaExpr>,
    },
    MethodReference {
        receiver: Box<JavaExpr>,
        method: JavaIdentifier,
    },
    Lambda {
        parameters: Vec<JavaIdentifier>,
        body: Box<JavaExpr>,
    },
    BlockLambda {
        parameters: Vec<JavaIdentifier>,
        body: Box<JavaStmt>,
    },
    New {
        enclosing: Option<Box<JavaExpr>>,
        ty: JavaType,
        target_type: Option<JavaType>,
        args: Vec<JavaExpr>,
        anonymous_body: Option<Box<super::JavaAnonymousClassBody>>,
    },
    NewArray {
        element_type: JavaType,
        dimensions: Vec<JavaExpr>,
        initializer: Vec<JavaExpr>,
    },
    Unary {
        op: JavaUnaryOp,
        operand: Box<JavaExpr>,
    },
    Update {
        op: JavaUpdateOp,
        target: Box<JavaExpr>,
        prefix: bool,
    },
    Binary {
        left: Box<JavaExpr>,
        op: JavaBinaryOp,
        right: Box<JavaExpr>,
    },
    Cast {
        ty: JavaType,
        value: Box<JavaExpr>,
    },
    InstanceOf {
        value: Box<JavaExpr>,
        ty: JavaType,
    },
    Conditional {
        condition: Box<JavaExpr>,
        when_true: Box<JavaExpr>,
        when_false: Box<JavaExpr>,
    },
    Assignment {
        target: Box<JavaExpr>,
        op: JavaAssignOp,
        value: Box<JavaExpr>,
    },
}

impl JavaExpr {
    pub(crate) fn negated(self) -> Self {
        Self::negated_form(self).0
    }

    fn negated_form(expression: Self) -> (Self, usize) {
        match expression {
            Self::Literal(JavaLiteral::Boolean(value)) => {
                (Self::Literal(JavaLiteral::Boolean(!value)), 0)
            }
            Self::Unary {
                op: JavaUnaryOp::LogicalNot,
                operand,
            } => (*operand, 0),
            Self::Binary {
                left,
                op: JavaBinaryOp::LogicalAnd,
                right,
            } => Self::negated_junction(*left, JavaBinaryOp::LogicalAnd, *right),
            Self::Binary {
                left,
                op: JavaBinaryOp::LogicalOr,
                right,
            } => Self::negated_junction(*left, JavaBinaryOp::LogicalOr, *right),
            Self::Binary { left, op, right } => match Self::complementary_operator(op) {
                Some(op) => (Self::Binary { left, op, right }, 0),
                None => (
                    Self::Unary {
                        op: JavaUnaryOp::LogicalNot,
                        operand: Box::new(Self::Binary { left, op, right }),
                    },
                    1,
                ),
            },
            expression => (
                Self::Unary {
                    op: JavaUnaryOp::LogicalNot,
                    operand: Box::new(expression),
                },
                1,
            ),
        }
    }

    fn negated_junction(left: Self, operator: JavaBinaryOp, right: Self) -> (Self, usize) {
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
                        JavaBinaryOp::LogicalAnd => JavaBinaryOp::LogicalOr,
                        JavaBinaryOp::LogicalOr => JavaBinaryOp::LogicalAnd,
                        _ => unreachable!("boolean junction requires a logical operator"),
                    },
                    right: Box::new(right),
                },
                transformed_cost,
            );
        }
        (
            Self::Unary {
                op: JavaUnaryOp::LogicalNot,
                operand: Box::new(original),
            },
            3,
        )
    }

    fn complementary_operator(operator: JavaBinaryOp) -> Option<JavaBinaryOp> {
        Some(match operator {
            JavaBinaryOp::Equal => JavaBinaryOp::NotEqual,
            JavaBinaryOp::NotEqual => JavaBinaryOp::Equal,
            JavaBinaryOp::Less => JavaBinaryOp::GreaterEqual,
            JavaBinaryOp::GreaterEqual => JavaBinaryOp::Less,
            JavaBinaryOp::Greater => JavaBinaryOp::LessEqual,
            JavaBinaryOp::LessEqual => JavaBinaryOp::Greater,
            JavaBinaryOp::Add
            | JavaBinaryOp::Subtract
            | JavaBinaryOp::Multiply
            | JavaBinaryOp::Divide
            | JavaBinaryOp::Remainder
            | JavaBinaryOp::BitAnd
            | JavaBinaryOp::BitOr
            | JavaBinaryOp::BitXor
            | JavaBinaryOp::ShiftLeft
            | JavaBinaryOp::ShiftRight
            | JavaBinaryOp::UnsignedShiftRight
            | JavaBinaryOp::LogicalAnd
            | JavaBinaryOp::LogicalOr => return None,
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
                | Self::StaticField { .. } => {}
            }
        }
        cost
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct JavaField {
    pub owner: JavaExpr,
    pub name: JavaIdentifier,
}

#[derive(Debug, Clone, PartialEq)]
pub struct JavaCatch {
    pub types: Vec<JavaType>,
    pub variable: JavaIdentifier,
    pub body: JavaStmt,
}

#[derive(Debug, Clone, PartialEq)]
pub struct JavaSwitchCase {
    pub labels: Vec<JavaExpr>,
    pub body: Vec<JavaStmt>,
    pub is_default: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JavaConstructorTarget {
    This,
    Super,
}

#[derive(Debug, Clone, PartialEq)]
pub enum JavaStmt {
    Empty,
    Block(Vec<JavaStmt>),
    Labeled {
        label: JavaIdentifier,
        body: Box<JavaStmt>,
    },
    Variable {
        ty: JavaType,
        name: JavaIdentifier,
        value: Option<JavaExpr>,
    },
    Expression(JavaExpr),
    ConstructorInvocation {
        target: JavaConstructorTarget,
        args: Vec<JavaExpr>,
    },
    Assign {
        target: JavaExpr,
        op: JavaAssignOp,
        value: JavaExpr,
    },
    If {
        condition: JavaExpr,
        then_stmt: Box<JavaStmt>,
        else_stmt: Option<Box<JavaStmt>>,
    },
    While {
        label: Option<JavaIdentifier>,
        condition: JavaExpr,
        body: Box<JavaStmt>,
    },
    DoWhile {
        label: Option<JavaIdentifier>,
        body: Box<JavaStmt>,
        condition: JavaExpr,
    },
    For {
        label: Option<JavaIdentifier>,
        init: Vec<JavaStmt>,
        condition: Option<JavaExpr>,
        update: Vec<JavaExpr>,
        body: Box<JavaStmt>,
    },
    ForEach {
        label: Option<JavaIdentifier>,
        ty: JavaType,
        variable: JavaIdentifier,
        iterable: JavaExpr,
        body: Box<JavaStmt>,
    },
    Switch {
        label: Option<JavaIdentifier>,
        selector: JavaExpr,
        cases: Vec<JavaSwitchCase>,
    },
    Try {
        body: Box<JavaStmt>,
        catches: Vec<JavaCatch>,
        finally: Option<Box<JavaStmt>>,
    },
    Synchronized {
        lock: JavaExpr,
        body: Box<JavaStmt>,
    },
    Return(Option<JavaExpr>),
    Throw(JavaExpr),
    Break(Option<JavaIdentifier>),
    Continue(Option<JavaIdentifier>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct JavaMethodBody {
    pub root: JavaStmt,
}
use crate::ir::Utf16String;
