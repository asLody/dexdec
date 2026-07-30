//! The part of Kotlin's declaration schema this decompiler consumes.
//!
//! Field numbers come from Kotlin's `descriptors.proto` and `jvm_descriptors
//! .proto` and are part of the on-disk format, so they are written here as the
//! constants they are. Only declarations that Java bytecode cannot express are
//! modelled; anything else is already recoverable from the DEX itself.

use super::names::NameResolver;
use super::wire::{Message, WireError};

/// Flag layouts are packed bit fields; each accessor names its own slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeclarationFlags(u64);

impl Default for DeclarationFlags {
    fn default() -> Self {
        Self(Self::OMITTED)
    }
}

impl DeclarationFlags {
    /// What a declaration's flags mean when the compiler omits them.
    ///
    /// Protocol buffers drop a field holding its default, and the default here
    /// is not zero: it is `public` and `final`. Reading an absent field as zero
    /// declares every such member `internal`.
    const OMITTED: u64 = 6;

    pub(super) fn of(flags: Option<u64>) -> Self {
        Self(flags.unwrap_or(Self::OMITTED))
    }

    fn bits(self, offset: u32, width: u32) -> u64 {
        (self.0 >> offset) & ((1 << width) - 1)
    }

    pub fn visibility(self) -> Visibility {
        match self.bits(1, 3) {
            0 => Visibility::Internal,
            1 => Visibility::Private,
            2 => Visibility::Protected,
            3 => Visibility::Public,
            4 => Visibility::PrivateToThis,
            _ => Visibility::Local,
        }
    }

    /// Whether a class permits only the subclasses declared beside it.
    pub fn is_sealed(self) -> bool {
        self.bits(4, 2) == 3
    }

    /// Whether a property is a compile-time constant.
    pub fn is_const(self) -> bool {
        self.bits(11, 1) == 1
    }

    /// What kind of declaration a class is.
    pub fn class_kind(self) -> ClassKind {
        match self.bits(6, 3) {
            1 => ClassKind::Interface,
            2 => ClassKind::EnumClass,
            3 => ClassKind::EnumEntry,
            4 => ClassKind::AnnotationClass,
            5 => ClassKind::Object,
            6 => ClassKind::CompanionObject,
            _ => ClassKind::Class,
        }
    }

    pub fn is_suspend(self) -> bool {
        self.bits(13, 1) == 1
    }

    /// Whether a property is `lateinit`, which the JVM leaves null until the
    /// first assignment even though the source declares it non-null.
    pub fn is_lateinit(self) -> bool {
        self.bits(12, 1) == 1
    }
}

/// A Kotlin declaration that bytecode renders as a class either way.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClassKind {
    Class,
    Interface,
    EnumClass,
    EnumEntry,
    AnnotationClass,
    Object,
    CompanionObject,
}

impl ClassKind {
    /// Whether the class has exactly one instance, held in a static field the
    /// compiler generates and never leaves null.
    pub fn is_singleton(self) -> bool {
        matches!(self, Self::Object | Self::CompanionObject)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Internal,
    Private,
    Protected,
    Public,
    PrivateToThis,
    Local,
}

/// A type reference, carried only for the facts bytecode erases.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeReference {
    pub nullable: bool,
    /// The declared class, dotted, when the type names one.
    pub name: Option<String>,
    pub arguments: Vec<TypeReference>,
}

impl TypeReference {
    const NULLABLE: u32 = 3;
    const CLASS_NAME: u32 = 6;
    const ARGUMENT: u32 = 2;
    // ProtoBuf.Type.Argument stores an inline type in field 2 and a type-table
    // index in field 3. Field 1 is the projection enum.
    const ARGUMENT_TYPE: u32 = 2;
    const ARGUMENT_TYPE_ID: u32 = 3;

    fn parse(
        message: &Message<'_>,
        names: &NameResolver,
        types: &TypeTable<'_>,
    ) -> Result<Self, WireError> {
        Self::parse_at(message, names, types, 0)
    }

    fn parse_at(
        message: &Message<'_>,
        names: &NameResolver,
        types: &TypeTable<'_>,
        depth: usize,
    ) -> Result<Self, WireError> {
        let mut arguments = Vec::new();
        for argument in message.messages(Self::ARGUMENT)? {
            if let Some(inner) = argument.message(Self::ARGUMENT_TYPE)? {
                arguments.push(Self::parse_at(&inner, names, types, depth + 1)?);
            } else if let Some(index) = argument.index(Self::ARGUMENT_TYPE_ID) {
                if let Some(inner) = types.resolve_at(index, names, depth + 1)? {
                    arguments.push(inner);
                }
            }
        }
        Ok(Self {
            nullable: message.flag(Self::NULLABLE),
            name: message
                .index(Self::CLASS_NAME)
                .and_then(|index| names.qualified_name(index)),
            arguments,
        })
    }

    fn jvm_descriptor(&self, position: JvmTypePosition) -> Option<String> {
        JvmTypeErasure::descriptor(self, position)
    }

    pub(crate) fn erased_return_descriptor(&self) -> Option<String> {
        self.jvm_descriptor(JvmTypePosition::Return)
    }
}

#[derive(Debug, Clone, Copy)]
enum JvmTypePosition {
    Parameter,
    Return,
    ArrayElement,
}

/// Erases Kotlin metadata types according to the Kotlin/JVM built-in mapping.
/// It deliberately returns `None` for a type variable or unsupported special
/// type instead of manufacturing a descriptor that could bind metadata to the
/// wrong overload.
struct JvmTypeErasure;

impl JvmTypeErasure {
    fn descriptor(ty: &TypeReference, position: JvmTypePosition) -> Option<String> {
        let name = ty.name.as_deref()?.replace('.', "/");
        if let Some(primitive) = Self::primitive(&name) {
            if ty.nullable || matches!(position, JvmTypePosition::ArrayElement) {
                return Some(Self::boxed(primitive).to_string());
            }
            return Some(primitive.to_string());
        }
        if name == "kotlin/Unit" && matches!(position, JvmTypePosition::Return) {
            return Some("V".to_string());
        }
        if let Some(element) = Self::primitive_array(&name) {
            return Some(format!("[{element}"));
        }
        if name == "kotlin/Array" {
            let element = ty.arguments.first()?;
            return Some(format!(
                "[{}",
                element.jvm_descriptor(JvmTypePosition::ArrayElement)?
            ));
        }
        let mapped = Self::class_name(&name)?;
        Some(format!("L{mapped};"))
    }

    fn primitive(name: &str) -> Option<&'static str> {
        match name {
            "kotlin/Boolean" => Some("Z"),
            "kotlin/Byte" => Some("B"),
            "kotlin/Char" => Some("C"),
            "kotlin/Short" => Some("S"),
            "kotlin/Int" => Some("I"),
            "kotlin/Long" => Some("J"),
            "kotlin/Float" => Some("F"),
            "kotlin/Double" => Some("D"),
            _ => None,
        }
    }

    fn boxed(descriptor: &str) -> &'static str {
        match descriptor {
            "Z" => "Ljava/lang/Boolean;",
            "B" => "Ljava/lang/Byte;",
            "C" => "Ljava/lang/Character;",
            "S" => "Ljava/lang/Short;",
            "I" => "Ljava/lang/Integer;",
            "J" => "Ljava/lang/Long;",
            "F" => "Ljava/lang/Float;",
            "D" => "Ljava/lang/Double;",
            _ => unreachable!("primitive descriptor"),
        }
    }

    fn primitive_array(name: &str) -> Option<&'static str> {
        match name {
            "kotlin/BooleanArray" => Some("Z"),
            "kotlin/ByteArray" => Some("B"),
            "kotlin/CharArray" => Some("C"),
            "kotlin/ShortArray" => Some("S"),
            "kotlin/IntArray" => Some("I"),
            "kotlin/LongArray" => Some("J"),
            "kotlin/FloatArray" => Some("F"),
            "kotlin/DoubleArray" => Some("D"),
            _ => None,
        }
    }

    fn class_name(name: &str) -> Option<&str> {
        Some(match name {
            "kotlin/Any" => "java/lang/Object",
            "kotlin/String" => "java/lang/String",
            "kotlin/CharSequence" => "java/lang/CharSequence",
            "kotlin/Throwable" => "java/lang/Throwable",
            "kotlin/Number" => "java/lang/Number",
            "kotlin/Comparable" => "java/lang/Comparable",
            "kotlin/Enum" => "java/lang/Enum",
            "kotlin/Annotation" => "java/lang/annotation/Annotation",
            "kotlin/collections/Iterable" => "java/lang/Iterable",
            "kotlin/collections/Collection" | "kotlin/collections/MutableCollection" => {
                "java/util/Collection"
            }
            "kotlin/collections/List" | "kotlin/collections/MutableList" => "java/util/List",
            "kotlin/collections/Set" | "kotlin/collections/MutableSet" => "java/util/Set",
            "kotlin/collections/Map" | "kotlin/collections/MutableMap" => "java/util/Map",
            "kotlin/Nothing" => return None,
            name => name,
        })
    }
}

/// The declaration-scoped table used when Kotlin replaces an inline `Type`
/// message with a compact integer ID.
#[derive(Debug, Default)]
struct TypeTable<'data> {
    types: Vec<Message<'data>>,
    first_nullable: Option<usize>,
}

impl<'data> TypeTable<'data> {
    const FIELD: u32 = 30;
    const TYPE: u32 = 1;
    const FIRST_NULLABLE: u32 = 2;
    const MAX_DEPTH: usize = 64;

    fn of(message: &Message<'data>) -> Result<Self, WireError> {
        let Some(table) = message.message(Self::FIELD)? else {
            return Ok(Self::default());
        };
        Ok(Self {
            types: table.messages(Self::TYPE)?,
            first_nullable: table
                .index(Self::FIRST_NULLABLE)
                .and_then(|index| usize::try_from(index).ok()),
        })
    }

    fn resolve(
        &self,
        index: u32,
        names: &NameResolver,
    ) -> Result<Option<TypeReference>, WireError> {
        self.resolve_at(index, names, 0)
    }

    fn resolve_at(
        &self,
        index: u32,
        names: &NameResolver,
        depth: usize,
    ) -> Result<Option<TypeReference>, WireError> {
        if depth >= Self::MAX_DEPTH {
            return Ok(None);
        }
        let index = usize::try_from(index).ok();
        let Some((index, message)) =
            index.and_then(|index| self.types.get(index).map(|ty| (index, ty)))
        else {
            return Ok(None);
        };
        let mut ty = TypeReference::parse_at(message, names, self, depth + 1)?;
        if self
            .first_nullable
            .is_some_and(|first_nullable| index >= first_nullable)
        {
            ty.nullable = true;
        }
        Ok(Some(ty))
    }
}

fn declared_type(
    message: &Message<'_>,
    inline: u32,
    indexed: u32,
    names: &NameResolver,
    types: &TypeTable<'_>,
) -> Result<Option<TypeReference>, WireError> {
    if let Some(ty) = message.message(inline)? {
        return TypeReference::parse(&ty, names, types).map(Some);
    }
    match message.index(indexed) {
        Some(index) => types.resolve(index, names),
        None => Ok(None),
    }
}

/// The JVM method a declaration compiled to, when the compiler recorded it.
///
/// Kotlin names and JVM names diverge — `internal` members carry a module
/// suffix, properties become accessors — so the recorded signature is the only
/// sound way to attach metadata to a decompiled member.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JvmSignature {
    pub name: String,
    pub descriptor: String,
}

impl JvmSignature {
    const NAME: u32 = 1;
    const DESCRIPTOR: u32 = 2;

    fn parse(message: &Message<'_>, names: &NameResolver, fallback: Option<&str>) -> Option<Self> {
        let name = message
            .index(Self::NAME)
            .and_then(|index| names.string(index))
            .or_else(|| fallback.map(str::to_string))?;
        let descriptor = message
            .index(Self::DESCRIPTOR)
            .and_then(|index| names.string(index))?;
        Some(Self { name, descriptor })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ValueParameter {
    pub name: String,
    pub ty: Option<TypeReference>,
    pub has_default: bool,
    /// The source element type of a `vararg` parameter. The JVM parameter type
    /// is an array and does not retain the element's Kotlin nullability.
    pub vararg_element_type: Option<TypeReference>,
}

impl ValueParameter {
    const FLAGS: u32 = 1;
    const NAME: u32 = 2;
    const TYPE: u32 = 3;
    const VARARG_ELEMENT_TYPE: u32 = 4;
    const TYPE_ID: u32 = 5;
    const VARARG_ELEMENT_TYPE_ID: u32 = 6;
    const DECLARES_DEFAULT_VALUE: u64 = 1 << 1;

    fn declares_default(flags: u64) -> bool {
        flags & Self::DECLARES_DEFAULT_VALUE != 0
    }

    fn parse(
        message: &Message<'_>,
        names: &NameResolver,
        types: &TypeTable<'_>,
    ) -> Result<Option<Self>, WireError> {
        let Some(name) = message
            .index(Self::NAME)
            .and_then(|index| names.string(index))
        else {
            return Ok(None);
        };
        let ty = declared_type(&message, Self::TYPE, Self::TYPE_ID, names, types)?;
        let vararg_element_type = declared_type(
            &message,
            Self::VARARG_ELEMENT_TYPE,
            Self::VARARG_ELEMENT_TYPE_ID,
            names,
            types,
        )?;
        Ok(Some(Self {
            name,
            ty,
            has_default: Self::declares_default(message.varint(Self::FLAGS).unwrap_or_default()),
            vararg_element_type,
        }))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    pub name: String,
    pub flags: DeclarationFlags,
    pub return_type: Option<TypeReference>,
    pub parameters: Vec<ValueParameter>,
    pub signature: Option<JvmSignature>,
    /// Whether the function is an extension, whose receiver the compiler passes
    /// as a parameter that the source parameter list does not mention.
    pub has_receiver: bool,
    /// The source receiver type when encoded inline. Some metadata versions
    /// refer through a type table instead; `has_receiver` remains authoritative
    /// for parameter layout in that case.
    pub receiver_type: Option<TypeReference>,
}

impl Function {
    /// Field 1 holds the flags of a metadata version this reader predates.
    const FLAGS: u32 = 9;
    const NAME: u32 = 2;
    const RETURN_TYPE: u32 = 3;
    const RETURN_TYPE_ID: u32 = 7;
    const RECEIVER_TYPE: u32 = 5;
    const RECEIVER_TYPE_ID: u32 = 8;
    const VALUE_PARAMETER: u32 = 6;
    /// `JvmProtoBuf.methodSignature`, an extension on `Function`.
    const JVM_SIGNATURE: u32 = 100;

    fn parse(
        message: &Message<'_>,
        names: &NameResolver,
        types: &TypeTable<'_>,
    ) -> Result<Option<Self>, WireError> {
        let Some(name) = message
            .index(Self::NAME)
            .and_then(|index| names.string(index))
        else {
            return Ok(None);
        };
        let mut parameters = Vec::new();
        for parameter in message.messages(Self::VALUE_PARAMETER)? {
            if let Some(parameter) = ValueParameter::parse(&parameter, names, types)? {
                parameters.push(parameter);
            }
        }
        let receiver_type = declared_type(
            message,
            Self::RECEIVER_TYPE,
            Self::RECEIVER_TYPE_ID,
            names,
            types,
        )?;
        Ok(Some(Self {
            signature: message
                .message(Self::JVM_SIGNATURE)?
                .and_then(|signature| JvmSignature::parse(&signature, names, Some(&name))),
            return_type: declared_type(
                message,
                Self::RETURN_TYPE,
                Self::RETURN_TYPE_ID,
                names,
                types,
            )?,
            has_receiver: receiver_type.is_some()
                || message.value(Self::RECEIVER_TYPE_ID).is_some(),
            receiver_type,
            flags: DeclarationFlags::of(message.varint(Self::FLAGS)),
            name,
            parameters,
        }))
    }

    /// The JVM signature implied by the source declaration when Kotlin omits
    /// the redundant `JvmProtoBuf.methodSignature` extension.
    pub(crate) fn default_jvm_signature(&self) -> Option<JvmSignature> {
        let mut descriptor = String::from("(");
        if self.has_receiver {
            descriptor.push_str(
                &self
                    .receiver_type
                    .as_ref()?
                    .jvm_descriptor(JvmTypePosition::Parameter)?,
            );
        }
        for parameter in &self.parameters {
            descriptor.push_str(
                &parameter
                    .ty
                    .as_ref()?
                    .jvm_descriptor(JvmTypePosition::Parameter)?,
            );
        }
        if self.flags.is_suspend() {
            descriptor.push_str("Lkotlin/coroutines/Continuation;");
        }
        descriptor.push(')');
        if self.flags.is_suspend() {
            descriptor.push_str("Ljava/lang/Object;");
        } else {
            descriptor.push_str(
                &self
                    .return_type
                    .as_ref()?
                    .jvm_descriptor(JvmTypePosition::Return)?,
            );
        }
        Some(JvmSignature {
            name: self.name.clone(),
            descriptor,
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Constructor {
    pub flags: DeclarationFlags,
    pub parameters: Vec<ValueParameter>,
    pub signature: Option<JvmSignature>,
}

impl Constructor {
    const FLAGS: u32 = 1;
    const VALUE_PARAMETER: u32 = 2;
    /// `JvmProtoBuf.constructorSignature`, an extension on `Constructor`.
    const JVM_SIGNATURE: u32 = 100;

    fn parse(
        message: &Message<'_>,
        names: &NameResolver,
        types: &TypeTable<'_>,
    ) -> Result<Self, WireError> {
        let mut parameters = Vec::new();
        for parameter in message.messages(Self::VALUE_PARAMETER)? {
            if let Some(parameter) = ValueParameter::parse(&parameter, names, types)? {
                parameters.push(parameter);
            }
        }
        Ok(Self {
            signature: message
                .message(Self::JVM_SIGNATURE)?
                .and_then(|signature| JvmSignature::parse(&signature, names, Some("<init>"))),
            flags: DeclarationFlags::of(message.varint(Self::FLAGS)),
            parameters,
        })
    }

    /// The JVM constructor signature implied by source parameter types when
    /// metadata omits the redundant signature extension.
    pub(crate) fn default_jvm_signature(&self) -> Option<JvmSignature> {
        let mut descriptor = String::from("(");
        for parameter in &self.parameters {
            descriptor.push_str(
                &parameter
                    .ty
                    .as_ref()?
                    .jvm_descriptor(JvmTypePosition::Parameter)?,
            );
        }
        descriptor.push_str(")V");
        Some(JvmSignature {
            name: "<init>".to_string(),
            descriptor,
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Property {
    pub name: String,
    pub flags: DeclarationFlags,
    pub ty: Option<TypeReference>,
    /// Whether the property is an extension whose receiver is the first JVM
    /// parameter of its accessors.
    pub has_receiver: bool,
    pub receiver_type: Option<TypeReference>,
    /// The backing field, when the property has one.
    pub field: Option<JvmSignature>,
    pub getter: Option<JvmSignature>,
    pub setter: Option<JvmSignature>,
    pub getter_is_default: bool,
    pub setter_is_default: bool,
}

impl Property {
    /// Field 1 holds the flags of a metadata version this reader predates.
    const FLAGS: u32 = 11;
    const NAME: u32 = 2;
    const RETURN_TYPE: u32 = 3;
    const RETURN_TYPE_ID: u32 = 9;
    const RECEIVER_TYPE: u32 = 5;
    const RECEIVER_TYPE_ID: u32 = 10;
    const GETTER_FLAGS: u32 = 7;
    const SETTER_FLAGS: u32 = 8;
    /// `JvmProtoBuf.propertySignature`, an extension on `Property`.
    const JVM_SIGNATURE: u32 = 100;
    const FIELD: u32 = 1;
    /// Field 2 is the synthetic method that carries a property's annotations.
    const GETTER: u32 = 3;
    const SETTER: u32 = 4;

    pub fn is_variable(&self) -> bool {
        self.flags.bits(8, 1) == 1
    }

    fn parse(
        message: &Message<'_>,
        names: &NameResolver,
        types: &TypeTable<'_>,
    ) -> Result<Option<Self>, WireError> {
        let Some(name) = message
            .index(Self::NAME)
            .and_then(|index| names.string(index))
        else {
            return Ok(None);
        };
        let signature = message.message(Self::JVM_SIGNATURE)?;
        let accessor = |field: u32| -> Result<Option<JvmSignature>, WireError> {
            let Some(signature) = signature.as_ref() else {
                return Ok(None);
            };
            Ok(signature
                .message(field)?
                .and_then(|accessor| JvmSignature::parse(&accessor, names, None)))
        };
        let field = match signature
            .as_ref()
            .map(|signature| signature.message(Self::FIELD))
        {
            Some(Ok(Some(field))) => {
                let name = field.index(1).and_then(|index| names.string(index));
                let descriptor = field.index(2).and_then(|index| names.string(index));
                name.zip(descriptor)
                    .map(|(name, descriptor)| JvmSignature { name, descriptor })
            }
            _ => None,
        };
        let receiver_type = declared_type(
            message,
            Self::RECEIVER_TYPE,
            Self::RECEIVER_TYPE_ID,
            names,
            types,
        )?;
        Ok(Some(Self {
            getter: accessor(Self::GETTER)?,
            setter: accessor(Self::SETTER)?,
            field,
            getter_is_default: message.varint(Self::GETTER_FLAGS).unwrap_or_default() & (1 << 6)
                == 0,
            setter_is_default: message.varint(Self::SETTER_FLAGS).unwrap_or_default() & (1 << 6)
                == 0,
            has_receiver: receiver_type.is_some()
                || message.value(Self::RECEIVER_TYPE_ID).is_some(),
            receiver_type,
            ty: declared_type(
                message,
                Self::RETURN_TYPE,
                Self::RETURN_TYPE_ID,
                names,
                types,
            )?,
            flags: DeclarationFlags::of(message.varint(Self::FLAGS)),
            name,
        }))
    }
}

/// The declarations of one Kotlin class or file facade.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Declarations {
    pub name: Option<String>,
    /// The flags of the class itself, where these declarations came from one.
    pub flags: DeclarationFlags,
    pub functions: Vec<Function>,
    pub constructors: Vec<Constructor>,
    pub properties: Vec<Property>,
}

impl Declarations {
    const CLASS_FLAGS: u32 = 1;
    const CLASS_FQ_NAME: u32 = 3;
    const CLASS_CONSTRUCTOR: u32 = 8;
    const CLASS_FUNCTION: u32 = 9;
    const CLASS_PROPERTY: u32 = 10;
    const PACKAGE_FUNCTION: u32 = 3;
    const PACKAGE_PROPERTY: u32 = 4;

    pub(super) fn class(message: &Message<'_>, names: &NameResolver) -> Result<Self, WireError> {
        let types = TypeTable::of(message)?;
        let mut declarations = Self {
            name: message
                .index(Self::CLASS_FQ_NAME)
                .and_then(|index| names.qualified_name(index)),
            flags: DeclarationFlags::of(message.varint(Self::CLASS_FLAGS)),
            ..Self::default()
        };
        for constructor in message.messages(Self::CLASS_CONSTRUCTOR)? {
            declarations
                .constructors
                .push(Constructor::parse(&constructor, names, &types)?);
        }
        declarations.collect_members(
            message,
            names,
            &types,
            Self::CLASS_FUNCTION,
            Self::CLASS_PROPERTY,
        )?;
        Ok(declarations)
    }

    pub(super) fn package(message: &Message<'_>, names: &NameResolver) -> Result<Self, WireError> {
        let types = TypeTable::of(message)?;
        let mut declarations = Self::default();
        declarations.collect_members(
            message,
            names,
            &types,
            Self::PACKAGE_FUNCTION,
            Self::PACKAGE_PROPERTY,
        )?;
        Ok(declarations)
    }

    fn collect_members(
        &mut self,
        message: &Message<'_>,
        names: &NameResolver,
        types: &TypeTable<'_>,
        function_field: u32,
        property_field: u32,
    ) -> Result<(), WireError> {
        for function in message.messages(function_field)? {
            if let Some(function) = Function::parse(&function, names, types)? {
                self.functions.push(function);
            }
        }
        for property in message.messages(property_field)? {
            if let Some(property) = Property::parse(&property, names, types)? {
                self.properties.push(property);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn type_reference(name: &str, nullable: bool) -> TypeReference {
        TypeReference {
            nullable,
            name: Some(name.to_string()),
            arguments: Vec::new(),
        }
    }

    #[test]
    fn decodes_inline_generic_argument_type() {
        // Type(class_name=0, argument=Argument(type=Type(class_name=1)))
        let message = Message::parse(&[0x12, 0x04, 0x12, 0x02, 0x30, 0x01, 0x30, 0x00]).unwrap();
        let names = NameResolver::new(
            &Message::default(),
            vec!["kotlin/Array".into(), "kotlin/String".into()],
        )
        .unwrap();

        assert_eq!(
            TypeReference::parse(&message, &names, &TypeTable::default()).unwrap(),
            TypeReference {
                nullable: false,
                name: Some("kotlin.Array".to_string()),
                arguments: vec![TypeReference {
                    nullable: false,
                    name: Some("kotlin.String".to_string()),
                    arguments: Vec::new(),
                }],
            }
        );
    }

    #[test]
    fn visibility_reads_its_own_slice_of_the_flags() {
        assert_eq!(DeclarationFlags(3 << 1).visibility(), Visibility::Public);
        assert_eq!(DeclarationFlags(0).visibility(), Visibility::Internal);
        assert_eq!(DeclarationFlags(1 << 1).visibility(), Visibility::Private);
    }

    #[test]
    fn derives_default_extension_signature_from_metadata_types() {
        let function = Function {
            name: "decorate".to_string(),
            flags: DeclarationFlags::default(),
            return_type: Some(type_reference("kotlin/String", false)),
            parameters: vec![ValueParameter {
                name: "times".to_string(),
                ty: Some(type_reference("kotlin/Int", false)),
                has_default: true,
                vararg_element_type: None,
            }],
            signature: None,
            has_receiver: true,
            receiver_type: Some(type_reference("kotlin/String", false)),
        };

        assert_eq!(
            function.default_jvm_signature(),
            Some(JvmSignature {
                name: "decorate".to_string(),
                descriptor: "(Ljava/lang/String;I)Ljava/lang/String;".to_string(),
            })
        );
    }

    #[test]
    fn separates_default_and_annotation_flags() {
        assert!(!ValueParameter::declares_default(1));
        assert!(ValueParameter::declares_default(1 << 1));
    }

    #[test]
    fn derives_suspend_continuation_and_object_return() {
        let function = Function {
            name: "fetch".to_string(),
            flags: DeclarationFlags(1 << 13),
            return_type: Some(type_reference("kotlin/String", false)),
            parameters: vec![ValueParameter {
                name: "input".to_string(),
                ty: Some(type_reference("kotlin/String", true)),
                has_default: false,
                vararg_element_type: None,
            }],
            signature: None,
            has_receiver: false,
            receiver_type: None,
        };

        assert_eq!(
            function.default_jvm_signature(),
            Some(JvmSignature {
                name: "fetch".to_string(),
                descriptor: concat!(
                    "(Ljava/lang/String;Lkotlin/coroutines/Continuation;)",
                    "Ljava/lang/Object;"
                )
                .to_string(),
            })
        );
    }
}
