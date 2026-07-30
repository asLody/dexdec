use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, Cursor, Read};
use std::path::Path;

use quick_xml::events::{BytesStart, Event};
use quick_xml::Reader;

use super::{
    PlatformAnnotation, PlatformAnnotationValue, PlatformConstant, PlatformConstantDomain,
    PlatformConstantKind, PlatformConstantMember, PlatformFieldReference, PlatformSymbolDatabase,
};

const MAX_XML_FILE_SIZE: u64 = 64 * 1024 * 1024;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct AndroidMetadataStats {
    pub files: usize,
    pub annotations: usize,
    pub constant_domains: usize,
}

pub(crate) struct AndroidMetadataImporter;

impl AndroidMetadataImporter {
    pub(crate) fn apply(
        database: &mut PlatformSymbolDatabase,
        archive: &Path,
        api: u16,
    ) -> io::Result<AndroidMetadataStats> {
        let resolver = AndroidSymbolResolver::new(database, api);
        let records = ExternalAnnotationArchive::read(archive)?;
        let mut stats = AndroidMetadataStats {
            files: records.files,
            ..AndroidMetadataStats::default()
        };
        for item in records.items {
            let Some(target) = ExternalMethodParameter::parse(&item.name, &resolver) else {
                continue;
            };
            let annotations = item
                .annotations
                .into_iter()
                .map(|annotation| annotation.resolve(&resolver))
                .collect::<Vec<_>>();
            let domain = annotations
                .iter()
                .filter_map(|annotation| {
                    ConstantDomainDeclaration::from_annotation(annotation, &resolver)
                })
                .next();
            let Some(method) =
                database.method_variant_mut(api, &target.owner, &target.name, &target.descriptor)
            else {
                continue;
            };
            if method.parameter_annotations.len() <= target.parameter {
                method
                    .parameter_annotations
                    .resize_with(target.parameter + 1, Vec::new);
            }
            let parameter_annotations = &mut method.parameter_annotations[target.parameter];
            let before = parameter_annotations.len();
            parameter_annotations.extend(annotations);
            parameter_annotations.sort();
            parameter_annotations.dedup();
            stats.annotations += parameter_annotations.len() - before;

            if method.parameter_domains.len() <= target.parameter {
                method
                    .parameter_domains
                    .resize_with(target.parameter + 1, || None);
            }
            if let Some(domain) = domain {
                let slot = &mut method.parameter_domains[target.parameter];
                if slot.as_ref().is_none_or(|current| current == &domain) {
                    if slot.is_none() {
                        stats.constant_domains += 1;
                    }
                    *slot = Some(domain);
                }
            }
        }
        Ok(stats)
    }
}

struct ExternalAnnotationArchive {
    files: usize,
    items: Vec<ExternalItem>,
}

impl ExternalAnnotationArchive {
    fn read(path: &Path) -> io::Result<Self> {
        let bytes = std::fs::read(path)?;
        let mut archive = zip::ZipArchive::new(Cursor::new(bytes))
            .map_err(|source| archive_error(path, source))?;
        let mut files = 0;
        let mut items = Vec::new();
        for index in 0..archive.len() {
            let mut entry = archive
                .by_index(index)
                .map_err(|source| archive_error(path, source))?;
            if entry.is_dir() || !entry.name().ends_with("annotations.xml") {
                continue;
            }
            if entry.size() > MAX_XML_FILE_SIZE {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "{} exceeds Android annotation XML safety limit",
                        entry.name()
                    ),
                ));
            }
            let mut xml = Vec::with_capacity(entry.size() as usize);
            entry
                .by_ref()
                .take(MAX_XML_FILE_SIZE + 1)
                .read_to_end(&mut xml)?;
            if xml.len() as u64 > MAX_XML_FILE_SIZE {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "Android annotation XML exceeds safety limit",
                ));
            }
            items.extend(ExternalAnnotationXml::parse(&xml)?);
            files += 1;
        }
        Ok(Self { files, items })
    }
}

struct ExternalAnnotationXml;

impl ExternalAnnotationXml {
    fn parse(xml: &[u8]) -> io::Result<Vec<ExternalItem>> {
        let mut reader = Reader::from_reader(xml);
        reader.config_mut().trim_text(true);
        let mut buffer = Vec::new();
        let mut items = Vec::new();
        let mut item: Option<ExternalItem> = None;
        let mut annotation: Option<ExternalAnnotation> = None;
        loop {
            match reader.read_event_into(&mut buffer).map_err(xml_error)? {
                Event::Start(event) if event.name().as_ref() == b"item" => {
                    item = attribute(&event, b"name")?.map(|name| ExternalItem {
                        name,
                        annotations: Vec::new(),
                    });
                }
                Event::Start(event) if event.name().as_ref() == b"annotation" => {
                    annotation = attribute(&event, b"name")?.map(|name| ExternalAnnotation {
                        name,
                        values: BTreeMap::new(),
                    });
                }
                Event::Empty(event) if event.name().as_ref() == b"val" => {
                    if let (Some(annotation), Some(name), Some(value)) = (
                        annotation.as_mut(),
                        attribute(&event, b"name")?,
                        attribute(&event, b"val")?,
                    ) {
                        annotation.values.insert(name, value);
                    }
                }
                Event::End(event) if event.name().as_ref() == b"annotation" => {
                    if let (Some(item), Some(annotation)) = (item.as_mut(), annotation.take()) {
                        item.annotations.push(annotation);
                    }
                }
                Event::End(event) if event.name().as_ref() == b"item" => {
                    if let Some(item) = item.take() {
                        items.push(item);
                    }
                }
                Event::Eof => break,
                _ => {}
            }
            buffer.clear();
        }
        Ok(items)
    }
}

#[derive(Debug)]
struct ExternalItem {
    name: String,
    annotations: Vec<ExternalAnnotation>,
}

#[derive(Debug)]
struct ExternalAnnotation {
    name: String,
    values: BTreeMap<String, String>,
}

impl ExternalAnnotation {
    fn resolve(self, resolver: &AndroidSymbolResolver) -> PlatformAnnotation {
        let descriptor = format!("L{};", self.name.replace('.', "/"));
        let parser = ExternalAnnotationValueParser { resolver };
        let elements = self
            .values
            .into_iter()
            .filter_map(|(name, value)| parser.parse(&value).map(|value| (name, value)))
            .collect();
        PlatformAnnotation {
            descriptor,
            elements,
        }
    }
}

struct ExternalAnnotationValueParser<'a> {
    resolver: &'a AndroidSymbolResolver,
}

impl ExternalAnnotationValueParser<'_> {
    fn parse(&self, source: &str) -> Option<PlatformAnnotationValue> {
        let source = source.trim();
        if source == "true" || source == "false" {
            return Some(PlatformAnnotationValue::Boolean(source == "true"));
        }
        if let Some(value) = source
            .strip_prefix('"')
            .and_then(|value| value.strip_suffix('"'))
        {
            return Some(PlatformAnnotationValue::String(value.to_string()));
        }
        if let Some(values) = source
            .strip_prefix('{')
            .and_then(|value| value.strip_suffix('}'))
        {
            let values = values
                .split(',')
                .map(str::trim)
                .filter(|value| !value.is_empty())
                .map(|value| self.parse_atom(value))
                .collect::<Option<Vec<_>>>()?;
            return Some(PlatformAnnotationValue::Array(values));
        }
        self.parse_atom(source)
    }

    fn parse_atom(&self, source: &str) -> Option<PlatformAnnotationValue> {
        if let Some(field) = self.resolver.field(source) {
            return Some(PlatformAnnotationValue::Field(field.field.clone()));
        }
        parse_integer(source).map(PlatformAnnotationValue::Integer)
    }
}

struct ConstantDomainDeclaration;

impl ConstantDomainDeclaration {
    fn from_annotation(
        annotation: &PlatformAnnotation,
        resolver: &AndroidSymbolResolver,
    ) -> Option<PlatformConstantDomain> {
        let kind = match annotation.descriptor.as_str() {
            "Landroidx/annotation/IntDef;" | "Landroid/annotation/IntDef;" => {
                PlatformConstantKind::Integer
            }
            "Landroidx/annotation/LongDef;" | "Landroid/annotation/LongDef;" => {
                PlatformConstantKind::Long
            }
            "Landroidx/annotation/StringDef;" | "Landroid/annotation/StringDef;" => {
                PlatformConstantKind::String
            }
            _ => return None,
        };
        let flags = matches!(
            annotation.elements.get("flag"),
            Some(PlatformAnnotationValue::Boolean(true))
        );
        let PlatformAnnotationValue::Array(values) = annotation.elements.get("value")? else {
            return None;
        };
        let mut members = Vec::new();
        let mut seen = BTreeSet::new();
        for value in values {
            let PlatformAnnotationValue::Field(field) = value else {
                continue;
            };
            let constant = resolver.constant(field)?.clone();
            let compatible = matches!(
                (&kind, &constant),
                (
                    PlatformConstantKind::Integer | PlatformConstantKind::Long,
                    PlatformConstant::Integer(_)
                ) | (PlatformConstantKind::String, PlatformConstant::String(_))
            );
            if compatible && seen.insert(field.clone()) {
                members.push(PlatformConstantMember {
                    field: field.clone(),
                    value: constant,
                });
            }
        }
        (!members.is_empty()).then_some(PlatformConstantDomain {
            kind,
            flags,
            members,
        })
    }
}

#[derive(Debug)]
struct ExternalMethodParameter {
    owner: String,
    name: String,
    descriptor: String,
    parameter: usize,
}

impl ExternalMethodParameter {
    fn parse(source: &str, resolver: &AndroidSymbolResolver) -> Option<Self> {
        let (signature, parameter) = source.rsplit_once(' ')?;
        let parameter = parameter.parse::<usize>().ok()?;
        let mut components = signature.split_whitespace();
        let owner = resolver.class(components.next()?)?.to_string();
        let return_type = resolver.descriptor(components.next()?)?;
        let call = components.next()?;
        if components.next().is_some() {
            return None;
        }
        let open = call.find('(')?;
        let close = call.rfind(')')?;
        if close + 1 != call.len() {
            return None;
        }
        let name = call[..open].to_string();
        let parameters = split_parameters(&call[open + 1..close])?;
        if parameter >= parameters.len() {
            return None;
        }
        let parameters = parameters
            .into_iter()
            .map(|parameter| resolver.descriptor(parameter))
            .collect::<Option<String>>()?;
        let descriptor = format!("({parameters}){return_type}");
        Some(Self {
            owner,
            name,
            descriptor,
            parameter,
        })
    }
}

struct AndroidSymbolResolver {
    classes: BTreeMap<String, Option<String>>,
    fields: BTreeMap<String, Option<PlatformConstantMember>>,
    constants: BTreeMap<PlatformFieldReference, PlatformConstant>,
}

impl AndroidSymbolResolver {
    fn new(database: &PlatformSymbolDatabase, api: u16) -> Self {
        let mut classes = BTreeMap::new();
        for class in database.android_classes(api) {
            let name = java_class_name(&class.descriptor);
            insert_unique(&mut classes, name, class.descriptor.clone());
        }
        let mut fields = BTreeMap::new();
        let mut constants = BTreeMap::new();
        for class in database.android_classes(api) {
            let owner = java_class_name(&class.descriptor);
            for field in class.fields.iter().filter(|field| field.constant.is_some()) {
                let member = PlatformConstantMember {
                    field: PlatformFieldReference {
                        owner: class.descriptor.clone(),
                        name: field.name.clone(),
                        descriptor: field.descriptor.clone(),
                    },
                    value: field.constant.clone().expect("constant checked above"),
                };
                constants.insert(member.field.clone(), member.value.clone());
                insert_unique(&mut fields, format!("{owner}.{}", field.name), member);
            }
        }
        Self {
            classes,
            fields,
            constants,
        }
    }

    fn class(&self, name: &str) -> Option<&str> {
        self.classes.get(name)?.as_deref()
    }

    fn field(&self, name: &str) -> Option<&PlatformConstantMember> {
        self.fields.get(name)?.as_ref()
    }

    fn constant(&self, field: &PlatformFieldReference) -> Option<&PlatformConstant> {
        self.constants.get(field)
    }

    fn descriptor(&self, source: &str) -> Option<String> {
        let source = erase_generics(source.trim())?;
        let (element, dimensions) = strip_array_dimensions(&source)?;
        let element = match element {
            "void" => "V".to_string(),
            "boolean" => "Z".to_string(),
            "byte" => "B".to_string(),
            "char" => "C".to_string(),
            "short" => "S".to_string(),
            "int" => "I".to_string(),
            "long" => "J".to_string(),
            "float" => "F".to_string(),
            "double" => "D".to_string(),
            class => self.class(class)?.to_string(),
        };
        Some(format!("{}{}", "[".repeat(dimensions), element))
    }
}

fn insert_unique<T: PartialEq>(map: &mut BTreeMap<String, Option<T>>, key: String, value: T) {
    match map.entry(key) {
        std::collections::btree_map::Entry::Vacant(entry) => {
            entry.insert(Some(value));
        }
        std::collections::btree_map::Entry::Occupied(mut entry) => {
            if entry.get().as_ref() != Some(&value) {
                entry.insert(None);
            }
        }
    }
}

fn split_parameters(parameters: &str) -> Option<Vec<&str>> {
    if parameters.trim().is_empty() {
        return Some(Vec::new());
    }
    let mut depth = 0usize;
    let mut start = 0usize;
    let mut values = Vec::new();
    for (offset, character) in parameters.char_indices() {
        match character {
            '<' => depth = depth.checked_add(1)?,
            '>' => depth = depth.checked_sub(1)?,
            ',' if depth == 0 => {
                let value = parameters[start..offset].trim();
                if value.is_empty() {
                    return None;
                }
                values.push(value);
                start = offset + character.len_utf8();
            }
            _ => {}
        }
    }
    if depth != 0 {
        return None;
    }
    let value = parameters[start..].trim();
    if value.is_empty() {
        return None;
    }
    values.push(value);
    Some(values)
}

fn erase_generics(source: &str) -> Option<String> {
    let mut erased = String::with_capacity(source.len());
    let mut depth = 0usize;
    for character in source.chars() {
        match character {
            '<' => depth = depth.checked_add(1)?,
            '>' => depth = depth.checked_sub(1)?,
            _ if depth == 0 => erased.push(character),
            _ => {}
        }
    }
    (depth == 0).then(|| erased.trim().to_string())
}

fn strip_array_dimensions(mut source: &str) -> Option<(&str, usize)> {
    let mut dimensions = 0;
    if let Some(element) = source.strip_suffix("...") {
        source = element;
        dimensions += 1;
    }
    while let Some(element) = source.strip_suffix("[]") {
        source = element;
        dimensions += 1;
    }
    (!source.is_empty()).then_some((source, dimensions))
}

fn parse_integer(source: &str) -> Option<i64> {
    let source = source
        .strip_suffix('L')
        .or_else(|| source.strip_suffix('l'))
        .unwrap_or(source);
    if let Some(hex) = source
        .strip_prefix("-0x")
        .or_else(|| source.strip_prefix("-0X"))
    {
        return i64::from_str_radix(hex, 16).ok()?.checked_neg();
    }
    if let Some(hex) = source
        .strip_prefix("0x")
        .or_else(|| source.strip_prefix("0X"))
    {
        return i64::from_str_radix(hex, 16).ok();
    }
    source.parse().ok()
}

fn java_class_name(descriptor: &str) -> String {
    descriptor
        .strip_prefix('L')
        .and_then(|name| name.strip_suffix(';'))
        .unwrap_or(descriptor)
        .replace(['/', '$'], ".")
}

fn attribute(event: &BytesStart<'_>, name: &[u8]) -> io::Result<Option<String>> {
    for attribute in event.attributes().with_checks(false) {
        let attribute = attribute.map_err(xml_error)?;
        if attribute.key.as_ref() == name {
            return attribute
                .unescape_value()
                .map(|value| Some(value.into_owned()))
                .map_err(xml_error);
        }
    }
    Ok(None)
}

fn xml_error(source: impl std::fmt::Display) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, source.to_string())
}

fn archive_error(path: &Path, source: zip::result::ZipError) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!("{}: {source}", path.display()),
    )
}
