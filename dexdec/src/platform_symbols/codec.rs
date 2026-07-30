use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, Cursor};

use super::{
    PlatformAnnotation, PlatformAnnotationValue, PlatformClass, PlatformConstant,
    PlatformConstantDomain, PlatformConstantKind, PlatformConstantMember, PlatformFamily,
    PlatformField, PlatformFieldReference, PlatformMethod, PlatformSymbolDatabase, PlatformTarget,
    SymbolAvailability, SymbolSource,
};

/// Deterministic, checksummed codec for `.dexsym` databases.
pub struct DexSymbolsCodec;

impl DexSymbolsCodec {
    const MAGIC: &'static [u8; 8] = b"DXSYMS\0\x01";
    const MAJOR: u16 = 2;
    const MINOR: u16 = 0;
    const FLAG_ZSTD: u32 = 1;
    const NONE: u32 = u32::MAX;
    const MAX_PAYLOAD: usize = 512 * 1024 * 1024;
    const MAX_COUNT: usize = 16 * 1024 * 1024;

    pub fn encode(database: &PlatformSymbolDatabase) -> io::Result<Vec<u8>> {
        let strings = StringPool::build(database)?;
        let mut payload = BinaryWriter::default();
        payload.u8(database.default_target.family.code());
        payload.u16(database.default_target.version);
        strings.write(&mut payload)?;
        payload.count(database.sources.len())?;
        for source in &database.sources {
            payload.u32(strings.id(&source.name)?);
            payload.u8(source.family.code());
            payload.i16(source.priority);
        }
        let variants = database.classes.values().map(Vec::len).sum::<usize>();
        payload.count(variants)?;
        for class in database.classes.values().flatten() {
            Self::write_class(&mut payload, &strings, class)?;
        }

        let raw = payload.finish();
        let checksum = crc32fast::hash(&raw);
        let stored = zstd::stream::encode_all(Cursor::new(&raw), 8)?;
        let mut output = BinaryWriter::default();
        output.bytes(Self::MAGIC);
        output.u16(Self::MAJOR);
        output.u16(Self::MINOR);
        output.u32(Self::FLAG_ZSTD);
        output.u64(raw.len() as u64);
        output.u64(stored.len() as u64);
        output.u32(checksum);
        output.bytes(&stored);
        Ok(output.finish())
    }

    pub fn decode(bytes: &[u8]) -> io::Result<PlatformSymbolDatabase> {
        let mut header = BinaryReader::new(bytes);
        if header.bytes(Self::MAGIC.len())? != Self::MAGIC {
            return Err(invalid_data("invalid dexsym header"));
        }
        let major = header.u16()?;
        let minor = header.u16()?;
        if major != Self::MAJOR || minor > Self::MINOR {
            return Err(invalid_data("unsupported dexsym format version"));
        }
        let flags = header.u32()?;
        if flags & !Self::FLAG_ZSTD != 0 {
            return Err(invalid_data("unsupported dexsym feature flags"));
        }
        let raw_len = header.usize_from_u64("payload")?;
        let stored_len = header.usize_from_u64("stored payload")?;
        if raw_len > Self::MAX_PAYLOAD || stored_len > Self::MAX_PAYLOAD {
            return Err(invalid_data("dexsym payload exceeds safety limit"));
        }
        let checksum = header.u32()?;
        let stored = header.bytes(stored_len)?;
        header.finish()?;

        let raw = if flags & Self::FLAG_ZSTD != 0 {
            let decoded = zstd::stream::decode_all(Cursor::new(stored))?;
            if decoded.len() != raw_len {
                return Err(invalid_data("dexsym uncompressed length mismatch"));
            }
            decoded
        } else {
            if stored.len() != raw_len {
                return Err(invalid_data("dexsym payload length mismatch"));
            }
            stored.to_vec()
        };
        if crc32fast::hash(&raw) != checksum {
            return Err(invalid_data("dexsym payload checksum mismatch"));
        }

        let mut reader = BinaryReader::new(&raw);
        let default_target = PlatformTarget {
            family: PlatformFamily::from_code(reader.u8()?)?,
            version: reader.u16()?,
        };
        let strings = StringPool::read(&mut reader)?;
        let source_count = reader.count("source")?;
        let mut sources = Vec::with_capacity(source_count);
        for _ in 0..source_count {
            sources.push(SymbolSource {
                name: strings.get(reader.u32()?)?.to_string(),
                family: PlatformFamily::from_code(reader.u8()?)?,
                priority: reader.i16()?,
            });
        }
        let class_count = reader.count("class")?;
        let mut classes = BTreeMap::<String, Vec<PlatformClass>>::new();
        for _ in 0..class_count {
            let class = Self::read_class(&mut reader, &strings, sources.len())?;
            classes
                .entry(class.descriptor.clone())
                .or_default()
                .push(class);
        }
        reader.finish()?;
        for variants in classes.values_mut() {
            variants.sort_by_key(|variant| {
                (
                    variant.source,
                    variant.availability.since,
                    variant.availability.until,
                )
            });
        }
        Ok(PlatformSymbolDatabase {
            default_target,
            sources,
            classes,
        })
    }

    fn write_class(
        writer: &mut BinaryWriter,
        strings: &StringPool,
        class: &PlatformClass,
    ) -> io::Result<()> {
        writer.u32(strings.id(&class.descriptor)?);
        writer.u32(class.source);
        writer.u16(class.availability.since);
        writer.u16(class.availability.until);
        writer.u32(class.access_flags);
        writer.option_string(strings, class.super_class.as_deref())?;
        writer.string_list(strings, &class.interfaces)?;
        writer.option_string(strings, class.signature.as_deref())?;
        writer.annotations(strings, &class.annotations)?;
        writer.count(class.fields.len())?;
        for field in &class.fields {
            writer.u32(strings.id(&field.name)?);
            writer.u32(strings.id(&field.descriptor)?);
            writer.option_string(strings, field.signature.as_deref())?;
            writer.u32(field.access_flags);
            writer.optional_constant(strings, field.constant.as_ref())?;
            writer.annotations(strings, &field.annotations)?;
        }
        writer.count(class.methods.len())?;
        for method in &class.methods {
            writer.u32(strings.id(&method.name)?);
            writer.u32(strings.id(&method.descriptor)?);
            writer.option_string(strings, method.signature.as_deref())?;
            writer.u32(method.access_flags);
            writer.string_list(strings, &method.exceptions)?;
            writer.count(method.parameter_names.len())?;
            for name in &method.parameter_names {
                writer.option_string(strings, name.as_deref())?;
            }
            writer.annotations(strings, &method.annotations)?;
            writer.count(method.parameter_annotations.len())?;
            for annotations in &method.parameter_annotations {
                writer.annotations(strings, annotations)?;
            }
            writer.count(method.parameter_domains.len())?;
            for domain in &method.parameter_domains {
                writer.constant_domain(strings, domain.as_ref())?;
            }
        }
        Ok(())
    }

    fn read_class(
        reader: &mut BinaryReader<'_>,
        strings: &StringPool,
        source_count: usize,
    ) -> io::Result<PlatformClass> {
        let descriptor = strings.get(reader.u32()?)?.to_string();
        let source = reader.u32()?;
        if source as usize >= source_count {
            return Err(invalid_data("class references an invalid source"));
        }
        let availability = SymbolAvailability::new(reader.u16()?, reader.u16()?)?;
        let access_flags = reader.u32()?;
        let super_class = reader.option_string(strings)?;
        let interfaces = reader.string_list(strings)?;
        let signature = reader.option_string(strings)?;
        let annotations = reader.annotations(strings)?;
        let field_count = reader.count("field")?;
        let mut fields = Vec::with_capacity(field_count);
        for _ in 0..field_count {
            let name = strings.get(reader.u32()?)?.to_string();
            let descriptor = strings.get(reader.u32()?)?.to_string();
            let signature = reader.option_string(strings)?;
            let access_flags = reader.u32()?;
            let constant = reader.optional_constant(strings)?;
            let annotations = reader.annotations(strings)?;
            fields.push(PlatformField {
                name,
                descriptor,
                signature,
                access_flags,
                constant,
                annotations,
            });
        }
        let method_count = reader.count("method")?;
        let mut methods = Vec::with_capacity(method_count);
        for _ in 0..method_count {
            let name = strings.get(reader.u32()?)?.to_string();
            let descriptor = strings.get(reader.u32()?)?.to_string();
            let signature = reader.option_string(strings)?;
            let access_flags = reader.u32()?;
            let exceptions = reader.string_list(strings)?;
            let parameter_count = reader.count("parameter")?;
            let mut parameter_names = Vec::with_capacity(parameter_count);
            for _ in 0..parameter_count {
                parameter_names.push(reader.option_string(strings)?);
            }
            let annotations = reader.annotations(strings)?;
            let annotation_parameter_count = reader.count("annotation parameter")?;
            let mut parameter_annotations = Vec::with_capacity(annotation_parameter_count);
            for _ in 0..annotation_parameter_count {
                parameter_annotations.push(reader.annotations(strings)?);
            }
            let domain_parameter_count = reader.count("constant-domain parameter")?;
            let mut parameter_domains = Vec::with_capacity(domain_parameter_count);
            for _ in 0..domain_parameter_count {
                parameter_domains.push(reader.constant_domain(strings)?);
            }
            methods.push(PlatformMethod {
                name,
                descriptor,
                signature,
                access_flags,
                exceptions,
                parameter_names,
                annotations,
                parameter_annotations,
                parameter_domains,
            });
        }
        Ok(PlatformClass {
            descriptor,
            source,
            availability,
            access_flags,
            super_class,
            interfaces,
            signature,
            annotations,
            fields,
            methods,
        })
    }
}

struct StringPool {
    strings: Vec<String>,
    ids: BTreeMap<String, u32>,
}

impl StringPool {
    fn build(database: &PlatformSymbolDatabase) -> io::Result<Self> {
        let mut strings = BTreeSet::new();
        for source in &database.sources {
            strings.insert(source.name.clone());
        }
        for class in database.classes.values().flatten() {
            strings.insert(class.descriptor.clone());
            strings.extend(class.super_class.iter().cloned());
            strings.extend(class.interfaces.iter().cloned());
            strings.extend(class.signature.iter().cloned());
            Self::collect_annotations(&mut strings, &class.annotations);
            for field in &class.fields {
                strings.insert(field.name.clone());
                strings.insert(field.descriptor.clone());
                strings.extend(field.signature.iter().cloned());
                if let Some(PlatformConstant::String(value)) = &field.constant {
                    strings.insert(value.clone());
                }
                Self::collect_annotations(&mut strings, &field.annotations);
            }
            for method in &class.methods {
                strings.insert(method.name.clone());
                strings.insert(method.descriptor.clone());
                strings.extend(method.signature.iter().cloned());
                strings.extend(method.exceptions.iter().cloned());
                strings.extend(method.parameter_names.iter().flatten().cloned());
                Self::collect_annotations(&mut strings, &method.annotations);
                for annotations in &method.parameter_annotations {
                    Self::collect_annotations(&mut strings, annotations);
                }
                for domain in method.parameter_domains.iter().flatten() {
                    for member in &domain.members {
                        Self::collect_field_reference(&mut strings, &member.field);
                        if let PlatformConstant::String(value) = &member.value {
                            strings.insert(value.clone());
                        }
                    }
                }
            }
        }
        if strings.len() > DexSymbolsCodec::MAX_COUNT {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "too many strings in symbol database",
            ));
        }
        let strings = strings.into_iter().collect::<Vec<_>>();
        let ids = strings
            .iter()
            .enumerate()
            .map(|(index, value)| (value.clone(), index as u32))
            .collect();
        Ok(Self { strings, ids })
    }

    fn collect_annotations(strings: &mut BTreeSet<String>, annotations: &[PlatformAnnotation]) {
        for annotation in annotations {
            strings.insert(annotation.descriptor.clone());
            for (name, value) in &annotation.elements {
                strings.insert(name.clone());
                Self::collect_annotation_value(strings, value);
            }
        }
    }

    fn collect_annotation_value(strings: &mut BTreeSet<String>, value: &PlatformAnnotationValue) {
        match value {
            PlatformAnnotationValue::Boolean(_)
            | PlatformAnnotationValue::Integer(_)
            | PlatformAnnotationValue::Float(_)
            | PlatformAnnotationValue::Double(_) => {}
            PlatformAnnotationValue::String(value) | PlatformAnnotationValue::Type(value) => {
                strings.insert(value.clone());
            }
            PlatformAnnotationValue::Enum {
                descriptor,
                constant,
            } => {
                strings.insert(descriptor.clone());
                strings.insert(constant.clone());
            }
            PlatformAnnotationValue::Field(field) => {
                Self::collect_field_reference(strings, field);
            }
            PlatformAnnotationValue::Annotation(annotation) => {
                Self::collect_annotations(strings, std::slice::from_ref(annotation));
            }
            PlatformAnnotationValue::Array(values) => {
                for value in values {
                    Self::collect_annotation_value(strings, value);
                }
            }
        }
    }

    fn collect_field_reference(strings: &mut BTreeSet<String>, field: &PlatformFieldReference) {
        strings.insert(field.owner.clone());
        strings.insert(field.name.clone());
        strings.insert(field.descriptor.clone());
    }

    fn write(&self, writer: &mut BinaryWriter) -> io::Result<()> {
        writer.count(self.strings.len())?;
        for value in &self.strings {
            writer.count(value.len())?;
            writer.bytes(value.as_bytes());
        }
        Ok(())
    }

    fn read(reader: &mut BinaryReader<'_>) -> io::Result<Self> {
        let count = reader.count("string")?;
        let mut strings = Vec::with_capacity(count);
        for _ in 0..count {
            let len = reader.count("string byte")?;
            let bytes = reader.bytes(len)?;
            let value = std::str::from_utf8(bytes)
                .map_err(|source| io::Error::new(io::ErrorKind::InvalidData, source))?
                .to_string();
            strings.push(value);
        }
        let ids = strings
            .iter()
            .enumerate()
            .map(|(index, value)| (value.clone(), index as u32))
            .collect();
        Ok(Self { strings, ids })
    }

    fn id(&self, value: &str) -> io::Result<u32> {
        self.ids
            .get(value)
            .copied()
            .ok_or_else(|| invalid_data("string missing from dexsym pool"))
    }

    fn get(&self, id: u32) -> io::Result<&str> {
        self.strings
            .get(id as usize)
            .map(String::as_str)
            .ok_or_else(|| invalid_data("invalid dexsym string id"))
    }
}

#[derive(Default)]
struct BinaryWriter {
    bytes: Vec<u8>,
}

impl BinaryWriter {
    fn finish(self) -> Vec<u8> {
        self.bytes
    }

    fn bytes(&mut self, value: &[u8]) {
        self.bytes.extend_from_slice(value);
    }

    fn u8(&mut self, value: u8) {
        self.bytes.push(value);
    }

    fn u16(&mut self, value: u16) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn i16(&mut self, value: i16) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn u32(&mut self, value: u32) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn u64(&mut self, value: u64) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn i64(&mut self, value: i64) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn count(&mut self, value: usize) -> io::Result<()> {
        let value = u32::try_from(value)
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "count exceeds u32"))?;
        self.u32(value);
        Ok(())
    }

    fn option_string(&mut self, strings: &StringPool, value: Option<&str>) -> io::Result<()> {
        self.u32(match value {
            Some(value) => strings.id(value)?,
            None => DexSymbolsCodec::NONE,
        });
        Ok(())
    }

    fn string_list(&mut self, strings: &StringPool, values: &[String]) -> io::Result<()> {
        self.count(values.len())?;
        for value in values {
            self.u32(strings.id(value)?);
        }
        Ok(())
    }

    fn annotations(
        &mut self,
        strings: &StringPool,
        values: &[PlatformAnnotation],
    ) -> io::Result<()> {
        self.count(values.len())?;
        for value in values {
            self.annotation(strings, value)?;
        }
        Ok(())
    }

    fn annotation(&mut self, strings: &StringPool, value: &PlatformAnnotation) -> io::Result<()> {
        self.u32(strings.id(&value.descriptor)?);
        self.count(value.elements.len())?;
        for (name, value) in &value.elements {
            self.u32(strings.id(name)?);
            self.annotation_value(strings, value)?;
        }
        Ok(())
    }

    fn annotation_value(
        &mut self,
        strings: &StringPool,
        value: &PlatformAnnotationValue,
    ) -> io::Result<()> {
        match value {
            PlatformAnnotationValue::Boolean(value) => {
                self.u8(0);
                self.u8(u8::from(*value));
            }
            PlatformAnnotationValue::Integer(value) => {
                self.u8(1);
                self.i64(*value);
            }
            PlatformAnnotationValue::Float(value) => {
                self.u8(2);
                self.u32(*value);
            }
            PlatformAnnotationValue::Double(value) => {
                self.u8(3);
                self.u64(*value);
            }
            PlatformAnnotationValue::String(value) => {
                self.u8(4);
                self.u32(strings.id(value)?);
            }
            PlatformAnnotationValue::Type(value) => {
                self.u8(5);
                self.u32(strings.id(value)?);
            }
            PlatformAnnotationValue::Enum {
                descriptor,
                constant,
            } => {
                self.u8(6);
                self.u32(strings.id(descriptor)?);
                self.u32(strings.id(constant)?);
            }
            PlatformAnnotationValue::Field(field) => {
                self.u8(7);
                self.field_reference(strings, field)?;
            }
            PlatformAnnotationValue::Annotation(annotation) => {
                self.u8(8);
                self.annotation(strings, annotation)?;
            }
            PlatformAnnotationValue::Array(values) => {
                self.u8(9);
                self.count(values.len())?;
                for value in values {
                    self.annotation_value(strings, value)?;
                }
            }
        }
        Ok(())
    }

    fn field_reference(
        &mut self,
        strings: &StringPool,
        field: &PlatformFieldReference,
    ) -> io::Result<()> {
        self.u32(strings.id(&field.owner)?);
        self.u32(strings.id(&field.name)?);
        self.u32(strings.id(&field.descriptor)?);
        Ok(())
    }

    fn optional_constant(
        &mut self,
        strings: &StringPool,
        value: Option<&PlatformConstant>,
    ) -> io::Result<()> {
        match value {
            None => self.u8(0),
            Some(value) => {
                self.u8(1);
                self.constant(strings, value)?;
            }
        }
        Ok(())
    }

    fn constant(&mut self, strings: &StringPool, value: &PlatformConstant) -> io::Result<()> {
        match value {
            PlatformConstant::Integer(value) => {
                self.u8(0);
                self.i64(*value);
            }
            PlatformConstant::Float(value) => {
                self.u8(1);
                self.u32(*value);
            }
            PlatformConstant::Double(value) => {
                self.u8(2);
                self.u64(*value);
            }
            PlatformConstant::String(value) => {
                self.u8(3);
                self.u32(strings.id(value)?);
            }
        }
        Ok(())
    }

    fn constant_domain(
        &mut self,
        strings: &StringPool,
        domain: Option<&PlatformConstantDomain>,
    ) -> io::Result<()> {
        let Some(domain) = domain else {
            self.u8(0);
            return Ok(());
        };
        self.u8(1);
        self.u8(match domain.kind {
            PlatformConstantKind::Integer => 0,
            PlatformConstantKind::Long => 1,
            PlatformConstantKind::String => 2,
        });
        self.u8(u8::from(domain.flags));
        self.count(domain.members.len())?;
        for member in &domain.members {
            self.field_reference(strings, &member.field)?;
            self.constant(strings, &member.value)?;
        }
        Ok(())
    }
}

struct BinaryReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> BinaryReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn finish(&self) -> io::Result<()> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(invalid_data("trailing bytes in dexsym data"))
        }
    }

    fn bytes(&mut self, len: usize) -> io::Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| io::Error::new(io::ErrorKind::UnexpectedEof, "truncated dexsym data"))?;
        let bytes = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(bytes)
    }

    fn array<const N: usize>(&mut self) -> io::Result<[u8; N]> {
        self.bytes(N)?
            .try_into()
            .map_err(|_| invalid_data("invalid fixed-width value"))
    }

    fn u8(&mut self) -> io::Result<u8> {
        Ok(self.array::<1>()?[0])
    }

    fn u16(&mut self) -> io::Result<u16> {
        Ok(u16::from_le_bytes(self.array()?))
    }

    fn i16(&mut self) -> io::Result<i16> {
        Ok(i16::from_le_bytes(self.array()?))
    }

    fn u32(&mut self) -> io::Result<u32> {
        Ok(u32::from_le_bytes(self.array()?))
    }

    fn u64(&mut self) -> io::Result<u64> {
        Ok(u64::from_le_bytes(self.array()?))
    }

    fn i64(&mut self) -> io::Result<i64> {
        Ok(i64::from_le_bytes(self.array()?))
    }

    fn count(&mut self, kind: &'static str) -> io::Result<usize> {
        let count = self.u32()? as usize;
        if count > DexSymbolsCodec::MAX_COUNT {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("{kind} count exceeds safety limit"),
            ));
        }
        Ok(count)
    }

    fn usize_from_u64(&mut self, kind: &'static str) -> io::Result<usize> {
        usize::try_from(self.u64()?).map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("{kind} length exceeds address space"),
            )
        })
    }

    fn option_string(&mut self, strings: &StringPool) -> io::Result<Option<String>> {
        let id = self.u32()?;
        if id == DexSymbolsCodec::NONE {
            Ok(None)
        } else {
            strings.get(id).map(|value| Some(value.to_string()))
        }
    }

    fn string_list(&mut self, strings: &StringPool) -> io::Result<Vec<String>> {
        let count = self.count("string list")?;
        let mut values = Vec::with_capacity(count);
        for _ in 0..count {
            values.push(strings.get(self.u32()?)?.to_string());
        }
        Ok(values)
    }

    fn annotations(&mut self, strings: &StringPool) -> io::Result<Vec<PlatformAnnotation>> {
        let count = self.count("annotation")?;
        let mut values = Vec::with_capacity(count);
        for _ in 0..count {
            values.push(self.annotation(strings)?);
        }
        Ok(values)
    }

    fn annotation(&mut self, strings: &StringPool) -> io::Result<PlatformAnnotation> {
        self.annotation_at(strings, 0)
    }

    fn annotation_at(
        &mut self,
        strings: &StringPool,
        depth: usize,
    ) -> io::Result<PlatformAnnotation> {
        if depth >= 64 {
            return Err(invalid_data("annotation nesting exceeds safety limit"));
        }
        let descriptor = strings.get(self.u32()?)?.to_string();
        let count = self.count("annotation element")?;
        let mut elements = BTreeMap::new();
        for _ in 0..count {
            let name = strings.get(self.u32()?)?.to_string();
            let value = self.annotation_value(strings, depth + 1)?;
            elements.insert(name, value);
        }
        Ok(PlatformAnnotation {
            descriptor,
            elements,
        })
    }

    fn annotation_value(
        &mut self,
        strings: &StringPool,
        depth: usize,
    ) -> io::Result<PlatformAnnotationValue> {
        if depth >= 64 {
            return Err(invalid_data("annotation nesting exceeds safety limit"));
        }
        Ok(match self.u8()? {
            0 => PlatformAnnotationValue::Boolean(match self.u8()? {
                0 => false,
                1 => true,
                _ => return Err(invalid_data("invalid Boolean annotation value")),
            }),
            1 => PlatformAnnotationValue::Integer(self.i64()?),
            2 => PlatformAnnotationValue::Float(self.u32()?),
            3 => PlatformAnnotationValue::Double(self.u64()?),
            4 => PlatformAnnotationValue::String(strings.get(self.u32()?)?.to_string()),
            5 => PlatformAnnotationValue::Type(strings.get(self.u32()?)?.to_string()),
            6 => PlatformAnnotationValue::Enum {
                descriptor: strings.get(self.u32()?)?.to_string(),
                constant: strings.get(self.u32()?)?.to_string(),
            },
            7 => PlatformAnnotationValue::Field(self.field_reference(strings)?),
            8 => PlatformAnnotationValue::Annotation(Box::new(
                self.annotation_at(strings, depth + 1)?,
            )),
            9 => {
                let count = self.count("annotation array value")?;
                let mut values = Vec::with_capacity(count);
                for _ in 0..count {
                    values.push(self.annotation_value(strings, depth + 1)?);
                }
                PlatformAnnotationValue::Array(values)
            }
            _ => return Err(invalid_data("invalid annotation value kind")),
        })
    }

    fn field_reference(&mut self, strings: &StringPool) -> io::Result<PlatformFieldReference> {
        Ok(PlatformFieldReference {
            owner: strings.get(self.u32()?)?.to_string(),
            name: strings.get(self.u32()?)?.to_string(),
            descriptor: strings.get(self.u32()?)?.to_string(),
        })
    }

    fn optional_constant(&mut self, strings: &StringPool) -> io::Result<Option<PlatformConstant>> {
        match self.u8()? {
            0 => Ok(None),
            1 => self.constant(strings).map(Some),
            _ => Err(invalid_data("invalid optional constant tag")),
        }
    }

    fn constant(&mut self, strings: &StringPool) -> io::Result<PlatformConstant> {
        Ok(match self.u8()? {
            0 => PlatformConstant::Integer(self.i64()?),
            1 => PlatformConstant::Float(self.u32()?),
            2 => PlatformConstant::Double(self.u64()?),
            3 => PlatformConstant::String(strings.get(self.u32()?)?.to_string()),
            _ => return Err(invalid_data("invalid constant kind")),
        })
    }

    fn constant_domain(
        &mut self,
        strings: &StringPool,
    ) -> io::Result<Option<PlatformConstantDomain>> {
        match self.u8()? {
            0 => return Ok(None),
            1 => {}
            _ => return Err(invalid_data("invalid constant-domain tag")),
        }
        let kind = match self.u8()? {
            0 => PlatformConstantKind::Integer,
            1 => PlatformConstantKind::Long,
            2 => PlatformConstantKind::String,
            _ => return Err(invalid_data("invalid constant-domain kind")),
        };
        let flags = match self.u8()? {
            0 => false,
            1 => true,
            _ => return Err(invalid_data("invalid constant-domain flags value")),
        };
        let count = self.count("constant-domain member")?;
        let mut members = Vec::with_capacity(count);
        for _ in 0..count {
            members.push(PlatformConstantMember {
                field: self.field_reference(strings)?,
                value: self.constant(strings)?,
            });
        }
        Ok(Some(PlatformConstantDomain {
            kind,
            flags,
            members,
        }))
    }
}

fn invalid_data(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
