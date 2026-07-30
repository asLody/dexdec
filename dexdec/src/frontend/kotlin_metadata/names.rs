//! Resolution of metadata string and name indices.
//!
//! The serialized declarations address every name by index. Most indices point
//! into the annotation's own string array, but the compiler also folds common
//! JVM names into shorter records that replay a small edit on a shared string,
//! so resolution has to consult those records first.

use super::wire::{Message, WireError};

/// How a folded record rebuilds its string.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RecordOperation {
    /// The string is used as written.
    None,
    /// A class identifier: `.` separates the package, `$` nested classes.
    InternalToClassId,
    /// A desugared collection type: `kotlin.collections` is prepended.
    DesugaredCollection,
}

impl RecordOperation {
    fn of(value: u64) -> Self {
        match value {
            1 => Self::InternalToClassId,
            2 => Self::DesugaredCollection,
            _ => Self::None,
        }
    }
}

#[derive(Debug, Clone)]
struct Record {
    range: u32,
    predefined: Option<u32>,
    string: Option<String>,
    operation: RecordOperation,
    substring: Option<(u32, u32)>,
    replace: Option<(u32, u32)>,
}

impl Record {
    fn parse(message: &Message<'_>) -> Self {
        let substring = message.varints(4).ok().and_then(|bounds| match bounds[..] {
            [start, end, ..] => Some((start as u32, end as u32)),
            _ => None,
        });
        let replace = message.varints(5).ok().and_then(|chars| match chars[..] {
            [from, to, ..] => Some((from as u32, to as u32)),
            _ => None,
        });
        Self {
            range: message.index(1).unwrap_or(1),
            predefined: message.index(2),
            string: message
                .value(6)
                .and_then(super::wire::WireValue::bytes)
                .map(|bytes| String::from_utf8_lossy(bytes).into_owned()),
            operation: RecordOperation::of(message.varint(3).unwrap_or_default()),
            substring,
            replace,
        }
    }

    fn resolve(&self) -> Option<String> {
        let mut value = match (&self.string, self.predefined) {
            (Some(string), _) => string.clone(),
            (None, Some(index)) => PREDEFINED_STRINGS.get(index as usize)?.to_string(),
            (None, None) => return None,
        };
        if let Some((start, end)) = self.substring {
            let start = usize::try_from(start).ok()?;
            let end = usize::try_from(end).ok()?;
            value = value.get(start..end)?.to_string();
        }
        if let Some((from, to)) = self.replace {
            let from = char::from_u32(from)?;
            let to = char::from_u32(to)?;
            value = value.replace(from, to.encode_utf8(&mut [0u8; 4]));
        }
        Some(match self.operation {
            RecordOperation::None => value,
            RecordOperation::InternalToClassId => value.replace('$', ".").replace('/', "."),
            RecordOperation::DesugaredCollection => format!("kotlin.collections.{value}"),
        })
    }
}

/// Predefined names the compiler may reference instead of writing them out.
///
/// The order is part of the metadata format; an index that falls outside it
/// simply has no name rather than the wrong one.
const PREDEFINED_STRINGS: &[&str] = &[
    "kotlin/Any",
    "kotlin/Nothing",
    "kotlin/Unit",
    "kotlin/Throwable",
    "kotlin/Number",
    "kotlin/Byte",
    "kotlin/Double",
    "kotlin/Float",
    "kotlin/Int",
    "kotlin/Long",
    "kotlin/Short",
    "kotlin/Boolean",
    "kotlin/Char",
    "kotlin/CharSequence",
    "kotlin/String",
    "kotlin/Comparable",
    "kotlin/Enum",
    "kotlin/Array",
    "kotlin/ByteArray",
    "kotlin/DoubleArray",
    "kotlin/FloatArray",
    "kotlin/IntArray",
    "kotlin/LongArray",
    "kotlin/ShortArray",
    "kotlin/BooleanArray",
    "kotlin/CharArray",
    "kotlin/Cloneable",
    "kotlin/Annotation",
    "kotlin/collections/Iterable",
    "kotlin/collections/MutableIterable",
    "kotlin/collections/Collection",
    "kotlin/collections/MutableCollection",
    "kotlin/collections/List",
    "kotlin/collections/MutableList",
    "kotlin/collections/Set",
    "kotlin/collections/MutableSet",
    "kotlin/collections/Map",
    "kotlin/collections/MutableMap",
    "kotlin/collections/Map.Entry",
    "kotlin/collections/MutableMap.MutableEntry",
    "kotlin/collections/Iterator",
    "kotlin/collections/MutableIterator",
    "kotlin/collections/ListIterator",
    "kotlin/collections/MutableListIterator",
];

/// Maps metadata indices onto the strings the annotation carries.
pub struct NameResolver {
    strings: Vec<String>,
    records: Vec<Record>,
    local_names: std::collections::BTreeSet<u32>,
}

impl NameResolver {
    pub(super) fn new(table: &Message<'_>, strings: Vec<String>) -> Result<Self, WireError> {
        let mut records = Vec::new();
        for message in table.messages(1)? {
            let record = Record::parse(&message);
            for _ in 0..record.range.max(1) {
                records.push(record.clone());
            }
        }
        Ok(Self {
            strings,
            records,
            local_names: table
                .varints(5)?
                .into_iter()
                .filter_map(|index| u32::try_from(index).ok())
                .collect(),
        })
    }

    /// Resolves a plain string index.
    pub fn string(&self, index: u32) -> Option<String> {
        if let Some(record) = self.records.get(index as usize) {
            if record.string.is_some() || record.predefined.is_some() {
                return record.resolve();
            }
        }
        self.strings.get(index as usize).cloned()
    }

    /// Resolves a class name index into a dotted name.
    ///
    /// Records may hold the name either as an internal name or as a full type
    /// descriptor, depending on how the compiler folded it, so both are reduced
    /// to the same dotted form.
    pub fn qualified_name(&self, index: u32) -> Option<String> {
        let name = self.string(index)?;
        let name = name
            .strip_prefix('L')
            .and_then(|name| name.strip_suffix(';'))
            .unwrap_or(&name);
        Some(name.replace('/', ".").replace('$', "."))
    }

    pub fn is_local(&self, index: u32) -> bool {
        self.local_names.contains(&index)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_plain_index_reads_the_annotation_string_array() {
        let resolver = NameResolver {
            strings: vec!["first".into(), "second".into()],
            records: Vec::new(),
            local_names: Default::default(),
        };
        assert_eq!(resolver.string(1).as_deref(), Some("second"));
        assert_eq!(resolver.string(7), None);
    }

    #[test]
    fn a_predefined_record_resolves_without_the_string_array() {
        let record = Record {
            range: 1,
            predefined: Some(14),
            string: None,
            operation: RecordOperation::None,
            substring: None,
            replace: None,
        };
        let resolver = NameResolver {
            strings: Vec::new(),
            records: vec![record],
            local_names: Default::default(),
        };
        assert_eq!(resolver.string(0).as_deref(), Some("kotlin/String"));
    }

    #[test]
    fn a_class_id_record_replaces_the_jvm_separators() {
        let record = Record {
            range: 1,
            predefined: None,
            string: Some("com/example/Outer$Inner".into()),
            operation: RecordOperation::InternalToClassId,
            substring: None,
            replace: None,
        };
        let resolver = NameResolver {
            strings: Vec::new(),
            records: vec![record],
            local_names: Default::default(),
        };
        assert_eq!(
            resolver.string(0).as_deref(),
            Some("com.example.Outer.Inner")
        );
    }
}
