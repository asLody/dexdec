//! Protocol buffer wire-format reader.
//!
//! Kotlin serializes its declaration metadata with protocol buffers, so reading
//! `@kotlin.Metadata` means reading that encoding. Only the wire format is
//! implemented here: fields are addressed by number and the shape of each
//! message stays with the schema that describes it.

/// One field as it appears on the wire, before a schema gives it meaning.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum WireValue<'data> {
    Varint(u64),
    Fixed64(u64),
    Length(&'data [u8]),
    Fixed32(u32),
}

impl<'data> WireValue<'data> {
    pub(super) fn varint(&self) -> Option<u64> {
        match self {
            Self::Varint(value) => Some(*value),
            _ => None,
        }
    }

    pub(super) fn bytes(&self) -> Option<&'data [u8]> {
        match self {
            Self::Length(value) => Some(value),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum WireError {
    Truncated,
    UnknownWireType(u8),
    OversizedVarint,
}

impl std::fmt::Display for WireError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Truncated => formatter.write_str("protobuf message ends inside a field"),
            Self::UnknownWireType(tag) => write!(formatter, "unknown protobuf wire type {tag}"),
            Self::OversizedVarint => formatter.write_str("protobuf varint exceeds 64 bits"),
        }
    }
}

/// A cursor over one encoded message.
pub(super) struct WireReader<'data> {
    data: &'data [u8],
    offset: usize,
}

impl<'data> WireReader<'data> {
    pub(super) fn new(data: &'data [u8]) -> Self {
        Self { data, offset: 0 }
    }

    pub(super) fn is_empty(&self) -> bool {
        self.offset >= self.data.len()
    }

    pub(super) fn varint(&mut self) -> Result<u64, WireError> {
        let mut value = 0u64;
        let mut shift = 0u32;
        loop {
            let byte = *self.data.get(self.offset).ok_or(WireError::Truncated)?;
            self.offset += 1;
            if shift >= 64 {
                return Err(WireError::OversizedVarint);
            }
            value |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return Ok(value);
            }
            shift += 7;
        }
    }

    fn take(&mut self, length: usize) -> Result<&'data [u8], WireError> {
        let end = self
            .offset
            .checked_add(length)
            .ok_or(WireError::Truncated)?;
        let slice = self
            .data
            .get(self.offset..end)
            .ok_or(WireError::Truncated)?;
        self.offset = end;
        Ok(slice)
    }

    /// Reads one length-delimited message, as `parseDelimitedFrom` writes it.
    pub(super) fn delimited(&mut self) -> Result<&'data [u8], WireError> {
        let length = usize::try_from(self.varint()?).map_err(|_| WireError::Truncated)?;
        self.take(length)
    }

    pub(super) fn remainder(&self) -> &'data [u8] {
        &self.data[self.offset.min(self.data.len())..]
    }

    pub(super) fn next(&mut self) -> Result<Option<(u32, WireValue<'data>)>, WireError> {
        if self.is_empty() {
            return Ok(None);
        }
        let tag = self.varint()?;
        let field = u32::try_from(tag >> 3).map_err(|_| WireError::Truncated)?;
        let value = match tag & 0x7 {
            0 => WireValue::Varint(self.varint()?),
            1 => WireValue::Fixed64(u64::from_le_bytes(
                self.take(8)?.try_into().map_err(|_| WireError::Truncated)?,
            )),
            2 => {
                let length = usize::try_from(self.varint()?).map_err(|_| WireError::Truncated)?;
                WireValue::Length(self.take(length)?)
            }
            5 => WireValue::Fixed32(u32::from_le_bytes(
                self.take(4)?.try_into().map_err(|_| WireError::Truncated)?,
            )),
            other => return Err(WireError::UnknownWireType(other as u8)),
        };
        Ok(Some((field, value)))
    }
}

/// The fields of one message, indexed by field number.
///
/// Protocol buffers allow a field to repeat, and Kotlin's schema uses that for
/// declaration lists, so every field keeps all of its occurrences in order.
#[derive(Debug, Default, Clone)]
pub(super) struct Message<'data> {
    fields: std::collections::BTreeMap<u32, Vec<WireValue<'data>>>,
}

impl<'data> Message<'data> {
    pub(super) fn parse(data: &'data [u8]) -> Result<Self, WireError> {
        let mut reader = WireReader::new(data);
        let mut fields = std::collections::BTreeMap::<u32, Vec<WireValue<'data>>>::new();
        while let Some((field, value)) = reader.next()? {
            fields.entry(field).or_default().push(value);
        }
        Ok(Self { fields })
    }

    pub(super) fn values(&self, field: u32) -> &[WireValue<'data>] {
        self.fields.get(&field).map(Vec::as_slice).unwrap_or(&[])
    }

    pub(super) fn value(&self, field: u32) -> Option<&WireValue<'data>> {
        self.values(field).first()
    }

    pub(super) fn varint(&self, field: u32) -> Option<u64> {
        self.value(field).and_then(WireValue::varint)
    }

    pub(super) fn index(&self, field: u32) -> Option<u32> {
        self.varint(field)
            .and_then(|value| u32::try_from(value).ok())
    }

    pub(super) fn flag(&self, field: u32) -> bool {
        self.varint(field).is_some_and(|value| value != 0)
    }

    /// Reads a repeated embedded message.
    pub(super) fn messages(&self, field: u32) -> Result<Vec<Message<'data>>, WireError> {
        self.values(field)
            .iter()
            .filter_map(WireValue::bytes)
            .map(Message::parse)
            .collect()
    }

    pub(super) fn message(&self, field: u32) -> Result<Option<Message<'data>>, WireError> {
        self.value(field)
            .and_then(WireValue::bytes)
            .map(Message::parse)
            .transpose()
    }

    /// Reads a repeated varint field in either encoding.
    ///
    /// A repeated numeric field may be written once per element or packed into
    /// one length-delimited run, and Kotlin's writer uses both.
    pub(super) fn varints(&self, field: u32) -> Result<Vec<u64>, WireError> {
        let mut values = Vec::new();
        for value in self.values(field) {
            match value {
                WireValue::Varint(value) => values.push(*value),
                WireValue::Length(packed) => {
                    let mut reader = WireReader::new(packed);
                    while !reader.is_empty() {
                        values.push(reader.varint()?);
                    }
                }
                _ => {}
            }
        }
        Ok(values)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_varints_across_multiple_bytes() {
        let mut reader = WireReader::new(&[0xac, 0x02]);
        assert_eq!(reader.varint(), Ok(300));
    }

    #[test]
    fn repeated_fields_keep_every_occurrence() {
        // field 1 varint 1, field 1 varint 2, field 2 length "ab"
        let message = Message::parse(&[0x08, 0x01, 0x08, 0x02, 0x12, 0x02, b'a', b'b']).unwrap();
        assert_eq!(message.varints(1), Ok(vec![1, 2]));
        assert_eq!(
            message.value(2).and_then(WireValue::bytes),
            Some(&b"ab"[..])
        );
    }

    #[test]
    fn packed_and_unpacked_repeats_read_alike() {
        let packed = Message::parse(&[0x0a, 0x03, 0x01, 0x02, 0x03]).unwrap();
        let unpacked = Message::parse(&[0x08, 0x01, 0x08, 0x02, 0x08, 0x03]).unwrap();
        assert_eq!(packed.varints(1), unpacked.varints(1));
    }

    #[test]
    fn truncated_length_delimited_field_is_an_error() {
        assert!(matches!(
            Message::parse(&[0x12, 0x08, b'a']),
            Err(WireError::Truncated)
        ));
    }
}
