//! Recovery of the metadata byte stream from its annotation string form.
//!
//! Annotation values hold strings, so the Kotlin compiler stores the serialized
//! declaration table as strings whose characters are the bytes. A leading NUL
//! marks that plain form; without it the bytes were packed seven to a character
//! by compilers old enough to predate it.

/// Marks a string array whose characters are bytes directly.
const BYTE_STRING_MARKER: u16 = 0;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum EncodingError {
    NonByteCharacter(u16),
    Empty,
}

impl std::fmt::Display for EncodingError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NonByteCharacter(unit) => {
                write!(formatter, "metadata character {unit:#06x} is not a byte")
            }
            Self::Empty => formatter.write_str("metadata carries no encoded data"),
        }
    }
}

pub(super) struct BitEncoding;

impl BitEncoding {
    pub(super) fn decode(parts: &[Vec<u16>]) -> Result<Vec<u8>, EncodingError> {
        let units = parts.iter().flatten().copied().collect::<Vec<_>>();
        let Some(&first) = units.first() else {
            return Err(EncodingError::Empty);
        };
        if first == BYTE_STRING_MARKER {
            return Self::bytes(&units[1..]);
        }
        Self::unpack_seven_bit(&Self::bytes(&units)?)
    }

    fn bytes(units: &[u16]) -> Result<Vec<u8>, EncodingError> {
        units
            .iter()
            .map(|unit| u8::try_from(*unit).map_err(|_| EncodingError::NonByteCharacter(*unit)))
            .collect()
    }

    /// Unpacks the pre-marker form, which stored eight-bit bytes seven bits at a
    /// time so that every character stayed inside the ASCII range.
    fn unpack_seven_bit(packed: &[u8]) -> Result<Vec<u8>, EncodingError> {
        let mut bytes = Vec::with_capacity(packed.len());
        let mut buffer = 0u32;
        let mut bits = 0u32;
        for unit in packed {
            buffer |= u32::from(*unit & 0x7f) << bits;
            bits += 7;
            while bits >= 8 {
                bytes.push((buffer & 0xff) as u8);
                buffer >>= 8;
                bits -= 8;
            }
        }
        Ok(bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_leading_nul_marks_characters_that_are_already_bytes() {
        let decoded = BitEncoding::decode(&[vec![0, 0x40, 0x0a], vec![0x02]]).unwrap();
        assert_eq!(decoded, vec![0x40, 0x0a, 0x02]);
    }

    #[test]
    fn a_character_wider_than_a_byte_is_rejected() {
        assert_eq!(
            BitEncoding::decode(&[vec![0, 0x1f4]]),
            Err(EncodingError::NonByteCharacter(0x1f4))
        );
    }

    #[test]
    fn seven_bit_packing_round_trips_a_known_run() {
        // 0xff 0xff packs into 0x7f 0x7f 0x03 seven bits at a time.
        let decoded = BitEncoding::decode(&[vec![0x7f, 0x7f, 0x03]]).unwrap();
        assert_eq!(decoded[..2], [0xff, 0xff]);
    }
}
