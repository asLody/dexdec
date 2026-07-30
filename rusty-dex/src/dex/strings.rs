#![allow(dead_code)]

//! Representation of strings
//!
//! This module defines the logic to decode strings from a DEX file as well as an ordering method
//! to ensure that we sort the strings in the order defined in the official documentation.
//! DEX strings are encoded as null-terminated Modified UTF-8 with a declared
//! UTF-16 code-unit count.

use std::io::BufRead;
use std::io::{Seek, SeekFrom};
use std::sync::OnceLock;

use crate::dex::reader::DexReader;
use crate::error::DexError;

#[derive(Debug, Clone)]
pub struct DexString {
    utf16: Vec<u16>,
    lossy: OnceLock<String>,
}

impl DexString {
    pub fn from_utf16(utf16: Vec<u16>) -> Self {
        Self {
            utf16,
            lossy: OnceLock::new(),
        }
    }

    pub fn as_str(&self) -> &str {
        self.lossy
            .get_or_init(|| String::from_utf16_lossy(&self.utf16))
    }

    pub fn utf16(&self) -> &[u16] {
        &self.utf16
    }
}

impl PartialEq for DexString {
    fn eq(&self, other: &Self) -> bool {
        self.utf16 == other.utf16
    }
}

impl Eq for DexString {}

impl PartialOrd for DexString {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for DexString {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.utf16.cmp(&other.utf16)
    }
}

impl std::hash::Hash for DexString {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.utf16.hash(state);
    }
}

impl From<String> for DexString {
    fn from(value: String) -> Self {
        Self::from_utf16(value.encode_utf16().collect())
    }
}

impl From<&str> for DexString {
    fn from(value: &str) -> Self {
        Self::from(value.to_string())
    }
}

impl std::fmt::Display for DexString {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(self.as_str())
    }
}

/// List of strings of a DEX file
#[derive(Debug)]
pub struct DexStrings {
    pub strings: Vec<DexString>,
}

impl DexStrings {
    /// Parse all strings from a DEX file
    pub fn build(dex_reader: &mut DexReader, offset: u32, size: u32) -> Result<Self, DexError> {
        // Move to start of map list
        dex_reader.bytes.seek(SeekFrom::Start(offset.into()))?;

        let mut strings = Vec::with_capacity(size as usize);

        for _ in 0..size {
            let string_offset = dex_reader.read_u32()?;
            let current_offset = dex_reader.bytes.position();

            dex_reader
                .bytes
                .seek(SeekFrom::Start(string_offset.into()))?;

            let (utf16_size, _) = dex_reader.read_uleb128()?;
            let mut raw_string = Vec::with_capacity(utf16_size as usize);
            dex_reader.bytes.read_until(0, &mut raw_string)?;
            if raw_string.pop() != Some(0) {
                return Err(DexError::InvalidMutf8("[MUTF-8] missing null terminator"));
            }
            let decoded = crate::mutf8::decode(&raw_string).map_err(DexError::InvalidMutf8)?;
            let actual = decoded.len();
            if actual != utf16_size as usize {
                return Err(DexError::InvalidStringLength {
                    expected: utf16_size,
                    actual,
                });
            }
            strings.push(DexString::from_utf16(decoded));

            dex_reader.bytes.seek(SeekFrom::Start(current_offset))?;
        }

        Ok(DexStrings { strings })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_with_empty_strings() {
        let data = vec![
            0x64, 0x65, 0x78, 0x0a, 0x30, 0x33, 0x35, 0x00, 0x00, 0x00, // DEX magic
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // nothing
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // nothing
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // nothing
            0x78, 0x56, 0x34, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // endianness tag
        ];
        let mut dex_reader = DexReader::build(data).unwrap();
        let dex_strings = DexStrings::build(&mut dex_reader, 44, 0).unwrap();

        assert_eq!(dex_strings.strings.len(), 0);
    }

    #[test]
    fn test_build_with_non_empty_strings() {
        let data = vec![
            0x64, 0x65, 0x78, 0x0a, 0x30, 0x33, 0x35, 0x00, 0x00, 0x00, // DEX magic
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // nothing
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // nothing
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // nothing
            0x78, 0x56, 0x34, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // endianness tag
            // offsets
            0x3E, 0x00, 0x00, 0x00, 0x46, 0x00, 0x00, 0x00, 0x68, 0x00, 0x00, 0x00,
            // strings size and data
            0x06, b'H', b'e', b'l', b'l', b'o', b'!', 0x00, // string #0 value
            0x20, b'T', b'h', b'i', b's', b' ', b'i', b's', b' ', b'a', b' ', b't', b'e', b's',
            b't', b'.', b' ', b'\"', b'A', b'B', b'C', b'D', b'\"', b' ', b'i', b'n', b' ', b'M',
            b'U', b'T', b'F', b'-', b'8', 0x00, // string #1 value
            0x00, 0x00,
        ];

        let mut dex_reader = DexReader::build(data).unwrap();
        let dex_strings = DexStrings::build(&mut dex_reader, 50, 3).unwrap();

        assert_eq!(dex_strings.strings.len(), 3);
        assert_eq!(dex_strings.strings[0].as_str(), "Hello!");
        assert_eq!(
            dex_strings.strings[1].as_str(),
            "This is a test. \"ABCD\" in MUTF-8"
        );
        assert_eq!(dex_strings.strings[2].as_str(), "");
    }

    #[test]
    fn test_build_with_invalid_string() {
        let data = vec![
            0x64, 0x65, 0x78, 0x0a, 0x30, 0x33, 0x35, 0x00, 0x00, 0x00, // DEX magic
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // nothing
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // nothing
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // nothing
            0x78, 0x56, 0x34, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // endianness tag
            // offsets
            0x36, 0x00, 0x00, 0x00, // string size and data
            0x02, 0xc3, 0x00, // incomplete MUTF-8 two-byte sequence
        ];

        let mut dex_reader = DexReader::build(data).unwrap();
        assert!(matches!(
            DexStrings::build(&mut dex_reader, 50, 1),
            Err(DexError::InvalidMutf8(_))
        ));
    }
}
