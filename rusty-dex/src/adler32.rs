//! Module to compute and verify the Adler-32 checksum of a file
//!
//! DEX files use Adler-32 to detect file corruption. Each DEX file contains a checksum value to
//! compare against. The checksum must be computed from the whole file except the magic number and
//! the checksum field in the header.
//!
//! # Example
//!
//! ```
//! use rusty_dex::adler32::verify_from_bytes;
//! use std::io::Cursor;
//!
//! let bytes: [u8; 16] = [0x44, 0x45, 0x58, 0x0a,
//!                        0x30, 0x33, 0x35, 0x00,
//!                        0x00, 0x00, 0x00, 0x00,
//!                        0x00, 0x00, 0x00, 0x00];
//! let cursor = Cursor::new(bytes.to_vec());
//! assert!(verify_from_bytes(&cursor, 0x00040001).unwrap());
//! ```

use std::io::Cursor;

use crate::error::DexError;

/// Constant used in the checksum computation
const MOD_ADLER: u32 = 65521;

/// Verify the Adler32 checksum of a cursor of bytes
///
/// Each DEX header contains an Adler-32 checksum of the file, minus the first
/// 11 bytes, which correspond to the space taken by the magic and the checksum.
/// This function computes the checksum of the file, and compares it to the one
/// found in the header.
pub fn verify_from_bytes<T: AsRef<[u8]>>(
    bytes: &Cursor<T>,
    checksum: u32,
) -> Result<bool, DexError> {
    // Define variable for checksum computation
    let mut a: u32 = 1;
    let mut b: u32 = 0;

    // 5552 bytes is the largest block that cannot overflow a 32-bit
    // accumulator. Reducing once per block avoids two divisions per byte.
    for block in bytes.get_ref().as_ref()[12..].chunks(5552) {
        for &byte in block {
            a += u32::from(byte);
            b += a;
        }
        a %= MOD_ADLER;
        b %= MOD_ADLER;
    }

    // Concatenating A and B
    let computed_checksum = (b << 16) | a;

    // Verification of the checksum read from the DEX header
    if computed_checksum == checksum {
        Ok(true)
    } else {
        Err(DexError::InvalidChecksumError)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_valid_from_bytes() {
        // Test data with valid checksum
        let bytes = Cursor::new(vec![
            0x44, 0x45, 0x58, 0x0a, 0x30, 0x33, 0x35, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00,
        ]);
        let checksum: u32 = 0x00040001;
        assert!(verify_from_bytes(&bytes, checksum).unwrap());
    }

    #[test]
    fn test_verify_invalid_from_bytes() {
        // Test data with invalid checksum
        let bytes = Cursor::new(vec![
            0x44, 0x45, 0x58, 0x0a, 0x30, 0x33, 0x35, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00,
        ]);
        let checksum: u32 = 0xcafebabe;
        assert_eq!(
            verify_from_bytes(&bytes, checksum).unwrap_err().to_string(),
            "computed checksum does not match one in header"
        );
    }
}
