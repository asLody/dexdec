//! DEX `debug_info_item` parser.
//!
//! Implements the AOSP `debug_info` decoding algorithm: a header with the
//! initial line number, parameter-name string-id table, and an opcode stream
//! that emits local-variable start/end events interleaved with line/address
//! advances. The result is a `LocalVariableTable` plus line-number table for a
//! single method's `code_item`.
//!
//! Reference: source.android.com/devices/tech/dalvik/dex-format (`debug_info_item`).

use std::io::{Seek, SeekFrom};

use crate::dex::{reader::DexReader, strings::DexStrings, types::DexTypes};
use crate::error::DexError;

/// Opcodes for the debug info opcode stream. Values match the DEX spec.
mod op {
    pub const DBG_END_SEQUENCE: u8 = 0x00;
    pub const DBG_ADVANCE_PC: u8 = 0x01;
    pub const DBG_ADVANCE_LINE: u8 = 0x02;
    pub const DBG_START_LOCAL: u8 = 0x03;
    pub const DBG_START_LOCAL_EXTENDED: u8 = 0x04;
    pub const DBG_END_LOCAL: u8 = 0x05;
    pub const DBG_RESTART_LOCAL: u8 = 0x06;
    pub const DBG_SET_PROLOGUE_END: u8 = 0x07;
    pub const DBG_SET_EPILOGUE_BEGIN: u8 = 0x08;
    pub const DBG_SET_FILE: u8 = 0x09;
    /// First "special opcode" — encodes a combined line/address advance.
    pub const DBG_FIRST_SPECIAL: u8 = 0x0a;
    /// Standard DWARF line range used by the special-opcode encoding.
    pub const DBG_LINE_RANGE: i32 = 15;
    /// Standard DWARF base line used by the special-opcode encoding.
    pub const DBG_BASE_LINE: i32 = -4;
}

/// A single local-variable entry recovered from the debug info stream.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DebugLocalVar {
    /// Variable name (resolved from `string_ids`).
    pub name: String,
    /// Type descriptor (e.g. `Ljava/lang/String;`, `I`).
    pub type_descriptor: String,
    /// Optional signature (resolved only by `DBG_START_LOCAL_EXTENDED`).
    pub signature: Option<String>,
    /// Register number this variable is bound to.
    pub register: u32,
    /// Bytecode offset (in 16-bit code units) where the variable starts.
    pub start_addr: u32,
    /// Bytecode offset where the variable ends (inclusive of its last use).
    pub end_addr: u32,
}

/// Decoded debug info for a single `code_item`.
#[derive(Clone, Debug, Default)]
pub struct DebugInfo {
    /// `(instruction_offset, line_number)` pairs in stream order.
    pub line_numbers: Vec<(u32, u32)>,
    /// Local variables in start order. End addresses are filled in by matching
    /// `DBG_END_LOCAL` / `DBG_RESTART_LOCAL` / sequence-end semantics.
    pub local_vars: Vec<DebugLocalVar>,
    /// Parameter names, one per declared parameter; `None` means "no name
    /// recorded" (encoded as the sentinel `0xFFFFFFFF` / `-1`).
    pub param_names: Vec<Option<String>>,
}

impl DebugInfo {
    /// Build a `DebugInfo` by parsing the debug info stream starting at
    /// `debug_info_off`. Returns `Ok(None)` when `debug_info_off == 0`
    /// (no debug info for this code item).
    pub fn build(
        dex_reader: &mut DexReader,
        debug_info_off: u32,
        strings: &DexStrings,
        types: &DexTypes,
    ) -> Result<Option<Self>, DexError> {
        if debug_info_off == 0 {
            return Ok(None);
        }
        let return_offset = dex_reader.bytes.position();
        dex_reader
            .bytes
            .seek(SeekFrom::Start(debug_info_off.into()))?;

        let result = Self::parse_stream(dex_reader, strings, types);

        // Restore the cursor so callers can continue parsing as if nothing
        // happened (matches the pattern used by `CodeItem::build` callers).
        dex_reader.bytes.seek(SeekFrom::Start(return_offset))?;
        result.map(Some)
    }

    fn parse_stream(
        dex_reader: &mut DexReader,
        strings: &DexStrings,
        types: &DexTypes,
    ) -> Result<Self, DexError> {
        let (line_start, _) = dex_reader.read_uleb128()?;
        let (parameters_size, _) = dex_reader.read_uleb128()?;

        let mut param_names = Vec::with_capacity(parameters_size as usize);
        for _ in 0..parameters_size {
            let (param_name_idx, _) = dex_reader.read_uleb128p1()?;
            param_names.push(resolve_name(param_name_idx, strings));
        }

        let mut line_numbers: Vec<(u32, u32)> = Vec::new();
        let mut local_vars: Vec<DebugLocalVar> = Vec::new();
        let mut address: u32 = 0;
        let mut line: i64 = line_start as i64;

        loop {
            let opcode = dex_reader.read_u8()?;
            if opcode == op::DBG_END_SEQUENCE {
                break;
            }
            if opcode == op::DBG_ADVANCE_PC {
                let (addr_diff, _) = dex_reader.read_uleb128()?;
                address = address.saturating_add(addr_diff);
                continue;
            }
            if opcode == op::DBG_ADVANCE_LINE {
                let (line_diff, _) = dex_reader.read_sleb128()?;
                line = line.saturating_add(line_diff as i64);
                continue;
            }
            if opcode == op::DBG_START_LOCAL || opcode == op::DBG_START_LOCAL_EXTENDED {
                let (register, _) = dex_reader.read_uleb128()?;
                let (name_idx, _) = dex_reader.read_uleb128p1()?;
                let (type_idx, _) = dex_reader.read_uleb128p1()?;
                let signature = if opcode == op::DBG_START_LOCAL_EXTENDED {
                    let (sig_idx, _) = dex_reader.read_uleb128p1()?;
                    resolve_signature(sig_idx, strings)
                } else {
                    None
                };
                // Close out any existing live range for the same register so the
                // most recent variable is the one recorded up to this address.
                if let Some(existing) = local_vars
                    .iter_mut()
                    .rev()
                    .find(|v| v.register == register && v.end_addr == 0)
                {
                    existing.end_addr = address;
                }
                local_vars.push(DebugLocalVar {
                    name: resolve_name(name_idx, strings)
                        .unwrap_or_else(|| format!("v{}", register)),
                    type_descriptor: resolve_type(type_idx, types)
                        .unwrap_or_else(|| format!("v{}", register)),
                    signature,
                    register,
                    start_addr: address,
                    end_addr: 0,
                });
                continue;
            }
            if opcode == op::DBG_END_LOCAL || opcode == op::DBG_RESTART_LOCAL {
                let (register, _) = dex_reader.read_uleb128()?;
                if let Some(existing) = local_vars
                    .iter_mut()
                    .rev()
                    .find(|v| v.register == register && v.end_addr == 0)
                {
                    existing.end_addr = address;
                }
                if opcode == op::DBG_RESTART_LOCAL {
                    // The same variable comes back into scope at this address.
                    if let Some(prev) = local_vars
                        .iter()
                        .rev()
                        .find(|v| v.register == register && v.end_addr == address)
                    {
                        local_vars.push(DebugLocalVar {
                            name: prev.name.clone(),
                            type_descriptor: prev.type_descriptor.clone(),
                            signature: prev.signature.clone(),
                            register,
                            start_addr: address,
                            end_addr: 0,
                        });
                    }
                }
                continue;
            }
            if opcode == op::DBG_SET_PROLOGUE_END || opcode == op::DBG_SET_EPILOGUE_BEGIN {
                continue;
            }
            if opcode == op::DBG_SET_FILE {
                let (_name_idx, _) = dex_reader.read_uleb128p1()?;
                continue;
            }
            // Special opcode: combined address + line advance.
            let adjusted = (opcode - op::DBG_FIRST_SPECIAL) as i32;
            let address_advance = adjusted / op::DBG_LINE_RANGE;
            let line_advance = adjusted % op::DBG_LINE_RANGE - op::DBG_BASE_LINE;
            address = address.saturating_add(address_advance as u32);
            line = line.saturating_add(line_advance as i64);
            if line > 0 {
                line_numbers.push((address, line as u32));
            }
        }

        // Any still-open local range ends at the last emitted address.
        for var in &mut local_vars {
            if var.end_addr == 0 {
                var.end_addr = address;
            }
        }

        Ok(Self {
            line_numbers,
            local_vars,
            param_names,
        })
    }
}

fn resolve_name(name_idx: i32, strings: &DexStrings) -> Option<String> {
    if name_idx < 0 {
        return None;
    }
    strings
        .strings
        .get(name_idx as usize)
        .filter(|name| is_valid_identifier(name.as_str()))
        .map(ToString::to_string)
}

fn resolve_signature(sig_idx: i32, strings: &DexStrings) -> Option<String> {
    if sig_idx < 0 {
        return None;
    }
    strings
        .strings
        .get(sig_idx as usize)
        .map(ToString::to_string)
}

fn resolve_type(type_idx: i32, types: &DexTypes) -> Option<String> {
    if type_idx < 0 {
        return None;
    }
    types.items.get(type_idx as usize).cloned()
}

fn is_valid_identifier(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first.is_ascii_alphabetic() || first == '_' || first == '$') {
        return false;
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$')
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Sanity-check the helpers used by the opcode stream parser. Full-stream
    /// coverage is exercised end-to-end through real DEX files in the dexdec
    /// real-corpus suite (which carries methods with LocalVariableTable info).
    #[test]
    fn special_opcode_constants_are_stable() {
        // These constants are part of the DEX spec and must not drift; pinning
        // them here catches accidental edits during refactors.
        assert_eq!(op::DBG_END_SEQUENCE, 0x00);
        assert_eq!(op::DBG_START_LOCAL, 0x03);
        assert_eq!(op::DBG_START_LOCAL_EXTENDED, 0x04);
        assert_eq!(op::DBG_END_LOCAL, 0x05);
        assert_eq!(op::DBG_FIRST_SPECIAL, 0x0a);
        assert_eq!(op::DBG_LINE_RANGE, 15);
        assert_eq!(op::DBG_BASE_LINE, -4);
    }
}
