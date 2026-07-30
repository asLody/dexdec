pub fn decode(raw: &[u8]) -> Result<Vec<u16>, &'static str> {
    Decoder::new(raw).decode()
}

struct Decoder<'a> {
    raw: &'a [u8],
    cursor: usize,
}

impl<'a> Decoder<'a> {
    fn new(raw: &'a [u8]) -> Self {
        Self { raw, cursor: 0 }
    }

    fn decode(mut self) -> Result<Vec<u16>, &'static str> {
        let mut output = Vec::new();
        while let Some(lead) = self.next() {
            match lead {
                0x01..=0x7f => output.push(u16::from(lead)),
                0xc0..=0xdf => {
                    let tail = self.continuation()?;
                    let unit = (u16::from(lead & 0x1f) << 6) | u16::from(tail & 0x3f);
                    if unit == 0 {
                        if lead != 0xc0 || tail != 0x80 {
                            return Err("[MUTF-8] invalid null encoding");
                        }
                    } else if unit < 0x80 {
                        return Err("[MUTF-8] overlong two-byte encoding");
                    }
                    output.push(unit);
                }
                0xe0..=0xef => {
                    let unit = self.three_byte_unit(lead)?;
                    output.push(unit);
                }
                _ => return Err("[MUTF-8] invalid leading byte"),
            }
        }
        Ok(output)
    }

    fn next(&mut self) -> Option<u8> {
        let byte = self.raw.get(self.cursor).copied()?;
        self.cursor += 1;
        Some(byte)
    }

    fn continuation(&mut self) -> Result<u8, &'static str> {
        let byte = self
            .next()
            .ok_or("[MUTF-8] truncated multi-byte encoding")?;
        ((byte & 0xc0) == 0x80)
            .then_some(byte)
            .ok_or("[MUTF-8] invalid continuation byte")
    }

    fn three_byte_unit(&mut self, lead: u8) -> Result<u16, &'static str> {
        let middle = self.continuation()?;
        let tail = self.continuation()?;
        let unit = (u16::from(lead & 0x0f) << 12)
            | (u16::from(middle & 0x3f) << 6)
            | u16::from(tail & 0x3f);
        (unit >= 0x800)
            .then_some(unit)
            .ok_or("[MUTF-8] overlong three-byte encoding")
    }
}

#[cfg(test)]
mod tests {
    use super::decode;

    #[test]
    fn decodes_ascii_and_multibyte_units() {
        assert_eq!(decode(b"A"), Ok(vec![u16::from(b'A')]));
        assert_eq!(decode(&[0xc3, 0xa9]), Ok("é".encode_utf16().collect()));
        assert_eq!(
            decode(&[0xe6, 0xb0, 0xb4]),
            Ok("水".encode_utf16().collect())
        );
    }

    #[test]
    fn decodes_modified_null() {
        assert_eq!(decode(&[0xc0, 0x80]), Ok(vec![0]));
    }

    #[test]
    fn decodes_surrogate_pair() {
        assert_eq!(
            decode(&[0xed, 0xa0, 0x80, 0xed, 0xb0, 0x80]),
            Ok(vec![0xd800, 0xdc00])
        );
    }

    #[test]
    fn preserves_unpaired_surrogates() {
        assert_eq!(decode(&[0xed, 0xa0, 0x80]), Ok(vec![0xd800]));
        assert_eq!(decode(&[0xed, 0xb0, 0x80]), Ok(vec![0xdc00]));
    }

    #[test]
    fn rejects_truncated_sequences() {
        assert!(decode(&[0xc3]).is_err());
        assert!(decode(&[0xe6, 0xb0]).is_err());
    }

    #[test]
    fn rejects_invalid_sequences() {
        assert!(decode(&[0x00]).is_err());
        assert!(decode(&[0xc2, 0x41]).is_err());
        assert!(decode(&[0xf0, 0x90, 0x80, 0x80]).is_err());
        assert!(decode(&[0xe0, 0x80, 0x80]).is_err());
    }
}
