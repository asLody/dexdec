//! Kotlin source literals shared by instruction and annotation lowering.

use super::KotlinLiteral;

pub(crate) struct KotlinLiterals;

impl KotlinLiterals {
    pub(crate) fn render(value: &KotlinLiteral) -> String {
        match value {
            KotlinLiteral::Null => "null".to_string(),
            KotlinLiteral::Boolean(value) => value.to_string(),
            KotlinLiteral::Integer(value) => value.to_string(),
            KotlinLiteral::Long(value) => format!("{value}L"),
            KotlinLiteral::Float(value) => Self::float(*value),
            KotlinLiteral::Double(value) => Self::double(*value),
            KotlinLiteral::Character(value) => Self::character(*value),
            KotlinLiteral::String(value) => Self::string(value),
        }
    }

    pub(crate) fn string(value: &crate::ir::Utf16String) -> String {
        let mut output = String::with_capacity(value.as_utf16().len() + 2);
        output.push('"');
        for unit in char::decode_utf16(value.as_utf16().iter().copied()) {
            match unit {
                Ok(ch) => output.push_str(&Self::escaped(ch, false)),
                Err(unpaired) => {
                    output.push_str(&format!("\\u{:04x}", unpaired.unpaired_surrogate()))
                }
            }
        }
        output.push('"');
        output
    }

    pub(crate) fn character(value: u16) -> String {
        let escaped = match value {
            value @ (0xd800..=0xdfff) => format!("\\u{value:04x}"),
            value => char::from_u32(value as u32)
                .map(|ch| Self::escaped(ch, true))
                .unwrap_or_else(|| format!("\\u{value:04x}")),
        };
        format!("'{escaped}'")
    }

    pub(crate) fn float(value: f32) -> String {
        if value.is_nan() {
            "Float.NaN".to_string()
        } else if value == f32::INFINITY {
            "Float.POSITIVE_INFINITY".to_string()
        } else if value == f32::NEG_INFINITY {
            "Float.NEGATIVE_INFINITY".to_string()
        } else {
            format!("{value:?}f")
        }
    }

    pub(crate) fn double(value: f64) -> String {
        if value.is_nan() {
            "Double.NaN".to_string()
        } else if value == f64::INFINITY {
            "Double.POSITIVE_INFINITY".to_string()
        } else if value == f64::NEG_INFINITY {
            "Double.NEGATIVE_INFINITY".to_string()
        } else {
            format!("{value:?}")
        }
    }

    fn escaped(ch: char, character: bool) -> String {
        match ch {
            '\\' => "\\\\".to_string(),
            '"' => "\\\"".to_string(),
            '\'' if character => "\\'".to_string(),
            '\n' => "\\n".to_string(),
            '\r' => "\\r".to_string(),
            '\t' => "\\t".to_string(),
            '\u{08}' => "\\b".to_string(),
            '\u{0c}' => "\\f".to_string(),
            ch if ch.is_control() && (ch as u32) <= 0xffff => {
                format!("\\u{:04x}", ch as u32)
            }
            ch => ch.to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::KotlinLiterals;
    use crate::ir::Utf16String;

    #[test]
    fn preserves_unpaired_surrogates_in_source_literals() {
        let value = Utf16String::from_utf16(vec![u16::from(b'a'), 0xd800, u16::from(b'b')]);
        assert_eq!(KotlinLiterals::string(&value), "\"a\\ud800b\"");
    }
}
