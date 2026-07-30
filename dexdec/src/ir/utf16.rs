//! Exact UTF-16 values used by DEX string constants.

#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Utf16String(Vec<u16>);

impl Utf16String {
    pub fn from_utf16(units: impl Into<Vec<u16>>) -> Self {
        Self(units.into())
    }

    pub fn as_utf16(&self) -> &[u16] {
        &self.0
    }

    pub fn to_string_lossy(&self) -> String {
        String::from_utf16_lossy(&self.0)
    }
}

impl From<&str> for Utf16String {
    fn from(value: &str) -> Self {
        Self(value.encode_utf16().collect())
    }
}

impl From<String> for Utf16String {
    fn from(value: String) -> Self {
        Self::from(value.as_str())
    }
}

impl std::fmt::Display for Utf16String {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.to_string_lossy())
    }
}
