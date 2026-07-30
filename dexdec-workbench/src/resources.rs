use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};

use abxml::decoder::Decoder;
use abxml::visitor::XmlVisitor;
use base64::Engine;
use schemars::JsonSchema;
use serde::Serialize;
use zip::ZipArchive;

use crate::apk_overview::{ApkOverviewBuilder, ApkOverviewDto, ResolvedManifestValues};
use crate::xml_format::XmlFormatter;

const MAX_PREVIEW_BYTES: u64 = 32 * 1024 * 1024;

#[derive(Debug)]
pub struct ApkResourceArchive {
    path: PathBuf,
    entries: Vec<ResourceEntryDto>,
    resource_table: Option<Vec<u8>>,
    overview: ApkOverviewDto,
}

impl ApkResourceArchive {
    pub fn open(path: &Path) -> Result<Option<Self>, ResourceError> {
        if !path.extension().is_some_and(|extension| {
            extension.eq_ignore_ascii_case("apk") || extension.eq_ignore_ascii_case("zip")
        }) {
            return Ok(None);
        }
        let file = File::open(path)?;
        let mut archive = ZipArchive::new(file)?;
        let mut entries = Vec::new();
        let mut resource_table = None;
        let mut manifest = None;
        let mut dex_file_count = 0;
        for index in 0..archive.len() {
            let mut entry = archive.by_index(index)?;
            if entry.is_dir() {
                continue;
            }
            let path = entry.name().trim_start_matches('/').to_string();
            if path.is_empty() {
                continue;
            }
            if path.ends_with(".dex") {
                dex_file_count += 1;
                continue;
            }
            if path == "resources.arsc" && entry.size() <= MAX_PREVIEW_BYTES {
                let mut bytes = Vec::with_capacity(entry.size() as usize);
                entry.read_to_end(&mut bytes)?;
                resource_table = Some(bytes);
            }
            if path == "AndroidManifest.xml" && entry.size() <= MAX_PREVIEW_BYTES {
                let mut bytes = Vec::with_capacity(entry.size() as usize);
                entry.read_to_end(&mut bytes)?;
                manifest = Some(bytes);
            }
            entries.push(ResourceEntryDto {
                kind: ResourceKind::classify(&path),
                path,
                size: entry.size(),
                compressed_size: entry.compressed_size(),
            });
        }
        entries.sort_by(|left, right| left.path.cmp(&right.path));
        let resolved_manifest =
            ResolvedManifestValues::parse(resource_table.as_deref(), manifest.as_deref());
        let manifest = manifest.as_deref().and_then(|bytes| {
            std::str::from_utf8(bytes)
                .ok()
                .filter(|text| text.trim_start().starts_with('<'))
                .map(str::to_string)
                .or_else(|| {
                    resource_table
                        .as_deref()
                        .and_then(|table| Self::decode_binary_xml(table, bytes).ok())
                })
        });
        let overview = ApkOverviewBuilder::new(&entries, dex_file_count)
            .build(manifest.as_deref(), &resolved_manifest);
        Ok(Some(Self {
            path: path.to_path_buf(),
            entries,
            resource_table,
            overview,
        }))
    }

    pub fn entries(&self) -> &[ResourceEntryDto] {
        &self.entries
    }

    pub fn overview(&self) -> &ApkOverviewDto {
        &self.overview
    }

    pub fn read(&self, requested_path: &str) -> Result<ResourceDocumentDto, ResourceError> {
        let indexed = self
            .entries
            .binary_search_by(|entry| entry.path.as_str().cmp(requested_path))
            .ok()
            .map(|index| &self.entries[index])
            .ok_or_else(|| ResourceError::NotFound(requested_path.to_string()))?;
        if indexed.size > MAX_PREVIEW_BYTES {
            return Ok(ResourceDocumentDto::binary(
                indexed,
                Some(format!(
                    "Preview is limited to {} MiB",
                    MAX_PREVIEW_BYTES / 1024 / 1024
                )),
            ));
        }
        let mut archive = ZipArchive::new(File::open(&self.path)?)?;
        let mut file = archive.by_name(requested_path)?;
        let mut bytes = Vec::with_capacity(file.size() as usize);
        file.read_to_end(&mut bytes)?;

        if indexed.kind == ResourceKind::Xml {
            if let Ok(text) = std::str::from_utf8(&bytes) {
                if text.trim_start().starts_with('<') {
                    return Ok(ResourceDocumentDto::text(
                        indexed,
                        Self::format_xml(text),
                        TextFormat::Xml,
                    ));
                }
            }
            if let Some(table) = self.resource_table.as_deref() {
                if let Ok(text) = Self::decode_binary_xml(table, &bytes) {
                    let text = Self::format_xml(&text);
                    return Ok(ResourceDocumentDto::text(indexed, text, TextFormat::Xml));
                }
            }
        }
        if let Some(mime_type) = indexed.kind.image_mime(&indexed.path) {
            let encoded = base64::engine::general_purpose::STANDARD.encode(bytes);
            return Ok(ResourceDocumentDto {
                path: indexed.path.clone(),
                kind: indexed.kind,
                mime_type: Some(mime_type.to_string()),
                text_format: None,
                size: indexed.size,
                text: None,
                data_url: Some(format!("data:{mime_type};base64,{encoded}")),
                message: None,
            });
        }
        if indexed.kind.is_text() || indexed.kind == ResourceKind::Binary {
            if let Some(text) = TextDecoder::decode(&bytes) {
                return Ok(ResourceDocumentDto::text(
                    indexed,
                    text,
                    TextFormat::for_path(&indexed.path).unwrap_or(TextFormat::Plain),
                ));
            }
        }
        Ok(ResourceDocumentDto::binary(indexed, None))
    }

    fn decode_binary_xml(table: &[u8], xml: &[u8]) -> Result<String, ResourceError> {
        let decoder = Decoder::from_buffer(table)
            .map_err(|error| ResourceError::Decode(error.to_string()))?;
        decoder
            .xml_visitor(&xml)
            .and_then(XmlVisitor::into_string)
            .map_err(|error| ResourceError::Decode(error.to_string()))
    }

    fn format_xml(text: &str) -> String {
        XmlFormatter::default()
            .format(text)
            .unwrap_or_else(|_| text.to_string())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub enum ResourceKind {
    Xml,
    Image,
    Text,
    Font,
    NativeLibrary,
    ResourceTable,
    Signature,
    Binary,
}

impl ResourceKind {
    fn classify(path: &str) -> Self {
        let lower = path.to_ascii_lowercase();
        if lower.ends_with(".xml") {
            Self::Xml
        } else if [".png", ".jpg", ".jpeg", ".gif", ".webp", ".bmp", ".svg"]
            .iter()
            .any(|extension| lower.ends_with(extension))
        {
            Self::Image
        } else if TextFormat::for_path(path).is_some() || is_text_filename(&lower) {
            Self::Text
        } else if [".ttf", ".otf", ".woff", ".woff2"]
            .iter()
            .any(|extension| lower.ends_with(extension))
        {
            Self::Font
        } else if lower.ends_with(".so") {
            Self::NativeLibrary
        } else if lower == "resources.arsc" {
            Self::ResourceTable
        } else if lower.starts_with("meta-inf/") {
            Self::Signature
        } else {
            Self::Binary
        }
    }

    fn is_text(self) -> bool {
        matches!(self, Self::Text | Self::Signature)
    }

    fn image_mime(self, path: &str) -> Option<&'static str> {
        if self != Self::Image {
            return None;
        }
        let lower = path.to_ascii_lowercase();
        Some(if lower.ends_with(".png") {
            "image/png"
        } else if lower.ends_with(".jpg") || lower.ends_with(".jpeg") {
            "image/jpeg"
        } else if lower.ends_with(".gif") {
            "image/gif"
        } else if lower.ends_with(".webp") {
            "image/webp"
        } else if lower.ends_with(".svg") {
            "image/svg+xml"
        } else {
            "image/bmp"
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub enum TextFormat {
    Plain,
    Xml,
    Json,
    Html,
    Css,
    Javascript,
    Typescript,
    Java,
    Kotlin,
    Aidl,
    Smali,
    Properties,
    Markdown,
    Yaml,
    Toml,
    Sql,
    Shell,
    C,
    Cpp,
    Proto,
    Gradle,
}

impl TextFormat {
    fn for_path(path: &str) -> Option<Self> {
        let lower = path.to_ascii_lowercase();
        let extension = lower.rsplit_once('.').map(|(_, extension)| extension)?;
        Some(match extension {
            "xml" => Self::Xml,
            "json" | "json5" | "jsonl" => Self::Json,
            "html" | "htm" => Self::Html,
            "css" | "scss" | "less" => Self::Css,
            "js" | "jsx" | "mjs" | "cjs" => Self::Javascript,
            "ts" | "tsx" | "mts" | "cts" => Self::Typescript,
            "java" => Self::Java,
            "kt" | "kts" => Self::Kotlin,
            "aidl" => Self::Aidl,
            "smali" => Self::Smali,
            "properties" | "pro" | "cfg" | "conf" | "ini" | "mf" | "sf" => Self::Properties,
            "md" | "markdown" => Self::Markdown,
            "yaml" | "yml" => Self::Yaml,
            "toml" => Self::Toml,
            "sql" => Self::Sql,
            "sh" | "bash" | "zsh" => Self::Shell,
            "c" | "h" => Self::C,
            "cc" | "cpp" | "cxx" | "hpp" | "hh" | "hxx" => Self::Cpp,
            "proto" => Self::Proto,
            "gradle" | "groovy" => Self::Gradle,
            "txt" | "csv" | "tsv" | "log" | "license" => Self::Plain,
            _ => return None,
        })
    }

    fn mime(self) -> &'static str {
        match self {
            Self::Xml => "text/xml",
            Self::Json => "application/json",
            Self::Html => "text/html",
            Self::Css => "text/css",
            Self::Javascript => "text/javascript",
            Self::Typescript => "text/typescript",
            Self::Java => "text/x-java",
            Self::Kotlin => "text/x-kotlin",
            Self::Aidl => "text/x-aidl",
            Self::Smali => "text/x-smali",
            Self::Properties => "text/x-java-properties",
            Self::Markdown => "text/markdown",
            Self::Yaml => "application/yaml",
            Self::Toml => "application/toml",
            Self::Sql => "application/sql",
            Self::Shell => "application/x-sh",
            Self::C => "text/x-c",
            Self::Cpp => "text/x-c++",
            Self::Proto => "text/x-protobuf",
            Self::Gradle => "text/x-gradle",
            Self::Plain => "text/plain",
        }
    }
}

fn is_text_filename(path: &str) -> bool {
    path.rsplit('/').next().is_some_and(|name| {
        [
            "license", "notice", "readme", "authors", "changes", "copying",
        ]
        .iter()
        .any(|prefix| {
            name.strip_prefix(prefix)
                .is_some_and(|suffix| suffix.is_empty() || suffix.starts_with('.'))
        }) || matches!(
            name,
            "android.bp" | "android.mk" | "makefile" | "dockerfile"
        )
    })
}

struct TextDecoder;

impl TextDecoder {
    fn decode(bytes: &[u8]) -> Option<String> {
        if let Some(body) = bytes.strip_prefix(&[0xef, 0xbb, 0xbf]) {
            return Self::utf8(body);
        }
        if let Some(body) = bytes.strip_prefix(&[0xff, 0xfe]) {
            return Self::utf16(body, u16::from_le_bytes);
        }
        if let Some(body) = bytes.strip_prefix(&[0xfe, 0xff]) {
            return Self::utf16(body, u16::from_be_bytes);
        }
        Self::utf8(bytes)
    }

    fn utf8(bytes: &[u8]) -> Option<String> {
        let text = std::str::from_utf8(bytes).ok()?;
        Self::looks_textual(text).then(|| text.to_string())
    }

    fn utf16(bytes: &[u8], decode: fn([u8; 2]) -> u16) -> Option<String> {
        if bytes.len() % 2 != 0 {
            return None;
        }
        let units = bytes
            .chunks_exact(2)
            .map(|chunk| decode([chunk[0], chunk[1]]))
            .collect::<Vec<_>>();
        let text = String::from_utf16(&units).ok()?;
        Self::looks_textual(&text).then_some(text)
    }

    fn looks_textual(text: &str) -> bool {
        if text.is_empty() {
            return true;
        }
        let controls = text
            .chars()
            .filter(|character| character.is_control() && !matches!(character, '\n' | '\r' | '\t'))
            .count();
        controls.saturating_mul(100) <= text.chars().count()
    }
}

#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ResourceEntryDto {
    pub path: String,
    pub kind: ResourceKind,
    pub size: u64,
    pub compressed_size: u64,
}

#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ResourceDocumentDto {
    pub path: String,
    pub kind: ResourceKind,
    pub mime_type: Option<String>,
    pub text_format: Option<TextFormat>,
    pub size: u64,
    pub text: Option<String>,
    pub data_url: Option<String>,
    pub message: Option<String>,
}

impl ResourceDocumentDto {
    fn text(entry: &ResourceEntryDto, text: String, text_format: TextFormat) -> Self {
        Self {
            path: entry.path.clone(),
            kind: entry.kind,
            mime_type: Some(text_format.mime().to_string()),
            text_format: Some(text_format),
            size: entry.size,
            text: Some(text),
            data_url: None,
            message: None,
        }
    }

    fn binary(entry: &ResourceEntryDto, message: Option<String>) -> Self {
        Self {
            path: entry.path.clone(),
            kind: entry.kind,
            mime_type: None,
            text_format: None,
            size: entry.size,
            text: None,
            data_url: None,
            message,
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ResourceError {
    #[error("resource not found: {0}")]
    NotFound(String),
    #[error("unable to decode Android resource: {0}")]
    Decode(String),
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Zip(#[from] zip::result::ZipError),
}

#[cfg(test)]
mod tests {
    use super::{ResourceKind, TextDecoder, TextFormat};

    #[test]
    fn classifies_source_and_configuration_text() {
        assert_eq!(
            ResourceKind::classify("src/api/Service.aidl"),
            ResourceKind::Text
        );
        assert_eq!(
            ResourceKind::classify("assets/config.yaml"),
            ResourceKind::Text
        );
        assert_eq!(
            ResourceKind::classify("assets/Android.bp"),
            ResourceKind::Text
        );
        assert_eq!(
            TextFormat::for_path("src/api/Service.aidl"),
            Some(TextFormat::Aidl)
        );
        assert_eq!(
            TextFormat::for_path("src/Example.kt"),
            Some(TextFormat::Kotlin)
        );
    }

    #[test]
    fn decodes_utf8_and_utf16_text() {
        assert_eq!(
            TextDecoder::decode(b"interface Service {}"),
            Some("interface Service {}".into())
        );

        let mut utf16 = vec![0xff, 0xfe];
        for unit in "parcelable Model;".encode_utf16() {
            utf16.extend_from_slice(&unit.to_le_bytes());
        }
        assert_eq!(
            TextDecoder::decode(&utf16),
            Some("parcelable Model;".into())
        );
    }

    #[test]
    fn rejects_control_heavy_binary_data() {
        assert_eq!(TextDecoder::decode(&[0, 1, 2, 3, 4, b'A']), None);
    }
}
