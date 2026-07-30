//! APK resource catalog and decoding commands.

use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};

use abxml::decoder::Decoder;
use abxml::visitor::XmlVisitor;
use quick_xml::events::Event;
use quick_xml::{Reader, Writer};
use serde::Serialize;
use zip::ZipArchive;

use super::error::{CliError, CliResult};
use super::model::{ResourceListRequest, ResourceReadRequest, ResourcesRequest};
use super::output::{CliHost, CommandContext};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum ResourceKind {
    Xml,
    Text,
    Image,
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
        } else if [
            ".json",
            ".json5",
            ".jsonl",
            ".html",
            ".css",
            ".js",
            ".ts",
            ".java",
            ".kt",
            ".kts",
            ".aidl",
            ".smali",
            ".properties",
            ".txt",
            ".md",
            ".yaml",
            ".yml",
            ".toml",
            ".sql",
            ".sh",
            ".c",
            ".h",
            ".cpp",
            ".hpp",
            ".proto",
            ".gradle",
        ]
        .iter()
        .any(|extension| lower.ends_with(extension))
            || Self::is_text_filename(&lower)
        {
            Self::Text
        } else if [".png", ".jpg", ".jpeg", ".gif", ".webp", ".bmp", ".svg"]
            .iter()
            .any(|extension| lower.ends_with(extension))
        {
            Self::Image
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

    pub fn name(self) -> &'static str {
        match self {
            Self::Xml => "xml",
            Self::Text => "text",
            Self::Image => "image",
            Self::Font => "font",
            Self::NativeLibrary => "native",
            Self::ResourceTable => "table",
            Self::Signature => "signature",
            Self::Binary => "binary",
        }
    }

    fn parse(value: &str) -> CliResult<Self> {
        match value.to_ascii_lowercase().as_str() {
            "xml" => Ok(Self::Xml),
            "text" => Ok(Self::Text),
            "image" => Ok(Self::Image),
            "font" => Ok(Self::Font),
            "native" | "native-library" | "so" => Ok(Self::NativeLibrary),
            "table" | "resource-table" | "arsc" => Ok(Self::ResourceTable),
            "signature" => Ok(Self::Signature),
            "binary" => Ok(Self::Binary),
            other => Err(CliError::usage(format!("unknown resource kind: {other}"))
                .with_hint("Use xml, text, image, font, native, table, signature, or binary.")),
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
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ResourceEntryView {
    pub path: String,
    pub kind: ResourceKind,
    pub size: u64,
    pub compressed_size: u64,
}

pub struct ResourceArchive {
    input: PathBuf,
    entries: Vec<ResourceEntryView>,
}

impl ResourceArchive {
    pub fn open(input: &Path) -> CliResult<Self> {
        let mut archive = ZipArchive::new(File::open(input)?)?;
        let mut entries = Vec::new();
        for index in 0..archive.len() {
            let entry = archive.by_index(index)?;
            if entry.is_dir() {
                continue;
            }
            let path = entry.name().trim_start_matches('/').to_string();
            if path.is_empty() || path.to_ascii_lowercase().ends_with(".dex") {
                continue;
            }
            entries.push(ResourceEntryView {
                kind: ResourceKind::classify(&path),
                path,
                size: entry.size(),
                compressed_size: entry.compressed_size(),
            });
        }
        entries.sort_unstable_by(|left, right| left.path.cmp(&right.path));
        Ok(Self {
            input: input.to_path_buf(),
            entries,
        })
    }

    pub fn open_optional(input: &Path) -> CliResult<Option<Self>> {
        let archive_like = input.extension().is_some_and(|extension| {
            extension.eq_ignore_ascii_case("apk") || extension.eq_ignore_ascii_case("zip")
        });
        if !archive_like {
            return Ok(None);
        }
        Self::open(input).map(Some)
    }

    pub fn entries(&self) -> &[ResourceEntryView] {
        &self.entries
    }

    fn read(&self, path: &str, max_bytes: u64) -> CliResult<ResourceContent> {
        let entry = self
            .entries
            .iter()
            .find(|entry| entry.path == path)
            .ok_or_else(|| CliError::not_found(format!("resource not found: {path}")))?;
        if max_bytes != 0 && entry.size > max_bytes {
            return Err(CliError::input(format!(
                "resource is {} bytes, above the {} byte safety limit",
                entry.size, max_bytes
            ))
            .with_hint("Increase --max-bytes or use --max-bytes 0 to disable the limit."));
        }

        let mut archive = ZipArchive::new(File::open(&self.input)?)?;
        let bytes = Self::read_entry(&mut archive, path)?;
        let text = match entry.kind {
            ResourceKind::Xml => Self::decode_xml(&mut archive, &bytes).ok(),
            ResourceKind::Text | ResourceKind::Signature => TextDecoder::decode(&bytes),
            _ => None,
        };
        Ok(ResourceContent {
            entry: entry.clone(),
            bytes,
            text,
        })
    }

    fn read_entry(archive: &mut ZipArchive<File>, path: &str) -> CliResult<Vec<u8>> {
        let mut file = archive.by_name(path)?;
        let mut bytes = Vec::with_capacity(usize::try_from(file.size()).unwrap_or(0));
        file.read_to_end(&mut bytes)?;
        Ok(bytes)
    }

    fn decode_xml(archive: &mut ZipArchive<File>, bytes: &[u8]) -> CliResult<String> {
        if let Ok(text) = std::str::from_utf8(bytes) {
            if text.trim_start().starts_with('<') {
                return Ok(XmlPrettyPrinter::format(text));
            }
        }
        let table = Self::read_entry(archive, "resources.arsc")?;
        let decoder = Decoder::from_buffer(&table).map_err(|error| {
            CliError::command(format!("unable to decode resources.arsc: {error}"))
        })?;
        let text = decoder
            .xml_visitor(&bytes)
            .and_then(XmlVisitor::into_string)
            .map_err(|error| CliError::command(format!("unable to decode binary XML: {error}")))?;
        Ok(XmlPrettyPrinter::format(&text))
    }
}

struct ResourceContent {
    entry: ResourceEntryView,
    bytes: Vec<u8>,
    text: Option<String>,
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

struct XmlPrettyPrinter;

impl XmlPrettyPrinter {
    fn format(text: &str) -> String {
        Self::try_format(text).unwrap_or_else(|_| text.to_string())
    }

    fn try_format(text: &str) -> CliResult<String> {
        let mut reader = Reader::from_str(text);
        reader.config_mut().trim_text(true);
        let mut writer = Writer::new_with_indent(Vec::new(), b' ', 2);
        loop {
            let event = reader
                .read_event()
                .map_err(|error| CliError::command(format!("unable to parse XML: {error}")))?;
            if matches!(event, Event::Eof) {
                break;
            }
            if matches!(&event, Event::Text(text) if text.as_ref().iter().all(u8::is_ascii_whitespace))
            {
                continue;
            }
            writer
                .write_event(event)
                .map_err(|error| CliError::command(format!("unable to format XML: {error}")))?;
        }
        String::from_utf8(writer.into_inner())
            .map_err(|error| CliError::command(format!("formatted XML is not UTF-8: {error}")))
    }
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ResourcePage<'a> {
    input: String,
    total: usize,
    offset: usize,
    limit: usize,
    results: &'a [ResourceEntryView],
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ResourceReadResult<'a> {
    path: &'a str,
    kind: ResourceKind,
    size: u64,
    output_file: Option<String>,
    content: Option<&'a str>,
}

pub struct ResourcesCommand;

impl ResourcesCommand {
    pub fn run<H: CliHost>(
        context: &mut CommandContext<'_, H>,
        request: &ResourcesRequest,
    ) -> CliResult<()> {
        match request {
            ResourcesRequest::List(request) => Self::list(context, request),
            ResourcesRequest::Read(request) => Self::read(context, request),
        }
    }

    fn list<H: CliHost>(
        context: &mut CommandContext<'_, H>,
        request: &ResourceListRequest,
    ) -> CliResult<()> {
        let archive = ResourceArchive::open(&request.input)?;
        let query = request.query.as_deref().map(str::to_ascii_lowercase);
        let kind = request
            .kind
            .as_deref()
            .map(ResourceKind::parse)
            .transpose()?;
        let matches = archive
            .entries()
            .iter()
            .filter(|entry| kind.is_none_or(|kind| entry.kind == kind))
            .filter(|entry| {
                query
                    .as_deref()
                    .is_none_or(|query| entry.path.to_ascii_lowercase().contains(query))
            })
            .cloned()
            .collect::<Vec<_>>();
        let total = matches.len();
        let results = matches
            .into_iter()
            .skip(request.offset)
            .take(if request.limit == 0 {
                usize::MAX
            } else {
                request.limit
            })
            .collect::<Vec<_>>();
        let page = ResourcePage {
            input: request.input.display().to_string(),
            total,
            offset: request.offset,
            limit: request.limit,
            results: &results,
        };
        let mut text = String::new();
        for entry in &results {
            text.push_str(&format!(
                "{}\t{}\t{}\n",
                entry.kind.name(),
                entry.size,
                entry.path
            ));
        }
        context.respond("resources.list", &page, &text)
    }

    fn read<H: CliHost>(
        context: &mut CommandContext<'_, H>,
        request: &ResourceReadRequest,
    ) -> CliResult<()> {
        if request.raw && request.output_file.is_none() {
            return Err(CliError::usage("--raw requires --output-file"));
        }
        let archive = ResourceArchive::open(&request.input)?;
        let content = archive.read(&request.path, request.max_bytes)?;
        let output_file = request
            .output_file
            .as_ref()
            .map(|path| path.display().to_string());

        if let Some(path) = request.output_file.as_deref() {
            if request.raw || content.text.is_none() {
                context.host_mut().write(path, &content.bytes)?;
            } else if let Some(text) = content.text.as_deref() {
                context.host_mut().write_file(path, text)?;
            }
            context
                .host_mut()
                .note(&format!("output={}", path.display()))?;
        } else if content.text.is_none() {
            return Err(
                CliError::unsupported(format!("resource is binary: {}", request.path))
                    .with_hint("Use --output-file <path> to extract it."),
            );
        }

        let response_content = if request.output_file.is_none() {
            content.text.clone()
        } else {
            None
        };
        let result = ResourceReadResult {
            path: &content.entry.path,
            kind: content.entry.kind,
            size: content.entry.size,
            output_file,
            content: response_content.as_deref(),
        };
        let text = if let Some(path) = request.output_file.as_deref() {
            format!("{}\n", path.display())
        } else {
            let mut text = content.text.unwrap_or_default();
            if !text.ends_with('\n') {
                text.push('\n');
            }
            text
        };
        context.respond("resources.read", &result, &text)
    }
}
