//! Output contracts and injected process I/O.

use std::fs::{self, OpenOptions};
use std::io::{self, Write};
use std::path::Path;

use serde::Serialize;

use super::error::{CliError, CliResult};
use super::model::{OutputFormat, OutputOptions};

pub const OUTPUT_SCHEMA: &str = "dexdec.cli/v1";

pub trait TextOutput {
    fn emit(&mut self, text: &str) -> CliResult<()>;
    fn write_file(&mut self, path: &Path, text: &str) -> CliResult<()>;
    fn note(&mut self, message: &str) -> CliResult<()>;

    fn emit_or_write(&mut self, path: Option<&Path>, text: &str) -> CliResult<()> {
        match path {
            Some(path) => {
                self.write_file(path, text)?;
                self.note(&format!("output={}", path.display()))
            }
            None => self.emit(text),
        }
    }
}

pub trait ProgressReporter {
    fn progress(&mut self, message: &str) -> CliResult<()>;
}

pub trait FileSystem {
    fn create_dir_all(&mut self, path: &Path) -> CliResult<()>;
    fn write(&mut self, path: &Path, contents: impl AsRef<[u8]>) -> CliResult<()>;
    fn append(&mut self, path: &Path, contents: impl AsRef<[u8]>) -> CliResult<()>;
    fn read_to_string(&mut self, path: &Path) -> CliResult<String>;
    fn metadata_len(&mut self, path: &Path) -> CliResult<u64>;
    fn is_dir(&self, path: &Path) -> bool;
    fn exists(&self, path: &Path) -> bool;
}

pub trait CliHost: TextOutput + ProgressReporter + FileSystem {}

impl<T> CliHost for T where T: TextOutput + ProgressReporter + FileSystem {}

#[derive(Debug, Default)]
pub struct ConsoleHost;

impl TextOutput for ConsoleHost {
    fn emit(&mut self, text: &str) -> CliResult<()> {
        let mut output = io::stdout().lock();
        output.write_all(text.as_bytes())?;
        output.flush()?;
        Ok(())
    }

    fn write_file(&mut self, path: &Path, text: &str) -> CliResult<()> {
        if let Some(parent) = path
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
        {
            fs::create_dir_all(parent)?;
        }
        fs::write(path, text)?;
        Ok(())
    }

    fn note(&mut self, message: &str) -> CliResult<()> {
        let mut diagnostics = io::stderr().lock();
        writeln!(diagnostics, "{message}")?;
        diagnostics.flush()?;
        Ok(())
    }
}

impl ProgressReporter for ConsoleHost {
    fn progress(&mut self, message: &str) -> CliResult<()> {
        self.note(message)
    }
}

impl FileSystem for ConsoleHost {
    fn create_dir_all(&mut self, path: &Path) -> CliResult<()> {
        fs::create_dir_all(path)?;
        Ok(())
    }

    fn write(&mut self, path: &Path, contents: impl AsRef<[u8]>) -> CliResult<()> {
        if let Some(parent) = path
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
        {
            fs::create_dir_all(parent)?;
        }
        fs::write(path, contents)?;
        Ok(())
    }

    fn append(&mut self, path: &Path, contents: impl AsRef<[u8]>) -> CliResult<()> {
        if let Some(parent) = path
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
        {
            fs::create_dir_all(parent)?;
        }
        let mut file = OpenOptions::new().create(true).append(true).open(path)?;
        file.write_all(contents.as_ref())?;
        file.flush()?;
        Ok(())
    }

    fn read_to_string(&mut self, path: &Path) -> CliResult<String> {
        Ok(fs::read_to_string(path)?)
    }

    fn metadata_len(&mut self, path: &Path) -> CliResult<u64> {
        Ok(fs::metadata(path)?.len())
    }

    fn is_dir(&self, path: &Path) -> bool {
        path.is_dir()
    }

    fn exists(&self, path: &Path) -> bool {
        path.exists()
    }
}

#[derive(Serialize)]
struct SuccessEnvelope<'a, T: Serialize> {
    schema: &'static str,
    ok: bool,
    command: &'a str,
    data: &'a T,
}

pub struct CommandContext<'a, H: CliHost> {
    host: &'a mut H,
    options: OutputOptions,
}

impl<'a, H: CliHost> CommandContext<'a, H> {
    pub fn new(host: &'a mut H, options: OutputOptions) -> Self {
        Self { host, options }
    }

    pub fn format(&self) -> OutputFormat {
        self.options.format
    }

    pub fn host_mut(&mut self) -> &mut H {
        self.host
    }

    pub fn progress(&mut self, message: &str) -> CliResult<()> {
        if self.options.quiet {
            return Ok(());
        }
        self.host.progress(message)
    }

    pub fn respond<T: Serialize>(&mut self, command: &str, data: &T, text: &str) -> CliResult<()> {
        match self.options.format {
            OutputFormat::Text => self.host.emit(text),
            OutputFormat::Json => {
                let envelope = SuccessEnvelope {
                    schema: OUTPUT_SCHEMA,
                    ok: true,
                    command,
                    data,
                };
                let mut encoded = if self.options.pretty {
                    serde_json::to_string_pretty(&envelope)?
                } else {
                    serde_json::to_string(&envelope)?
                };
                encoded.push('\n');
                self.host.emit(&encoded)
            }
            OutputFormat::JsonLines => {
                let envelope = SuccessEnvelope {
                    schema: OUTPUT_SCHEMA,
                    ok: true,
                    command,
                    data,
                };
                let mut encoded = serde_json::to_string(&envelope)?;
                encoded.push('\n');
                self.host.emit(&encoded)
            }
        }
    }

    pub fn require_text(&self, command: &str) -> CliResult<()> {
        if self.options.format == OutputFormat::Text {
            return Ok(());
        }
        Err(CliError::unsupported(format!(
            "{command} produces a developer text artifact and does not support structured output"
        ))
        .with_hint("Use --format text and --output <file>."))
    }
}

pub fn render_error(format: OutputFormat, pretty: bool, error: &CliError) -> String {
    if format == OutputFormat::Text {
        return format!("error[{}]: {error}\n", error.code());
    }
    let value = serde_json::json!({
        "schema": OUTPUT_SCHEMA,
        "ok": false,
        "error": {
            "code": error.code(),
            "message": error.message(),
            "hint": error.hint(),
        }
    });
    let mut encoded = if format == OutputFormat::Json && pretty {
        serde_json::to_string_pretty(&value).unwrap_or_else(|_| value.to_string())
    } else {
        value.to_string()
    };
    encoded.push('\n');
    encoded
}
