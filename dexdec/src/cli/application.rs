//! Process lifecycle, dispatch, and stable failure rendering.

use std::ffi::OsString;
use std::path::Path;

use clap::error::ErrorKind as ClapErrorKind;
use clap::Parser;

use super::args::Cli;
use super::capabilities::CapabilitiesCommand;
use super::cfg::CfgCommand;
use super::decompile::DecompileCommand;
use super::error::{CliError, CliResult};
use super::inspect::InspectCommand;
use super::ir::IrCommand;
use super::model::{Command, DebugRequest, ExitStatus, Invocation, OutputFormat};
use super::output::{render_error, CliHost, CommandContext};
use super::references::ReferencesCommand;
use super::resources::ResourcesCommand;
use super::search::SearchCommand;
use super::symbols::SymbolsCommand;
use super::trace::{TracePassesCommand, TraceRegionsCommand, TraceSemanticCommand};

pub struct CliApplication<H> {
    host: H,
}

impl<H: CliHost> CliApplication<H> {
    pub fn new(host: H) -> Self {
        Self { host }
    }

    pub fn run_env(&mut self) -> i32 {
        self.run_from(std::env::args_os())
    }

    pub fn run_from<I, T>(&mut self, arguments: I) -> i32
    where
        I: IntoIterator<Item = T>,
        T: Into<OsString> + Clone,
    {
        let arguments = arguments
            .into_iter()
            .map(Into::into)
            .collect::<Vec<OsString>>();
        let detected = DetectedOutput::from_arguments(&arguments);
        let cli = match Cli::try_parse_from(&arguments) {
            Ok(cli) => cli,
            Err(error)
                if matches!(
                    error.kind(),
                    ClapErrorKind::DisplayHelp | ClapErrorKind::DisplayVersion
                ) =>
            {
                let _ = self.host.emit(&error.to_string());
                return 0;
            }
            Err(error) => {
                let error = CliError::usage(error.to_string());
                let rendered = render_error(detected.format, detected.pretty, &error);
                let _ = self.host.note(rendered.trim_end());
                return error.exit_code();
            }
        };
        let invocation = cli.into_invocation();
        let format = invocation.output.format;
        let pretty = invocation.output.pretty;
        if let Err(error) = RequestValidator::validate(&self.host, &invocation.command) {
            let rendered = render_error(format, pretty, &error);
            let _ = self.host.note(rendered.trim_end());
            return error.exit_code();
        }
        match Self::execute(&mut self.host, invocation) {
            Ok(status) => status.code(),
            Err(error) => {
                let rendered = render_error(format, pretty, &error);
                let _ = self.host.note(rendered.trim_end());
                error.exit_code()
            }
        }
    }

    pub fn execute(host: &mut H, invocation: Invocation) -> CliResult<ExitStatus> {
        let mut context = CommandContext::new(host, invocation.output);
        match invocation.command {
            Command::Capabilities => {
                CapabilitiesCommand::run(&mut context)?;
                Ok(ExitStatus::Success)
            }
            Command::Inspect(request) => {
                InspectCommand::run(&mut context, &request)?;
                Ok(ExitStatus::Success)
            }
            Command::Search(request) => {
                SearchCommand::run(&mut context, &request)?;
                Ok(ExitStatus::Success)
            }
            Command::Decompile(request) => DecompileCommand::run(&mut context, &request),
            Command::References(request) => {
                ReferencesCommand::run(&mut context, &request)?;
                Ok(ExitStatus::Success)
            }
            Command::Resources(request) => {
                ResourcesCommand::run(&mut context, &request)?;
                Ok(ExitStatus::Success)
            }
            Command::Debug(request) => {
                context.require_text("debug")?;
                match request {
                    DebugRequest::Cfg(request) => CfgCommand::run(context.host_mut(), &request)?,
                    DebugRequest::Ir(request) => IrCommand::run(context.host_mut(), &request)?,
                    DebugRequest::TracePasses(request) => {
                        TracePassesCommand::run(context.host_mut(), &request)?
                    }
                    DebugRequest::TraceRegions(request) => {
                        TraceRegionsCommand::run(context.host_mut(), &request)?
                    }
                    DebugRequest::TraceSemantic(request) => {
                        TraceSemanticCommand::run(context.host_mut(), &request)?
                    }
                }
                Ok(ExitStatus::Success)
            }
            Command::Symbols(request) => {
                context.require_text("symbols")?;
                SymbolsCommand::run(context.host_mut(), &request)?;
                Ok(ExitStatus::Success)
            }
        }
    }
}

struct RequestValidator;

impl RequestValidator {
    fn validate<H: CliHost>(host: &H, command: &Command) -> CliResult<()> {
        let requirements = InputRequirements::from_command(command);
        for input in requirements.files {
            if !host.exists(input) {
                return Err(CliError::input(format!(
                    "input does not exist: {}",
                    input.display()
                )));
            }
            if host.is_dir(input) {
                return Err(CliError::input(format!(
                    "input must be a file: {}",
                    input.display()
                )));
            }
        }
        for input in requirements.directories {
            if !host.exists(input) {
                return Err(CliError::input(format!(
                    "input directory does not exist: {}",
                    input.display()
                )));
            }
            if !host.is_dir(input) {
                return Err(CliError::input(format!(
                    "input must be a directory: {}",
                    input.display()
                )));
            }
        }
        Ok(())
    }
}

#[derive(Default)]
struct InputRequirements<'a> {
    files: Vec<&'a Path>,
    directories: Vec<&'a Path>,
}

impl<'a> InputRequirements<'a> {
    fn from_command(command: &'a Command) -> Self {
        let mut requirements = Self::default();
        match command {
            Command::Capabilities => {}
            Command::Inspect(request) => requirements.files.push(&request.input),
            Command::Search(request) => requirements.files.push(&request.input),
            Command::Decompile(request) => {
                requirements.files.push(&request.input);
                requirements.files.extend(request.class_file.as_deref());
            }
            Command::References(request) => requirements.files.push(&request.input),
            Command::Resources(request) => match request {
                super::model::ResourcesRequest::List(request) => {
                    requirements.files.push(&request.input)
                }
                super::model::ResourcesRequest::Read(request) => {
                    requirements.files.push(&request.input)
                }
            },
            Command::Debug(request) => requirements.files.push(match request {
                DebugRequest::Cfg(request) => &request.input,
                DebugRequest::Ir(request) => &request.input,
                DebugRequest::TracePasses(request) => &request.input,
                DebugRequest::TraceRegions(request) => &request.input,
                DebugRequest::TraceSemantic(request) => &request.input,
            }),
            Command::Symbols(request) => match request {
                super::model::SymbolsRequest::Build(request) => {
                    requirements.files.extend(request.base_database.as_deref());
                    requirements
                        .files
                        .extend(request.library_archives.iter().map(|path| path.as_path()));
                    requirements.directories.extend(request.jdk_home.as_deref());
                    requirements
                        .directories
                        .extend(request.android_sdk.as_deref());
                }
                super::model::SymbolsRequest::Inspect(request) => {
                    requirements.files.push(&request.database)
                }
            },
        }
        requirements
    }
}

struct DetectedOutput {
    format: OutputFormat,
    pretty: bool,
}

impl DetectedOutput {
    fn from_arguments(arguments: &[OsString]) -> Self {
        let mut format = OutputFormat::Text;
        let mut pretty = false;
        let mut index = 0usize;
        while index < arguments.len() {
            let argument = arguments[index].to_string_lossy();
            if argument == "--pretty" {
                pretty = true;
            } else if let Some(value) = argument.strip_prefix("--format=") {
                format = Self::parse_format(value);
            } else if argument == "--format" {
                if let Some(value) = arguments.get(index + 1) {
                    format = Self::parse_format(&value.to_string_lossy());
                    index += 1;
                }
            }
            index += 1;
        }
        Self { format, pretty }
    }

    fn parse_format(value: &str) -> OutputFormat {
        match value {
            "json" => OutputFormat::Json,
            "jsonl" => OutputFormat::JsonLines,
            _ => OutputFormat::Text,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use serde_json::Value;

    use super::*;
    use crate::cli::output::{FileSystem, ProgressReporter, TextOutput, OUTPUT_SCHEMA};

    #[derive(Default)]
    struct MemoryHost {
        stdout: String,
        stderr: String,
    }

    impl TextOutput for MemoryHost {
        fn emit(&mut self, text: &str) -> CliResult<()> {
            self.stdout.push_str(text);
            Ok(())
        }

        fn write_file(&mut self, _path: &Path, _text: &str) -> CliResult<()> {
            Err(CliError::unsupported("test host does not write files"))
        }

        fn note(&mut self, message: &str) -> CliResult<()> {
            self.stderr.push_str(message);
            self.stderr.push('\n');
            Ok(())
        }
    }

    impl ProgressReporter for MemoryHost {
        fn progress(&mut self, message: &str) -> CliResult<()> {
            self.note(message)
        }
    }

    impl FileSystem for MemoryHost {
        fn create_dir_all(&mut self, _path: &Path) -> CliResult<()> {
            Err(CliError::unsupported("test host does not write files"))
        }

        fn write(&mut self, _path: &Path, _contents: impl AsRef<[u8]>) -> CliResult<()> {
            Err(CliError::unsupported("test host does not write files"))
        }

        fn append(&mut self, _path: &Path, _contents: impl AsRef<[u8]>) -> CliResult<()> {
            Err(CliError::unsupported("test host does not write files"))
        }

        fn read_to_string(&mut self, _path: &Path) -> CliResult<String> {
            Err(CliError::unsupported("test host does not read files"))
        }

        fn metadata_len(&mut self, _path: &Path) -> CliResult<u64> {
            Err(CliError::unsupported("test host does not read files"))
        }

        fn is_dir(&self, _path: &Path) -> bool {
            false
        }

        fn exists(&self, _path: &Path) -> bool {
            false
        }
    }

    #[test]
    fn capabilities_are_versioned_json_on_stdout() {
        let mut application = CliApplication::new(MemoryHost::default());
        let exit = application.run_from(["dexdec", "capabilities", "--format", "json"]);

        assert_eq!(exit, 0);
        assert!(application.host.stderr.is_empty());
        let value: Value = serde_json::from_str(&application.host.stdout).unwrap();
        assert_eq!(value["schema"], OUTPUT_SCHEMA);
        assert_eq!(value["command"], "capabilities");
        assert_eq!(value["ok"], true);
    }

    #[test]
    fn missing_input_is_a_structured_path_aware_error() {
        let mut application = CliApplication::new(MemoryHost::default());
        let exit = application.run_from(["dexdec", "inspect", "missing.dex", "--format", "json"]);

        assert_eq!(exit, 3);
        assert!(application.host.stdout.is_empty());
        let value: Value = serde_json::from_str(&application.host.stderr).unwrap();
        assert_eq!(value["error"]["code"], "invalid_input");
        assert!(value["error"]["message"]
            .as_str()
            .unwrap()
            .contains("missing.dex"));
    }

    #[test]
    fn output_detection_supports_equals_syntax() {
        let arguments = [
            OsString::from("dexdec"),
            OsString::from("--format=jsonl"),
            OsString::from("--pretty"),
        ];
        let detected = DetectedOutput::from_arguments(&arguments);

        assert_eq!(detected.format, OutputFormat::JsonLines);
        assert!(detected.pretty);
    }
}
