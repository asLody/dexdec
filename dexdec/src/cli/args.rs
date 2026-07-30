//! Command-line syntax and conversion into clap-free request models.

use std::path::PathBuf;

use clap::{ArgAction, Args, Parser, Subcommand, ValueEnum};

use super::model::*;
use crate::SourceLanguage;

#[derive(Parser, Debug)]
#[command(name = "dexdec")]
#[command(version)]
#[command(about = "Fast, resilient DEX and APK decompilation")]
#[command(
    arg_required_else_help = true,
    subcommand_required = true,
    next_line_help = true
)]
#[command(
    after_help = "Agent workflow:\n  dexdec capabilities --format json\n  dexdec inspect app.apk --format json\n  dexdec search app.apk 'MainActivity' --kind class --format json\n  dexdec decompile app.apk --class com.example.MainActivity --language java\n\nPrimary data is written to stdout. Diagnostics and progress are written to stderr."
)]
pub struct Cli {
    /// Output contract for command results.
    #[arg(long, global = true, value_enum, default_value_t = OutputFormatArg::Text)]
    pub format: OutputFormatArg,

    /// Pretty-print JSON documents. JSON Lines always remains one object per line.
    #[arg(long, global = true)]
    pub pretty: bool,

    /// Suppress progress diagnostics on stderr.
    #[arg(long, global = true)]
    pub quiet: bool,

    #[command(subcommand)]
    pub command: CliCommands,
}

impl Cli {
    pub fn into_invocation(self) -> Invocation {
        Invocation {
            output: OutputOptions {
                format: self.format.into(),
                pretty: self.pretty,
                quiet: self.quiet,
            },
            command: self.command.into_command(),
        }
    }
}

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum OutputFormatArg {
    Text,
    Json,
    Jsonl,
}

impl From<OutputFormatArg> for OutputFormat {
    fn from(value: OutputFormatArg) -> Self {
        match value {
            OutputFormatArg::Text => Self::Text,
            OutputFormatArg::Json => Self::Json,
            OutputFormatArg::Jsonl => Self::JsonLines,
        }
    }
}

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum TargetLanguage {
    Auto,
    Java,
    Kotlin,
}

impl From<TargetLanguage> for LanguageSelection {
    fn from(value: TargetLanguage) -> Self {
        match value {
            TargetLanguage::Auto => Self::Auto,
            TargetLanguage::Java => Self::Fixed(SourceLanguage::Java),
            TargetLanguage::Kotlin => Self::Fixed(SourceLanguage::Kotlin),
        }
    }
}

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum SearchKindArg {
    Any,
    Class,
    Field,
    Method,
    Resource,
}

impl From<SearchKindArg> for SearchKind {
    fn from(value: SearchKindArg) -> Self {
        match value {
            SearchKindArg::Any => Self::Any,
            SearchKindArg::Class => Self::Class,
            SearchKindArg::Field => Self::Field,
            SearchKindArg::Method => Self::Method,
            SearchKindArg::Resource => Self::Resource,
        }
    }
}

#[derive(Subcommand, Debug)]
pub enum CliCommands {
    /// Describe supported inputs, outputs, commands, and exit codes.
    Capabilities,

    /// Inspect an archive or one class without generating source.
    Inspect {
        /// DEX or APK input.
        input: PathBuf,

        /// Class descriptor or qualified name to inspect.
        #[arg(long)]
        class: Option<String>,
    },

    /// Search classes, members, and APK resources.
    Search {
        /// DEX or APK input.
        input: PathBuf,

        /// Case-insensitive substring to find.
        query: String,

        /// Restrict the result kind.
        #[arg(long, value_enum, default_value_t = SearchKindArg::Any)]
        kind: SearchKindArg,

        /// Number of matching results to skip.
        #[arg(long, default_value_t = 0)]
        offset: usize,

        /// Maximum results to return; zero means unlimited.
        #[arg(long, default_value_t = 100)]
        limit: usize,
    },

    /// Decompile one method, selected classes, or an entire archive.
    Decompile {
        /// DEX or APK input.
        input: PathBuf,

        /// Class descriptor or qualified name. Repeat to select multiple classes.
        #[arg(short = 'c', long = "class", action = ArgAction::Append)]
        classes: Vec<String>,

        /// Text file containing one descriptor or qualified class name per line.
        #[arg(long)]
        class_file: Option<PathBuf>,

        /// Method name. Requires exactly one selected class.
        #[arg(short = 'm', long)]
        method: Option<String>,

        /// JVM method descriptor used to select an overload.
        #[arg(long, requires = "method")]
        descriptor: Option<String>,

        /// Directory for class source files. Required for multiple classes.
        #[arg(long, conflicts_with = "output_file")]
        output_dir: Option<PathBuf>,

        /// File for one class or method result.
        #[arg(long, conflicts_with = "output_dir")]
        output_file: Option<PathBuf>,

        /// Source language. Auto follows Kotlin metadata and otherwise uses Java.
        #[arg(long, value_enum, default_value_t = TargetLanguage::Auto)]
        language: TargetLanguage,

        /// Do not include nested class source in enclosing classes.
        #[arg(long)]
        no_nested: bool,

        /// Stop at the first class-generation failure.
        #[arg(long)]
        fail_fast: bool,
    },

    /// Find bytecode references to a class, field, or method.
    References {
        /// DEX or APK input.
        input: PathBuf,

        #[command(subcommand)]
        target: ReferenceCommands,
    },

    /// List or read packaged APK resources.
    Resources {
        #[command(subcommand)]
        command: ResourceCommands,
    },

    /// Developer diagnostics for one exact method.
    Debug {
        #[command(subcommand)]
        command: DebugCommands,
    },

    /// Build or inspect versioned platform symbol metadata.
    Symbols {
        #[command(subcommand)]
        command: CliSymbolCommands,
    },
}

impl CliCommands {
    fn into_command(self) -> Command {
        match self {
            Self::Capabilities => Command::Capabilities,
            Self::Inspect { input, class } => Command::Inspect(InspectRequest { input, class }),
            Self::Search {
                input,
                query,
                kind,
                offset,
                limit,
            } => Command::Search(SearchRequest {
                input,
                query,
                kind: kind.into(),
                offset,
                limit,
            }),
            Self::Decompile {
                input,
                classes,
                class_file,
                method,
                descriptor,
                output_dir,
                output_file,
                language,
                no_nested,
                fail_fast,
            } => Command::Decompile(DecompileRequest {
                input,
                classes,
                class_file,
                method,
                descriptor,
                output_dir,
                output_file,
                language: language.into(),
                include_nested: !no_nested,
                fail_fast,
            }),
            Self::References { input, target } => Command::References(ReferencesRequest {
                input,
                target: target.into_query(),
            }),
            Self::Resources { command } => Command::Resources(command.into_request()),
            Self::Debug { command } => Command::Debug(command.into_request()),
            Self::Symbols { command } => Command::Symbols(command.into_request()),
        }
    }
}

#[derive(Subcommand, Debug)]
pub enum ReferenceCommands {
    /// References to a class.
    Class {
        /// Class descriptor or qualified name.
        #[arg(long)]
        class: String,
    },

    /// References to a field. Descriptor is optional when the name is unique.
    Field {
        /// Declaring class descriptor or qualified name.
        #[arg(long)]
        class: String,
        /// Field name.
        #[arg(long)]
        name: String,
        #[arg(long)]
        descriptor: Option<String>,
    },

    /// References to a method. Descriptor is optional when the name is unique.
    Method {
        /// Declaring class descriptor or qualified name.
        #[arg(long)]
        class: String,
        /// Method name.
        #[arg(long)]
        name: String,
        #[arg(long)]
        descriptor: Option<String>,
    },
}

impl ReferenceCommands {
    fn into_query(self) -> ReferenceQuery {
        match self {
            Self::Class { class } => ReferenceQuery::Class { class },
            Self::Field {
                class,
                name,
                descriptor,
            } => ReferenceQuery::Field {
                class,
                name,
                descriptor,
            },
            Self::Method {
                class,
                name,
                descriptor,
            } => ReferenceQuery::Method {
                class,
                name,
                descriptor,
            },
        }
    }
}

#[derive(Subcommand, Debug)]
pub enum ResourceCommands {
    /// List packaged resources without extracting them.
    List {
        input: PathBuf,
        #[arg(long)]
        query: Option<String>,
        /// Resource kind: xml, text, image, font, native, table, signature, or binary.
        #[arg(long)]
        kind: Option<String>,
        #[arg(long, default_value_t = 0)]
        offset: usize,
        /// Maximum results to return; zero means unlimited.
        #[arg(long, default_value_t = 100)]
        limit: usize,
    },

    /// Read and, when possible, decode one packaged resource.
    Read {
        input: PathBuf,
        path: String,
        #[arg(long)]
        output_file: Option<PathBuf>,
        /// Preserve the exact archived bytes. Requires --output-file.
        #[arg(long, requires = "output_file")]
        raw: bool,
        /// Safety limit in bytes; zero disables the limit.
        #[arg(long, default_value_t = 33_554_432)]
        max_bytes: u64,
    },
}

impl ResourceCommands {
    fn into_request(self) -> ResourcesRequest {
        match self {
            Self::List {
                input,
                query,
                kind,
                offset,
                limit,
            } => ResourcesRequest::List(ResourceListRequest {
                input,
                query,
                kind,
                offset,
                limit,
            }),
            Self::Read {
                input,
                path,
                output_file,
                raw,
                max_bytes,
            } => ResourcesRequest::Read(ResourceReadRequest {
                input,
                path,
                output_file,
                raw,
                max_bytes,
            }),
        }
    }
}

#[derive(Args, Debug)]
pub struct MethodTargetArgs {
    /// DEX or APK input.
    input: PathBuf,
    /// Class descriptor or qualified name.
    #[arg(long)]
    class: String,
    #[arg(long)]
    method: String,
    /// JVM method descriptor used to select an overload.
    #[arg(long)]
    descriptor: Option<String>,
}

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum GraphFormat {
    Dot,
    Text,
}

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum TraceStage {
    Passes,
    Regions,
    Semantic,
}

#[derive(Subcommand, Debug)]
pub enum DebugCommands {
    /// Print a control-flow graph as DOT or text.
    Cfg {
        #[command(flatten)]
        target: MethodTargetArgs,
        #[arg(long, value_enum, default_value_t = GraphFormat::Dot)]
        graph_format: GraphFormat,
        #[arg(long)]
        output: Option<PathBuf>,
    },
    /// Print decoded instruction blocks.
    Ir {
        #[command(flatten)]
        target: MethodTargetArgs,
        #[arg(long)]
        output: Option<PathBuf>,
    },
    /// Trace one verified recovery stage.
    Trace {
        #[command(flatten)]
        target: MethodTargetArgs,
        #[arg(long, value_enum)]
        stage: TraceStage,
        #[arg(long)]
        blocks: Option<String>,
        #[arg(long)]
        changed_details: bool,
        #[arg(long, value_enum, default_value_t = TargetLanguage::Java)]
        language: TargetLanguage,
        #[arg(long)]
        output: Option<PathBuf>,
    },
}

impl DebugCommands {
    fn into_request(self) -> DebugRequest {
        match self {
            Self::Cfg {
                target,
                graph_format,
                output,
            } => DebugRequest::Cfg(CfgRequest {
                input: target.input,
                class: target.class,
                method: target.method,
                descriptor: target.descriptor,
                format: match graph_format {
                    GraphFormat::Dot => "dot",
                    GraphFormat::Text => "text",
                }
                .to_string(),
                output,
            }),
            Self::Ir { target, output } => DebugRequest::Ir(IrRequest {
                input: target.input,
                class: target.class,
                method: target.method,
                descriptor: target.descriptor,
                output,
            }),
            Self::Trace {
                target,
                stage,
                blocks,
                changed_details,
                language,
                output,
            } => match stage {
                TraceStage::Passes => DebugRequest::TracePasses(TracePassesRequest {
                    input: target.input,
                    class: target.class,
                    method: target.method,
                    descriptor: target.descriptor,
                    blocks,
                    changed_details,
                    output,
                }),
                TraceStage::Regions => DebugRequest::TraceRegions(TraceRegionsRequest {
                    input: target.input,
                    class: target.class,
                    method: target.method,
                    descriptor: target.descriptor,
                    output,
                }),
                TraceStage::Semantic => DebugRequest::TraceSemantic(TraceSemanticRequest {
                    input: target.input,
                    class: target.class,
                    method: target.method,
                    descriptor: target.descriptor,
                    language: match language {
                        TargetLanguage::Kotlin => SourceLanguage::Kotlin,
                        TargetLanguage::Auto | TargetLanguage::Java => SourceLanguage::Java,
                    },
                    output,
                }),
            },
        }
    }
}

#[derive(Subcommand, Debug)]
pub enum CliSymbolCommands {
    /// Build a .dexsym database from JDK, Android, and library archives.
    Build {
        #[arg(long)]
        output: PathBuf,
        #[arg(long)]
        base: Option<PathBuf>,
        #[arg(long)]
        jdk_home: Option<PathBuf>,
        #[arg(long)]
        java_release: Option<u16>,
        #[arg(long, value_delimiter = ',')]
        jdk_module: Vec<String>,
        #[arg(long)]
        android_sdk: Option<PathBuf>,
        #[arg(long, value_delimiter = ',')]
        android_api: Vec<u16>,
        #[arg(long = "library")]
        library_archive: Vec<PathBuf>,
    },
    /// Show provenance and symbol counts for a .dexsym database.
    Inspect { database: PathBuf },
}

impl CliSymbolCommands {
    fn into_request(self) -> SymbolsRequest {
        match self {
            Self::Build {
                output,
                base,
                jdk_home,
                java_release,
                jdk_module,
                android_sdk,
                android_api,
                library_archive,
            } => SymbolsRequest::Build(SymbolsBuildRequest {
                output,
                base_database: base,
                jdk_home,
                java_release,
                jdk_modules: jdk_module,
                android_sdk,
                android_apis: android_api,
                library_archives: library_archive,
            }),
            Self::Inspect { database } => {
                SymbolsRequest::Inspect(SymbolsInspectRequest { database })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_exact_method_reference_with_named_selectors() {
        let cli = Cli::try_parse_from([
            "dexdec",
            "references",
            "app.apk",
            "method",
            "--class",
            "com.example.MainActivity",
            "--name",
            "onCreate",
            "--descriptor",
            "(Landroid/os/Bundle;)V",
            "--format",
            "json",
        ])
        .expect("reference request should parse");

        let invocation = cli.into_invocation();
        assert_eq!(invocation.output.format, OutputFormat::Json);
        let Command::References(request) = invocation.command else {
            panic!("expected references command");
        };
        let ReferenceQuery::Method {
            class,
            name,
            descriptor,
        } = request.target
        else {
            panic!("expected method reference query");
        };
        assert_eq!(class, "com.example.MainActivity");
        assert_eq!(name, "onCreate");
        assert_eq!(descriptor.as_deref(), Some("(Landroid/os/Bundle;)V"));
    }

    #[test]
    fn parses_repeatable_class_selection() {
        let cli = Cli::try_parse_from([
            "dexdec",
            "decompile",
            "classes.dex",
            "--class",
            "com.example.First",
            "--class",
            "com.example.Second",
            "--output-dir",
            "source",
        ])
        .expect("decompile request should parse");

        let Command::Decompile(request) = cli.into_invocation().command else {
            panic!("expected decompile command");
        };
        assert_eq!(request.classes, ["com.example.First", "com.example.Second"]);
        assert_eq!(request.output_dir, Some(PathBuf::from("source")));
    }
}
