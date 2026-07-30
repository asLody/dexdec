//! Machine-readable CLI discovery.

use serde::Serialize;

use super::error::CliResult;
use super::output::{CliHost, CommandContext, OUTPUT_SCHEMA};

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct Capabilities {
    schema: &'static str,
    version: &'static str,
    inputs: [&'static str; 2],
    source_languages: [&'static str; 3],
    output_formats: [&'static str; 3],
    commands: Vec<CommandCapability>,
    exit_codes: Vec<ExitCodeCapability>,
    conventions: Conventions,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct CommandCapability {
    name: &'static str,
    purpose: &'static str,
    example: &'static str,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ExitCodeCapability {
    code: i32,
    meaning: &'static str,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct Conventions {
    primary_output: &'static str,
    diagnostics: &'static str,
    class_selectors: &'static str,
    method_selectors: &'static str,
    batch_output: &'static str,
}

pub struct CapabilitiesCommand;

impl CapabilitiesCommand {
    pub fn run<H: CliHost>(context: &mut CommandContext<'_, H>) -> CliResult<()> {
        let capabilities = Capabilities {
            schema: OUTPUT_SCHEMA,
            version: env!("CARGO_PKG_VERSION"),
            inputs: ["dex", "apk"],
            source_languages: ["auto", "java", "kotlin"],
            output_formats: ["text", "json", "jsonl"],
            commands: vec![
                CommandCapability {
                    name: "inspect",
                    purpose: "summarize an archive or inspect one class declaration",
                    example: "dexdec inspect app.apk --format json",
                },
                CommandCapability {
                    name: "search",
                    purpose: "find classes, fields, methods, and resources",
                    example: "dexdec search app.apk MainActivity --kind class --format json",
                },
                CommandCapability {
                    name: "decompile",
                    purpose: "generate one method, selected classes, or a complete source tree",
                    example: "dexdec decompile app.apk --class com.example.MainActivity --language java",
                },
                CommandCapability {
                    name: "references",
                    purpose: "find bytecode usages of an exact class or member",
                    example: "dexdec references app.apk method --class com.example.MainActivity --name onCreate --descriptor '(Landroid/os/Bundle;)V' --format json",
                },
                CommandCapability {
                    name: "resources",
                    purpose: "list, extract, and decode APK resources",
                    example: "dexdec resources read app.apk AndroidManifest.xml",
                },
                CommandCapability {
                    name: "debug",
                    purpose: "emit method CFG, IR, and recovery traces for decompiler development",
                    example: "dexdec debug cfg classes.dex --class 'Lcom/example/App;' --method onCreate --output cfg.dot",
                },
                CommandCapability {
                    name: "symbols",
                    purpose: "build and inspect platform symbol databases",
                    example: "dexdec symbols inspect platform.dexsym",
                },
            ],
            exit_codes: vec![
                ExitCodeCapability {
                    code: 0,
                    meaning: "success",
                },
                ExitCodeCapability {
                    code: 1,
                    meaning: "decompilation or command failure",
                },
                ExitCodeCapability {
                    code: 2,
                    meaning: "invalid, ambiguous, or unsupported request",
                },
                ExitCodeCapability {
                    code: 3,
                    meaning: "input or filesystem failure",
                },
                ExitCodeCapability {
                    code: 4,
                    meaning: "class, member, or resource not found",
                },
                ExitCodeCapability {
                    code: 5,
                    meaning: "batch completed with one or more class failures",
                },
            ],
            conventions: Conventions {
                primary_output: "stdout contains only the requested result",
                diagnostics: "stderr contains progress and errors; --quiet suppresses progress",
                class_selectors: "commands accept an exact DEX descriptor or qualified class name",
                method_selectors: "supply --descriptor whenever a method name is overloaded",
                batch_output: "multiple classes require --output-dir and return a machine-readable summary",
            },
        };
        let text = concat!(
            "DexDec CLI capabilities\n",
            "\n",
            "Inputs: dex, apk\n",
            "Source languages: auto, java, kotlin\n",
            "Output formats: text, json, jsonl\n",
            "\n",
            "Commands:\n",
            "  inspect       Archive or class metadata\n",
            "  search        Classes, members, and resources\n",
            "  decompile     Method, class, selection, or full archive\n",
            "  references    Exact class or member usages\n",
            "  resources     APK resources and decoded XML\n",
            "  debug         CFG, IR, and recovery diagnostics\n",
            "  symbols       Platform symbol databases\n",
            "\n",
            "Use `dexdec capabilities --format json` for the full automation contract.\n",
        );
        context.respond("capabilities", &capabilities, text)
    }
}
