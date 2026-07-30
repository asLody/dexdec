//! Agent-oriented command-line application for DexDec.

mod application;
mod args;
mod capabilities;
mod cfg;
mod decompile;
mod error;
mod format_insn;
mod inspect;
mod ir;
mod method_decode;
mod model;
mod output;
mod references;
mod resolve;
mod resources;
mod search;
mod symbols;
mod trace;

pub use application::CliApplication;
pub use args::Cli;
pub use error::{cli_err, CliError, CliResult, ErrorKind};
pub use model::*;
pub use output::{CliHost, ConsoleHost, FileSystem, ProgressReporter, TextOutput};

pub fn main() {
    let _profile = crate::profiling::start_from_env();
    let exit_code = CliApplication::new(ConsoleHost).run_env();
    if exit_code != 0 {
        std::process::exit(exit_code);
    }
}

pub fn run_with_host<H: CliHost>(host: &mut H, invocation: Invocation) -> CliResult<ExitStatus> {
    CliApplication::execute(host, invocation)
}
