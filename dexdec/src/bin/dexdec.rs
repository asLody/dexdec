//! Dexdec CLI - thin process entry.
//!
//! Argument parsing, dependency assembly, and command dispatch live in
//! `dexdec::cli`. This binary only starts the process and hands off.

fn main() {
    dexdec::cli::main();
}
