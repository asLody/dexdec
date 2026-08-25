//! Dexdec CLI - thin process entry.
//!
//! Argument parsing, dependency assembly, and command dispatch live in
//! `dexdec::cli`. This binary only starts the process and hands off.

// Archive decompilation is dominated by short-lived IR/AST node allocations
// across the rayon pool; mimalloc serves that traffic noticeably faster than
// the system allocator without changing any program behavior.
#[global_allocator]
static GLOBAL_ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
    dexdec::cli::main();
}
