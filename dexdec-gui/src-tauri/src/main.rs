fn main() {
    if std::env::args_os().nth(1).as_deref() == Some(std::ffi::OsStr::new("--mcp")) {
        if let Err(error) = dexdec_mcp::McpRuntime::serve_embedded_stdio() {
            eprintln!("DexDec MCP server failed: {error}");
            std::process::exit(1);
        }
        return;
    }
    dexdec_app_lib::run();
}
