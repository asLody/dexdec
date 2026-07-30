use clap::Parser;
use dexdec_mcp::{McpOptions, McpRuntime};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    McpRuntime::new(McpOptions::parse()).serve_stdio().await
}
