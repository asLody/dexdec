use std::path::{Path, PathBuf};

use clap::Parser;

#[derive(Debug, Clone, Parser)]
#[command(name = "dexdec-mcp", version, about = "DexDec MCP server")]
pub struct McpOptions {
    /// Directory an agent may read. Repeat to grant multiple roots.
    #[arg(long = "allow-root", value_name = "DIRECTORY")]
    pub allowed_roots: Vec<PathBuf>,
}

#[derive(Debug, Clone)]
pub struct AccessPolicy {
    roots: Vec<PathBuf>,
}

impl AccessPolicy {
    pub fn from_options(options: McpOptions) -> Result<Self, std::io::Error> {
        let roots = if options.allowed_roots.is_empty() {
            vec![std::env::current_dir()?]
        } else {
            options.allowed_roots
        };
        roots
            .into_iter()
            .map(std::fs::canonicalize)
            .collect::<Result<Vec<_>, _>>()
            .map(|roots| Self { roots })
    }

    pub fn authorize_file(&self, requested: &Path) -> Result<PathBuf, String> {
        let path = std::fs::canonicalize(requested)
            .map_err(|error| format!("cannot open {}: {error}", requested.display()))?;
        if !path.is_file() {
            return Err(format!("input is not a file: {}", path.display()));
        }
        if !self.roots.iter().any(|root| path.starts_with(root)) {
            return Err(format!(
                "input is outside the configured MCP roots: {}",
                path.display()
            ));
        }
        Ok(path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_files_outside_allowed_roots() {
        let root = std::env::temp_dir().join(format!("dexdec-mcp-root-{}", std::process::id()));
        std::fs::create_dir_all(&root).unwrap();
        let policy = AccessPolicy::from_options(McpOptions {
            allowed_roots: vec![root.clone()],
        })
        .unwrap();

        assert!(policy
            .authorize_file(std::env::current_exe().unwrap().as_path())
            .is_err());
        std::fs::remove_dir_all(root).unwrap();
    }
}
