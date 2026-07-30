use std::path::PathBuf;

use directories::BaseDirs;

use super::command::{
    claude_add, claude_remove, codex_add, codex_remove, grok_add, grok_remove, AddMcpInstaller,
    ProgramSpec, ReplaceCliInstaller,
};
use super::config::{JsonConfigurationProbe, TomlConfigurationProbe};
use super::AgentAdapter;

pub struct AgentCatalog<'a> {
    directories: &'a BaseDirs,
}

impl<'a> AgentCatalog<'a> {
    pub fn new(directories: &'a BaseDirs) -> Self {
        Self { directories }
    }

    pub fn build(&self) -> Vec<AgentAdapter> {
        vec![
            self.codex(),
            self.claude_code(),
            self.cursor(),
            self.vscode(),
            self.grok(),
        ]
    }

    fn codex(&self) -> AgentAdapter {
        let home = self.directories.home_dir();
        let config_home = std::env::var_os("CODEX_HOME")
            .map(PathBuf::from)
            .unwrap_or_else(|| home.join(".codex"));
        AgentAdapter::new(
            "codex",
            "Codex",
            ProgramSpec::new(
                "codex",
                vec![
                    home.join(".local/bin/codex"),
                    home.join(".cargo/bin/codex"),
                    PathBuf::from("/opt/homebrew/bin/codex"),
                    PathBuf::from("/usr/local/bin/codex"),
                ],
            ),
            Box::new(TomlConfigurationProbe::new(config_home.join("config.toml"))),
            Box::new(ReplaceCliInstaller::new(codex_remove, codex_add)),
        )
    }

    fn claude_code(&self) -> AgentAdapter {
        let home = self.directories.home_dir();
        AgentAdapter::new(
            "claude-code",
            "Claude Code",
            ProgramSpec::new(
                "claude",
                vec![
                    home.join(".local/bin/claude"),
                    PathBuf::from("/opt/homebrew/bin/claude"),
                    PathBuf::from("/usr/local/bin/claude"),
                ],
            ),
            Box::new(JsonConfigurationProbe::new(
                home.join(".claude.json"),
                "mcpServers",
            )),
            Box::new(ReplaceCliInstaller::new(claude_remove, claude_add)),
        )
    }

    fn cursor(&self) -> AgentAdapter {
        let home = self.directories.home_dir();
        AgentAdapter::new(
            "cursor",
            "Cursor",
            ProgramSpec::new(
                "cursor",
                vec![
                    PathBuf::from("/usr/local/bin/cursor"),
                    PathBuf::from("/opt/homebrew/bin/cursor"),
                    PathBuf::from("/Applications/Cursor.app/Contents/Resources/app/bin/cursor"),
                ],
            ),
            Box::new(JsonConfigurationProbe::new(
                home.join(".cursor/mcp.json"),
                "mcpServers",
            )),
            Box::new(AddMcpInstaller),
        )
    }

    fn vscode(&self) -> AgentAdapter {
        AgentAdapter::new(
            "vscode",
            "Visual Studio Code",
            ProgramSpec::new(
                "code",
                vec![
                    PathBuf::from("/usr/local/bin/code"),
                    PathBuf::from("/opt/homebrew/bin/code"),
                    PathBuf::from(
                        "/Applications/Visual Studio Code.app/Contents/Resources/app/bin/code",
                    ),
                ],
            ),
            Box::new(JsonConfigurationProbe::new(
                self.directories.config_dir().join("Code/User/mcp.json"),
                "servers",
            )),
            Box::new(AddMcpInstaller),
        )
    }

    fn grok(&self) -> AgentAdapter {
        let home = self.directories.home_dir();
        let grok_home = std::env::var_os("GROK_HOME")
            .map(PathBuf::from)
            .unwrap_or_else(|| home.join(".grok"));
        AgentAdapter::new(
            "grok",
            "Grok",
            ProgramSpec::new(
                "grok",
                vec![
                    grok_home.join("bin/grok"),
                    home.join(".local/bin/grok"),
                    home.join(".cargo/bin/grok"),
                    PathBuf::from("/opt/homebrew/bin/grok"),
                    PathBuf::from("/usr/local/bin/grok"),
                ],
            ),
            Box::new(TomlConfigurationProbe::new(grok_home.join("config.toml"))),
            Box::new(ReplaceCliInstaller::new(grok_remove, grok_add)),
        )
    }
}
