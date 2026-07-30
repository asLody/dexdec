use std::env;
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use super::{IntegrationError, McpLaunchSpec};

#[derive(Clone)]
pub struct ProgramSpec {
    name: &'static str,
    candidates: Vec<PathBuf>,
}

impl ProgramSpec {
    pub fn new(name: &'static str, candidates: Vec<PathBuf>) -> Self {
        Self { name, candidates }
    }
}

pub struct CommandLocator {
    home: PathBuf,
}

impl CommandLocator {
    pub fn new(home: PathBuf) -> Self {
        Self { home }
    }

    pub fn locate(&self, program: &ProgramSpec) -> Option<PathBuf> {
        let from_path = env::var_os("PATH").and_then(|path| {
            env::split_paths(&path)
                .map(|directory| directory.join(program.name))
                .find(|candidate| candidate.is_file())
        });
        from_path.or_else(|| {
            program
                .candidates
                .iter()
                .map(|candidate| {
                    if candidate.is_absolute() {
                        candidate.clone()
                    } else {
                        self.home.join(candidate)
                    }
                })
                .find(|candidate| candidate.is_file())
        })
    }
}

pub trait AgentInstaller: Send + Sync {
    fn install(&self, executable: &Path, launch: &McpLaunchSpec) -> Result<(), IntegrationError>;
}

pub struct ReplaceCliInstaller {
    remove: fn() -> Vec<OsString>,
    add: fn(&McpLaunchSpec) -> Result<Vec<OsString>, IntegrationError>,
}

impl ReplaceCliInstaller {
    pub fn new(
        remove: fn() -> Vec<OsString>,
        add: fn(&McpLaunchSpec) -> Result<Vec<OsString>, IntegrationError>,
    ) -> Self {
        Self { remove, add }
    }
}

impl AgentInstaller for ReplaceCliInstaller {
    fn install(&self, executable: &Path, launch: &McpLaunchSpec) -> Result<(), IntegrationError> {
        let _ = CommandRunner::run(executable, (self.remove)());
        CommandRunner::run(executable, (self.add)(launch)?)?;
        Ok(())
    }
}

pub struct AddMcpInstaller;

impl AgentInstaller for AddMcpInstaller {
    fn install(&self, executable: &Path, launch: &McpLaunchSpec) -> Result<(), IntegrationError> {
        let payload = serde_json::json!({
            "name": "dexdec",
            "command": launch.command().to_string_lossy(),
            "args": launch.args(),
        });
        CommandRunner::run(
            executable,
            [
                OsString::from("--add-mcp"),
                OsString::from(payload.to_string()),
            ],
        )?;
        Ok(())
    }
}

struct CommandRunner;

impl CommandRunner {
    fn run(
        executable: &Path,
        arguments: impl IntoIterator<Item = OsString>,
    ) -> Result<Output, IntegrationError> {
        let output = Command::new(executable).args(arguments).output()?;
        if output.status.success() {
            return Ok(output);
        }
        let message = String::from_utf8_lossy(&output.stderr).trim().to_string();
        let message = if message.is_empty() {
            String::from_utf8_lossy(&output.stdout).trim().to_string()
        } else {
            message
        };
        Err(IntegrationError::Command {
            program: executable.display().to_string(),
            message: if message.is_empty() {
                format!("exited with {}", output.status)
            } else {
                message.chars().take(1200).collect()
            },
        })
    }
}

pub fn codex_remove() -> Vec<OsString> {
    ["mcp", "remove", "dexdec"]
        .into_iter()
        .map(OsString::from)
        .collect()
}

pub fn codex_add(launch: &McpLaunchSpec) -> Result<Vec<OsString>, IntegrationError> {
    let mut args = ["mcp", "add", "dexdec", "--"]
        .into_iter()
        .map(OsString::from)
        .collect::<Vec<_>>();
    args.push(launch.command().as_os_str().to_os_string());
    args.extend(launch.args().iter().map(OsString::from));
    Ok(args)
}

pub fn claude_remove() -> Vec<OsString> {
    ["mcp", "remove", "dexdec", "--scope", "user"]
        .into_iter()
        .map(OsString::from)
        .collect()
}

pub fn claude_add(launch: &McpLaunchSpec) -> Result<Vec<OsString>, IntegrationError> {
    let payload = serde_json::json!({
        "type": "stdio",
        "command": launch.command().to_string_lossy(),
        "args": launch.args(),
    });
    Ok(vec![
        OsString::from("mcp"),
        OsString::from("add-json"),
        OsString::from("dexdec"),
        OsString::from(payload.to_string()),
        OsString::from("--scope"),
        OsString::from("user"),
    ])
}

pub fn grok_remove() -> Vec<OsString> {
    ["mcp", "remove", "--scope", "user", "dexdec"]
        .into_iter()
        .map(OsString::from)
        .collect()
}

pub fn grok_add(launch: &McpLaunchSpec) -> Result<Vec<OsString>, IntegrationError> {
    let mut args = ["mcp", "add", "--scope", "user", "dexdec"]
        .into_iter()
        .map(OsString::from)
        .collect::<Vec<_>>();
    args.push(OsString::from("--"));
    args.push(launch.command().as_os_str().to_os_string());
    args.extend(launch.args().iter().map(OsString::from));
    Ok(args)
}

#[cfg(test)]
mod tests {
    use super::{grok_add, grok_remove};
    use crate::mcp_agents::McpLaunchSpec;
    use std::ffi::OsString;
    use std::path::PathBuf;

    #[test]
    fn grok_registration_is_user_scoped_stdio() {
        let launch = McpLaunchSpec::new(PathBuf::from(
            "/Applications/DexDec.app/Contents/MacOS/DexDec",
        ));

        assert_eq!(
            grok_remove(),
            os_args(["mcp", "remove", "--scope", "user", "dexdec"])
        );
        assert_eq!(
            grok_add(&launch).expect("build Grok registration"),
            os_args([
                "mcp",
                "add",
                "--scope",
                "user",
                "dexdec",
                "--",
                "/Applications/DexDec.app/Contents/MacOS/DexDec",
                "--mcp",
            ])
        );
    }

    fn os_args<const N: usize>(args: [&str; N]) -> Vec<OsString> {
        args.into_iter().map(OsString::from).collect()
    }
}
