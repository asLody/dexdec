mod catalog;
mod command;
mod config;

use std::path::{Path, PathBuf};

use catalog::AgentCatalog;
use command::{AgentInstaller, CommandLocator, ProgramSpec};
use config::{ConfigurationBackup, ConfigurationProbe, RegistrationState};
use directories::BaseDirs;
use serde::Serialize;

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct McpLaunchDto {
    pub command: String,
    pub args: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentIntegrationDto {
    pub id: &'static str,
    pub name: &'static str,
    pub available: bool,
    pub configured: bool,
    pub needs_update: bool,
    pub config_path: String,
    pub message: Option<String>,
}

#[derive(Debug, Clone)]
pub struct McpLaunchSpec {
    command: PathBuf,
    args: Vec<String>,
}

impl McpLaunchSpec {
    fn new(command: PathBuf) -> Self {
        Self {
            command,
            args: vec!["--mcp".to_string()],
        }
    }

    pub fn command(&self) -> &Path {
        &self.command
    }

    pub fn args(&self) -> &[String] {
        &self.args
    }

    fn matches(&self, command: &str, args: &[String]) -> bool {
        if Path::new(command) != self.command || args.first().map(String::as_str) != Some("--mcp") {
            return false;
        }
        args == self.args
    }

    fn into_dto(self) -> McpLaunchDto {
        McpLaunchDto {
            command: self.command.to_string_lossy().into_owned(),
            args: self.args,
        }
    }
}

pub struct AgentIntegrationService {
    command: PathBuf,
    locator: CommandLocator,
    agents: Vec<AgentAdapter>,
}

impl AgentIntegrationService {
    pub fn discover() -> Result<Self, IntegrationError> {
        let command = std::env::current_exe()?;
        let directories = BaseDirs::new().ok_or(IntegrationError::HomeDirectory)?;
        let locator = CommandLocator::new(directories.home_dir().to_path_buf());
        let agents = AgentCatalog::new(&directories).build();
        Ok(Self {
            command,
            locator,
            agents,
        })
    }

    pub fn launch(&self) -> McpLaunchDto {
        McpLaunchSpec::new(self.command.clone()).into_dto()
    }

    pub fn integrations(&self) -> Vec<AgentIntegrationDto> {
        let launch = McpLaunchSpec::new(self.command.clone());
        self.agents
            .iter()
            .map(|agent| agent.status(&self.locator, &launch))
            .collect()
    }

    pub fn configure(&self, agent_id: &str) -> Result<AgentIntegrationDto, IntegrationError> {
        let launch = McpLaunchSpec::new(self.command.clone());
        let agent = self
            .agents
            .iter()
            .find(|agent| agent.id == agent_id)
            .ok_or_else(|| IntegrationError::UnknownAgent(agent_id.to_string()))?;
        agent.configure(&self.locator, &launch)?;
        Ok(agent.status(&self.locator, &launch))
    }

    pub fn unconfigure(&self, agent_id: &str) -> Result<AgentIntegrationDto, IntegrationError> {
        let launch = McpLaunchSpec::new(self.command.clone());
        let agent = self
            .agents
            .iter()
            .find(|agent| agent.id == agent_id)
            .ok_or_else(|| IntegrationError::UnknownAgent(agent_id.to_string()))?;
        agent.unconfigure(&launch)?;
        Ok(agent.status(&self.locator, &launch))
    }

    pub fn configure_all(&self) -> Vec<AgentIntegrationDto> {
        let launch = McpLaunchSpec::new(self.command.clone());
        self.agents
            .iter()
            .map(|agent| {
                if self.locator.locate(&agent.program).is_none() {
                    return agent.status(&self.locator, &launch);
                }
                if matches!(
                    agent.configuration.inspect(&launch),
                    Ok(RegistrationState::Current)
                ) {
                    return agent.status(&self.locator, &launch);
                }
                match agent.configure(&self.locator, &launch) {
                    Ok(()) => agent.status(&self.locator, &launch),
                    Err(error) => {
                        agent.status_with_message(&self.locator, &launch, error.to_string())
                    }
                }
            })
            .collect()
    }
}

struct AgentAdapter {
    id: &'static str,
    name: &'static str,
    program: ProgramSpec,
    configuration: Box<dyn ConfigurationProbe>,
    installer: Box<dyn AgentInstaller>,
}

impl AgentAdapter {
    fn new(
        id: &'static str,
        name: &'static str,
        program: ProgramSpec,
        configuration: Box<dyn ConfigurationProbe>,
        installer: Box<dyn AgentInstaller>,
    ) -> Self {
        Self {
            id,
            name,
            program,
            configuration,
            installer,
        }
    }

    fn status(&self, locator: &CommandLocator, launch: &McpLaunchSpec) -> AgentIntegrationDto {
        self.status_with_optional_message(locator, launch, None)
    }

    fn status_with_message(
        &self,
        locator: &CommandLocator,
        launch: &McpLaunchSpec,
        message: String,
    ) -> AgentIntegrationDto {
        self.status_with_optional_message(locator, launch, Some(message))
    }

    fn status_with_optional_message(
        &self,
        locator: &CommandLocator,
        launch: &McpLaunchSpec,
        message: Option<String>,
    ) -> AgentIntegrationDto {
        let available = locator.locate(&self.program).is_some();
        let (state, inspection_error) = match self.configuration.inspect(launch) {
            Ok(state) => (state, None),
            Err(error) => (RegistrationState::Missing, Some(error.to_string())),
        };
        AgentIntegrationDto {
            id: self.id,
            name: self.name,
            available,
            configured: state == RegistrationState::Current,
            needs_update: state == RegistrationState::Stale,
            config_path: self.configuration.path().to_string_lossy().into_owned(),
            message: message.or(inspection_error),
        }
    }

    fn configure(
        &self,
        locator: &CommandLocator,
        launch: &McpLaunchSpec,
    ) -> Result<(), IntegrationError> {
        let executable = locator
            .locate(&self.program)
            .ok_or_else(|| IntegrationError::AgentUnavailable(self.name.to_string()))?;
        let backup = ConfigurationBackup::capture(self.configuration.path())?;
        if let Err(error) = self.installer.install(&executable, launch) {
            backup.restore()?;
            return Err(error);
        }
        match self.configuration.inspect(launch) {
            Ok(RegistrationState::Current) => Ok(()),
            Ok(_) => {
                backup.restore()?;
                Err(IntegrationError::RegistrationRejected {
                    agent: self.name.to_string(),
                    path: self.configuration.path().display().to_string(),
                })
            }
            Err(error) => {
                backup.restore()?;
                Err(error)
            }
        }
    }

    fn unconfigure(&self, launch: &McpLaunchSpec) -> Result<(), IntegrationError> {
        let backup = ConfigurationBackup::capture(self.configuration.path())?;
        if let Err(error) = self.configuration.remove() {
            backup.restore()?;
            return Err(error);
        }
        match self.configuration.inspect(launch) {
            Ok(RegistrationState::Missing) => Ok(()),
            Ok(_) => {
                backup.restore()?;
                Err(IntegrationError::RemovalRejected {
                    agent: self.name.to_string(),
                    path: self.configuration.path().display().to_string(),
                })
            }
            Err(error) => {
                backup.restore()?;
                Err(error)
            }
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum IntegrationError {
    #[error("unable to locate the user home directory")]
    HomeDirectory,
    #[error("unknown agent integration: {0}")]
    UnknownAgent(String),
    #[error("{0} is not installed or its command could not be found")]
    AgentUnavailable(String),
    #[error("unable to parse {path}: {message}")]
    Configuration { path: String, message: String },
    #[error("{program} failed: {message}")]
    Command { program: String, message: String },
    #[error("{agent} did not write a valid DexDec MCP registration to {path}")]
    RegistrationRejected { agent: String, path: String },
    #[error("unable to remove the {agent} DexDec MCP registration from {path}")]
    RemovalRejected { agent: String, path: String },
    #[error(transparent)]
    Json(#[from] serde_json::Error),
    #[error(transparent)]
    Io(#[from] std::io::Error),
}

#[cfg(test)]
mod tests {
    use super::McpLaunchSpec;
    use std::path::PathBuf;

    #[test]
    fn launch_registration_requires_the_exact_command_and_arguments() {
        let launch = McpLaunchSpec::new(PathBuf::from(
            "/Applications/DexDec.app/Contents/MacOS/DexDec",
        ));

        assert!(launch.matches(
            "/Applications/DexDec.app/Contents/MacOS/DexDec",
            &["--mcp".to_string()]
        ));
        assert!(!launch.matches(
            "/Applications/DexDec.app/Contents/MacOS/DexDec",
            &[
                "--mcp".to_string(),
                "--allow-root".to_string(),
                "/tmp/project".to_string()
            ]
        ));
    }
}
