use std::fs;
use std::path::{Path, PathBuf};

use toml_edit::DocumentMut;

use super::{IntegrationError, McpLaunchSpec};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegistrationState {
    Missing,
    Current,
    Stale,
}

pub trait ConfigurationProbe: Send + Sync {
    fn path(&self) -> &Path;
    fn inspect(&self, launch: &McpLaunchSpec) -> Result<RegistrationState, IntegrationError>;
    fn remove(&self) -> Result<(), IntegrationError>;
}

pub struct JsonConfigurationProbe {
    path: PathBuf,
    root: &'static str,
}

impl JsonConfigurationProbe {
    pub fn new(path: PathBuf, root: &'static str) -> Self {
        Self { path, root }
    }
}

impl ConfigurationProbe for JsonConfigurationProbe {
    fn path(&self) -> &Path {
        &self.path
    }

    fn inspect(&self, launch: &McpLaunchSpec) -> Result<RegistrationState, IntegrationError> {
        if !self.path.exists() {
            return Ok(RegistrationState::Missing);
        }
        let bytes = fs::read(&self.path)?;
        let document: serde_json::Value =
            serde_json::from_slice(&bytes).map_err(|error| IntegrationError::Configuration {
                path: self.path.display().to_string(),
                message: error.to_string(),
            })?;
        let Some(server) = document
            .get(self.root)
            .and_then(|servers| servers.get("dexdec"))
        else {
            return Ok(RegistrationState::Missing);
        };
        let command = server
            .get("command")
            .and_then(serde_json::Value::as_str)
            .unwrap_or_default();
        let args = server
            .get("args")
            .and_then(serde_json::Value::as_array)
            .map(|args| {
                args.iter()
                    .filter_map(serde_json::Value::as_str)
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        Ok(if launch.matches(command, &args) {
            RegistrationState::Current
        } else {
            RegistrationState::Stale
        })
    }

    fn remove(&self) -> Result<(), IntegrationError> {
        if !self.path.exists() {
            return Ok(());
        }
        let bytes = fs::read(&self.path)?;
        let mut document: serde_json::Value =
            serde_json::from_slice(&bytes).map_err(|error| IntegrationError::Configuration {
                path: self.path.display().to_string(),
                message: error.to_string(),
            })?;
        let removed = document
            .get_mut(self.root)
            .and_then(serde_json::Value::as_object_mut)
            .and_then(|servers| servers.remove("dexdec"))
            .is_some();
        if removed {
            let mut contents = serde_json::to_vec_pretty(&document)?;
            contents.push(b'\n');
            fs::write(&self.path, contents)?;
        }
        Ok(())
    }
}

pub struct TomlConfigurationProbe {
    path: PathBuf,
}

impl TomlConfigurationProbe {
    pub fn new(path: PathBuf) -> Self {
        Self { path }
    }
}

impl ConfigurationProbe for TomlConfigurationProbe {
    fn path(&self) -> &Path {
        &self.path
    }

    fn inspect(&self, launch: &McpLaunchSpec) -> Result<RegistrationState, IntegrationError> {
        if !self.path.exists() {
            return Ok(RegistrationState::Missing);
        }
        let source = fs::read_to_string(&self.path)?;
        let document =
            source
                .parse::<DocumentMut>()
                .map_err(|error| IntegrationError::Configuration {
                    path: self.path.display().to_string(),
                    message: error.to_string(),
                })?;
        let Some(server) = document
            .get("mcp_servers")
            .and_then(|servers| servers.get("dexdec"))
        else {
            return Ok(RegistrationState::Missing);
        };
        let command = server
            .get("command")
            .and_then(toml_edit::Item::as_str)
            .unwrap_or_default();
        let args = server
            .get("args")
            .and_then(toml_edit::Item::as_array)
            .map(|args| {
                args.iter()
                    .filter_map(toml_edit::Value::as_str)
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        Ok(if launch.matches(command, &args) {
            RegistrationState::Current
        } else {
            RegistrationState::Stale
        })
    }

    fn remove(&self) -> Result<(), IntegrationError> {
        if !self.path.exists() {
            return Ok(());
        }
        let source = fs::read_to_string(&self.path)?;
        let mut document =
            source
                .parse::<DocumentMut>()
                .map_err(|error| IntegrationError::Configuration {
                    path: self.path.display().to_string(),
                    message: error.to_string(),
                })?;
        let removed = document
            .get_mut("mcp_servers")
            .and_then(toml_edit::Item::as_table_like_mut)
            .and_then(|servers| servers.remove("dexdec"))
            .is_some();
        if removed {
            fs::write(&self.path, document.to_string())?;
        }
        Ok(())
    }
}

pub struct ConfigurationBackup {
    path: PathBuf,
    contents: Option<Vec<u8>>,
}

impl ConfigurationBackup {
    pub fn capture(path: &Path) -> Result<Self, IntegrationError> {
        let contents = if path.exists() {
            Some(fs::read(path)?)
        } else {
            None
        };
        Ok(Self {
            path: path.to_path_buf(),
            contents,
        })
    }

    pub fn restore(self) -> Result<(), IntegrationError> {
        match self.contents {
            Some(contents) => {
                if let Some(parent) = self.path.parent() {
                    fs::create_dir_all(parent)?;
                }
                fs::write(self.path, contents)?;
            }
            None if self.path.exists() => fs::remove_file(self.path)?,
            None => {}
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{
        ConfigurationBackup, ConfigurationProbe, JsonConfigurationProbe, RegistrationState,
        TomlConfigurationProbe,
    };
    use crate::mcp_agents::McpLaunchSpec;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::time::{SystemTime, UNIX_EPOCH};

    struct TestDirectory(PathBuf);

    impl TestDirectory {
        fn create() -> Self {
            let nonce = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("clock")
                .as_nanos();
            let path = std::env::temp_dir().join(format!(
                "dexdec-agent-config-{}-{nonce}",
                std::process::id()
            ));
            fs::create_dir_all(&path).expect("create test directory");
            Self(path)
        }

        fn path(&self, name: &str) -> PathBuf {
            self.0.join(name)
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn launch() -> McpLaunchSpec {
        McpLaunchSpec::new(PathBuf::from(
            "/Applications/DexDec.app/Contents/MacOS/DexDec",
        ))
    }

    #[test]
    fn json_probe_distinguishes_current_and_stale_registration() {
        let directory = TestDirectory::create();
        let path = directory.path("mcp.json");
        let probe = JsonConfigurationProbe::new(path.clone(), "mcpServers");
        fs::write(
            &path,
            r#"{"mcpServers":{"dexdec":{"command":"/Applications/DexDec.app/Contents/MacOS/DexDec","args":["--mcp"]}}}"#,
        )
        .expect("write config");
        assert_eq!(
            probe.inspect(&launch()).expect("inspect config"),
            RegistrationState::Current
        );

        fs::write(
            &path,
            r#"{"mcpServers":{"dexdec":{"command":"/old/DexDec","args":["--mcp"]}}}"#,
        )
        .expect("write stale config");
        assert_eq!(
            probe.inspect(&launch()).expect("inspect stale config"),
            RegistrationState::Stale
        );
    }

    #[test]
    fn toml_probe_reads_codex_registration() {
        let directory = TestDirectory::create();
        let path = directory.path("config.toml");
        fs::write(
            &path,
            r#"[mcp_servers.dexdec]
command = "/Applications/DexDec.app/Contents/MacOS/DexDec"
args = ["--mcp"]
"#,
        )
        .expect("write config");
        let probe = TomlConfigurationProbe::new(path);
        assert_eq!(
            probe.inspect(&launch()).expect("inspect config"),
            RegistrationState::Current
        );
    }

    #[test]
    fn backup_restores_existing_content_and_removes_new_files() {
        let directory = TestDirectory::create();
        let existing = directory.path("existing.json");
        fs::write(&existing, b"before").expect("write original");
        let backup = ConfigurationBackup::capture(&existing).expect("capture backup");
        fs::write(&existing, b"after").expect("write replacement");
        backup.restore().expect("restore backup");
        assert_eq!(fs::read(&existing).expect("read restored"), b"before");

        let created = directory.path("created.json");
        let backup = ConfigurationBackup::capture(Path::new(&created)).expect("capture absence");
        fs::write(&created, b"created").expect("write created file");
        backup.restore().expect("remove created file");
        assert!(!created.exists());
    }

    #[test]
    fn removal_preserves_unrelated_json_and_toml_servers() {
        let directory = TestDirectory::create();
        let json_path = directory.path("mcp.json");
        fs::write(
            &json_path,
            r#"{"mcpServers":{"dexdec":{"command":"DexDec"},"other":{"command":"other"}},"setting":true}"#,
        )
        .expect("write JSON config");
        JsonConfigurationProbe::new(json_path.clone(), "mcpServers")
            .remove()
            .expect("remove JSON registration");
        let json: serde_json::Value =
            serde_json::from_slice(&fs::read(json_path).expect("read JSON config"))
                .expect("parse JSON config");
        assert!(json["mcpServers"].get("dexdec").is_none());
        assert_eq!(json["mcpServers"]["other"]["command"], "other");
        assert_eq!(json["setting"], true);

        let toml_path = directory.path("config.toml");
        fs::write(
            &toml_path,
            r#"theme = "dark"

[mcp_servers.dexdec]
command = "DexDec"

[mcp_servers.other]
command = "other"
"#,
        )
        .expect("write TOML config");
        TomlConfigurationProbe::new(toml_path.clone())
            .remove()
            .expect("remove TOML registration");
        let toml = fs::read_to_string(toml_path).expect("read TOML config");
        assert!(!toml.contains("mcp_servers.dexdec"));
        assert!(toml.contains("mcp_servers.other"));
        assert!(toml.contains("theme = \"dark\""));
    }
}
