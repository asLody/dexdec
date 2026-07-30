//! Stable command failures and process exit codes.

use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorKind {
    Usage,
    Input,
    NotFound,
    Ambiguous,
    Unsupported,
    Command,
}

impl ErrorKind {
    pub fn code(self) -> &'static str {
        match self {
            Self::Usage => "invalid_request",
            Self::Input => "invalid_input",
            Self::NotFound => "not_found",
            Self::Ambiguous => "ambiguous_symbol",
            Self::Unsupported => "unsupported_operation",
            Self::Command => "command_failed",
        }
    }

    pub fn exit_code(self) -> i32 {
        match self {
            Self::Usage | Self::Ambiguous | Self::Unsupported => 2,
            Self::Input => 3,
            Self::NotFound => 4,
            Self::Command => 1,
        }
    }
}

#[derive(Debug)]
pub struct CliError {
    kind: ErrorKind,
    message: String,
    hint: Option<String>,
}

impl CliError {
    pub fn new(kind: ErrorKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
            hint: None,
        }
    }

    pub fn usage(message: impl Into<String>) -> Self {
        Self::new(ErrorKind::Usage, message)
    }

    pub fn input(message: impl Into<String>) -> Self {
        Self::new(ErrorKind::Input, message)
    }

    pub fn not_found(message: impl Into<String>) -> Self {
        Self::new(ErrorKind::NotFound, message)
    }

    pub fn ambiguous(message: impl Into<String>) -> Self {
        Self::new(ErrorKind::Ambiguous, message)
    }

    pub fn unsupported(message: impl Into<String>) -> Self {
        Self::new(ErrorKind::Unsupported, message)
    }

    pub fn command(message: impl Into<String>) -> Self {
        Self::new(ErrorKind::Command, message)
    }

    pub fn with_hint(mut self, hint: impl Into<String>) -> Self {
        self.hint = Some(hint.into());
        self
    }

    pub fn kind(&self) -> ErrorKind {
        self.kind
    }

    pub fn code(&self) -> &'static str {
        self.kind.code()
    }

    pub fn exit_code(&self) -> i32 {
        self.kind.exit_code()
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn hint(&self) -> Option<&str> {
        self.hint.as_deref()
    }
}

impl Display for CliError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.message)?;
        if let Some(hint) = self.hint() {
            write!(formatter, "\nHint: {hint}")?;
        }
        Ok(())
    }
}

impl std::error::Error for CliError {}

impl From<std::io::Error> for CliError {
    fn from(error: std::io::Error) -> Self {
        Self::input(error.to_string())
    }
}

impl From<crate::DexError> for CliError {
    fn from(error: crate::DexError) -> Self {
        Self::input(error.to_string())
    }
}

impl From<crate::DecompileError> for CliError {
    fn from(error: crate::DecompileError) -> Self {
        use crate::DecompileError;
        match error {
            DecompileError::ClassNotFound(class) => {
                Self::not_found(format!("class not found: {class}"))
            }
            DecompileError::MethodNotFound {
                class,
                method,
                descriptor,
            } => Self::not_found(format!(
                "method not found: {class}->{method}{}",
                descriptor.unwrap_or_default()
            )),
            DecompileError::AmbiguousMethod {
                class,
                method,
                descriptors,
            } => Self::ambiguous(format!("method is overloaded: {class}->{method}")).with_hint(
                format!("Choose --descriptor from: {}", descriptors.join(", ")),
            ),
            DecompileError::DexError(error) => Self::input(error.to_string()),
            other => Self::command(other.to_string()),
        }
    }
}

impl From<serde_json::Error> for CliError {
    fn from(error: serde_json::Error) -> Self {
        Self::command(format!("unable to encode command output: {error}"))
    }
}

impl From<zip::result::ZipError> for CliError {
    fn from(error: zip::result::ZipError) -> Self {
        Self::input(format!("unable to read APK resources: {error}"))
    }
}

impl From<Box<dyn std::error::Error>> for CliError {
    fn from(error: Box<dyn std::error::Error>) -> Self {
        Self::command(error.to_string())
    }
}

impl From<String> for CliError {
    fn from(error: String) -> Self {
        Self::command(error)
    }
}

pub type CliResult<T> = Result<T, CliError>;

pub fn cli_err(error: impl Display) -> CliError {
    CliError::command(error.to_string())
}
