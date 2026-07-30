use dexdec_workbench::{ArchiveDto, ReferenceTargetDto, SymbolSearchResultDto};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::ui_context::UiContextSnapshot;

#[derive(Debug, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ProjectOpenParams {
    pub path: String,
}

#[derive(Debug, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ProjectParams {
    pub project_id: u64,
}

#[derive(Debug, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct SymbolSearchParams {
    pub project_id: u64,
    pub query: String,
    #[serde(default = "default_search_limit")]
    pub limit: usize,
}

#[derive(Debug, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ClassParams {
    pub project_id: u64,
    pub descriptor: String,
}

#[derive(Debug, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ClassDecompileParams {
    pub project_id: u64,
    pub descriptor: String,
    #[serde(default = "default_language")]
    pub language: String,
    #[serde(default = "default_indent")]
    pub indent_width: u8,
    #[serde(default = "default_include_nested")]
    pub include_nested: bool,
}

#[derive(Debug, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct MethodDecompileParams {
    pub project_id: u64,
    pub class: String,
    pub method: String,
    pub descriptor: Option<String>,
    #[serde(default = "default_language")]
    pub language: String,
    #[serde(default = "default_indent")]
    pub indent_width: u8,
    #[serde(default = "default_include_nested")]
    pub include_nested: bool,
}

#[derive(Debug, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ReferenceParams {
    pub project_id: u64,
    pub kind: ReferenceKind,
    pub class: String,
    pub name: Option<String>,
    pub descriptor: Option<String>,
}

#[derive(Debug, Clone, Copy, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub enum ReferenceKind {
    Class,
    Field,
    Method,
}

impl ReferenceParams {
    pub fn into_target(self) -> Result<ReferenceTargetDto, String> {
        let Self {
            kind,
            class,
            name,
            descriptor,
            ..
        } = self;
        match kind {
            ReferenceKind::Class => Ok(ReferenceTargetDto::Class {
                class_descriptor: class,
            }),
            ReferenceKind::Field => Ok(ReferenceTargetDto::Field {
                class_descriptor: class,
                name: Self::required(name, "name")?,
                descriptor: Self::required(descriptor, "descriptor")?,
            }),
            ReferenceKind::Method => Ok(ReferenceTargetDto::Method {
                class_descriptor: class,
                name: Self::required(name, "name")?,
                descriptor: Self::required(descriptor, "descriptor")?,
            }),
        }
    }

    fn required(value: Option<String>, field: &str) -> Result<String, String> {
        value
            .filter(|value| !value.is_empty())
            .ok_or_else(|| format!("{field} is required for field and method references"))
    }
}

#[derive(Debug, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ResourceReadParams {
    pub project_id: u64,
    pub path: String,
}

#[derive(Debug, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ActiveClassDecompileParams {
    pub language: Option<String>,
    #[serde(default = "default_indent")]
    pub indent_width: u8,
    #[serde(default = "default_include_nested")]
    pub include_nested: bool,
}

#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ProjectSummary {
    pub project_id: u64,
    pub path: String,
    pub name: String,
    pub class_count: usize,
    pub resource_count: usize,
    pub package_name: Option<String>,
}

impl From<ArchiveDto> for ProjectSummary {
    fn from(archive: ArchiveDto) -> Self {
        Self {
            project_id: archive.session_id,
            path: archive.path,
            name: archive.name,
            class_count: archive.class_count,
            resource_count: archive.resources.len(),
            package_name: archive.overview.and_then(|overview| overview.package_name),
        }
    }
}

#[derive(Debug, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ProjectList {
    pub projects: Vec<ProjectSummary>,
}

#[derive(Debug, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct SymbolSearchResults {
    pub results: Vec<SymbolSearchResultDto>,
}

#[derive(Debug, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ProjectCloseResult {
    pub closed: bool,
}

#[derive(Debug, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct UiContextResult {
    pub available: bool,
    pub context: Option<UiContextSnapshot>,
    pub message: Option<String>,
}

#[derive(Debug, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct UiNavigationResult {
    pub accepted: bool,
}

pub fn default_language() -> String {
    "java".to_string()
}

pub fn default_indent() -> u8 {
    4
}

pub fn default_include_nested() -> bool {
    true
}

fn default_search_limit() -> usize {
    100
}
