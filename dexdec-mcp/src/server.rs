use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use dexdec_workbench::{
    DecompileOptionsDto, MethodRequestDto, ResourceDocumentDto, ServiceError, Workbench,
};
use rmcp::service::RequestContext;
use rmcp::{
    handler::server::{router::tool::ToolRouter, wrapper::Parameters},
    model::*,
    service::ServiceExt,
    tool, tool_handler, tool_router, ErrorData, Json, RoleServer, ServerHandler,
};
use url::Url;

use crate::access::{AccessPolicy, McpOptions};
use crate::model::{
    ActiveClassDecompileParams, ClassDecompileParams, ClassParams, MethodDecompileParams,
    ProjectCloseResult, ProjectList, ProjectOpenParams, ProjectParams, ProjectSummary,
    ReferenceParams, ResourceReadParams, SymbolSearchParams, SymbolSearchResults, UiContextResult,
    UiNavigationResult,
};
use crate::ui_context::{
    UiContextClient, UiContextSnapshot, UiDocumentContext, UiNavigationRequest, UiProjectContext,
};

pub struct McpRuntime {
    options: McpOptions,
}

impl McpRuntime {
    pub fn new(options: McpOptions) -> Self {
        Self { options }
    }

    pub async fn serve_stdio(self) -> Result<(), Box<dyn std::error::Error>> {
        let policy = AccessPolicy::from_options(self.options)?;
        let server = DexDecMcpServer::new(
            Arc::new(Workbench::default()),
            policy,
            UiContextClient::discover()?,
        );
        server
            .serve(rmcp::transport::stdio())
            .await?
            .waiting()
            .await?;
        Ok(())
    }

    pub fn serve_embedded_stdio() -> Result<(), Box<dyn std::error::Error>> {
        use clap::Parser;

        let mut args = std::env::args_os();
        let program = args.next().unwrap_or_else(|| "DexDec".into());
        let _mode = args.next();
        let options = McpOptions::parse_from(std::iter::once(program).chain(args));
        tokio::runtime::Builder::new_multi_thread()
            .enable_all()
            .build()?
            .block_on(Self::new(options).serve_stdio())
    }
}

#[derive(Clone)]
struct DexDecMcpServer {
    workbench: Arc<Workbench>,
    policy: AccessPolicy,
    ui_context: UiContextClient,
    requests: Arc<AtomicU64>,
    tool_router: ToolRouter<Self>,
}

#[tool_router(router = tool_router)]
impl DexDecMcpServer {
    fn new(workbench: Arc<Workbench>, policy: AccessPolicy, ui_context: UiContextClient) -> Self {
        Self {
            workbench,
            policy,
            ui_context,
            requests: Arc::new(AtomicU64::new(1)),
            tool_router: Self::tool_router(),
        }
    }

    #[tool(
        name = "get_ui_context",
        description = "Return the live DexDec desktop context: current APK or DEX, active class or resource, selected member, caret, and open class tabs. Returns available=false when the GUI is not running."
    )]
    async fn get_ui_context(&self) -> Result<Json<UiContextResult>, ErrorData> {
        let client = self.ui_context.clone();
        let result = tokio::task::spawn_blocking(move || client.context())
            .await
            .map_err(|error| ErrorData::internal_error(error.to_string(), None))?;
        Ok(Json(match result {
            Ok(context) => UiContextResult {
                available: true,
                context: Some(context),
                message: None,
            },
            Err(error) => UiContextResult {
                available: false,
                context: None,
                message: Some(error.to_string()),
            },
        }))
    }

    #[tool(
        name = "open_active_project",
        description = "Open or reuse the APK or DEX currently displayed by the DexDec desktop UI and return its MCP project ID. The authenticated UI-selected file is trusted even when it is outside the MCP process working directory."
    )]
    async fn open_active_project(&self) -> Result<Json<ProjectSummary>, ErrorData> {
        let context = self.live_ui_context().await?;
        let project = context.project.ok_or_else(|| {
            ErrorData::resource_not_found("the DexDec UI has no open project", None)
        })?;
        let workbench = Arc::clone(&self.workbench);
        Self::run(move || Self::ensure_project(&workbench, project)).await
    }

    #[tool(
        name = "decompile_active_class",
        description = "Decompile the class currently focused in the DexDec desktop UI. Opens or reuses the UI project automatically and defaults to the language shown in the editor."
    )]
    async fn decompile_active_class(
        &self,
        context: RequestContext<RoleServer>,
        Parameters(params): Parameters<ActiveClassDecompileParams>,
    ) -> Result<Json<dexdec_workbench::SourceDocumentDto>, ErrorData> {
        let ui = self.live_ui_context().await?;
        let project = ui.project.ok_or_else(|| {
            ErrorData::resource_not_found("the DexDec UI has no open project", None)
        })?;
        let (descriptor, ui_language) = match ui.active_document {
            Some(UiDocumentContext::Class {
                descriptor,
                language,
                ..
            }) => (descriptor, language),
            Some(UiDocumentContext::Resource { .. }) => {
                return Err(ErrorData::invalid_params(
                    "the active DexDec UI document is a resource, not a class",
                    None,
                ));
            }
            None => {
                return Err(ErrorData::resource_not_found(
                    "the DexDec UI has no active document",
                    None,
                ));
            }
        };
        let workbench = Arc::clone(&self.workbench);
        let project = Self::run(move || Self::ensure_project(&workbench, project))
            .await?
            .0;
        let language = params.language.unwrap_or(ui_language);
        let workbench = Arc::clone(&self.workbench);
        self.run_request(project.project_id, context, move |request_id| {
            workbench.decompile_class(
                project.project_id,
                request_id,
                descriptor,
                language,
                DecompileOptionsDto {
                    indent_width: params.indent_width,
                    include_nested: params.include_nested,
                },
            )
        })
        .await
    }

    #[tool(
        name = "reveal_in_ui",
        description = "Open and focus an exact class, member, source position, or archive resource in the running DexDec desktop UI. Class and member identities must use canonical DEX descriptors."
    )]
    async fn reveal_in_ui(
        &self,
        Parameters(request): Parameters<UiNavigationRequest>,
    ) -> Result<Json<UiNavigationResult>, ErrorData> {
        let client = self.ui_context.clone();
        tokio::task::spawn_blocking(move || client.navigate(request))
            .await
            .map_err(|error| ErrorData::internal_error(error.to_string(), None))?
            .map_err(Self::ui_error)?;
        Ok(Json(UiNavigationResult { accepted: true }))
    }

    #[tool(
        name = "open_project",
        description = "Open an APK or DEX file and return a project ID for all later calls. The path must be inside an allowed root."
    )]
    async fn open_project(
        &self,
        Parameters(params): Parameters<ProjectOpenParams>,
    ) -> Result<Json<ProjectSummary>, ErrorData> {
        let path = self
            .policy
            .authorize_file(PathBuf::from(params.path).as_path())
            .map_err(Self::invalid_params)?;
        let workbench = Arc::clone(&self.workbench);
        Self::run(move || workbench.open(path).map(ProjectSummary::from)).await
    }

    #[tool(
        name = "list_projects",
        description = "List APK or DEX projects currently open in this MCP session."
    )]
    async fn list_projects(&self) -> Result<Json<ProjectList>, ErrorData> {
        let workbench = Arc::clone(&self.workbench);
        Self::run(move || {
            workbench.projects().map(|projects| ProjectList {
                projects: projects.into_iter().map(ProjectSummary::from).collect(),
            })
        })
        .await
    }

    #[tool(
        name = "close_project",
        description = "Close an MCP project and release its decompiler and archive resources."
    )]
    async fn close_project(
        &self,
        Parameters(params): Parameters<ProjectParams>,
    ) -> Result<Json<ProjectCloseResult>, ErrorData> {
        let workbench = Arc::clone(&self.workbench);
        Self::run(move || {
            workbench.close(params.project_id)?;
            Ok(ProjectCloseResult { closed: true })
        })
        .await
    }

    #[tool(
        name = "search_symbols",
        description = "Search class, field, method, and archive-resource names in an open project. Use this before decompiling when the exact DEX descriptor is unknown."
    )]
    async fn search_symbols(
        &self,
        Parameters(params): Parameters<SymbolSearchParams>,
    ) -> Result<Json<SymbolSearchResults>, ErrorData> {
        let workbench = Arc::clone(&self.workbench);
        Self::run(move || {
            workbench
                .search_symbols(params.project_id, &params.query, params.limit.clamp(1, 500))
                .map(|results| SymbolSearchResults { results })
        })
        .await
    }

    #[tool(
        name = "inspect_class",
        description = "Return a class outline with hierarchy, fields, methods, and exact DEX descriptors without decompiling method bodies."
    )]
    async fn inspect_class(
        &self,
        Parameters(params): Parameters<ClassParams>,
    ) -> Result<Json<dexdec_workbench::ClassOutlineDto>, ErrorData> {
        let workbench = Arc::clone(&self.workbench);
        Self::run(move || workbench.inspect_class(params.project_id, params.descriptor)).await
    }

    #[tool(
        name = "decompile_class",
        description = "Decompile one class on demand as Java or Kotlin. This does not decompile the whole archive."
    )]
    async fn decompile_class(
        &self,
        context: RequestContext<RoleServer>,
        Parameters(params): Parameters<ClassDecompileParams>,
    ) -> Result<Json<dexdec_workbench::SourceDocumentDto>, ErrorData> {
        let workbench = Arc::clone(&self.workbench);
        self.run_request(params.project_id, context, move |request_id| {
            workbench.decompile_class(
                params.project_id,
                request_id,
                params.descriptor,
                params.language,
                DecompileOptionsDto {
                    indent_width: params.indent_width,
                    include_nested: params.include_nested,
                },
            )
        })
        .await
    }

    #[tool(
        name = "decompile_method",
        description = "Decompile one method on demand. Pass the method descriptor to select an overload exactly."
    )]
    async fn decompile_method(
        &self,
        context: RequestContext<RoleServer>,
        Parameters(params): Parameters<MethodDecompileParams>,
    ) -> Result<Json<dexdec_workbench::MethodDocumentDto>, ErrorData> {
        let workbench = Arc::clone(&self.workbench);
        self.run_request(params.project_id, context, move |request_id| {
            workbench.decompile_method(
                params.project_id,
                request_id,
                MethodRequestDto {
                    class: params.class,
                    method: params.method,
                    descriptor: params.descriptor,
                },
                params.language,
                DecompileOptionsDto {
                    indent_width: params.indent_width,
                    include_nested: params.include_nested,
                },
            )
        })
        .await
    }

    #[tool(
        name = "find_references",
        description = "Find exact DEX references to a class, field, or method. Field and method targets require both name and descriptor."
    )]
    async fn find_references(
        &self,
        context: RequestContext<RoleServer>,
        Parameters(params): Parameters<ReferenceParams>,
    ) -> Result<Json<dexdec_workbench::ReferenceResultsDto>, ErrorData> {
        let project_id = params.project_id;
        let target = params.into_target().map_err(Self::invalid_params)?;
        let workbench = Arc::clone(&self.workbench);
        self.run_request(project_id, context, move |request_id| {
            workbench.find_references(project_id, request_id, target)
        })
        .await
    }

    #[tool(
        name = "read_archive_resource",
        description = "Read and decode one non-DEX file from an APK, such as AndroidManifest.xml, a layout, AIDL, JSON, or an image."
    )]
    async fn read_archive_resource(
        &self,
        Parameters(params): Parameters<ResourceReadParams>,
    ) -> Result<Json<ResourceDocumentDto>, ErrorData> {
        let workbench = Arc::clone(&self.workbench);
        Self::run(move || workbench.read_resource(params.project_id, &params.path)).await
    }

    fn next_request_id(&self) -> u64 {
        self.requests.fetch_add(1, Ordering::Relaxed)
    }

    async fn live_ui_context(&self) -> Result<UiContextSnapshot, ErrorData> {
        let client = self.ui_context.clone();
        tokio::task::spawn_blocking(move || client.context())
            .await
            .map_err(|error| ErrorData::internal_error(error.to_string(), None))?
            .map_err(Self::ui_error)
    }

    fn ensure_project(
        workbench: &Workbench,
        project: UiProjectContext,
    ) -> Result<ProjectSummary, ServiceError> {
        if let Some(open) = workbench
            .projects()?
            .into_iter()
            .find(|open| open.path == project.path)
        {
            return Ok(ProjectSummary::from(open));
        }
        workbench
            .open(PathBuf::from(project.path))
            .map(ProjectSummary::from)
    }

    fn ui_error(error: impl ToString) -> ErrorData {
        ErrorData::resource_not_found(error.to_string(), None)
    }

    async fn run_request<T, F>(
        &self,
        project_id: u64,
        context: RequestContext<RoleServer>,
        operation: F,
    ) -> Result<Json<T>, ErrorData>
    where
        T: Send + 'static,
        F: FnOnce(u64) -> Result<T, ServiceError> + Send + 'static,
    {
        let request_id = self.next_request_id();
        self.workbench
            .begin_request(project_id, request_id)
            .map_err(Self::service_error)?;
        let cancellation = context.ct;
        let workbench = Arc::clone(&self.workbench);
        let forwarding = tokio::spawn(async move {
            cancellation.cancelled().await;
            workbench.cancel_request(project_id, request_id);
        });
        let result = Self::run(move || operation(request_id)).await;
        forwarding.abort();
        result
    }

    async fn run<T, F>(operation: F) -> Result<Json<T>, ErrorData>
    where
        T: Send + 'static,
        F: FnOnce() -> Result<T, ServiceError> + Send + 'static,
    {
        tokio::task::spawn_blocking(operation)
            .await
            .map_err(|error| ErrorData::internal_error(error.to_string(), None))?
            .map(Json)
            .map_err(Self::service_error)
    }

    fn invalid_params(message: impl Into<String>) -> ErrorData {
        ErrorData::invalid_params(message.into(), None)
    }

    fn service_error(error: ServiceError) -> ErrorData {
        match error {
            ServiceError::StatePoisoned => ErrorData::internal_error(error.to_string(), None),
            ServiceError::SessionExpired => ErrorData::resource_not_found(error.to_string(), None),
            _ => Self::invalid_params(error.to_string()),
        }
    }

    fn resource_error(error: ServiceError) -> ErrorData {
        match error {
            ServiceError::StatePoisoned => ErrorData::internal_error(error.to_string(), None),
            _ => ErrorData::resource_not_found(error.to_string(), None),
        }
    }

    async fn read_project_resource(
        &self,
        resource: DexDecResource,
        uri: String,
        context: RequestContext<RoleServer>,
    ) -> Result<ReadResourceResult, ErrorData> {
        match resource {
            DexDecResource::Summary { project_id } => {
                let workbench = Arc::clone(&self.workbench);
                let Json(project) = Self::run(move || workbench.project(project_id)).await?;
                let text = serde_json::to_string_pretty(&ProjectSummary::from(project))
                    .map_err(|error| ErrorData::internal_error(error.to_string(), None))?;
                Ok(ReadResourceResult::new(vec![ResourceContents::text(
                    text, uri,
                )
                .with_mime_type("application/json")]))
            }
            DexDecResource::ClassSource {
                project_id,
                descriptor,
                language,
            } => {
                let workbench = Arc::clone(&self.workbench);
                let Json(document) = self
                    .run_request(project_id, context, move |request_id| {
                        workbench.decompile_class(
                            project_id,
                            request_id,
                            descriptor,
                            language,
                            DecompileOptionsDto {
                                indent_width: 4,
                                include_nested: true,
                            },
                        )
                    })
                    .await?;
                let mime = if document.language == "kotlin" {
                    "text/x-kotlin"
                } else {
                    "text/x-java"
                };
                Ok(ReadResourceResult::new(vec![ResourceContents::text(
                    document.source,
                    uri,
                )
                .with_mime_type(mime)]))
            }
            DexDecResource::ArchiveResource { project_id, path } => {
                let workbench = Arc::clone(&self.workbench);
                let document =
                    tokio::task::spawn_blocking(move || workbench.read_resource(project_id, &path))
                        .await
                        .map_err(|error| ErrorData::internal_error(error.to_string(), None))?
                        .map_err(Self::resource_error)?;
                Ok(ReadResourceResult::new(vec![Self::resource_contents(
                    document, uri,
                )?]))
            }
        }
    }

    fn resource_contents(
        document: ResourceDocumentDto,
        uri: String,
    ) -> Result<ResourceContents, ErrorData> {
        if let Some(text) = document.text {
            return Ok(ResourceContents::text(text, uri).with_mime_type(
                document
                    .mime_type
                    .unwrap_or_else(|| "text/plain".to_string()),
            ));
        }
        if let Some(data_url) = document.data_url {
            let (_, encoded) = data_url.split_once(',').ok_or_else(|| {
                ErrorData::internal_error("archive resource has an invalid data URL", None)
            })?;
            return Ok(ResourceContents::blob(encoded, uri).with_mime_type(
                document
                    .mime_type
                    .unwrap_or_else(|| "application/octet-stream".to_string()),
            ));
        }
        let description = document
            .message
            .unwrap_or_else(|| "This binary resource is not decoded by DexDec.".to_string());
        Ok(ResourceContents::text(description, uri).with_mime_type("text/plain"))
    }
}

#[tool_handler(router = self.tool_router)]
impl ServerHandler for DexDecMcpServer {
    fn get_info(&self) -> ServerInfo {
        ServerInfo::new(
            ServerCapabilities::builder()
                .enable_tools()
                .enable_resources()
                .build(),
        )
        .with_server_info(
            Implementation::new("dexdec-mcp", env!("CARGO_PKG_VERSION"))
                .with_title("DexDec")
                .with_description("Fast semantic decompilation for Android bytecode"),
        )
        .with_instructions(
            "When the user refers to the current project, class, method, editor, or selection, call get_ui_context first. Use open_active_project or decompile_active_class to work from the desktop selection without asking for paths or descriptors. Use reveal_in_ui to show relevant findings in DexDec. Otherwise open an APK or DEX with open_project, then search, inspect, and decompile only what is needed. Project IDs remain scoped to this MCP process.",
        )
    }

    async fn list_resources(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: rmcp::service::RequestContext<rmcp::RoleServer>,
    ) -> Result<ListResourcesResult, ErrorData> {
        let workbench = Arc::clone(&self.workbench);
        let Json(projects) = Self::run(move || workbench.projects()).await?;
        Ok(ListResourcesResult::with_all_items(
            projects
                .into_iter()
                .map(|project| {
                    Resource::new(
                        DexDecResource::summary_uri(project.session_id),
                        format!("project-{}-summary", project.session_id),
                    )
                    .with_title(format!("{} summary", project.name))
                    .with_description("Open DexDec project metadata")
                    .with_mime_type("application/json")
                })
                .collect(),
        ))
    }

    async fn list_resource_templates(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: rmcp::service::RequestContext<rmcp::RoleServer>,
    ) -> Result<ListResourceTemplatesResult, ErrorData> {
        Ok(ListResourceTemplatesResult::with_all_items(vec![
            ResourceTemplate::new(
                "dexdec://project/{projectId}/class-source{?descriptor,language}",
                "class-source",
            )
            .with_title("Decompiled class source")
            .with_description("Java or Kotlin source generated on demand for one DEX class"),
            ResourceTemplate::new(
                "dexdec://project/{projectId}/archive-resource{?path}",
                "archive-resource",
            )
            .with_title("APK archive resource")
            .with_description("Decoded text, XML, or image content from an open APK"),
        ]))
    }

    async fn read_resource(
        &self,
        request: ReadResourceRequestParams,
        context: RequestContext<RoleServer>,
    ) -> Result<ReadResourceResult, ErrorData> {
        let resource = DexDecResource::parse(&request.uri)?;
        self.read_project_resource(resource, request.uri, context)
            .await
    }
}

enum DexDecResource {
    Summary {
        project_id: u64,
    },
    ClassSource {
        project_id: u64,
        descriptor: String,
        language: String,
    },
    ArchiveResource {
        project_id: u64,
        path: String,
    },
}

impl DexDecResource {
    fn parse(uri: &str) -> Result<Self, ErrorData> {
        let url = Url::parse(uri).map_err(|error| {
            ErrorData::resource_not_found(format!("invalid DexDec resource URI: {error}"), None)
        })?;
        if url.scheme() != "dexdec" || url.host_str() != Some("project") {
            return Err(ErrorData::resource_not_found(
                "resource URI must start with dexdec://project/",
                None,
            ));
        }
        let segments = url.path_segments().map_or_else(Vec::new, Iterator::collect);
        if segments.len() != 2 {
            return Err(ErrorData::resource_not_found(
                "resource URI must contain a project ID and resource kind",
                None,
            ));
        }
        let project_id = segments[0].parse::<u64>().map_err(|_| {
            ErrorData::resource_not_found("resource URI contains an invalid project ID", None)
        })?;
        let query = url
            .query_pairs()
            .collect::<std::collections::HashMap<_, _>>();
        match segments[1] {
            "summary" => Ok(Self::Summary { project_id }),
            "class-source" => Ok(Self::ClassSource {
                project_id,
                descriptor: Self::required_query(&query, "descriptor")?,
                language: query
                    .get("language")
                    .map_or_else(|| "java".to_string(), |value| value.to_string()),
            }),
            "archive-resource" => Ok(Self::ArchiveResource {
                project_id,
                path: Self::required_query(&query, "path")?,
            }),
            _ => Err(ErrorData::resource_not_found(
                "unknown DexDec resource kind",
                None,
            )),
        }
    }

    fn required_query(
        query: &std::collections::HashMap<std::borrow::Cow<'_, str>, std::borrow::Cow<'_, str>>,
        name: &str,
    ) -> Result<String, ErrorData> {
        query
            .get(name)
            .filter(|value| !value.is_empty())
            .map(ToString::to_string)
            .ok_or_else(|| {
                ErrorData::resource_not_found(
                    format!("resource URI is missing the {name} query parameter"),
                    None,
                )
            })
    }

    fn summary_uri(project_id: u64) -> String {
        format!("dexdec://project/{project_id}/summary")
    }
}

#[cfg(test)]
mod tests {
    use super::DexDecResource;

    #[test]
    fn parses_encoded_class_source_uri() {
        let resource = DexDecResource::parse(
            "dexdec://project/7/class-source?descriptor=Lcom%2Fexample%2FMain%3B&language=kotlin",
        )
        .expect("valid URI");
        assert!(matches!(
            resource,
            DexDecResource::ClassSource {
                project_id: 7,
                descriptor,
                language
            } if descriptor == "Lcom/example/Main;" && language == "kotlin"
        ));
    }

    #[test]
    fn rejects_non_dexdec_resource_uri() {
        assert!(DexDecResource::parse("file:///tmp/classes.dex").is_err());
    }
}
