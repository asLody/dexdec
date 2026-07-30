mod mcp_agents;
#[cfg(not(any(target_os = "android", target_os = "ios")))]
mod menu;
mod project;
#[cfg(not(any(target_os = "android", target_os = "ios")))]
mod shutdown;

use std::path::PathBuf;
use std::sync::Arc;

use dexdec_mcp::{UiContextBridge, UiContextSnapshot};
use dexdec_workbench::{
    ArchiveDto, ClassOutlineDto, CodeSearchEventDto, CodeSearchObserver, CodeSearchRequestDto,
    CodeSearchSummaryDto, DecompileOptionsDto, MethodDocumentDto, MethodRequestDto,
    ReferenceResultsDto, ReferenceTargetDto, ResourceDocumentDto, SourceDocumentDto,
    SymbolSearchResultDto, Workbench,
};
use mcp_agents::{AgentIntegrationDto, AgentIntegrationService, McpLaunchDto};
use project::{DexDb, ProjectSnapshotDto};
use tauri::{ipc::Channel, AppHandle, Emitter, Manager, State};

const UI_NAVIGATION_EVENT: &str = "dexdec://ui-navigation";

#[tauri::command]
async fn open_archive(
    path: String,
    service: State<'_, Arc<Workbench>>,
) -> Result<ArchiveDto, String> {
    let service = Arc::clone(service.inner());
    tauri::async_runtime::spawn_blocking(move || service.open(PathBuf::from(path)))
        .await
        .map_err(|error| error.to_string())?
        .map_err(|error| error.to_string())
}

#[tauri::command]
async fn inspect_class(
    session_id: u64,
    descriptor: String,
    service: State<'_, Arc<Workbench>>,
) -> Result<ClassOutlineDto, String> {
    let service = Arc::clone(service.inner());
    tauri::async_runtime::spawn_blocking(move || service.inspect_class(session_id, descriptor))
        .await
        .map_err(|error| error.to_string())?
        .map_err(|error| error.to_string())
}

#[tauri::command]
async fn decompile_class(
    session_id: u64,
    request_id: u64,
    descriptor: String,
    language: String,
    options: DecompileOptionsDto,
    service: State<'_, Arc<Workbench>>,
) -> Result<SourceDocumentDto, String> {
    service
        .begin_request(session_id, request_id)
        .map_err(|error| error.to_string())?;
    let service = Arc::clone(service.inner());
    tauri::async_runtime::spawn_blocking(move || {
        service.decompile_class(session_id, request_id, descriptor, language, options)
    })
    .await
    .map_err(|error| error.to_string())?
    .map_err(|error| error.to_string())
}

#[tauri::command]
async fn decompile_method(
    session_id: u64,
    request_id: u64,
    request: MethodRequestDto,
    language: String,
    options: DecompileOptionsDto,
    service: State<'_, Arc<Workbench>>,
) -> Result<MethodDocumentDto, String> {
    service
        .begin_request(session_id, request_id)
        .map_err(|error| error.to_string())?;
    let service = Arc::clone(service.inner());
    tauri::async_runtime::spawn_blocking(move || {
        service.decompile_method(session_id, request_id, request, language, options)
    })
    .await
    .map_err(|error| error.to_string())?
    .map_err(|error| error.to_string())
}

#[tauri::command]
fn cancel_decompile_request(session_id: u64, request_id: u64, service: State<'_, Arc<Workbench>>) {
    service.cancel_request(session_id, request_id);
}

#[tauri::command]
async fn read_resource(
    session_id: u64,
    path: String,
    service: State<'_, Arc<Workbench>>,
) -> Result<ResourceDocumentDto, String> {
    let service = Arc::clone(service.inner());
    tauri::async_runtime::spawn_blocking(move || service.read_resource(session_id, &path))
        .await
        .map_err(|error| error.to_string())?
        .map_err(|error| error.to_string())
}

#[tauri::command]
async fn find_references(
    session_id: u64,
    request_id: u64,
    target: ReferenceTargetDto,
    service: State<'_, Arc<Workbench>>,
) -> Result<ReferenceResultsDto, String> {
    service
        .begin_request(session_id, request_id)
        .map_err(|error| error.to_string())?;
    let service = Arc::clone(service.inner());
    tauri::async_runtime::spawn_blocking(move || {
        service.find_references(session_id, request_id, target)
    })
    .await
    .map_err(|error| error.to_string())?
    .map_err(|error| error.to_string())
}

#[tauri::command]
async fn search_symbols(
    session_id: u64,
    query: String,
    limit: usize,
    service: State<'_, Arc<Workbench>>,
) -> Result<Vec<SymbolSearchResultDto>, String> {
    let service = Arc::clone(service.inner());
    tauri::async_runtime::spawn_blocking(move || service.search_symbols(session_id, &query, limit))
        .await
        .map_err(|error| error.to_string())?
        .map_err(|error| error.to_string())
}

struct ChannelCodeSearchObserver(Channel<CodeSearchEventDto>);

impl CodeSearchObserver for ChannelCodeSearchObserver {
    fn emit(&mut self, event: CodeSearchEventDto) -> bool {
        self.0.send(event).is_ok()
    }
}

#[tauri::command]
async fn search_code(
    session_id: u64,
    request_id: u64,
    search: CodeSearchRequestDto,
    language: String,
    options: DecompileOptionsDto,
    on_event: Channel<CodeSearchEventDto>,
    service: State<'_, Arc<Workbench>>,
) -> Result<CodeSearchSummaryDto, String> {
    service
        .begin_code_search(session_id, request_id)
        .map_err(|error| error.to_string())?;
    let service = Arc::clone(service.inner());
    tauri::async_runtime::spawn_blocking(move || {
        let mut observer = ChannelCodeSearchObserver(on_event);
        service.search_code(
            session_id,
            request_id,
            search,
            language,
            options,
            &mut observer,
        )
    })
    .await
    .map_err(|error| error.to_string())?
    .map_err(|error| error.to_string())
}

#[tauri::command]
fn cancel_code_search(session_id: u64, request_id: u64, service: State<'_, Arc<Workbench>>) {
    service.cancel_code_search(session_id, request_id);
}

#[tauri::command]
async fn close_archive(session_id: u64, service: State<'_, Arc<Workbench>>) -> Result<(), String> {
    let service = Arc::clone(service.inner());
    tauri::async_runtime::spawn_blocking(move || service.close(session_id))
        .await
        .map_err(|error| error.to_string())?
        .map_err(|error| error.to_string())
}

#[tauri::command]
async fn load_project(path: String) -> Result<ProjectSnapshotDto, String> {
    tauri::async_runtime::spawn_blocking(move || DexDb::load(PathBuf::from(path).as_path()))
        .await
        .map_err(|error| error.to_string())?
        .map_err(|error| error.to_string())
}

#[tauri::command]
async fn save_project(path: String, snapshot: ProjectSnapshotDto) -> Result<(), String> {
    tauri::async_runtime::spawn_blocking(move || {
        DexDb::save(PathBuf::from(path).as_path(), &snapshot)
    })
    .await
    .map_err(|error| error.to_string())?
    .map_err(|error| error.to_string())
}

#[tauri::command]
fn mcp_configuration(service: State<'_, Arc<AgentIntegrationService>>) -> McpLaunchDto {
    service.launch()
}

#[tauri::command]
async fn mcp_agent_integrations(
    service: State<'_, Arc<AgentIntegrationService>>,
) -> Result<Vec<AgentIntegrationDto>, String> {
    let service = Arc::clone(service.inner());
    tauri::async_runtime::spawn_blocking(move || service.integrations())
        .await
        .map_err(|error| error.to_string())
}

#[tauri::command]
async fn configure_mcp_agent(
    agent_id: String,
    service: State<'_, Arc<AgentIntegrationService>>,
) -> Result<AgentIntegrationDto, String> {
    let service = Arc::clone(service.inner());
    tauri::async_runtime::spawn_blocking(move || service.configure(&agent_id))
        .await
        .map_err(|error| error.to_string())?
        .map_err(|error| error.to_string())
}

#[tauri::command]
async fn unconfigure_mcp_agent(
    agent_id: String,
    service: State<'_, Arc<AgentIntegrationService>>,
) -> Result<AgentIntegrationDto, String> {
    let service = Arc::clone(service.inner());
    tauri::async_runtime::spawn_blocking(move || service.unconfigure(&agent_id))
        .await
        .map_err(|error| error.to_string())?
        .map_err(|error| error.to_string())
}

#[tauri::command]
async fn configure_all_mcp_agents(
    service: State<'_, Arc<AgentIntegrationService>>,
) -> Result<Vec<AgentIntegrationDto>, String> {
    let service = Arc::clone(service.inner());
    tauri::async_runtime::spawn_blocking(move || service.configure_all())
        .await
        .map_err(|error| error.to_string())
}

#[tauri::command]
fn publish_ui_context(snapshot: UiContextSnapshot, bridge: State<'_, Arc<UiContextBridge>>) {
    bridge.publish(snapshot);
}

#[cfg(not(any(target_os = "android", target_os = "ios")))]
#[tauri::command]
fn cancel_exit(shutdown: State<'_, shutdown::ShutdownController>) {
    shutdown.cancel();
}

#[cfg(not(any(target_os = "android", target_os = "ios")))]
#[tauri::command]
fn confirm_exit(app: AppHandle, shutdown: State<'_, shutdown::ShutdownController>) {
    shutdown.confirm(&app);
}

#[cfg(not(any(target_os = "android", target_os = "ios")))]
#[tauri::command]
fn set_project_open(app: AppHandle, open: bool) -> Result<(), String> {
    menu::DesktopMenu::set_project_open(&app, open).map_err(|error| error.to_string())
}

#[cfg(not(any(target_os = "android", target_os = "ios")))]
#[tauri::command]
fn set_recent_projects(app: AppHandle, labels: Vec<String>) -> Result<(), String> {
    menu::DesktopMenu::set_recent_projects(&app, labels).map_err(|error| error.to_string())
}

#[cfg_attr(mobile, tauri::mobile_entry_point)]
pub fn run() {
    let agent_integrations =
        AgentIntegrationService::discover().expect("failed to initialize MCP agent integrations");
    let mut builder = tauri::Builder::default()
        .plugin(tauri_plugin_dialog::init())
        .manage(Arc::new(Workbench::default()))
        .manage(Arc::new(agent_integrations))
        .setup(|app| {
            let handle = app.handle().clone();
            let bridge = UiContextBridge::start(move |request| {
                handle
                    .emit(UI_NAVIGATION_EVENT, request)
                    .map_err(|error| error.to_string())
            })?;
            app.manage(Arc::new(bridge));
            Ok(())
        });

    #[cfg(not(any(target_os = "android", target_os = "ios")))]
    {
        builder = builder
            .manage(shutdown::ShutdownController::default())
            .menu(menu::DesktopMenu::build)
            .on_menu_event(menu::DesktopMenu::handle)
            .on_window_event(shutdown::ShutdownController::handle_window_event);
    }

    let app = builder
        .invoke_handler(tauri::generate_handler![
            open_archive,
            close_archive,
            inspect_class,
            decompile_class,
            decompile_method,
            cancel_decompile_request,
            read_resource,
            find_references,
            search_symbols,
            search_code,
            cancel_code_search,
            load_project,
            save_project,
            mcp_configuration,
            mcp_agent_integrations,
            configure_mcp_agent,
            unconfigure_mcp_agent,
            configure_all_mcp_agents,
            publish_ui_context,
            #[cfg(not(any(target_os = "android", target_os = "ios")))]
            cancel_exit,
            #[cfg(not(any(target_os = "android", target_os = "ios")))]
            confirm_exit,
            #[cfg(not(any(target_os = "android", target_os = "ios")))]
            set_project_open,
            #[cfg(not(any(target_os = "android", target_os = "ios")))]
            set_recent_projects
        ])
        .build(tauri::generate_context!())
        .expect("failed to build DexDec");

    #[cfg(not(any(target_os = "android", target_os = "ios")))]
    app.run(shutdown::ShutdownController::handle_run_event);

    #[cfg(any(target_os = "android", target_os = "ios"))]
    app.run(|_, _| {});
}
