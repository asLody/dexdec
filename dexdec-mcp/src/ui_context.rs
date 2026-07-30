use std::fs::{self, OpenOptions};
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, RwLock};
use std::thread::{self, JoinHandle};
use std::time::Duration;

use directories::ProjectDirs;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

const PROTOCOL_VERSION: u16 = 1;
const MAX_MESSAGE_BYTES: usize = 1024 * 1024;
const IO_TIMEOUT: Duration = Duration::from_secs(2);

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct UiContextSnapshot {
    pub revision: u64,
    pub updated_at_ms: u64,
    pub project: Option<UiProjectContext>,
    pub active_document: Option<UiDocumentContext>,
    pub selected_member: Option<UiMemberContext>,
    pub caret: Option<UiCaretContext>,
    pub open_tabs: Vec<UiTabContext>,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct UiProjectContext {
    pub path: String,
    pub name: String,
    pub package_name: Option<String>,
    pub class_count: usize,
    pub resource_count: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum UiDocumentContext {
    Class {
        descriptor: String,
        qualified_name: String,
        language: String,
    },
    Resource {
        path: String,
        resource_kind: String,
        text_format: Option<String>,
    },
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub enum UiMemberKind {
    Field,
    Method,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct UiMemberContext {
    pub kind: UiMemberKind,
    pub name: String,
    pub descriptor: Option<String>,
    pub arity: Option<usize>,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct UiCaretContext {
    pub line: usize,
    pub column: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct UiTabContext {
    pub descriptor: String,
    pub qualified_name: String,
    pub language: String,
    pub group: String,
    pub active: bool,
    pub pinned: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct UiNavigationRequest {
    pub target: UiNavigationTarget,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum UiNavigationTarget {
    Class {
        descriptor: String,
        member: Option<UiMemberTarget>,
        line: Option<usize>,
        column: Option<usize>,
    },
    Resource {
        path: String,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct UiMemberTarget {
    pub kind: UiMemberKind,
    pub name: String,
    pub descriptor: String,
}

type NavigationHandler = dyn Fn(UiNavigationRequest) -> Result<(), String> + Send + Sync + 'static;

pub struct UiContextBridge {
    context: Arc<RwLock<Option<UiContextSnapshot>>>,
    shutdown: Arc<AtomicBool>,
    worker: Mutex<Option<JoinHandle<()>>>,
    address: SocketAddr,
    registry_path: PathBuf,
    instance_id: String,
}

impl UiContextBridge {
    pub fn start<F>(navigation: F) -> Result<Self, UiContextBridgeError>
    where
        F: Fn(UiNavigationRequest) -> Result<(), String> + Send + Sync + 'static,
    {
        Self::start_with_registry(navigation, registry_path()?)
    }

    fn start_with_registry<F>(
        navigation: F,
        registry_path: PathBuf,
    ) -> Result<Self, UiContextBridgeError>
    where
        F: Fn(UiNavigationRequest) -> Result<(), String> + Send + Sync + 'static,
    {
        let listener = TcpListener::bind(("127.0.0.1", 0))?;
        listener.set_nonblocking(true)?;
        let address = listener.local_addr()?;
        let token = random_token()?;
        let instance_id = random_token()?;
        write_registry(
            &registry_path,
            &UiBridgeRegistry {
                version: PROTOCOL_VERSION,
                address,
                token: token.clone(),
                instance_id: instance_id.clone(),
            },
        )?;

        let context = Arc::new(RwLock::new(None));
        let shutdown = Arc::new(AtomicBool::new(false));
        let worker_context = Arc::clone(&context);
        let worker_shutdown = Arc::clone(&shutdown);
        let navigation: Arc<NavigationHandler> = Arc::new(navigation);
        let worker = thread::Builder::new()
            .name("dexdec-ui-context".to_string())
            .spawn(move || {
                serve_bridge(listener, token, worker_context, worker_shutdown, navigation)
            })?;

        Ok(Self {
            context,
            shutdown,
            worker: Mutex::new(Some(worker)),
            address,
            registry_path,
            instance_id,
        })
    }

    pub fn publish(&self, context: UiContextSnapshot) {
        if let Ok(mut current) = self.context.write() {
            if current
                .as_ref()
                .is_some_and(|published| published.revision >= context.revision)
            {
                return;
            }
            *current = Some(context);
        }
    }
}

impl Drop for UiContextBridge {
    fn drop(&mut self) {
        self.shutdown.store(true, Ordering::Release);
        let _ = TcpStream::connect_timeout(&self.address, Duration::from_millis(100));
        if let Ok(worker) = self.worker.get_mut() {
            if let Some(worker) = worker.take() {
                let _ = worker.join();
            }
        }
        remove_own_registry(&self.registry_path, &self.instance_id);
    }
}

#[derive(Clone)]
pub(crate) struct UiContextClient {
    registry_path: PathBuf,
}

impl UiContextClient {
    pub fn discover() -> Result<Self, UiContextBridgeError> {
        Ok(Self {
            registry_path: registry_path()?,
        })
    }

    #[cfg(test)]
    fn from_registry(registry_path: PathBuf) -> Self {
        Self { registry_path }
    }

    pub fn context(&self) -> Result<UiContextSnapshot, UiContextBridgeError> {
        self.exchange(UiBridgeOperation::GetContext)?
            .context
            .ok_or_else(|| UiContextBridgeError::Protocol("response has no context".to_string()))
    }

    pub fn navigate(&self, request: UiNavigationRequest) -> Result<(), UiContextBridgeError> {
        let response = self.exchange(UiBridgeOperation::Navigate { request })?;
        if response.accepted == Some(true) {
            Ok(())
        } else {
            Err(UiContextBridgeError::Protocol(
                "navigation was not accepted".to_string(),
            ))
        }
    }

    fn exchange(
        &self,
        operation: UiBridgeOperation,
    ) -> Result<UiBridgeResponse, UiContextBridgeError> {
        let registry = read_registry(&self.registry_path)?;
        if registry.version != PROTOCOL_VERSION {
            return Err(UiContextBridgeError::Protocol(format!(
                "unsupported UI bridge version {}",
                registry.version
            )));
        }
        let mut stream = TcpStream::connect_timeout(&registry.address, IO_TIMEOUT)
            .map_err(|error| UiContextBridgeError::Unavailable(error.to_string()))?;
        stream.set_read_timeout(Some(IO_TIMEOUT))?;
        stream.set_write_timeout(Some(IO_TIMEOUT))?;
        write_message(
            &mut stream,
            &UiBridgeRequest {
                version: PROTOCOL_VERSION,
                token: registry.token,
                operation,
            },
        )?;
        let response: UiBridgeResponse = read_message(&mut stream)?;
        if response.version != PROTOCOL_VERSION {
            return Err(UiContextBridgeError::Protocol(
                "UI bridge returned an incompatible response".to_string(),
            ));
        }
        if let Some(error) = response.error {
            return Err(UiContextBridgeError::Remote(error));
        }
        Ok(response)
    }
}

fn serve_bridge(
    listener: TcpListener,
    token: String,
    context: Arc<RwLock<Option<UiContextSnapshot>>>,
    shutdown: Arc<AtomicBool>,
    navigation: Arc<NavigationHandler>,
) {
    while !shutdown.load(Ordering::Acquire) {
        match listener.accept() {
            Ok((mut stream, _)) => {
                let _ = stream.set_read_timeout(Some(IO_TIMEOUT));
                let _ = stream.set_write_timeout(Some(IO_TIMEOUT));
                let response = handle_request(&mut stream, &token, &context, navigation.as_ref())
                    .unwrap_or_else(UiBridgeResponse::error);
                let _ = write_message(&mut stream, &response);
            }
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                thread::sleep(Duration::from_millis(20));
            }
            Err(_) => break,
        }
    }
}

fn handle_request(
    stream: &mut TcpStream,
    token: &str,
    context: &RwLock<Option<UiContextSnapshot>>,
    navigation: &NavigationHandler,
) -> Result<UiBridgeResponse, String> {
    let request: UiBridgeRequest = read_message(stream).map_err(|error| error.to_string())?;
    if request.version != PROTOCOL_VERSION {
        return Err("unsupported UI bridge protocol version".to_string());
    }
    if request.token != token {
        return Err("UI bridge authentication failed".to_string());
    }
    match request.operation {
        UiBridgeOperation::GetContext => {
            let snapshot = context
                .read()
                .map_err(|_| "UI context state is unavailable".to_string())?
                .clone()
                .ok_or_else(|| "the GUI has not published its workspace context yet".to_string())?;
            Ok(UiBridgeResponse::context(snapshot))
        }
        UiBridgeOperation::Navigate { request } => {
            navigation(request)?;
            Ok(UiBridgeResponse::accepted())
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
struct UiBridgeRegistry {
    version: u16,
    address: SocketAddr,
    token: String,
    instance_id: String,
}

#[derive(Debug, Serialize, Deserialize)]
struct UiBridgeRequest {
    version: u16,
    token: String,
    operation: UiBridgeOperation,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
enum UiBridgeOperation {
    GetContext,
    Navigate { request: UiNavigationRequest },
}

#[derive(Debug, Serialize, Deserialize)]
struct UiBridgeResponse {
    version: u16,
    context: Option<UiContextSnapshot>,
    accepted: Option<bool>,
    error: Option<String>,
}

impl UiBridgeResponse {
    fn context(context: UiContextSnapshot) -> Self {
        Self {
            version: PROTOCOL_VERSION,
            context: Some(context),
            accepted: None,
            error: None,
        }
    }

    fn accepted() -> Self {
        Self {
            version: PROTOCOL_VERSION,
            context: None,
            accepted: Some(true),
            error: None,
        }
    }

    fn error(error: String) -> Self {
        Self {
            version: PROTOCOL_VERSION,
            context: None,
            accepted: None,
            error: Some(error),
        }
    }
}

fn registry_path() -> Result<PathBuf, UiContextBridgeError> {
    let directories =
        ProjectDirs::from("com", "dexdec", "app").ok_or(UiContextBridgeError::HomeDirectory)?;
    Ok(directories.config_dir().join("ui-context.json"))
}

fn write_registry(path: &PathBuf, registry: &UiBridgeRegistry) -> Result<(), UiContextBridgeError> {
    let parent = path.parent().ok_or(UiContextBridgeError::HomeDirectory)?;
    fs::create_dir_all(parent)?;
    let temporary = path.with_extension(format!("{}.tmp", std::process::id()));
    let mut options = OpenOptions::new();
    options.create(true).truncate(true).write(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options.open(&temporary)?;
    serde_json::to_writer(&mut file, registry)?;
    file.flush()?;
    let _ = fs::remove_file(path);
    fs::rename(temporary, path)?;
    Ok(())
}

fn read_registry(path: &PathBuf) -> Result<UiBridgeRegistry, UiContextBridgeError> {
    let contents =
        fs::read(path).map_err(|error| UiContextBridgeError::Unavailable(error.to_string()))?;
    serde_json::from_slice(&contents)
        .map_err(|error| UiContextBridgeError::Unavailable(error.to_string()))
}

fn remove_own_registry(path: &PathBuf, instance_id: &str) {
    if read_registry(path)
        .map(|registry| registry.instance_id == instance_id)
        .unwrap_or(false)
    {
        let _ = fs::remove_file(path);
    }
}

fn random_token() -> Result<String, UiContextBridgeError> {
    let mut bytes = [0u8; 32];
    getrandom::fill(&mut bytes).map_err(|error| UiContextBridgeError::Random(error.to_string()))?;
    Ok(bytes.iter().map(|byte| format!("{byte:02x}")).collect())
}

fn write_message<T: Serialize>(
    stream: &mut TcpStream,
    message: &T,
) -> Result<(), UiContextBridgeError> {
    serde_json::to_writer(&mut *stream, message)?;
    stream.write_all(b"\n")?;
    stream.flush()?;
    Ok(())
}

fn read_message<T: for<'de> Deserialize<'de>>(
    stream: &mut TcpStream,
) -> Result<T, UiContextBridgeError> {
    let mut line = String::new();
    let bytes = BufReader::new(stream)
        .take((MAX_MESSAGE_BYTES + 1) as u64)
        .read_line(&mut line)?;
    if bytes == 0 || bytes > MAX_MESSAGE_BYTES {
        return Err(UiContextBridgeError::Protocol(
            "UI bridge message is empty or too large".to_string(),
        ));
    }
    Ok(serde_json::from_str(&line)?)
}

#[derive(Debug, thiserror::Error)]
pub enum UiContextBridgeError {
    #[error("DexDec UI is unavailable: {0}")]
    Unavailable(String),
    #[error("unable to locate the user configuration directory")]
    HomeDirectory,
    #[error("UI bridge protocol error: {0}")]
    Protocol(String),
    #[error("DexDec UI rejected the request: {0}")]
    Remote(String),
    #[error("unable to create a UI bridge credential: {0}")]
    Random(String),
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Json(#[from] serde_json::Error),
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::mpsc;

    fn snapshot(revision: u64) -> UiContextSnapshot {
        UiContextSnapshot {
            revision,
            updated_at_ms: 7,
            project: Some(UiProjectContext {
                path: "/tmp/app.apk".to_string(),
                name: "app.apk".to_string(),
                package_name: Some("example.app".to_string()),
                class_count: 10,
                resource_count: 20,
            }),
            active_document: Some(UiDocumentContext::Class {
                descriptor: "Lexample/Main;".to_string(),
                qualified_name: "example.Main".to_string(),
                language: "java".to_string(),
            }),
            selected_member: None,
            caret: Some(UiCaretContext {
                line: 12,
                column: 4,
            }),
            open_tabs: Vec::new(),
        }
    }

    #[test]
    fn bridge_publishes_context_and_forwards_navigation() {
        let registry = std::env::temp_dir().join(format!(
            "dexdec-ui-context-test-{}-{}.json",
            std::process::id(),
            random_token().expect("test token")
        ));
        let (sender, receiver) = mpsc::channel();
        let bridge = UiContextBridge::start_with_registry(
            move |request| sender.send(request).map_err(|error| error.to_string()),
            registry.clone(),
        )
        .expect("start bridge");
        bridge.publish(snapshot(3));
        bridge.publish(snapshot(2));

        let client = UiContextClient::from_registry(registry);
        assert_eq!(client.context().expect("read context").revision, 3);
        let request = UiNavigationRequest {
            target: UiNavigationTarget::Class {
                descriptor: "Lexample/Other;".to_string(),
                member: None,
                line: Some(8),
                column: Some(2),
            },
        };
        client.navigate(request).expect("forward navigation");
        assert!(matches!(
            receiver.recv_timeout(Duration::from_secs(1)).expect("navigation"),
            UiNavigationRequest {
                target: UiNavigationTarget::Class { descriptor, .. }
            } if descriptor == "Lexample/Other;"
        ));
    }
}
