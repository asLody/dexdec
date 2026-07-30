//! MCP adapter for the shared DexDec workbench.

mod access;
mod model;
mod server;
mod ui_context;

pub use access::McpOptions;
pub use server::McpRuntime;
pub use ui_context::{
    UiCaretContext, UiContextBridge, UiContextBridgeError, UiContextSnapshot, UiDocumentContext,
    UiMemberContext, UiMemberKind, UiMemberTarget, UiNavigationRequest, UiNavigationTarget,
    UiProjectContext, UiTabContext,
};
