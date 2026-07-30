use std::sync::atomic::{AtomicBool, Ordering};

use tauri::{AppHandle, Emitter, Manager, RunEvent, Runtime, Window, WindowEvent};

pub const CLOSE_REQUESTED_EVENT: &str = "dexdec://close-requested";

#[derive(Default)]
pub struct ShutdownController {
    confirmed: AtomicBool,
    prompt_pending: AtomicBool,
}

impl ShutdownController {
    pub fn handle_window_event<R: Runtime>(window: &Window<R>, event: &WindowEvent) {
        let WindowEvent::CloseRequested { api, .. } = event else {
            return;
        };
        let controller = window.state::<Self>();
        if controller.confirmed.load(Ordering::Acquire) {
            return;
        }
        api.prevent_close();
        controller.request_prompt(window.app_handle());
    }

    pub fn handle_run_event<R: Runtime>(app: &AppHandle<R>, event: RunEvent) {
        let RunEvent::ExitRequested { api, .. } = event else {
            return;
        };
        let controller = app.state::<Self>();
        if controller.confirmed.load(Ordering::Acquire) {
            return;
        }
        api.prevent_exit();
        controller.request_prompt(app);
    }

    pub fn cancel(&self) {
        self.prompt_pending.store(false, Ordering::Release);
    }

    pub fn confirm<R: Runtime>(&self, app: &AppHandle<R>) {
        self.confirmed.store(true, Ordering::Release);
        app.exit(0);
    }

    fn request_prompt<R: Runtime>(&self, app: &AppHandle<R>) {
        if !self.prompt_pending.swap(true, Ordering::AcqRel) {
            let _ = app.emit(CLOSE_REQUESTED_EVENT, ());
        }
    }
}
