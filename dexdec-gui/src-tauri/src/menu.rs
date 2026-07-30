use tauri::{
    menu::{AboutMetadata, Menu, MenuEvent, MenuItem, PredefinedMenuItem, Submenu},
    AppHandle, Emitter, Runtime,
};

pub const MENU_EVENT: &str = "dexdec://menu";

pub struct DesktopMenu;

impl DesktopMenu {
    const PROJECT_COMMANDS: &'static [&'static str] = &[
        "file.close-project",
        "file.save",
        "file.save-as",
        "file.close-editor",
        "file.reopen-editor",
        "edit.undo",
        "edit.redo",
        "edit.rename",
        "edit.find-in-files",
        "view.problems",
        "navigate.class",
        "navigate.member",
        "navigate.symbol",
        "navigate.declaration-or-usages",
        "navigate.find-usages",
        "navigate.back",
        "navigate.forward",
    ];

    pub fn build<R: Runtime>(app: &AppHandle<R>) -> tauri::Result<Menu<R>> {
        let package = app.package_info();
        let about = AboutMetadata {
            name: Some(package.name.clone()),
            version: Some(package.version.to_string()),
            ..Default::default()
        };

        let application = Submenu::with_items(
            app,
            package.name.clone(),
            true,
            &[
                &PredefinedMenuItem::about(app, None, Some(about.clone()))?,
                &PredefinedMenuItem::separator(app)?,
                &Self::command(app, "app.settings", "Settings…", "CmdOrCtrl+,")?,
                &PredefinedMenuItem::separator(app)?,
                &PredefinedMenuItem::services(app, None)?,
                &PredefinedMenuItem::separator(app)?,
                &PredefinedMenuItem::hide(app, None)?,
                &PredefinedMenuItem::hide_others(app, None)?,
                &PredefinedMenuItem::show_all(app, None)?,
                &PredefinedMenuItem::separator(app)?,
                &PredefinedMenuItem::quit(app, None)?,
            ],
        )?;

        let file = Submenu::with_items(
            app,
            "File",
            true,
            &[
                &Self::command(app, "file.open", "Open Archive…", "CmdOrCtrl+O")?,
                &Submenu::with_id_and_items(
                    app,
                    "file.open-recent",
                    "Open Recent",
                    true,
                    &[&MenuItem::with_id(
                        app,
                        "file.recent.empty",
                        "No Recent Projects",
                        false,
                        None::<&str>,
                    )?],
                )?,
                &Self::project_command(
                    app,
                    "file.close-project",
                    "Close Project",
                    "CmdOrCtrl+Shift+W",
                )?,
                &PredefinedMenuItem::separator(app)?,
                &Self::project_command(app, "file.save", "Save", "CmdOrCtrl+S")?,
                &Self::project_command(app, "file.save-as", "Save As…", "CmdOrCtrl+Shift+S")?,
                &PredefinedMenuItem::separator(app)?,
                &Self::project_command(app, "file.close-editor", "Close Editor", "CmdOrCtrl+W")?,
                &Self::project_command(
                    app,
                    "file.reopen-editor",
                    "Reopen Closed Editor",
                    "CmdOrCtrl+Shift+T",
                )?,
            ],
        )?;

        let edit = Submenu::with_items(
            app,
            "Edit",
            true,
            &[
                &Self::plain_project_command(app, "edit.undo", "Undo Rename")?,
                &Self::plain_project_command(app, "edit.redo", "Redo Rename")?,
                &PredefinedMenuItem::separator(app)?,
                &PredefinedMenuItem::cut(app, None)?,
                &PredefinedMenuItem::copy(app, None)?,
                &PredefinedMenuItem::paste(app, None)?,
                &PredefinedMenuItem::select_all(app, None)?,
                &PredefinedMenuItem::separator(app)?,
                &Self::project_command(
                    app,
                    "edit.find-in-files",
                    "Find in Files…",
                    "CmdOrCtrl+Shift+F",
                )?,
                &Self::project_command(app, "edit.rename", "Rename Symbol…", "Shift+F6")?,
            ],
        )?;

        let view = Submenu::with_items(
            app,
            "View",
            true,
            &[
                &Self::command(app, "view.explorer", "Toggle Explorer", "CmdOrCtrl+1")?,
                &Self::command(app, "view.outline", "Toggle Outline", "CmdOrCtrl+7")?,
                &Self::project_command(app, "view.problems", "Toggle Problems", "CmdOrCtrl+6")?,
                &PredefinedMenuItem::separator(app)?,
                &PredefinedMenuItem::fullscreen(app, None)?,
            ],
        )?;

        let navigate = Submenu::with_items(
            app,
            "Navigate",
            true,
            &[
                &Self::plain_project_command(app, "navigate.class", "Go to Class…")?,
                &Self::project_command(app, "navigate.member", "Go to Member…", "CmdOrCtrl+F12")?,
                &Self::project_command(
                    app,
                    "navigate.symbol",
                    "Search Symbols…",
                    "CmdOrCtrl+Alt+O",
                )?,
                &Self::project_command(
                    app,
                    "navigate.declaration-or-usages",
                    "Go to Declaration or Usages",
                    "CmdOrCtrl+B",
                )?,
                &Self::project_command(app, "navigate.find-usages", "Find Usages", "Alt+F7")?,
                &PredefinedMenuItem::separator(app)?,
                &Self::project_command(app, "navigate.back", "Back", "CmdOrCtrl+[")?,
                &Self::project_command(app, "navigate.forward", "Forward", "CmdOrCtrl+]")?,
            ],
        )?;

        let window = Submenu::with_items(
            app,
            "Window",
            true,
            &[
                &PredefinedMenuItem::minimize(app, None)?,
                &PredefinedMenuItem::maximize(app, None)?,
                &PredefinedMenuItem::separator(app)?,
                &PredefinedMenuItem::bring_all_to_front(app, None)?,
            ],
        )?;

        let help = Submenu::with_items(
            app,
            "Help",
            true,
            &[&PredefinedMenuItem::about(
                app,
                Some("About DexDec"),
                Some(about),
            )?],
        )?;

        Menu::with_items(
            app,
            &[&application, &file, &edit, &view, &navigate, &window, &help],
        )
    }

    pub fn handle<R: Runtime>(app: &AppHandle<R>, event: MenuEvent) {
        let id = event.id().as_ref();
        if id.contains('.') {
            let _ = app.emit_to("main", MENU_EVENT, id.to_string());
        }
    }

    pub fn set_project_open<R: Runtime>(app: &AppHandle<R>, open: bool) -> tauri::Result<()> {
        let Some(menu) = app.menu() else {
            return Ok(());
        };
        for id in Self::PROJECT_COMMANDS {
            for item in menu.items()? {
                let Some(submenu) = item.as_submenu() else {
                    continue;
                };
                let Some(item) = submenu.get(*id) else {
                    continue;
                };
                if let Some(item) = item.as_menuitem() {
                    item.set_enabled(open)?;
                }
                break;
            }
        }
        Self::set_accelerator(&menu, "file.open", (!open).then_some("CmdOrCtrl+O"))?;
        Self::set_accelerator(&menu, "navigate.class", open.then_some("CmdOrCtrl+O"))?;
        Ok(())
    }

    pub fn set_recent_projects<R: Runtime>(
        app: &AppHandle<R>,
        labels: Vec<String>,
    ) -> tauri::Result<()> {
        let Some(menu) = app.menu() else {
            return Ok(());
        };
        let recent = menu
            .items()?
            .into_iter()
            .filter_map(|item| item.as_submenu().cloned())
            .find_map(|submenu| submenu.get("file.open-recent"))
            .and_then(|item| item.as_submenu().cloned());
        let Some(recent) = recent else {
            return Ok(());
        };

        while !recent.items()?.is_empty() {
            recent.remove_at(0)?;
        }

        if labels.is_empty() {
            recent.append(&MenuItem::with_id(
                app,
                "file.recent.empty",
                "No Recent Projects",
                false,
                None::<&str>,
            )?)?;
            return Ok(());
        }

        for (index, label) in labels.into_iter().enumerate() {
            recent.append(&MenuItem::with_id(
                app,
                format!("file.open-recent.{index}"),
                label,
                true,
                None::<&str>,
            )?)?;
        }
        recent.append(&PredefinedMenuItem::separator(app)?)?;
        recent.append(&MenuItem::with_id(
            app,
            "file.recent.clear",
            "Clear Menu",
            true,
            None::<&str>,
        )?)?;
        Ok(())
    }

    fn command<R: Runtime>(
        app: &AppHandle<R>,
        id: &str,
        label: &str,
        accelerator: &str,
    ) -> tauri::Result<MenuItem<R>> {
        MenuItem::with_id(app, id, label, true, Some(accelerator))
    }

    fn project_command<R: Runtime>(
        app: &AppHandle<R>,
        id: &str,
        label: &str,
        accelerator: &str,
    ) -> tauri::Result<MenuItem<R>> {
        MenuItem::with_id(app, id, label, false, Some(accelerator))
    }

    fn plain_project_command<R: Runtime>(
        app: &AppHandle<R>,
        id: &str,
        label: &str,
    ) -> tauri::Result<MenuItem<R>> {
        MenuItem::with_id(app, id, label, false, None::<&str>)
    }

    fn set_accelerator<R: Runtime>(
        menu: &Menu<R>,
        id: &str,
        accelerator: Option<&str>,
    ) -> tauri::Result<()> {
        for item in menu.items()? {
            let Some(submenu) = item.as_submenu() else {
                continue;
            };
            let Some(item) = submenu.get(id) else {
                continue;
            };
            if let Some(item) = item.as_menuitem() {
                item.set_accelerator(accelerator)?;
            }
            break;
        }
        Ok(())
    }
}
