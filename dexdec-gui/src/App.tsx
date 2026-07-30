import { useEffect, useState } from "react";

import { ArchiveDropOverlay } from "./components/ArchiveDropOverlay";
import { ActivityCenter } from "./components/ActivityCenter";
import { Explorer } from "./components/Explorer";
import { GlobalSearch } from "./components/GlobalSearch";
import { MemberOpen } from "./components/MemberOpen";
import { Outline } from "./components/Outline";
import { QuickOpen } from "./components/QuickOpen";
import { SettingsDialog } from "./components/SettingsDialog";
import { SourceWorkspace } from "./components/SourceWorkspace";
import { StatusBar } from "./components/StatusBar";
import { Toolbar } from "./components/Toolbar";
import { ToastViewport } from "./components/ToastViewport";
import {
  NativeMenu,
  type NativeMenuCommand,
} from "./services/nativeMenu";
import {
  NativeArchiveDrop,
  type ArchiveDropIntent,
} from "./services/archiveDrop";
import { t } from "./i18n";
import { projectClient } from "./services/projectClient";
import { uiContextService } from "./services/uiContext";
import {
  EXPLORER_DEFAULT_WIDTH,
  OUTLINE_DEFAULT_WIDTH,
  useWorkspace,
} from "./state/workspace";
import { useAppearance } from "./state/appearance";

function executeNativeMenu(command: NativeMenuCommand): void {
  const workspace = useWorkspace.getState();
  if (command.startsWith("file.open-recent.")) {
    const index = Number(command.slice("file.open-recent.".length));
    const project = workspace.recentProjects[index];
    if (project) void workspace.openArchive(project.path);
    return;
  }
  switch (command) {
    case "app.settings":
      useAppearance.getState().setSettingsOpen(true);
      break;
    case "file.open":
      void workspace.chooseArchive();
      break;
    case "file.recent.clear":
      workspace.clearRecentProjects();
      break;
    case "file.close-project":
      void workspace.closeProject();
      break;
    case "file.save":
      void workspace.saveProject();
      break;
    case "file.save-as":
      void workspace.saveProjectAs();
      break;
    case "file.close-editor":
      workspace.closeActiveDocument();
      break;
    case "file.reopen-editor":
      workspace.reopenClosedTab();
      break;
    case "edit.undo":
      workspace.undo();
      break;
    case "edit.redo":
      workspace.redo();
      break;
    case "edit.rename":
      window.dispatchEvent(new CustomEvent("dexdec:rename"));
      break;
    case "edit.find-in-files":
      if (workspace.archive) workspace.setCodeSearchVisible(true);
      break;
    case "navigate.declaration-or-usages":
      window.dispatchEvent(new CustomEvent("dexdec:declaration-or-usages"));
      break;
    case "navigate.find-usages":
      window.dispatchEvent(new CustomEvent("dexdec:find-usages"));
      break;
    case "view.explorer":
      workspace.toggleExplorer();
      break;
    case "view.outline":
      workspace.toggleOutline();
      break;
    case "view.problems":
      workspace.setProblemsOpen(!workspace.problemsOpen);
      break;
    case "navigate.class":
      if (workspace.archive) {
        workspace.setQuickOpenVisible(true);
      }
      break;
    case "navigate.member":
      if (workspace.activeDescriptor) {
        workspace.setMemberOpenVisible(true);
      }
      break;
    case "navigate.symbol":
      if (workspace.archive) {
        workspace.setGlobalSearchVisible(true);
      }
      break;
    case "navigate.back":
      workspace.goBack();
      break;
    case "navigate.forward":
      workspace.goForward();
      break;
  }
}

export default function App() {
  const explorerVisible = useWorkspace((state) => state.explorerVisible);
  const outlineVisible = useWorkspace((state) => state.outlineVisible);
  const explorerWidth = useWorkspace((state) => state.explorerWidth);
  const outlineWidth = useWorkspace((state) => state.outlineWidth);
  const quickOpenVisible = useWorkspace((state) => state.quickOpenVisible);
  const memberOpenVisible = useWorkspace((state) => state.memberOpenVisible);
  const globalSearchVisible = useWorkspace((state) => state.globalSearchVisible);
  const activeDescriptor = useWorkspace((state) => state.activeDescriptor);
  const documents = useWorkspace((state) => state.documents);
  const projectDirty = useWorkspace((state) => state.projectDirty);
  const projectOpen = useWorkspace((state) => state.archive !== null);
  const recentProjects = useWorkspace((state) => state.recentProjects);
  const [archiveDrop, setArchiveDrop] = useState<
    Extract<ArchiveDropIntent, { type: "hover" }> | null
  >(null);

  useEffect(() => {
    document.body.classList.toggle(
      "platform-macos",
      /Mac|macOS/.test(navigator.userAgent),
    );
    void useWorkspace.getState().restoreSession();
  }, []);

  useEffect(() => uiContextService.start(), []);

  useEffect(() => {
    let unlisten: (() => void) | null = null;
    let disposed = false;
    void projectClient.listenForClose(() => {
      void useWorkspace.getState().requestExit();
    }).then((stop) => {
      if (disposed) {
        stop();
      } else {
        unlisten = stop;
      }
    }).catch(() => {
      /* Browser preview has no native lifecycle channel. */
    });
    return () => {
      disposed = true;
      unlisten?.();
    };
  }, []);

  useEffect(() => {
    return NativeMenu.subscribe(executeNativeMenu);
  }, []);

  useEffect(() => {
    void NativeMenu.setProjectOpen(projectOpen).catch(() => {
      /* Browser preview has no native menu. */
    });
  }, [projectOpen]);

  useEffect(() => {
    void NativeMenu.setRecentProjects(
      recentProjects.map((project) => project.name),
    ).catch(() => {
      /* Browser preview has no native menu. */
    });
  }, [recentProjects]);

  useEffect(
    () =>
      NativeArchiveDrop.subscribe((intent) => {
        switch (intent.type) {
          case "hover":
            setArchiveDrop(intent);
            break;
          case "leave":
            setArchiveDrop(null);
            break;
          case "drop": {
            setArchiveDrop(null);
            const path = intent.path;
            if (!path) {
              useWorkspace.getState().reportError(t("drop.unsupported"));
              break;
            }
            // Off the native drag-drop callback: opening can put a modal on
            // screen, and asking for one from inside the drop that raised it
            // is how a drop ends up doing nothing at all.
            setTimeout(() => {
              void useWorkspace.getState().openArchive(path);
            }, 0);
            break;
          }
        }
      }),
    [],
  );

  useEffect(() => {
    const onKeyDown = (event: KeyboardEvent) => {
      if (
        event.defaultPrevented ||
        useAppearance.getState().settingsOpen
      ) {
        return;
      }
      const state = useWorkspace.getState();
      if (
        event.key === "Escape" &&
        state.peek &&
        !state.quickOpenVisible &&
        !state.memberOpenVisible
      ) {
        state.closePeek();
        return;
      }
      const mod = event.metaKey || event.ctrlKey;
      if (!mod) {
        return;
      }
      const key = event.key.toLowerCase();
      if (key === "o" && !event.shiftKey && !event.altKey) {
        event.preventDefault();
        if (state.archive) {
          state.setQuickOpenVisible(!state.quickOpenVisible);
        } else {
          void state.chooseArchive();
        }
      } else if (key === "f12" && !event.shiftKey && !event.altKey) {
        event.preventDefault();
        if (state.activeDescriptor) {
          state.setMemberOpenVisible(!state.memberOpenVisible);
        }
      } else if (key === "o" && event.altKey && !event.shiftKey) {
        event.preventDefault();
        if (state.archive) {
          state.setGlobalSearchVisible(!state.globalSearchVisible);
        }
      } else if (key === "f" && event.shiftKey && !event.altKey) {
        event.preventDefault();
        if (state.archive) {
          state.setCodeSearchVisible(!state.codeSearchVisible);
        }
      } else if (key === "t" && event.shiftKey) {
        event.preventDefault();
        state.reopenClosedTab();
      } else if (key === "[") {
        event.preventDefault();
        state.goBack();
      } else if (key === "]") {
        event.preventDefault();
        state.goForward();
      } else if (key === "1" && !event.shiftKey && !event.altKey) {
        event.preventDefault();
        state.toggleExplorer();
      } else if (key === "7" && !event.shiftKey && !event.altKey) {
        event.preventDefault();
        state.toggleOutline();
      } else if (key === "6" && !event.shiftKey && !event.altKey) {
        event.preventDefault();
        state.setProblemsOpen(!state.problemsOpen);
      } else if (key === "w" && event.shiftKey && !event.altKey) {
        event.preventDefault();
        void state.closeProject();
      } else if (key === "w" && !event.shiftKey && !event.altKey) {
        event.preventDefault();
        state.closeActiveDocument();
      } else if (key === "," && !event.shiftKey && !event.altKey) {
        event.preventDefault();
        useAppearance.getState().setSettingsOpen(true);
      } else if (key === "s" && !event.altKey) {
        event.preventDefault();
        void (event.shiftKey ? state.saveProjectAs() : state.saveProject());
      } else if (
        key === "z" &&
        !event.altKey &&
        !isEditableTarget(event.target)
      ) {
        event.preventDefault();
        event.shiftKey ? state.redo() : state.undo();
      } else if (
        key === "y" &&
        !event.shiftKey &&
        !event.altKey &&
        !isEditableTarget(event.target)
      ) {
        event.preventDefault();
        state.redo();
      }
    };
    window.addEventListener("keydown", onKeyDown, true);
    return () => window.removeEventListener("keydown", onKeyDown, true);
  }, []);

  const activeDocument = documents.find(
    (document) => document.descriptor === activeDescriptor,
  );
  useEffect(() => {
    document.title = activeDocument
      ? `${projectDirty ? "● " : ""}${activeDocument.outline.qualifiedName.split(".").at(-1)} — DexDec`
      : `${projectDirty ? "● " : ""}DexDec`;
  }, [activeDocument, projectDirty]);

  return (
    <div className="app-shell flex h-screen min-h-0 flex-col overflow-hidden bg-[var(--workspace)] text-[var(--text)]">
      <Toolbar />
      <div className="flex min-h-0 flex-1 overflow-hidden">
        {explorerVisible ? (
          <>
            <div
              className="min-h-0 shrink-0 [&>aside]:h-full"
              style={{ width: explorerWidth }}
            >
              <Explorer />
            </div>
            <ResizeHandle side="left" />
          </>
        ) : null}
        <SourceWorkspace />
        {outlineVisible && activeDescriptor ? (
          <>
            <ResizeHandle side="right" />
            <div
              className="min-h-0 shrink-0 [&>aside]:h-full"
              style={{ width: outlineWidth }}
            >
              <Outline />
            </div>
          </>
        ) : null}
      </div>
      <StatusBar />
      {quickOpenVisible ? <QuickOpen /> : null}
      {memberOpenVisible ? <MemberOpen /> : null}
      {globalSearchVisible ? <GlobalSearch /> : null}
      <SettingsDialog />
      <ActivityCenter />
      <ToastViewport />
      {archiveDrop ? <ArchiveDropOverlay {...archiveDrop} /> : null}
    </div>
  );
}

function isEditableTarget(target: EventTarget | null): boolean {
  if (
    target instanceof Element &&
    target.closest('[aria-readonly="true"]')
  ) {
    return false;
  }
  return (
    target instanceof HTMLInputElement ||
    target instanceof HTMLTextAreaElement ||
    (target instanceof HTMLElement && target.isContentEditable)
  );
}

function ResizeHandle({ side }: { side: "left" | "right" }) {
  const onMouseDown = (event: React.MouseEvent) => {
    event.preventDefault();
    const startX = event.clientX;
    const state = useWorkspace.getState();
    const startWidth = side === "left" ? state.explorerWidth : state.outlineWidth;
    document.body.classList.add("col-resizing");
    const onMove = (move: MouseEvent) => {
      const delta = move.clientX - startX;
      const next = side === "left" ? startWidth + delta : startWidth - delta;
      const current = useWorkspace.getState();
      if (side === "left") {
        current.setExplorerWidth(next);
      } else {
        current.setOutlineWidth(next);
      }
    };
    const onUp = () => {
      document.body.classList.remove("col-resizing");
      window.removeEventListener("mousemove", onMove);
      window.removeEventListener("mouseup", onUp);
    };
    window.addEventListener("mousemove", onMove);
    window.addEventListener("mouseup", onUp);
  };

  const resetWidth = () => {
    const state = useWorkspace.getState();
    if (side === "left") {
      state.setExplorerWidth(EXPLORER_DEFAULT_WIDTH);
    } else {
      state.setOutlineWidth(OUTLINE_DEFAULT_WIDTH);
    }
  };

  return (
    <div
      className="sidebar-resize-handle"
      role="separator"
      aria-orientation="vertical"
      aria-label={side === "left" ? "Resize explorer" : "Resize outline"}
      title="Drag to resize · double-click to reset"
      onMouseDown={onMouseDown}
      onDoubleClick={resetWidth}
    />
  );
}
