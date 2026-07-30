import { isTauri } from "@tauri-apps/api/core";
import type { UnlistenFn } from "@tauri-apps/api/event";
import {
  getCurrentWindow,
  type DragDropEvent,
} from "@tauri-apps/api/window";

export type ArchiveDropIntent =
  | {
      type: "hover";
      accepted: boolean;
      displayName: string;
    }
  | {
      type: "drop";
      path: string | null;
    }
  | {
      type: "leave";
    };

type ArchiveDropHandler = (intent: ArchiveDropIntent) => void;

export class NativeArchiveDrop {
  static subscribe(handler: ArchiveDropHandler): UnlistenFn {
    if (!isTauri()) {
      return () => {};
    }

    let active = true;
    let unlisten: UnlistenFn | null = null;
    let editorDragBlocked = false;
    let releaseTimer: ReturnType<typeof setTimeout> | null = null;
    const beginEditorDrag = (event: DragEvent) => {
      if (
        !(event.target instanceof Element) ||
        !event.target.closest("[data-editor-tab]")
      ) {
        return;
      }
      if (releaseTimer) clearTimeout(releaseTimer);
      releaseTimer = null;
      editorDragBlocked = true;
      handler({ type: "leave" });
    };
    const finishEditorDrag = () => {
      if (!editorDragBlocked) return;
      if (releaseTimer) clearTimeout(releaseTimer);
      releaseTimer = setTimeout(() => {
        releaseTimer = null;
        editorDragBlocked = false;
      }, 300);
    };
    window.addEventListener("dragstart", beginEditorDrag, true);
    window.addEventListener("dragend", finishEditorDrag, true);
    window.addEventListener("drop", finishEditorDrag, true);
    void getCurrentWindow()
      .onDragDropEvent((event) => {
        if (!active || editorDragBlocked) {
          return;
        }
        const intent = this.intent(event.payload);
        if (intent) {
          handler(intent);
        }
      })
      .then((stop) => {
        if (active) {
          unlisten = stop;
        } else {
          stop();
        }
      })
      .catch((error: unknown) => {
        if (active) {
          console.error("Failed to attach native archive drop listener", error);
        }
      });

    return () => {
      active = false;
      window.removeEventListener("dragstart", beginEditorDrag, true);
      window.removeEventListener("dragend", finishEditorDrag, true);
      window.removeEventListener("drop", finishEditorDrag, true);
      if (releaseTimer) clearTimeout(releaseTimer);
      unlisten?.();
      unlisten = null;
    };
  }

  private static intent(event: DragDropEvent): ArchiveDropIntent | null {
    switch (event.type) {
      case "enter": {
        if (event.paths.length === 0) {
          return null;
        }
        const path = this.supportedPath(event.paths);
        const displayPath = path ?? event.paths[0] ?? "";
        return {
          type: "hover",
          accepted: path != null,
          displayName: this.displayName(displayPath),
        };
      }
      case "drop":
        return event.paths.length === 0
          ? null
          : { type: "drop", path: this.supportedPath(event.paths) };
      case "leave":
        return { type: "leave" };
      case "over":
        return null;
    }
  }

  private static supportedPath(paths: string[]): string | null {
    return (
      paths.find((path) => /\.(?:apk|dex|dexdb)$/i.test(path.trim())) ?? null
    );
  }

  private static displayName(path: string): string {
    return path.split(/[\\/]/).at(-1) ?? path;
  }
}
