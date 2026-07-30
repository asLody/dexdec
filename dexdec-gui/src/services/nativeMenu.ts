import { listen, type UnlistenFn } from "@tauri-apps/api/event";
import { invoke, isTauri } from "@tauri-apps/api/core";

type StaticNativeMenuCommand =
  | "app.settings"
  | "file.open"
  | "file.recent.clear"
  | "file.close-project"
  | "file.save"
  | "file.save-as"
  | "file.close-editor"
  | "file.reopen-editor"
  | "edit.undo"
  | "edit.redo"
  | "edit.rename"
  | "edit.find-in-files"
  | "view.explorer"
  | "view.outline"
  | "view.problems"
  | "navigate.class"
  | "navigate.member"
  | "navigate.symbol"
  | "navigate.declaration-or-usages"
  | "navigate.find-usages"
  | "navigate.back"
  | "navigate.forward";

export type NativeMenuCommand =
  | StaticNativeMenuCommand
  | `file.open-recent.${number}`;

const MENU_EVENT = "dexdec://menu";
const COMMANDS = new Set<StaticNativeMenuCommand>([
  "app.settings",
  "file.open",
  "file.recent.clear",
  "file.close-project",
  "file.save",
  "file.save-as",
  "file.close-editor",
  "file.reopen-editor",
  "edit.undo",
  "edit.redo",
  "edit.rename",
  "edit.find-in-files",
  "view.explorer",
  "view.outline",
  "view.problems",
  "navigate.class",
  "navigate.member",
  "navigate.symbol",
  "navigate.declaration-or-usages",
  "navigate.find-usages",
  "navigate.back",
  "navigate.forward",
]);

interface NativeMenuBridgeState {
  handlers: Set<(command: NativeMenuCommand) => void>;
  connecting: Promise<void> | null;
  unlisten: UnlistenFn | null;
  retryTimer: ReturnType<typeof setTimeout> | null;
}

const globalScope = globalThis as typeof globalThis & {
  __dexdecNativeMenuBridge?: NativeMenuBridgeState;
};
const bridge =
  globalScope.__dexdecNativeMenuBridge ??
  (globalScope.__dexdecNativeMenuBridge = {
    handlers: new Set(),
    connecting: null,
    unlisten: null,
    retryTimer: null,
  });

export class NativeMenu {
  static setProjectOpen(open: boolean): Promise<void> {
    return invoke<void>("set_project_open", { open });
  }

  static setRecentProjects(labels: string[]): Promise<void> {
    return invoke<void>("set_recent_projects", { labels });
  }

  static subscribe(handler: (command: NativeMenuCommand) => void): UnlistenFn {
    bridge.handlers.add(handler);
    if (isTauri()) void this.connect();
    return () => {
      bridge.handlers.delete(handler);
      if (!bridge.handlers.size && bridge.retryTimer) {
        clearTimeout(bridge.retryTimer);
        bridge.retryTimer = null;
      }
    };
  }

  private static async connect(): Promise<void> {
    if (bridge.unlisten || bridge.connecting) {
      return bridge.connecting ?? Promise.resolve();
    }
    bridge.connecting = listen<string>(MENU_EVENT, (event) => {
      const command = event.payload as NativeMenuCommand;
      if (
        !COMMANDS.has(command as StaticNativeMenuCommand) &&
        !/^file\.open-recent\.\d+$/.test(command)
      ) {
        return;
      }
      for (const handler of bridge.handlers) {
        handler(command);
      }
    })
      .then((unlisten) => {
        bridge.unlisten = unlisten;
      })
      .catch(() => {
        this.scheduleReconnect();
      })
      .finally(() => {
        bridge.connecting = null;
      });
    return bridge.connecting;
  }

  private static scheduleReconnect(): void {
    if (!bridge.handlers.size || bridge.retryTimer) return;
    bridge.retryTimer = setTimeout(() => {
      bridge.retryTimer = null;
      void this.connect();
    }, 250);
  }
}
