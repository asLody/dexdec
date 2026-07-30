import { listen, type UnlistenFn } from "@tauri-apps/api/event";
import { invoke } from "@tauri-apps/api/core";
import {
  message,
  save as chooseSavePath,
} from "@tauri-apps/plugin-dialog";

import type { ProjectSnapshot } from "../domain/models";
import { t } from "../i18n";

export type UnsavedDecision = "save" | "discard" | "cancel";

export interface ProjectClient {
  load(path: string): Promise<ProjectSnapshot>;
  save(path: string, snapshot: ProjectSnapshot): Promise<void>;
  chooseSavePath(suggestedPath: string): Promise<string | null>;
  askUnsavedChanges(projectName: string): Promise<UnsavedDecision>;
  listenForClose(handler: () => void): Promise<UnlistenFn>;
  cancelExit(): Promise<void>;
  confirmExit(): Promise<void>;
}

export class TauriProjectClient implements ProjectClient {
  load(path: string): Promise<ProjectSnapshot> {
    return invoke<ProjectSnapshot>("load_project", { path });
  }

  save(path: string, snapshot: ProjectSnapshot): Promise<void> {
    return invoke<void>("save_project", { path, snapshot });
  }

  chooseSavePath(suggestedPath: string): Promise<string | null> {
    return chooseSavePath({
      title: t("project.saveDialogTitle"),
      defaultPath: suggestedPath,
      filters: [{ name: "DexDec database", extensions: ["dexdb"] }],
    });
  }

  async askUnsavedChanges(projectName: string): Promise<UnsavedDecision> {
    const result = await message(
      t("project.unsavedMessage", projectName),
      {
        title: t("project.unsavedTitle"),
        kind: "warning",
        buttons: {
          yes: t("project.save"),
          no: t("project.discard"),
          cancel: t("project.cancel"),
        },
      },
    );
    return result === t("project.save") || result === "Yes"
      ? "save"
      : result === t("project.discard") || result === "No"
        ? "discard"
        : "cancel";
  }

  async listenForClose(handler: () => void): Promise<UnlistenFn> {
    return listen("dexdec://close-requested", handler);
  }

  cancelExit(): Promise<void> {
    return invoke<void>("cancel_exit");
  }

  confirmExit(): Promise<void> {
    return invoke<void>("confirm_exit");
  }
}

export const projectClient: ProjectClient = new TauriProjectClient();
