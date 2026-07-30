import { invoke } from "@tauri-apps/api/core";
import { listen, type UnlistenFn } from "@tauri-apps/api/event";

import { arityOf } from "../domain/descriptors";
import type { SourceDocument } from "../domain/models";
import { useWorkspace } from "../state/workspace";

type WorkspaceSnapshot = ReturnType<typeof useWorkspace.getState>;

export interface UiContextSnapshot {
  revision: number;
  updatedAtMs: number;
  project: UiProjectContext | null;
  activeDocument: UiDocumentContext | null;
  selectedMember: UiMemberContext | null;
  caret: UiCaretContext | null;
  openTabs: UiTabContext[];
}

interface UiProjectContext {
  path: string;
  name: string;
  packageName: string | null;
  classCount: number;
  resourceCount: number;
}

type UiDocumentContext =
  | {
      kind: "class";
      descriptor: string;
      qualifiedName: string;
      language: string;
    }
  | {
      kind: "resource";
      path: string;
      resourceKind: string;
      textFormat: string | null;
    };

interface UiMemberContext {
  kind: "field" | "method";
  name: string;
  descriptor: string | null;
  arity: number | null;
}

interface UiCaretContext {
  line: number;
  column: number;
}

interface UiTabContext {
  descriptor: string;
  qualifiedName: string;
  language: string;
  group: string;
  active: boolean;
  pinned: boolean;
}

interface UiMemberTarget {
  kind: "field" | "method";
  name: string;
  descriptor: string;
}

interface UiNavigationRequest {
  target:
    | {
        kind: "class";
        descriptor: string;
        member: UiMemberTarget | null;
        line: number | null;
        column: number | null;
      }
    | {
        kind: "resource";
        path: string;
      };
}

class UiContextSnapshotBuilder {
  private revision = Date.now() * 1000;

  build(state: WorkspaceSnapshot): UiContextSnapshot {
    const revision = Math.max(this.revision + 1, Date.now() * 1000);
    this.revision = revision;
    const activeDocument = this.activeDocument(state);
    const sourceDocument =
      activeDocument?.kind === "class"
        ? state.documents.find(
            (document) => document.descriptor === activeDocument.descriptor,
          ) ?? null
        : null;
    return {
      revision,
      updatedAtMs: Date.now(),
      project: state.archive
        ? {
            path: state.archive.path,
            name: state.archive.name,
            packageName: state.archive.overview?.packageName ?? null,
            classCount: state.archive.classCount,
            resourceCount: state.archive.resources.length,
          }
        : null,
      activeDocument,
      selectedMember: this.selectedMember(state, sourceDocument),
      caret:
        activeDocument?.kind === "class" && state.caret
          ? { line: state.caret.line, column: state.caret.column }
          : null,
      openTabs: this.openTabs(state),
    };
  }

  private activeDocument(state: WorkspaceSnapshot): UiDocumentContext | null {
    const focused = state.editorLayout.focused;
    if (state.resourceDocument && state.resourceGroup === focused) {
      return {
        kind: "resource",
        path: state.resourceDocument.path,
        resourceKind: state.resourceDocument.kind,
        textFormat: state.resourceDocument.textFormat,
      };
    }
    const descriptor =
      state.editorLayout.active[focused] ?? state.activeDescriptor;
    if (!descriptor || !state.archive) return null;
    const document = state.documents.find(
      (candidate) => candidate.descriptor === descriptor,
    );
    const summary = state.archive.classes.find(
      (candidate) => candidate.descriptor === descriptor,
    );
    if (!document && !summary) return null;
    return {
      kind: "class",
      descriptor,
      qualifiedName: document?.outline.qualifiedName ?? summary!.qualifiedName,
      language:
        document?.language ??
        state.detectedLanguages[descriptor] ??
        (state.sourceLanguage === "auto" ? "java" : state.sourceLanguage),
    };
  }

  private selectedMember(
    state: WorkspaceSnapshot,
    document: SourceDocument | null,
  ): UiMemberContext | null {
    if (!state.caretMember || !document) return null;
    const caret = state.caretMember;
    if (caret.kind === "field") {
      const candidates = document.outline.fields.filter(
        (field) => field.name === caret.name || field.originalName === caret.name,
      );
      const field = candidates.length === 1 ? candidates[0] : null;
      return {
        kind: "field",
        name: field?.originalName ?? field?.name ?? caret.name,
        descriptor: field?.descriptor ?? null,
        arity: null,
      };
    }
    const candidates = document.outline.methods.filter(
      (method) =>
        (method.name === caret.name || method.originalName === caret.name) &&
        (caret.arity === null || arityOf(method.descriptor) === caret.arity),
    );
    const method = candidates.length === 1 ? candidates[0] : null;
    return {
      kind: "method",
      name: method?.originalName ?? method?.name ?? caret.name,
      descriptor: method?.descriptor ?? null,
      arity: caret.arity,
    };
  }

  private openTabs(state: WorkspaceSnapshot): UiTabContext[] {
    return Object.entries(state.editorLayout.tabs).flatMap(
      ([group, descriptors]) =>
        descriptors.flatMap((descriptor) => {
          const document = state.documents.find(
            (candidate) => candidate.descriptor === descriptor,
          );
          const summary = state.archive?.classes.find(
            (candidate) => candidate.descriptor === descriptor,
          );
          if (!document && !summary) return [];
          return [
            {
              descriptor,
              qualifiedName:
                document?.outline.qualifiedName ?? summary!.qualifiedName,
              language:
                document?.language ??
                state.detectedLanguages[descriptor] ??
                (state.sourceLanguage === "auto" ? "java" : state.sourceLanguage),
              group,
              active: state.editorLayout.active[group] === descriptor,
              pinned: state.pinned.includes(descriptor),
            },
          ];
        }),
    );
  }
}

class UiNavigationController {
  async navigate(request: UiNavigationRequest): Promise<void> {
    const target = request.target;
    const state = useWorkspace.getState();
    if (!state.archive) return;
    if (target.kind === "resource") {
      if (state.archive.resources.some((resource) => resource.path === target.path)) {
        await state.openResource(target.path);
      }
      return;
    }
    if (
      !state.archive.classes.some(
        (candidate) => candidate.descriptor === target.descriptor,
      )
    ) {
      return;
    }
    await state.selectClass(target.descriptor, { preview: false });
    const selected = useWorkspace.getState();
    if (target.member) {
      selected.navigateToMember({
        classDescriptor: target.descriptor,
        kind: target.member.kind,
        name: target.member.name,
        descriptor: target.member.descriptor,
      });
    } else if (target.line !== null) {
      selected.restorePosition(target.descriptor, {
        line: target.line,
        column: target.column ?? 0,
      });
    }
  }
}

class UiContextService {
  private readonly builder = new UiContextSnapshotBuilder();
  private readonly navigation = new UiNavigationController();
  private timer: number | null = null;
  private unlisten: UnlistenFn | null = null;
  private generation = 0;

  start(): () => void {
    const generation = ++this.generation;
    const unsubscribe = useWorkspace.subscribe(() => this.schedule());
    this.schedule(0);
    void listen<UiNavigationRequest>("dexdec://ui-navigation", (event) => {
      if (generation !== this.generation) return;
      void this.navigation.navigate(event.payload);
    }).then((unlisten) => {
      if (generation !== this.generation) unlisten();
      else this.unlisten = unlisten;
    }).catch(() => {
      /* Browser preview has no native UI context bridge. */
    });
    return () => {
      unsubscribe();
      if (generation !== this.generation) return;
      this.generation++;
      this.unlisten?.();
      this.unlisten = null;
      if (this.timer !== null) window.clearTimeout(this.timer);
      this.timer = null;
    };
  }

  private schedule(delay = 60): void {
    if (this.timer !== null) window.clearTimeout(this.timer);
    this.timer = window.setTimeout(() => {
      this.timer = null;
      const snapshot = this.builder.build(useWorkspace.getState());
      void invoke("publish_ui_context", { snapshot }).catch(() => {
        /* Browser preview has no native UI context bridge. */
      });
    }, delay);
  }
}

export const uiContextService = new UiContextService();
