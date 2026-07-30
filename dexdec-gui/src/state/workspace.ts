import { create } from "zustand";
import type { EditorState } from "@codemirror/state";

import type {
  Archive,
  LanguagePreference,
  MemberNavigation,
  MethodOutline,
  ReferenceLocation,
  ReferenceTarget,
  ResourceDocument,
  ResourceNavigation,
  ResourceNavigationTarget,
  SourceDocument,
  SourceLanguage,
  SymbolDestination,
} from "../domain/models";
import type {
  ResolvedSymbol,
  SourceDefinitionResolver,
} from "../domain/sourceDefinitionResolver";
import {
  EditorLayout,
  ROOT_EDITOR_GROUP,
  type EditorGroup,
  type EditorLayoutState,
  type EditorSplitAxis,
  type EditorSplitSide,
} from "../domain/editorLayout";
import { ProjectSession } from "../domain/projectSession";
import {
  recentProjectHistory,
  type RecentProject,
} from "../domain/recentProjects";
import { t } from "../i18n";
import { ArchiveMemberResolver } from "../services/archiveMemberResolver";
import { ApplicationIconService } from "../services/applicationIcon";
import { decompilerClient } from "../services/decompilerClient";
import {
  loadDecompileOptions,
  saveDecompileOptions,
  type DecompileOptions,
} from "./decompileOptions";
import { projectClient } from "../services/projectClient";
import {
  RenameService,
  type RenameIssue,
} from "../services/renameService";
import { ActivityCenter, type ActivityHandle } from "./activity";

const DOCUMENT_LIMIT = 12;
const CLOSED_TABS_LIMIT = 10;
const HISTORY_LIMIT = 100;
const SESSION_STORAGE_KEY = "dexdec.session";

export const EXPLORER_DEFAULT_WIDTH = 248;
export const OUTLINE_DEFAULT_WIDTH = 264;
export const EXPLORER_WIDTH_RANGE: [number, number] = [176, 420];
export const OUTLINE_WIDTH_RANGE: [number, number] = [200, 440];

const clamp = (value: number, [min, max]: [number, number]) =>
  Math.min(max, Math.max(min, Math.round(value)));

function storedWidth(key: string, fallback: number, range: [number, number]): number {
  try {
    const value = Number(localStorage.getItem(key));
    return Number.isFinite(value) && value > 0 ? clamp(value, range) : fallback;
  } catch {
    return fallback;
  }
}

export interface CaretPosition {
  line: number;
  column: number;
}

/** Member under the editor caret, matched against outline rows. */
export interface CaretMember {
  kind: "field" | "method";
  name: string;
  arity: number | null;
}

export interface ProblemEntry {
  id: number;
  descriptor: string;
  message: string;
  at: number;
}

const PROBLEMS_LIMIT = 50;

export interface HistoryEntry {
  descriptor: string;
  group?: EditorGroup;
  member?: {
    kind: "field" | "method";
    name: string;
    descriptor: string;
  };
  /** Where the caret sat when this stop was left, so returning lands there. */
  position?: CaretPosition;
}

export interface PeekState {
  classDescriptor: string;
  name: string;
  descriptor: string;
  displaySignature: string;
  language: SourceLanguage;
  state: "loading" | "ready" | "error";
  source: string | null;
  elapsedMs: number | null;
  error: string | null;
}

export interface ReferencesState {
  sequence: number;
  label: string;
  state: "loading" | "ready" | "error";
  locations: ReferenceLocation[];
  elapsedMs: number | null;
  error: string | null;
}

export interface SelectOptions {
  recordHistory?: boolean;
  group?: EditorGroup;
  preview?: boolean;
}

interface WorkspaceState {
  archive: Archive | null;
  sourceLanguage: LanguagePreference;
  recentProjects: RecentProject[];
  /**
   * What `auto` found each class to be written in. Only requests made under
   * `auto` teach it: asking for Java gets Java back whatever the class is.
   */
  detectedLanguages: Record<string, SourceLanguage>;
  documents: SourceDocument[];
  closedTabs: SourceDocument[];
  pinned: string[];
  editorLayout: EditorLayoutState;
  activeDescriptor: string | null;
  loadingDescriptor: string | null;
  resourceDocument: ResourceDocument | null;
  resourceGroup: EditorGroup;
  loadingResourcePath: string | null;
  resourceRequestId: number;
  resourceNavigation: ResourceNavigation | null;
  openingArchive: boolean;
  projectPath: string | null;
  projectDirty: boolean;
  canUndo: boolean;
  canRedo: boolean;
  savingProject: boolean;
  error: string | null;
  problems: ProblemEntry[];
  problemsOpen: boolean;
  requestId: number;
  explorerVisible: boolean;
  outlineVisible: boolean;
  explorerWidth: number;
  outlineWidth: number;
  quickOpenVisible: boolean;
  memberOpenVisible: boolean;
  globalSearchVisible: boolean;
  codeSearchVisible: boolean;
  navigation: MemberNavigation | null;
  positionRestore: (CaretPosition & {
    sequence: number;
    descriptor: string;
  }) | null;
  caret: CaretPosition | null;
  caretMember: CaretMember | null;
  history: HistoryEntry[];
  historyIndex: number;
  peek: PeekState | null;
  references: ReferencesState | null;
  revealRequest: { descriptor: string; sequence: number } | null;
  sessionRestored: boolean;
  decompileOptions: DecompileOptions;
  /** Documents decompiled under superseded options; re-fetched on activation. */
  staleDocuments: string[];
  setSourceLanguage: (language: LanguagePreference) => void;
  setDecompileOptions: (patch: Partial<DecompileOptions>) => void;
  chooseArchive: () => Promise<void>;
  openArchive: (path: string) => Promise<void>;
  removeRecentProject: (path: string) => void;
  clearRecentProjects: () => void;
  closeProject: () => Promise<boolean>;
  saveProject: () => Promise<boolean>;
  saveProjectAs: () => Promise<boolean>;
  undo: () => void;
  redo: () => void;
  renameSymbol: (
    descriptor: string,
    state: EditorState,
    symbol: ResolvedSymbol,
    resolver: SourceDefinitionResolver,
    name: string,
  ) => Promise<RenameIssue | null>;
  requestExit: () => Promise<void>;
  selectClass: (descriptor: string, options?: SelectOptions) => Promise<void>;
  openResource: (
    path: string,
    target?: ResourceNavigationTarget,
  ) => Promise<void>;
  closeResource: () => void;
  closeDocument: (descriptor: string, group?: EditorGroup) => void;
  closeActiveDocument: () => void;
  closeOtherDocuments: (descriptor: string, group?: EditorGroup) => void;
  closeAllDocuments: (group?: EditorGroup) => void;
  closeDocumentsToRight: (descriptor: string, group?: EditorGroup) => void;
  reopenClosedTab: () => void;
  moveDocument: (
    source: string,
    target: string | null,
    sourceGroup: EditorGroup,
    targetGroup: EditorGroup,
  ) => void;
  splitDocument: (
    descriptor: string,
    sourceGroup: EditorGroup,
    targetGroup: EditorGroup,
    axis: EditorSplitAxis,
    side: EditorSplitSide,
  ) => void;
  activateDocumentAt: (index: number) => void;
  activateDocument: (descriptor: string, group: EditorGroup) => void;
  focusEditorGroup: (group: EditorGroup) => void;
  splitEditor: (
    descriptor?: string,
    group?: EditorGroup,
    axis?: EditorSplitAxis,
    side?: EditorSplitSide,
  ) => void;
  closeEditorGroup: (group: EditorGroup) => void;
  promotePreview: (descriptor: string, group?: EditorGroup) => void;
  togglePin: (descriptor: string) => void;
  revealInExplorer: (descriptor: string) => void;
  reportError: (message: string) => void;
  clearError: () => void;
  clearProblems: () => void;
  setProblemsOpen: (open: boolean) => void;
  toggleExplorer: () => void;
  toggleOutline: () => void;
  setExplorerWidth: (width: number) => void;
  setOutlineWidth: (width: number) => void;
  setQuickOpenVisible: (visible: boolean) => void;
  setMemberOpenVisible: (visible: boolean) => void;
  setGlobalSearchVisible: (visible: boolean) => void;
  setCodeSearchVisible: (visible: boolean) => void;
  setCaret: (caret: CaretPosition | null, member?: CaretMember | null) => void;
  goBack: () => void;
  goForward: () => void;
  restorePosition: (descriptor: string, position: CaretPosition) => void;
  openPeek: (classDescriptor: string, method: MethodOutline) => Promise<void>;
  closePeek: () => void;
  findReferences: (destination: SymbolDestination, label: string) => Promise<void>;
  closeReferences: () => void;
  restoreSession: () => Promise<void>;
  navigateToMember: (
    member: Omit<MemberNavigation, "sequence">,
    options?: SelectOptions,
  ) => void;
  navigateToDefinition: (destination: SymbolDestination) => Promise<void>;
}

function messageFrom(error: unknown): string {
  return error instanceof Error ? error.message : String(error);
}

let problemSeq = 0;
let resourceNavigationSeq = 0;
const memberResolver = new ArchiveMemberResolver(decompilerClient);
const projectSession = new ProjectSession();
const renameService = new RenameService(projectSession, memberResolver);
let presentationRevision = 0;

/*
 * Drops the oldest unpinned documents past the cache limit. Tab order is the
 * user's — set by opening and by dragging — so the surviving entries keep their
 * relative positions; pinning is what moves a tab, not trimming.
 */
function trimDocuments(documents: SourceDocument[], pinned: string[]): SourceDocument[] {
  const unpinned = documents.filter(
    (document) => !pinned.includes(document.descriptor),
  );
  const excess = unpinned.length - DOCUMENT_LIMIT;
  if (excess <= 0) {
    return documents;
  }
  const dropped = new Set(
    unpinned.slice(0, excess).map((document) => document.descriptor),
  );
  return documents.filter((document) => !dropped.has(document.descriptor));
}

/*
 * Records where the caret is in the stop we are about to leave, so Back (and
 * Forward, on the way out again) returns to that spot instead of the top of
 * the file. Only the entry matching the active document can be stamped.
 */
function stampPosition(
  state: Pick<
    WorkspaceState,
    "history" | "historyIndex" | "caret" | "activeDescriptor" | "editorLayout"
  >,
): HistoryEntry[] {
  const entry = state.history[state.historyIndex];
  if (!entry || !state.caret || entry.descriptor !== state.activeDescriptor) {
    return state.history;
  }
  const history = [...state.history];
  history[state.historyIndex] = {
    ...entry,
    group: state.editorLayout.focused,
    position: state.caret,
  };
  return history;
}

/**
 * The language a class will be read as, or `null` when `auto` has not been
 * told yet — the first request for a class is what discovers it.
 */
export function documentLanguage(
  state: Pick<WorkspaceState, "sourceLanguage" | "detectedLanguages">,
  descriptor: string,
): SourceLanguage | null {
  return state.sourceLanguage === "auto"
    ? (state.detectedLanguages[descriptor] ?? null)
    : state.sourceLanguage;
}

/** Appends an entry, dropping forward entries and consecutive duplicates. */
function pushHistory(
  history: HistoryEntry[],
  historyIndex: number,
  entry: HistoryEntry,
): { history: HistoryEntry[]; historyIndex: number } {
  const base = history.slice(0, historyIndex + 1);
  const last = base[base.length - 1];
  const sameStop =
    last &&
    last.descriptor === entry.descriptor &&
    last.group === entry.group &&
    last.member?.kind === entry.member?.kind &&
    last.member?.name === entry.member?.name &&
    last.member?.descriptor === entry.member?.descriptor;
  if (sameStop) {
    return { history: base, historyIndex: base.length - 1 };
  }
  const next = [...base, entry].slice(-HISTORY_LIMIT);
  return { history: next, historyIndex: next.length - 1 };
}

export const useWorkspace = create<WorkspaceState>((set, get) => ({
  archive: null,
  sourceLanguage: "java",
  recentProjects: recentProjectHistory.load(),
  detectedLanguages: {},
  documents: [],
  closedTabs: [],
  pinned: [],
  editorLayout: EditorLayout.empty(),
  activeDescriptor: null,
  loadingDescriptor: null,
  resourceDocument: null,
  resourceGroup: ROOT_EDITOR_GROUP,
  loadingResourcePath: null,
  resourceRequestId: 0,
  resourceNavigation: null,
  openingArchive: false,
  projectPath: null,
  projectDirty: false,
  canUndo: false,
  canRedo: false,
  savingProject: false,
  error: null,
  problems: [],
  problemsOpen: false,
  requestId: 0,
  explorerVisible: true,
  outlineVisible: true,
  explorerWidth: storedWidth("dexdec.explorerWidth", EXPLORER_DEFAULT_WIDTH, EXPLORER_WIDTH_RANGE),
  outlineWidth: storedWidth("dexdec.outlineWidth", OUTLINE_DEFAULT_WIDTH, OUTLINE_WIDTH_RANGE),
  quickOpenVisible: false,
  memberOpenVisible: false,
  globalSearchVisible: false,
  codeSearchVisible: false,
  navigation: null,
  positionRestore: null,
  caret: null,
  caretMember: null,
  history: [],
  historyIndex: -1,
  peek: null,
  references: null,
  revealRequest: null,
  sessionRestored: false,
  decompileOptions: loadDecompileOptions(),
  staleDocuments: [],

  setSourceLanguage: (sourceLanguage) => {
    const state = get();
    if (state.sourceLanguage === sourceLanguage) {
      return;
    }
    const activeDescriptor = state.activeDescriptor;
    set({
      sourceLanguage,
      loadingDescriptor: null,
      navigation: null,
      peek: null,
    });
    if (activeDescriptor) {
      void get().selectClass(activeDescriptor, { recordHistory: false });
    }
  },

  /*
   * Output settings change the source text, so every cached document is marked
   * stale rather than dropped: tabs survive and re-decompile when activated.
   */
  setDecompileOptions: (patch) => {
    const state = get();
    const decompileOptions = { ...state.decompileOptions, ...patch };
    if (
      decompileOptions.indentWidth === state.decompileOptions.indentWidth &&
      decompileOptions.includeNested === state.decompileOptions.includeNested
    ) {
      return;
    }
    saveDecompileOptions(decompileOptions);
    set({
      decompileOptions,
      staleDocuments: state.documents.map((document) => document.descriptor),
      loadingDescriptor: null,
      navigation: null,
      peek: null,
    });
    if (state.activeDescriptor) {
      void get().selectClass(state.activeDescriptor, { recordHistory: false });
    }
  },

  chooseArchive: async () => {
    try {
      const path = await decompilerClient.chooseArchive();
      if (path) {
        await get().openArchive(path);
      }
    } catch (error) {
      set({ error: messageFrom(error) });
    }
  },

  openArchive: async (path) => {
    let activity: ActivityHandle | null = null;
    try {
      // Inside the guarded region: a confirmation that fails is an error to
      // report, not a silent refusal to open anything.
      if (!(await confirmProjectReplacement(get()))) {
        return;
      }
      const current = get();
      if (current.loadingDescriptor || current.peek?.state === "loading") {
        if (current.archive) {
          void decompilerClient.cancelRequest(
            current.archive.sessionId,
            current.requestId,
          );
        }
        set({ requestId: current.requestId + 1, loadingDescriptor: null, peek: null });
      }
      ActivityCenter.cancelScope("references");
      activity = ActivityCenter.begin({
        kind: "archive",
        title: t("activity.openingArchive"),
        detail: path.split(/[/\\]/).at(-1) ?? path,
        scope: "archive",
      });
      set({ openingArchive: true, error: null });
      const snapshot = path.toLocaleLowerCase().endsWith(".dexdb")
        ? await projectClient.load(path)
        : null;
      const archivePath = snapshot?.archivePath ?? path;
      const rawArchive = await decompilerClient.openArchive(archivePath);
      if (current.archive?.sessionId !== undefined) {
        await decompilerClient
          .closeArchive(current.archive.sessionId)
          .catch(() => undefined);
      }
      if (snapshot) {
        projectSession.activateSnapshot(snapshot);
      } else {
        projectSession.activateArchive(archivePath);
      }
      presentationRevision += 1;
      const archive = renameService.activateArchive(rawArchive);
      const recentProjects = recentProjectHistory.remember(path);
      set({
        archive,
        recentProjects,
        documents: [],
        // Descriptors are only unique within an archive.
        detectedLanguages: {},
        closedTabs: [],
        pinned: [],
        editorLayout: EditorLayout.empty(),
        activeDescriptor: null,
        loadingDescriptor: null,
        resourceDocument: null,
        resourceGroup: ROOT_EDITOR_GROUP,
        loadingResourcePath: null,
        resourceRequestId: 0,
        resourceNavigation: null,
        openingArchive: false,
        projectPath: projectSession.databasePath,
        projectDirty: projectSession.dirty,
        canUndo: projectSession.canUndo,
        canRedo: projectSession.canRedo,
        savingProject: false,
        requestId: 0,
        navigation: null,
        caret: null,
        caretMember: null,
        history: [],
        historyIndex: -1,
        peek: null,
        references: null,
        problems: [],
        problemsOpen: false,
        quickOpenVisible: false,
        memberOpenVisible: false,
        globalSearchVisible: false,
        codeSearchVisible: false,
      });
      activity.complete(archive.name);
      void new ApplicationIconService(archive)
        .thumbnail()
        .then((iconData) => {
          if (!iconData) return;
          set({
            recentProjects: recentProjectHistory.setIcon(path, iconData),
          });
        })
        .catch(() => {
          /* Archives without a readable application icon use the file icon. */
        });
    } catch (error) {
      activity?.fail(error);
      set({ openingArchive: false, error: messageFrom(error) });
    }
  },

  removeRecentProject: (path) => {
    set({ recentProjects: recentProjectHistory.remove(path) });
  },

  clearRecentProjects: () => {
    set({ recentProjects: recentProjectHistory.clear() });
  },

  closeProject: async () => {
    const state = get();
    const archive = state.archive;
    if (!archive) {
      return true;
    }
    try {
      if (!(await confirmProjectReplacement(state))) {
        return false;
      }
      const requestId = state.requestId + 1;
      ActivityCenter.cancelScope("references");
      projectSession.close();
      renameService.closeArchive();
      presentationRevision += 1;
      set({
        archive: null,
        detectedLanguages: {},
        documents: [],
        closedTabs: [],
        pinned: [],
        editorLayout: EditorLayout.empty(),
        activeDescriptor: null,
        loadingDescriptor: null,
        resourceDocument: null,
        resourceGroup: ROOT_EDITOR_GROUP,
        loadingResourcePath: null,
        resourceRequestId: state.resourceRequestId + 1,
        resourceNavigation: null,
        openingArchive: false,
        projectPath: null,
        projectDirty: false,
        canUndo: false,
        canRedo: false,
        savingProject: false,
        error: null,
        problems: [],
        problemsOpen: false,
        requestId,
        quickOpenVisible: false,
        memberOpenVisible: false,
        globalSearchVisible: false,
        codeSearchVisible: false,
        navigation: null,
        positionRestore: null,
        caret: null,
        caretMember: null,
        history: [],
        historyIndex: -1,
        peek: null,
        references: null,
        revealRequest: null,
        staleDocuments: [],
      });
      try {
        localStorage.removeItem(SESSION_STORAGE_KEY);
      } catch {
        /* storage unavailable */
      }
      void decompilerClient.closeArchive(archive.sessionId).catch((error) => {
        const current = get();
        if (current.archive || current.requestId !== requestId) return;
        set({ error: messageFrom(error) });
      });
      return true;
    } catch (error) {
      if (get().archive?.sessionId === archive.sessionId) {
        set({ error: messageFrom(error) });
      }
      return false;
    }
  },

  saveProject: () => persistProject(false),
  saveProjectAs: () => persistProject(true),

  undo: () => {
    if (!projectSession.undo()) {
      return;
    }
    set({
      ...projectStatus(),
      archive: renameService.presentArchive(),
      peek: null,
      navigation: null,
    });
    void refreshProjectPresentation(++presentationRevision);
  },

  redo: () => {
    if (!projectSession.redo()) {
      return;
    }
    set({
      ...projectStatus(),
      archive: renameService.presentArchive(),
      peek: null,
      navigation: null,
    });
    void refreshProjectPresentation(++presentationRevision);
  },

  renameSymbol: async (descriptor, editorState, symbol, resolver, name) => {
    const state = get();
    const archive = state.archive;
    const document = state.documents.find(
      (entry) => entry.descriptor === descriptor,
    );
    if (!archive || !document) {
      return "unresolved";
    }
    const prepared = await renameService.prepare(
      archive.sessionId,
      document,
      archive,
      state.documents,
      editorState,
      symbol,
      resolver,
    );
    if (!prepared) {
      return "unresolved";
    }
    const clearAlias = name.length === 0;
    const effectiveName = clearAlias ? prepared.target.originalName : name;
    if (!clearAlias) {
      const issue = await renameService.validate(
        archive.sessionId,
        prepared,
        effectiveName,
        document,
        archive,
        state.documents,
        editorState,
      );
      if (issue) {
        return issue;
      }
    }
    const current = get();
    if (
      current.archive?.sessionId !== archive.sessionId ||
      !current.documents.some(
        (entry) =>
          entry.descriptor === descriptor &&
          entry.source === document.source,
      )
    ) {
      return "unresolved";
    }
    if (!projectSession.rename(prepared.target, effectiveName)) {
      return null;
    }
    const revision = ++presentationRevision;
    set({
      ...projectStatus(),
      archive: renameService.presentArchive(),
      peek: null,
      navigation: null,
      error: null,
    });
    await refreshProjectPresentation(revision);
    return null;
  },

  requestExit: async () => {
    try {
      if (!(await confirmProjectReplacement(get()))) {
        await projectClient.cancelExit();
        return;
      }
      await projectClient.confirmExit();
    } catch (error) {
      set({ error: messageFrom(error) });
      await projectClient.cancelExit();
    }
  },

  selectClass: async (descriptor, options) => {
    const recordHistory = options?.recordHistory ?? true;
    ActivityCenter.cancelScope("references");
    const state = get();
    if (!state.archive) {
      return;
    }
    const sessionId = state.archive.sessionId;
    const opened = new EditorLayout(state.editorLayout).open(descriptor, {
      group: options?.group,
      preview: options?.preview ?? true,
    });
    const documents = opened.replacedPreview &&
      !new EditorLayout(opened.state).contains(opened.replacedPreview)
      ? state.documents.filter(
          (document) => document.descriptor !== opened.replacedPreview,
        )
      : state.documents;
    const historyPatch = recordHistory
      ? pushHistory(stampPosition(state), state.historyIndex, {
          descriptor,
          group: opened.state.focused,
        })
      : {};
    const cached = state.staleDocuments.includes(descriptor)
      ? undefined
      : documents.find(
          (document) =>
            document.descriptor === descriptor &&
            document.language === documentLanguage(state, descriptor),
        );
    if (cached) {
      set({
        documents,
        editorLayout: opened.state,
        activeDescriptor: descriptor,
        loadingDescriptor: null,
        resourceDocument: null,
        loadingResourcePath: null,
        resourceNavigation: null,
        error: null,
        navigation: null,
        peek: null,
        ...historyPatch,
      });
      return;
    }

    const requestId = state.requestId + 1;
    const language = state.sourceLanguage;
    set({
      documents,
      editorLayout: opened.state,
      activeDescriptor: descriptor,
      loadingDescriptor: descriptor,
      resourceDocument: null,
      loadingResourcePath: null,
      resourceNavigation: null,
      requestId,
      error: null,
      navigation: null,
      peek: null,
      ...historyPatch,
    });
    try {
      const rawDocument = await decompilerClient.decompileClass(
        sessionId,
        requestId,
        descriptor,
        language,
        state.decompileOptions,
      );
      let current = get();
      if (
        current.archive?.sessionId !== sessionId ||
        current.requestId !== requestId ||
        current.sourceLanguage !== language
      ) {
        // Superseded by a newer request. If the selection still points at
        // this class and nothing is fetching it, the newer request was a
        // same-descriptor race (or was itself superseded) — re-issue so the
        // active tab never strands on an uncached document.
        if (
          current.activeDescriptor === descriptor &&
          current.loadingDescriptor === null &&
          !current.documents.some(
            (entry) =>
              entry.descriptor === descriptor &&
              entry.language === documentLanguage(current, descriptor),
          )
        ) {
          void current.selectClass(descriptor, { recordHistory: false });
        }
        return;
      }
      const document = await renameService.presentDocument(
        sessionId,
        rawDocument,
        current.documents,
      );
      current = get();
      if (
        current.archive?.sessionId !== sessionId ||
        current.requestId !== requestId ||
        current.sourceLanguage !== language
      ) {
        return;
      }
      const documents = trimDocuments(
        [
          ...current.documents.filter(
            (candidate) => candidate.descriptor !== document.descriptor,
          ),
          document,
        ],
        current.pinned,
      );
      const editorLayout = new EditorLayout(current.editorLayout).retain(
        new Set(documents.map((entry) => entry.descriptor)),
      );
      set({
        documents,
        editorLayout,
        loadingDescriptor: null,
        // Only an `auto` request says anything about the class: asking for one
        // language gets that language back whatever the class was written in.
        detectedLanguages:
          language === "auto"
            ? {
                ...current.detectedLanguages,
                [document.descriptor]: document.language,
              }
            : current.detectedLanguages,
        staleDocuments: current.staleDocuments.filter(
          (entry) => entry !== document.descriptor,
        ),
      });
    } catch (error) {
      const current = get();
      if (
        current.archive?.sessionId === sessionId &&
        current.requestId === requestId
      ) {
        const message = messageFrom(error);
        if (message.includes("superseded")) {
          set({ loadingDescriptor: null });
          if (
            current.activeDescriptor === descriptor &&
            !current.documents.some(
              (entry) =>
                entry.descriptor === descriptor &&
                entry.language === documentLanguage(current, descriptor),
            )
          ) {
            void get().selectClass(descriptor, { recordHistory: false });
          }
        } else {
          set((state) => ({
            loadingDescriptor: null,
            error: message,
            problems: [
              ...state.problems,
              { id: ++problemSeq, descriptor, message, at: Date.now() },
            ].slice(-PROBLEMS_LIMIT),
          }));
        }
      }
    }
  },

  openResource: async (path, target) => {
    let state = get();
    if (!state.archive) {
      return;
    }
    const sessionId = state.archive.sessionId;
    if (state.loadingDescriptor || state.peek?.state === "loading") {
      void decompilerClient.cancelRequest(sessionId, state.requestId);
      set({ requestId: state.requestId + 1, loadingDescriptor: null, peek: null });
      state = get();
    }
    const resourceNavigation = target
      ? { sequence: ++resourceNavigationSeq, path, target }
      : null;
    if (state.resourceDocument?.path === path && !state.loadingResourcePath) {
      set({ resourceNavigation });
      return;
    }
    const resourceRequestId = state.resourceRequestId + 1;
    set({
      activeDescriptor: null,
      loadingDescriptor: null,
      resourceDocument: null,
      resourceGroup: state.editorLayout.focused,
      loadingResourcePath: path,
      resourceRequestId,
      resourceNavigation,
      navigation: null,
      peek: null,
      references: null,
      error: null,
    });
    try {
      const resourceDocument = await decompilerClient.readResource(sessionId, path);
      const current = get();
      if (
        current.archive?.sessionId !== sessionId ||
        current.resourceRequestId !== resourceRequestId ||
        current.loadingResourcePath !== path
      ) {
        return;
      }
      set({ resourceDocument, loadingResourcePath: null });
    } catch (error) {
      const current = get();
      if (
        current.archive?.sessionId === sessionId &&
        current.resourceRequestId === resourceRequestId
      ) {
        set({ loadingResourcePath: null, error: messageFrom(error) });
      }
    }
  },

  closeResource: () => {
    set((state) => ({
      activeDescriptor: state.editorLayout.active[state.resourceGroup],
      resourceDocument: null,
      loadingResourcePath: null,
      resourceNavigation: null,
      resourceRequestId: state.resourceRequestId + 1,
    }));
  },

  closeDocument: (descriptor, requestedGroup) => {
    const state = get();
    const closed = state.documents.find(
      (document) => document.descriptor === descriptor,
    );
    if (!closed) return;
    const layout = new EditorLayout(state.editorLayout);
    const group = requestedGroup ?? layout.groupOf(descriptor);
    const editorLayout = layout.close(group, descriptor);
    const stillOpen = new EditorLayout(editorLayout).contains(descriptor);
    set({
      documents: stillOpen
        ? state.documents
        : state.documents.filter((document) => document.descriptor !== descriptor),
      editorLayout,
      closedTabs: [...state.closedTabs, closed].slice(-CLOSED_TABS_LIMIT),
      pinned: stillOpen
        ? state.pinned
        : state.pinned.filter((entry) => entry !== descriptor),
      activeDescriptor: editorLayout.active[editorLayout.focused],
      navigation: null,
      peek:
        !stillOpen && state.peek?.classDescriptor === descriptor
          ? null
          : state.peek,
    });
  },

  closeActiveDocument: () => {
    const {
      activeDescriptor,
      closeDocument,
      closeResource,
      loadingResourcePath,
      resourceDocument,
    } = get();
    if (activeDescriptor) {
      closeDocument(activeDescriptor, get().editorLayout.focused);
    } else if (resourceDocument || loadingResourcePath) {
      closeResource();
    }
  },

  closeOtherDocuments: (descriptor, requestedGroup) =>
    set((state) => {
      const layout = new EditorLayout(state.editorLayout);
      const group = requestedGroup ?? layout.groupOf(descriptor);
      const closed = new Set(
        layout.tabsIn(group).filter(
          (candidate) =>
            candidate !== descriptor && !state.pinned.includes(candidate),
        ),
      );
      if (!closed.size) return state;
      const editorLayout = layout.remove(group, closed);
      const nextLayout = new EditorLayout(editorLayout);
      const closedDocuments = state.documents.filter((document) =>
        closed.has(document.descriptor),
      );
      return {
        documents: state.documents.filter(
          (document) =>
            !closed.has(document.descriptor) || nextLayout.contains(document.descriptor),
        ),
        editorLayout,
        closedTabs: [...state.closedTabs, ...closedDocuments].slice(
          -CLOSED_TABS_LIMIT,
        ),
        activeDescriptor: editorLayout.active[editorLayout.focused],
        navigation: null,
        peek: state.peek && nextLayout.contains(state.peek.classDescriptor)
          ? state.peek
          : null,
      };
    }),

  closeDocumentsToRight: (descriptor, requestedGroup) =>
    set((state) => {
      const layout = new EditorLayout(state.editorLayout);
      const group = requestedGroup ?? layout.groupOf(descriptor);
      const groupDocuments = layout.tabsIn(group);
      const index = groupDocuments.indexOf(descriptor);
      const closed = new Set(
        groupDocuments
          .slice(index + 1)
          .filter((candidate) => !state.pinned.includes(candidate)),
      );
      if (index < 0 || !closed.size) return state;
      const closedDocuments = state.documents.filter((document) =>
        closed.has(document.descriptor),
      );
      const editorLayout = layout.remove(group, closed);
      const nextLayout = new EditorLayout(editorLayout);
      return {
        documents: state.documents.filter(
          (document) =>
            !closed.has(document.descriptor) || nextLayout.contains(document.descriptor),
        ),
        editorLayout,
        activeDescriptor: editorLayout.active[editorLayout.focused],
        closedTabs: [...state.closedTabs, ...closedDocuments].slice(
          -CLOSED_TABS_LIMIT,
        ),
        navigation: closed.has(state.navigation?.classDescriptor ?? "")
          ? null
          : state.navigation,
      };
    }),

  closeAllDocuments: (requestedGroup) =>
    set((state) => {
      if (!requestedGroup) {
        return {
          documents: [],
          editorLayout: EditorLayout.empty(),
          closedTabs: [...state.closedTabs, ...state.documents].slice(
            -CLOSED_TABS_LIMIT,
          ),
          pinned: [],
          activeDescriptor: null,
          resourceDocument: null,
          loadingResourcePath: null,
          resourceRequestId: state.resourceRequestId + 1,
          navigation: null,
          peek: null,
        };
      }
      const layout = new EditorLayout(state.editorLayout);
      const closed = new Set(layout.tabsIn(requestedGroup));
      const editorLayout = layout.remove(requestedGroup, closed);
      const nextLayout = new EditorLayout(editorLayout);
      const closedDocuments = state.documents.filter((document) =>
        closed.has(document.descriptor),
      );
      return {
        documents: state.documents.filter(
          (document) =>
            !closed.has(document.descriptor) || nextLayout.contains(document.descriptor),
        ),
        editorLayout,
        closedTabs: [...state.closedTabs, ...closedDocuments].slice(
          -CLOSED_TABS_LIMIT,
        ),
        pinned: state.pinned.filter((descriptor) => nextLayout.contains(descriptor)),
        activeDescriptor: editorLayout.active[editorLayout.focused],
        resourceDocument:
          state.resourceGroup === requestedGroup ? null : state.resourceDocument,
        loadingResourcePath:
          state.resourceGroup === requestedGroup ? null : state.loadingResourcePath,
        resourceRequestId:
          state.resourceGroup === requestedGroup
            ? state.resourceRequestId + 1
            : state.resourceRequestId,
        navigation: null,
        peek: state.peek && nextLayout.contains(state.peek.classDescriptor)
          ? state.peek
          : null,
      };
    }),

  revealInExplorer: (descriptor) =>
    set((state) => ({
      explorerVisible: true,
      revealRequest: {
        descriptor,
        sequence: (state.revealRequest?.sequence ?? 0) + 1,
      },
    })),

  reopenClosedTab: () => {
    const state = get();
    const document = state.closedTabs[state.closedTabs.length - 1];
    if (!document || !state.archive) {
      return;
    }
    const documents = trimDocuments(
      [
        ...state.documents.filter(
          (candidate) => candidate.descriptor !== document.descriptor,
        ),
        document,
      ],
      state.pinned,
    );
    const historyPatch = pushHistory(stampPosition(state), state.historyIndex, {
      descriptor: document.descriptor,
      group: state.editorLayout.focused,
    });
    const opened = new EditorLayout(state.editorLayout).open(document.descriptor, {
      group: state.editorLayout.focused,
      preview: false,
    });
    const editorLayout = new EditorLayout(opened.state).retain(
      new Set(documents.map((entry) => entry.descriptor)),
    );
    set({
      documents,
      editorLayout,
      closedTabs: state.closedTabs.slice(0, -1),
      activeDescriptor: document.descriptor,
      navigation: null,
      ...historyPatch,
    });
    if (document.language !== documentLanguage(state, document.descriptor)) {
      void get().selectClass(document.descriptor, { recordHistory: false });
    }
  },

  /** Moves one editor tab; the decompiled document remains a shared cache entry. */
  moveDocument: (source, target, sourceGroup, targetGroup) =>
    set((state) => {
      const editorLayout = new EditorLayout(state.editorLayout).move(
        source,
        sourceGroup,
        targetGroup,
        target,
      );
      const layout = new EditorLayout(editorLayout);
      return {
        editorLayout,
        activeDescriptor: source,
        resourceGroup: layout.has(state.resourceGroup)
          ? state.resourceGroup
          : editorLayout.focused,
      };
    }),

  splitDocument: (descriptor, sourceGroup, targetGroup, axis, side) =>
    set((state) => {
      const editorLayout = new EditorLayout(state.editorLayout).splitMove(
        descriptor,
        sourceGroup,
        targetGroup,
        axis,
        side,
      );
      return { editorLayout, activeDescriptor: descriptor };
    }),

  /** Tab shortcuts: 0-based, with the last index meaning "the last tab". */
  activateDocumentAt: (index) => {
    const { documents, editorLayout, selectClass } = get();
    const tabs = new EditorLayout(editorLayout).tabsIn(editorLayout.focused);
    const descriptor = index < 0 ? tabs.at(-1) : tabs[index];
    if (descriptor && documents.some((document) => document.descriptor === descriptor)) {
      void selectClass(descriptor, { group: editorLayout.focused });
    }
  },

  activateDocument: (descriptor, group) => {
    void get().selectClass(descriptor, { group });
  },

  focusEditorGroup: (group) =>
    set((state) => ({
      editorLayout: new EditorLayout(state.editorLayout).focus(group),
      activeDescriptor:
        state.resourceDocument && state.resourceGroup === group
          ? null
          : state.editorLayout.active[group],
      caret: null,
      caretMember: null,
    })),

  splitEditor: (descriptor, requestedGroup, axis = "horizontal", side = "after") =>
    set((state) => {
      const group = requestedGroup ?? state.editorLayout.focused;
      const target = descriptor ?? state.editorLayout.active[group] ?? null;
      const editorLayout = new EditorLayout(state.editorLayout).split(
        group,
        target,
        axis,
        side,
      );
      return {
        editorLayout,
        activeDescriptor: editorLayout.active[editorLayout.focused],
      };
    }),

  closeEditorGroup: (group) =>
    set((state) => {
      const layout = new EditorLayout(state.editorLayout);
      if (layout.groupCount() === 1) return state;
      const closed = new Set(layout.tabsIn(group));
      const editorLayout = layout.closeGroup(group);
      const nextLayout = new EditorLayout(editorLayout);
      const closedDocuments = state.documents.filter((document) =>
        closed.has(document.descriptor),
      );
      return {
        documents: state.documents.filter(
          (document) =>
            !closed.has(document.descriptor) || nextLayout.contains(document.descriptor),
        ),
        editorLayout,
        activeDescriptor: editorLayout.active[editorLayout.focused],
        resourceGroup: nextLayout.has(state.resourceGroup)
          ? state.resourceGroup
          : editorLayout.focused,
        resourceDocument:
          state.resourceGroup === group ? null : state.resourceDocument,
        loadingResourcePath:
          state.resourceGroup === group ? null : state.loadingResourcePath,
        resourceRequestId:
          state.resourceGroup === group
            ? state.resourceRequestId + 1
            : state.resourceRequestId,
        closedTabs: [...state.closedTabs, ...closedDocuments].slice(
          -CLOSED_TABS_LIMIT,
        ),
        pinned: state.pinned.filter((descriptor) => nextLayout.contains(descriptor)),
        navigation: null,
      };
    }),

  promotePreview: (descriptor, group) =>
    set((state) => ({
      editorLayout: new EditorLayout(state.editorLayout).promote(descriptor, group),
    })),

  togglePin: (descriptor) =>
    set((state) => {
      const pinning = !state.pinned.includes(descriptor);
      const pinned = pinning
        ? [...state.pinned, descriptor]
        : state.pinned.filter((entry) => entry !== descriptor);
      const retained = trimDocuments(state.documents, pinned);
      const layout = pinning
        ? new EditorLayout(state.editorLayout).promote(descriptor)
        : state.editorLayout;
      const retainedLayout = new EditorLayout(layout).retain(
        new Set(retained.map((entry) => entry.descriptor)),
      );
      return {
        pinned,
        documents: retained,
        editorLayout: new EditorLayout(retainedLayout).orderPinned(new Set(pinned)),
      };
    }),

  clearProblems: () => set({ problems: [], problemsOpen: false }),
  setProblemsOpen: (open) =>
    set({
      problemsOpen: open,
      ...(open ? { references: null, codeSearchVisible: false } : {}),
    }),

  reportError: (error) => set({ error }),
  clearError: () => set({ error: null }),
  toggleExplorer: () => set((state) => ({ explorerVisible: !state.explorerVisible })),
  toggleOutline: () => set((state) => ({ outlineVisible: !state.outlineVisible })),
  setExplorerWidth: (width) => {
    const explorerWidth = clamp(width, EXPLORER_WIDTH_RANGE);
    try {
      localStorage.setItem("dexdec.explorerWidth", String(explorerWidth));
    } catch {
      /* storage unavailable */
    }
    set({ explorerWidth });
  },
  setOutlineWidth: (width) => {
    const outlineWidth = clamp(width, OUTLINE_WIDTH_RANGE);
    try {
      localStorage.setItem("dexdec.outlineWidth", String(outlineWidth));
    } catch {
      /* storage unavailable */
    }
    set({ outlineWidth });
  },
  setQuickOpenVisible: (visible) => set({ quickOpenVisible: visible }),
  setMemberOpenVisible: (visible) => set({ memberOpenVisible: visible }),
  setGlobalSearchVisible: (visible) => set({ globalSearchVisible: visible }),
  setCodeSearchVisible: (visible) =>
    set({
      codeSearchVisible: visible,
      ...(visible ? { references: null, problemsOpen: false } : {}),
    }),
  setCaret: (caret, member = null) =>
    set((state) => {
      const sameCaret =
        state.caret?.line === caret?.line && state.caret?.column === caret?.column;
      const sameMember =
        state.caretMember?.kind === member?.kind &&
        state.caretMember?.name === member?.name &&
        state.caretMember?.arity === member?.arity;
      if (sameCaret && sameMember) {
        return state;
      }
      return { caret, caretMember: member };
    }),

  goBack: () => {
    const state = get();
    if (state.historyIndex <= 0) {
      return;
    }
    const history = stampPosition(state);
    const index = state.historyIndex - 1;
    set({ history, historyIndex: index });
    void applyHistoryEntry(history[index]);
  },

  goForward: () => {
    const state = get();
    if (state.historyIndex >= state.history.length - 1) {
      return;
    }
    const history = stampPosition(state);
    const index = state.historyIndex + 1;
    set({ history, historyIndex: index });
    void applyHistoryEntry(history[index]);
  },

  restorePosition: (descriptor, position) =>
    set((state) => ({
      positionRestore: {
        ...position,
        descriptor,
        sequence: (state.positionRestore?.sequence ?? 0) + 1,
      },
    })),

  openPeek: async (classDescriptor, method) => {
    const state = get();
    if (!state.archive || !method.hasCode) {
      return;
    }
    const requestId = state.requestId + 1;
    const sessionId = state.archive.sessionId;
    const language = state.sourceLanguage;
    set({
      requestId,
      peek: {
        classDescriptor,
        name: method.originalName ?? method.name,
        descriptor: method.descriptor,
        displaySignature: method.displaySignature,
        // Highlighting needs a language before the answer arrives; the class
        // is already open, so read it off the document it is being peeked from.
        language:
          documentLanguage(state, classDescriptor) ??
          state.documents.find(
            (document) => document.descriptor === classDescriptor,
          )?.language ??
          "kotlin",
        state: "loading",
        source: null,
        elapsedMs: null,
        error: null,
      },
    });
    try {
      const document = await decompilerClient.decompileMethod(
        sessionId,
        requestId,
        {
          class: classDescriptor,
          method: method.originalName ?? method.name,
          descriptor: method.descriptor,
        },
        state.sourceLanguage,
        state.decompileOptions,
      );
      const current = get();
      if (
        current.archive?.sessionId !== sessionId ||
        current.sourceLanguage !== language ||
        current.peek?.classDescriptor !== classDescriptor ||
        current.peek.descriptor !== method.descriptor
      ) {
        return;
      }
      set({
        peek: {
          ...current.peek,
          language: document.language,
          state: document.source != null ? "ready" : "error",
          source: document.source,
          elapsedMs: document.elapsedMs,
          error: document.source != null ? null : "No source recovered",
        },
      });
    } catch (error) {
      const current = get();
      if (!current.peek) {
        return;
      }
      set({
        peek: {
          ...current.peek,
          state: "error",
          source: null,
          error: messageFrom(error),
        },
      });
    }
  },

  closePeek: () => {
    const state = get();
    if (state.peek?.state === "loading") {
      if (state.archive) {
        void decompilerClient.cancelRequest(
          state.archive.sessionId,
          state.requestId,
        );
      }
      set({ requestId: state.requestId + 1, peek: null });
    } else {
      set({ peek: null });
    }
  },

  findReferences: async (destination, label) => {
    if (destination.kind === "local") {
      return;
    }
    ActivityCenter.cancelScope("references");
    let state = get();
    if (state.loadingDescriptor || state.peek?.state === "loading") {
      if (state.archive) {
        void decompilerClient.cancelRequest(
          state.archive.sessionId,
          state.requestId,
        );
      }
      set({ requestId: state.requestId + 1, loadingDescriptor: null, peek: null });
      state = get();
    }
    if (!state.archive) {
      return;
    }
    const sessionId = state.archive.sessionId;
    const sequence = (state.references?.sequence ?? 0) + 1;
    const requestId = state.requestId + 1;
    set({
      requestId,
      references: {
        sequence,
        label,
        state: "loading",
        locations: [],
        elapsedMs: null,
        error: null,
      },
      peek: null,
      problemsOpen: false,
      codeSearchVisible: false,
    });
    const activity = ActivityCenter.begin({
      kind: "references",
      title: t("activity.findingReferences"),
      detail: label,
      scope: "references",
      cancellable: true,
      onCancel: () => {
        void decompilerClient.cancelRequest(sessionId, requestId);
        const current = get();
        if (current.references?.sequence === sequence) {
          set({ requestId: requestId + 1, references: null });
        }
      },
    });

    let target: ReferenceTarget | null;
    try {
      target = destination.kind === "class"
        ? destination
        : await memberResolver.referenceTarget(
            state.archive.sessionId,
            destination,
            state.documents,
          );
      const current = get();
      if (
        current.archive?.sessionId !== state.archive.sessionId ||
        current.requestId !== requestId ||
        current.references?.sequence !== sequence
      ) {
        activity.cancel();
        return;
      }
      if (!target) {
        activity.fail(t("references.ambiguous"));
        set({
          references: {
            ...current.references,
            state: "error",
            error: t("references.ambiguous"),
          },
        });
        return;
      }
    } catch (error) {
      activity.fail(error);
      const current = get();
      if (current.references?.sequence === sequence) {
        set({
          references: {
            ...current.references,
            state: "error",
            error: messageFrom(error),
          },
        });
      }
      return;
    }

    try {
      const results = await decompilerClient.findReferences(
        state.archive.sessionId,
        requestId,
        target,
      );
      const current = get();
      if (
        current.archive?.sessionId !== state.archive.sessionId ||
        current.requestId !== requestId ||
        current.references?.sequence !== sequence
      ) {
        activity.cancel();
        return;
      }
      set({
        references: {
          ...current.references,
          state: "ready",
          locations: renameService.presentReferenceLocations(results.locations),
          elapsedMs: results.elapsedMs,
          error: null,
        },
      });
      activity.complete(`${results.locations.length}`);
    } catch (error) {
      const current = get();
      if (current.references?.sequence !== sequence) {
        activity.cancel();
        return;
      }
      activity.fail(error);
      set({
        references: {
          ...current.references,
          state: "error",
          error: messageFrom(error),
        },
      });
    }
  },

  closeReferences: () => {
    ActivityCenter.cancelScope("references");
    set({ references: null });
  },

  restoreSession: async () => {
    if (get().sessionRestored) {
      return;
    }
    set({ sessionRestored: true });
    let raw: string | null = null;
    try {
      raw = localStorage.getItem(SESSION_STORAGE_KEY);
    } catch {
      return;
    }
    if (!raw) {
      return;
    }
    try {
      const session = JSON.parse(raw) as {
        path?: string;
        tabs?: string[];
        active?: string | null;
        pinned?: string[];
        language?: LanguagePreference;
        editorLayout?: EditorLayoutState;
      };
      if (!session.path) {
        return;
      }
      await get().openArchive(session.path);
      if (!get().archive) {
        return;
      }
      if (session.language === "kotlin") {
        set({ sourceLanguage: "kotlin" });
      } else if (session.language === "auto" || session.language === "java") {
        set({ sourceLanguage: "java" });
      }
      if (session.pinned?.length) {
        set({ pinned: session.pinned });
      }
      // A session may outlive the archive that produced it (same path,
      // different file) — skip descriptors the archive no longer contains.
      const known = new Set(
        get().archive!.classes.map((entry) => entry.descriptor),
      );
      const savedTabs = session.editorLayout?.tabs;
      let restoredGroup = ROOT_EDITOR_GROUP;
      if (savedTabs) {
        const restored = EditorLayout.restore(session.editorLayout);
        restoredGroup = restored.focused;
        const groups = new EditorLayout(restored).groups();
        set({
          editorLayout: {
            ...restored,
            tabs: Object.fromEntries(groups.map((group) => [group, []])),
            active: Object.fromEntries(groups.map((group) => [group, null])),
            preview: Object.fromEntries(groups.map((group) => [group, null])),
          },
        });
        for (const group of groups) {
          for (const descriptor of restored.tabs[group] ?? []) {
            if (known.has(descriptor)) {
              await get().selectClass(descriptor, {
                recordHistory: false,
                group,
                preview: false,
              });
            }
          }
        }
        for (const group of groups) {
          const descriptor = restored.active[group];
          if (descriptor && known.has(descriptor)) {
            await get().selectClass(descriptor, {
              recordHistory: false,
              group,
              preview: false,
            });
          }
        }
      } else {
        for (const descriptor of session.tabs ?? []) {
          if (known.has(descriptor)) {
            await get().selectClass(descriptor, {
              recordHistory: false,
              group: ROOT_EDITOR_GROUP,
              preview: false,
            });
          }
        }
      }
      if (session.active && known.has(session.active)) {
        await get().selectClass(session.active, {
          recordHistory: true,
          group: restoredGroup,
        });
      }
    } catch {
      /* a stale session must never block startup */
    }
  },

  navigateToMember: (member, options) => {
    member = MemberTargetResolver.canonical(get().documents, member);
    const recordHistory = options?.recordHistory ?? true;
    const historyPatch = recordHistory
      ? pushHistory(stampPosition(get()), get().historyIndex, {
          descriptor: member.classDescriptor,
          group: options?.group ?? get().editorLayout.focused,
          member: {
            kind: member.kind,
            name: member.name,
            descriptor: member.descriptor,
          },
        })
      : {};
    set((state) => ({
      navigation: {
        ...member,
        sequence: (state.navigation?.sequence ?? 0) + 1,
      },
      ...historyPatch,
    }));
  },

  navigateToDefinition: async (destination) => {
    if (destination.kind === "local") {
      return;
    }
    const state = get();
    if (!state.archive) {
      return;
    }
    if (!state.archive.classes.some(
      (candidate) => candidate.descriptor === destination.classDescriptor,
    )) {
      return;
    }
    // Stamp the origin before the active document changes: once the target
    // class is selected, the entry being left no longer matches it.
    set({ history: stampPosition(state) });
    if (destination.kind === "class") {
      await state.selectClass(destination.classDescriptor);
      return;
    }

    const target = await memberResolver.resolve(
      state.archive.sessionId,
      destination,
      state.documents,
    );
    const current = get();
    if (current.archive?.sessionId !== state.archive.sessionId) {
      return;
    }
    if (!target) {
      return;
    }
    if (!current.archive.classes.some(
      (candidate) => candidate.descriptor === target.classDescriptor,
    )) {
      return;
    }
    await current.selectClass(target.classDescriptor, { recordHistory: false });
    const selected = get();
    if (
      selected.archive?.sessionId === state.archive.sessionId &&
      selected.activeDescriptor === target.classDescriptor
    ) {
      selected.navigateToMember(target);
    }
  },
}));

function projectStatus(): Pick<
  WorkspaceState,
  "projectPath" | "projectDirty" | "canUndo" | "canRedo"
> {
  return {
    projectPath: projectSession.databasePath,
    projectDirty: projectSession.dirty,
    canUndo: projectSession.canUndo,
    canRedo: projectSession.canRedo,
  };
}

class MemberTargetResolver {
  static canonical(
    documents: SourceDocument[],
    member: Omit<MemberNavigation, "sequence">,
  ): Omit<MemberNavigation, "sequence"> {
    const outline = documents.find(
      (document) => document.descriptor === member.classDescriptor,
    )?.outline;
    if (!outline) return member;
    const candidates = member.kind === "field"
      ? outline.fields.filter((field) => field.descriptor === member.descriptor)
      : outline.methods.filter((method) => method.descriptor === member.descriptor);
    const declaration = candidates.find(
      (candidate) =>
        candidate.name === member.name ||
        candidate.originalName === member.name,
    ) ?? (candidates.length === 1 ? candidates[0] : null);
    return declaration
      ? { ...member, name: declaration.originalName ?? declaration.name }
      : member;
  }
}

async function persistProject(forcePathSelection: boolean): Promise<boolean> {
  const state = useWorkspace.getState();
  if (!state.archive || !projectSession.archivePath) {
    return false;
  }
  let path = forcePathSelection ? null : projectSession.databasePath;
  if (!path) {
    path = await projectClient.chooseSavePath(
      DexDbPath.suggest(projectSession.archivePath),
    );
    if (!path) {
      return false;
    }
  }
  path = DexDbPath.withExtension(path);
  useWorkspace.setState({ savingProject: true, error: null });
  try {
    const snapshot = projectSession.snapshot();
    await projectClient.save(path, {
      ...snapshot,
      databasePath: path,
    });
    projectSession.markSaved(path);
    useWorkspace.setState({
      ...projectStatus(),
      savingProject: false,
    });
    ActivityCenter.notify(t("toast.projectSaved"), "success");
    return true;
  } catch (error) {
    useWorkspace.setState({
      savingProject: false,
      error: messageFrom(error),
    });
    return false;
  }
}

async function confirmProjectReplacement(
  state: WorkspaceState,
): Promise<boolean> {
  if (!state.projectDirty) {
    return true;
  }
  const name =
    state.projectPath?.split(/[/\\]/).at(-1) ??
    state.archive?.name ??
    "this project";
  const decision = await projectClient.askUnsavedChanges(name);
  if (decision === "discard") {
    return true;
  }
  if (decision === "cancel") {
    return false;
  }
  return persistProject(false);
}

async function refreshProjectPresentation(revision: number): Promise<void> {
  const state = useWorkspace.getState();
  if (!state.archive) {
    return;
  }
  const sessionId = state.archive.sessionId;
  const allDocuments = [...state.documents, ...state.closedTabs];
  const presentation = await renameService.presentWorkspace(
    sessionId,
    allDocuments,
  );
  const current = useWorkspace.getState();
  if (
    revision !== presentationRevision ||
    current.archive?.sessionId !== sessionId
  ) {
    return;
  }
  const byDescriptor = new Map(
    presentation.documents.map((document) => [
      document.descriptor,
      document,
    ]),
  );
  useWorkspace.setState({
    archive: presentation.archive,
    documents: current.documents.map(
      (document) => byDescriptor.get(document.descriptor) ?? document,
    ),
    closedTabs: current.closedTabs.map(
      (document) => byDescriptor.get(document.descriptor) ?? document,
    ),
  });
}

class DexDbPath {
  static suggest(archivePath: string): string {
    const separator = Math.max(
      archivePath.lastIndexOf("/"),
      archivePath.lastIndexOf("\\"),
    );
    const directory = archivePath.slice(0, separator + 1);
    const file = archivePath.slice(separator + 1);
    const extension = file.lastIndexOf(".");
    const stem = extension > 0 ? file.slice(0, extension) : file;
    return `${directory}${stem}.dexdb`;
  }

  static withExtension(path: string): string {
    return path.toLocaleLowerCase().endsWith(".dexdb")
      ? path
      : `${path}.dexdb`;
  }
}

/** Replays a history entry without recording it again. */
async function applyHistoryEntry(entry: HistoryEntry): Promise<void> {
  const state = useWorkspace.getState();
  const layout = new EditorLayout(state.editorLayout);
  const requested = entry.group ?? layout.groupOf(entry.descriptor);
  const group = layout.has(requested) ? requested : state.editorLayout.focused;
  await state.selectClass(entry.descriptor, {
    recordHistory: false,
    group,
    preview: false,
  });
  const current = useWorkspace.getState();
  if (current.activeDescriptor !== entry.descriptor) {
    return;
  }
  // A stamped caret is more precise than the member declaration it sits in.
  if (entry.position) {
    current.restorePosition(entry.descriptor, entry.position);
    return;
  }
  if (entry.member) {
    useWorkspace.getState().navigateToMember(
      {
        classDescriptor: entry.descriptor,
        kind: entry.member.kind,
        name: entry.member.name,
        descriptor: entry.member.descriptor,
      },
      { recordHistory: false },
    );
  }
}

/* ---- session persistence ---------------------------------------------- */

let persistTimer: ReturnType<typeof setTimeout> | undefined;

useWorkspace.subscribe((state) => {
  clearTimeout(persistTimer);
  persistTimer = setTimeout(() => {
    try {
      // Null archive means "not restored yet" (or a failed open) — never
      // erase a stored session; it is only overwritten by a live one.
      if (!state.archive) {
        return;
      }
      localStorage.setItem(
        SESSION_STORAGE_KEY,
        JSON.stringify({
          path: state.projectPath ?? state.archive.path,
          tabs: state.documents.map((document) => document.descriptor),
          active: state.activeDescriptor,
          pinned: state.pinned,
          editorLayout: state.editorLayout,
          language: state.sourceLanguage,
        }),
      );
    } catch {
      /* storage unavailable */
    }
  }, 400);
});
