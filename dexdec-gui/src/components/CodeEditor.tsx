import {
    HighlightStyle,
    StreamLanguage,
    foldService,
    syntaxHighlighting,
    unfoldAll,
} from "@codemirror/language";
import { java } from "@codemirror/lang-java";
import { kotlin } from "@codemirror/legacy-modes/mode/clike";
import { type EditorState, StateEffect, StateField } from "@codemirror/state";
import {
  Decoration,
  type DecorationSet,
  EditorView,
  WidgetType,
} from "@codemirror/view";
import { tags } from "@lezer/highlight";
import CodeMirror from "@uiw/react-codemirror";
import {
  Braces,
  Check,
  Copy,
  CornerDownRight,
  Hash,
  ListTree,
  Pencil,
  Rows3,
  ScanText,
  Search,
} from "lucide-react";
import { useEffect, useMemo, useRef, useState } from "react";

import type { ResolvedSymbol } from "../domain/sourceDefinitionResolver";
import {
  createSourceDefinitionResolver,
  type SourceDefinitionResolver,
} from "../domain/sourceDefinitionResolver";
import { overviewRuler } from "./overviewRuler";
import {
  type IntegerDisplayMode,
  JavaIntegerLiteral,
} from "../domain/javaIntegerLiteral";
import { JavaSourceIndex } from "../domain/javaSourceIndex";
import type {
  MemberNavigation,
  SourceDocument,
} from "../domain/models";
import type { EditorGroup } from "../domain/editorLayout";
import { useTranslation } from "../i18n";
import { hasPrimaryModifier, MOD_CLICK, sc } from "../platform";
import { copyText } from "../services/clipboard";
import { useAppearance } from "../state/appearance";
import { ActivityCenter } from "../state/activity";
import { useWorkspace } from "../state/workspace";
import { ContextMenu, type ContextMenuEntry } from "./ContextMenu";
import { EditorLinkInteraction } from "./editorLinks";
import {
  EditorNavigationFocus,
  navigationFocusExtension,
} from "./editorNavigationFocus";

/*
 * Editor chrome lives in styles.css (.source-editor …); this layer only sets
 * caret/selection behavior and the Kotlin syntax palette. Hues are muted and
 * warm-balanced against the graphite workspace; the green accent is reserved
 * for UI state, so types read teal and strings read sage. Exported so the
 * lazily-loaded peek view can share the same theme chunk.
 */
export const editorTheme = EditorView.theme(
  {
    "&": {
      backgroundColor: "var(--editor-background)",
      color: "var(--editor-foreground)",
    },
    ".cm-content .tok-kotlin-type": { color: "var(--syntax-type)" },
    ".cm-content .tok-kotlin-function": { color: "var(--syntax-function)" },
    ".cm-content .tok-kotlin-property": { color: "var(--syntax-property)" },
    ".cm-content .tok-kotlin-variable": { color: "var(--syntax-variable)" },
    ".cm-content .tok-kotlin-annotation": { color: "var(--syntax-annotation)" },
    ".cm-content .tok-kotlin-label": { color: "var(--syntax-label)" },
  },
);

class SemanticTokenDecorations {
  constructor(
    private readonly resolver: SourceDefinitionResolver,
    private readonly source: string,
  ) {}

  extension() {
    return StateField.define<DecorationSet>({
      create: (state) => this.forState(state),
      update: (value, transaction) =>
        transaction.docChanged ? this.forState(transaction.state) : value,
      provide: (field) => EditorView.decorations.from(field),
    });
  }

  private forState(state: EditorState): DecorationSet {
    if (
      state.doc.length !== this.source.length ||
      state.doc.toString() !== this.source
    ) {
      return Decoration.none;
    }

    const decorations = (this.resolver.semanticTokens?.() ?? [])
      .filter(
        (token) =>
          token.from >= 0 &&
          token.to > token.from &&
          token.to <= state.doc.length,
      )
      .map((token) =>
        Decoration.mark({ class: `tok-kotlin-${token.kind}` }).range(
          token.from,
          token.to,
        ),
      );
    return Decoration.set(decorations, true);
  }
}

export const sourceHighlight = HighlightStyle.define([
  {
    tag: [tags.keyword, tags.modifier, tags.controlKeyword],
    color: "var(--syntax-keyword)",
  },
  {
    tag: [tags.string, tags.special(tags.string), tags.docString],
    color: "var(--syntax-string)",
  },
  { tag: [tags.character, tags.escape], color: "var(--syntax-character)" },
  {
    tag: [tags.number, tags.bool, tags.null, tags.atom],
    color: "var(--syntax-constant)",
  },
  {
    tag: [tags.typeName, tags.className, tags.standard(tags.typeName), tags.tagName],
    color: "var(--syntax-type)",
  },
  {
    tag: [tags.function(tags.variableName), tags.function(tags.propertyName)],
    color: "var(--syntax-function)",
  },
  {
    tag: [tags.propertyName, tags.attributeName],
    color: "var(--syntax-property)",
  },
  {
    tag: [tags.variableName, tags.definition(tags.variableName)],
    color: "var(--syntax-variable)",
  },
  { tag: [tags.annotation, tags.meta], color: "var(--syntax-annotation)" },
  { tag: tags.labelName, color: "var(--syntax-label)" },
  {
    tag: [tags.comment, tags.blockComment],
    color: "var(--syntax-comment)",
    fontStyle: "italic",
  },
  {
    tag: [tags.operator, tags.operatorKeyword],
    color: "var(--syntax-operator)",
  },
  { tag: tags.punctuation, color: "var(--syntax-punctuation)" },
  { tag: tags.invalid, color: "var(--danger)" },
]);

/*
 * Kotlin runs through the legacy stream mode, which carries no fold ranges, so
 * the fold gutter stays empty for every Kotlin document. This service derives
 * the ranges from the braces themselves, skipping the ones that live inside
 * comments and literals. Java keeps the fold ranges from its Lezer grammar.
 */
const BRACE_FOLD_SCAN_LIMIT = 100_000;

const braceFold = foldService.of((state, lineStart, lineEnd) => {
  const text = state.doc.sliceString(
    lineStart,
    Math.min(state.doc.length, lineStart + BRACE_FOLD_SCAN_LIMIT),
  );
  const range = braceBlockAfter(text, lineEnd - lineStart);
  return range ? { from: lineStart + range.from, to: lineStart + range.to } : null;
});

/*
 * Locates the block opened by a brace within the first `lineLength` characters
 * and returns the offsets between that brace and its match. Blocks that close
 * on the same line are skipped: folding them would hide nothing.
 */
function braceBlockAfter(
  text: string,
  lineLength: number,
): { from: number; to: number } | null {
  type Mode = "code" | "line-comment" | "block-comment" | "string" | "char" | "raw-string";
  let mode: Mode = "code";
  let depth = 0;
  let open = -1;
  for (let index = 0; index < text.length; index += 1) {
    const char = text[index];
    if (mode === "line-comment") {
      if (char === "\n") {
        mode = "code";
      }
      continue;
    }
    if (mode === "block-comment") {
      if (char === "*" && text[index + 1] === "/") {
        mode = "code";
        index += 1;
      }
      continue;
    }
    if (mode === "string" || mode === "char") {
      if (char === "\\") {
        index += 1;
      } else if (char === "\n" || char === (mode === "string" ? '"' : "'")) {
        mode = "code";
      }
      continue;
    }
    if (mode === "raw-string") {
      if (char === '"' && text[index + 1] === '"' && text[index + 2] === '"') {
        mode = "code";
        index += 2;
      }
      continue;
    }
    if (char === "/" && (text[index + 1] === "/" || text[index + 1] === "*")) {
      mode = text[index + 1] === "/" ? "line-comment" : "block-comment";
      index += 1;
    } else if (char === '"') {
      if (text[index + 1] === '"' && text[index + 2] === '"') {
        mode = "raw-string";
        index += 2;
      } else {
        mode = "string";
      }
    } else if (char === "'") {
      mode = "char";
    } else if (char === "{") {
      if (depth === 0) {
        if (index >= lineLength) {
          return null;
        }
        open = index;
      }
      depth += 1;
    } else if (char === "}" && depth > 0) {
      depth -= 1;
      if (depth === 0) {
        if (index > lineLength) {
          return { from: open + 1, to: index };
        }
        open = -1;
      }
    }
  }
  return null;
}

interface IntegerDisplay {
  literal: JavaIntegerLiteral;
  mode: IntegerDisplayMode;
}

const setIntegerDisplay = StateEffect.define<IntegerDisplay>();
const integerDisplays = StateField.define<ReadonlyMap<string, IntegerDisplay>>({
  create: () => new Map(),
  update: (displays, transaction) => {
    const next = transaction.docChanged
      ? new Map<string, IntegerDisplay>()
      : new Map(displays);
    for (const effect of transaction.effects) {
      if (!effect.is(setIntegerDisplay)) {
        continue;
      }
      const key = integerDisplayKey(effect.value.literal);
      if (effect.value.mode === "original") {
        next.delete(key);
      } else {
        next.set(key, effect.value);
      }
    }
    return next;
  },
  provide: (field) =>
    EditorView.decorations.compute([field], (state) => {
      const displays = [...state.field(field).values()].sort(
        (left, right) => left.literal.range.from - right.literal.range.from,
      );
      return Decoration.set(
        displays.map(({ literal, mode }) =>
          Decoration.replace({
            widget: new IntegerDisplayWidget(literal.format(mode)),
          }).range(literal.range.from, literal.range.to),
        ),
      );
    }),
});

class IntegerDisplayWidget extends WidgetType {
  constructor(private readonly text: string) {
    super();
  }

  eq(other: IntegerDisplayWidget): boolean {
    return this.text === other.text;
  }

  toDOM(): HTMLElement {
    const element = document.createElement("span");
    element.className = "cm-integer-display";
    element.textContent = this.text;
    return element;
  }
}

function integerDisplayKey(literal: JavaIntegerLiteral): string {
  return `${literal.range.from}:${literal.range.to}`;
}

type EditorContextKind =
  | "symbol"
  | "number"
  | "selection"
  | "gutter"
  | "code";

interface RenameEditorState {
  symbol: ResolvedSymbol;
  name: string;
  left: number;
  top: number;
  width: number;
  pending: boolean;
  issue: import("../services/renameService").RenameIssue | null;
}

const RENAME_ISSUE_KEYS = {
  invalid: "rename.invalid",
  keyword: "rename.keyword",
  conflict: "rename.conflict",
  unresolved: "rename.unresolved",
} as const;

class EditorContextTarget {
  private constructor(
    readonly x: number,
    readonly y: number,
    readonly kind: EditorContextKind,
    readonly symbol: ResolvedSymbol | null,
    readonly integerLiteral: JavaIntegerLiteral | null,
    readonly selectionText: string | null,
    readonly symbolText: string | null,
    readonly lineText: string,
  ) {}

  static capture(
    event: Pick<MouseEvent, "clientX" | "clientY" | "target">,
    view: EditorView,
    resolver: SourceDefinitionResolver | null,
  ): EditorContextTarget {
    const target = event.target instanceof Element ? event.target : null;
    const inGutter = Boolean(target?.closest(".cm-gutters"));
    const contentRect = view.contentDOM.getBoundingClientRect();
    const offset =
      view.posAtCoords({
        x: inGutter ? contentRect.left + 1 : event.clientX,
        y: event.clientY,
      }) ?? view.state.selection.main.head;
    const selection = view.state.selection.main;
    const insideSelection =
      !selection.empty && offset >= selection.from && offset <= selection.to;

    if (!insideSelection) {
      view.dispatch({ selection: { anchor: offset } });
    }

    const state = view.state;
    const preservedSelection = insideSelection ? state.selection.main : null;
    const integerLiteral =
      !inGutter && !preservedSelection
        ? JavaIntegerLiteral.at(state, offset)
        : null;
    const symbol =
      !inGutter && !preservedSelection && !integerLiteral
        ? resolver?.resolveReferenceTarget(state, offset) ?? null
        : null;
    const line = state.doc.lineAt(offset);
    const kind: EditorContextKind = inGutter
      ? "gutter"
      : preservedSelection
        ? "selection"
        : integerLiteral
          ? "number"
        : symbol
          ? "symbol"
          : "code";

    return new EditorContextTarget(
      event.clientX,
      event.clientY,
      kind,
      symbol,
      integerLiteral,
      preservedSelection
        ? state.doc.sliceString(preservedSelection.from, preservedSelection.to)
        : null,
      symbol ? state.doc.sliceString(symbol.range.from, symbol.range.to) : null,
      line.text,
    );
  }
}

class DefinitionInteraction {
  private readonly links: EditorLinkInteraction<ResolvedSymbol>;

  constructor(private readonly resolver: SourceDefinitionResolver) {
    this.links = new EditorLinkInteraction(
      {
        resolve: (state, offset) =>
          this.resolver.resolveReferenceTarget(state, offset),
      },
      (symbol, view) => this.activate(symbol, view),
    );
  }

  extension() {
    return this.links.extension();
  }

  handleShortcut(event: KeyboardEvent, view: EditorView): void {
    if (event.repeat) {
      return;
    }
    const key = event.key.toLowerCase();
    const declarationOrUsages =
      key === "b" &&
      hasPrimaryModifier(event) &&
      !event.shiftKey &&
      !event.altKey;
    const findUsages =
      key === "f7" &&
      event.altKey &&
      !event.metaKey &&
      !event.ctrlKey &&
      !event.shiftKey;
    if (!declarationOrUsages && !findUsages) return;
    const symbol = this.resolver.resolveReferenceTarget(
      view.state,
      view.state.selection.main.head,
    );
    if (!symbol) {
      return;
    }
    if (declarationOrUsages) this.activate(symbol, view);
    else if (!this.findReferences(symbol, view)) return;
    event.preventDefault();
  }

  activate(symbol: ResolvedSymbol, view: EditorView): void {
    if (
      symbol.destination.kind !== "local" &&
      this.resolver.isDeclaration(view.state, symbol) &&
      this.findReferences(symbol, view)
    ) {
      return;
    }
    this.navigate(symbol, view);
  }

  navigate(symbol: ResolvedSymbol, view: EditorView): void {
    if (symbol.destination.kind === "local") {
      view.dispatch({
        selection: {
          anchor: symbol.destination.from,
          head: symbol.destination.to,
        },
        effects: EditorView.scrollIntoView(symbol.destination.from, {
          y: "center",
        }),
      });
      view.focus();
      return;
    }
    // Park the caret on the link before leaving: the history stamp reads the
    // caret, and Back should return to the symbol that was clicked.
    view.dispatch({
      selection: { anchor: symbol.range.from, head: symbol.range.to },
    });
    void useWorkspace
      .getState()
      .navigateToDefinition(symbol.destination);
  }

  findReferences(symbol: ResolvedSymbol, view: EditorView): boolean {
    if (symbol.destination.kind === "local") {
      return false;
    }
    const label = view.state.doc.sliceString(
      symbol.range.from,
      symbol.range.to,
    );
    void useWorkspace
      .getState()
      .findReferences(symbol.destination, label);
    return true;
  }

}

export default function CodeEditor({
  group,
  document,
  navigation,
}: {
  group: EditorGroup;
  document: SourceDocument;
  navigation: MemberNavigation | null;
}) {
  const { t } = useTranslation();
  const codeFolding = useAppearance((state) => state.codeFolding);
  const wordWrap = useAppearance((state) => state.wordWrap);
  const archive = useWorkspace((state) => state.archive);
  const positionRestore = useWorkspace((state) => state.positionRestore);
  const definitionResolver = useMemo(
    () =>
      archive
        ? createSourceDefinitionResolver(document, archive)
        : null,
    [archive, document],
  );
  const definitionInteraction = useMemo(
    () =>
      definitionResolver
        ? new DefinitionInteraction(definitionResolver)
        : null,
    [definitionResolver],
  );
  const caretReporter = useMemo(
    () =>
      EditorView.updateListener.of((update) => {
        if (!update.selectionSet && !update.docChanged && !update.transactions.length) {
          return;
        }
        const head = update.state.selection.main.head;
        const line = update.state.doc.lineAt(head);
        const workspace = useWorkspace.getState();
        if (workspace.editorLayout.focused !== group) return;
        workspace.setCaret(
          { line: line.number, column: head - line.from + 1 },
          definitionResolver?.memberAtOffset?.(update.state, head) ??
            (document.language === "java"
              ? JavaSourceIndex.memberAtOffset(update.state, head)
              : null),
        );
      }),
    [definitionResolver, document.language, group],
  );
  const extensions = useMemo(
    () => [
      document.language === "java"
        ? java()
        : [StreamLanguage.define(kotlin), braceFold],
      wordWrap ? EditorView.lineWrapping : [],
      editorTheme,
      syntaxHighlighting(sourceHighlight),
      overviewRuler,
      caretReporter,
      navigationFocusExtension,
      integerDisplays,
      definitionInteraction?.extension() ?? [],
      definitionResolver?.semanticTokens
        ? new SemanticTokenDecorations(
            definitionResolver,
            document.source,
          ).extension()
        : [],
    ],
    [
      caretReporter,
      definitionInteraction,
      definitionResolver,
      document.language,
      document.source,
      wordWrap,
    ],
  );
  const [view, setView] = useState<EditorView | null>(null);
  const [contextTarget, setContextTarget] =
    useState<EditorContextTarget | null>(null);
  const [rename, setRename] = useState<RenameEditorState | null>(null);
  const rootRef = useRef<HTMLDivElement>(null);
  const renameInputRef = useRef<HTMLInputElement>(null);
  const navigationFocus = useMemo(() => new EditorNavigationFocus(), []);

  useEffect(() => {
    return () => {
      navigationFocus.dispose();
      const workspace = useWorkspace.getState();
      if (workspace.editorLayout.focused === group) workspace.setCaret(null);
    };
  }, [group, navigationFocus]);

  useEffect(() => {
    setContextTarget(null);
    setRename(null);
  }, [document.descriptor, document.language, document.source]);

  useEffect(() => {
    if (!codeFolding && view) {
      unfoldAll(view);
    }
  }, [codeFolding, document.descriptor, view]);

  useEffect(() => {
    if (rename) {
      renameInputRef.current?.focus();
      renameInputRef.current?.select();
    }
  }, [rename?.symbol.range.from]);

  const beginRename = (symbol?: ResolvedSymbol) => {
    if (!view || !definitionResolver || !rootRef.current) {
      return;
    }
    const target =
      symbol ??
      definitionResolver.resolveReferenceTarget(
        view.state,
        view.state.selection.main.head,
      );
    if (!target) {
      return;
    }
    const coordinates = view.coordsAtPos(target.range.from);
    if (!coordinates) {
      return;
    }
    const bounds = rootRef.current.getBoundingClientRect();
    const name = view.state.doc.sliceString(target.range.from, target.range.to);
    const width = Math.max(112, Math.min(320, name.length * 8 + 30));
    const left = Math.max(
      7,
      Math.min(bounds.width - width - 7, coordinates.left - bounds.left - 5),
    );
    const top = Math.max(
      4,
      Math.min(bounds.height - 34, coordinates.top - bounds.top - 4),
    );
    view.dispatch({
      selection: { anchor: target.range.from, head: target.range.to },
    });
    setContextTarget(null);
    setRename({
      symbol: target,
      name,
      left,
      top,
      width,
      pending: false,
      issue: null,
    });
  };

  const setDisplayMode = (
    literal: JavaIntegerLiteral,
    mode: IntegerDisplayMode,
  ) => {
    if (!view || !literal.supports(mode)) {
      return false;
    }
    view.dispatch({ effects: setIntegerDisplay.of({ literal, mode }) });
    view.focus();
    return true;
  };

  const commitRename = async () => {
    if (!rename || !view || !definitionResolver || rename.pending) {
      return;
    }
    if (rename.name === view.state.doc.sliceString(
      rename.symbol.range.from,
      rename.symbol.range.to,
    )) {
      setRename(null);
      view.focus();
      return;
    }
    setRename((current) =>
      current ? { ...current, pending: true, issue: null } : null,
    );
    const issue = await useWorkspace.getState().renameSymbol(
      document.descriptor,
      view.state,
      rename.symbol,
      definitionResolver,
      rename.name,
    );
    if (issue) {
      setRename((current) =>
        current ? { ...current, pending: false, issue } : null,
      );
      return;
    }
    ActivityCenter.notify(t("rename.complete"), "success");
    setRename(null);
    requestAnimationFrame(() => view.focus());
  };

  useEffect(() => {
    if (!view || !navigation) {
      return;
    }
    if (!definitionResolver) {
      return;
    }
    const range = definitionResolver.locateMember?.(view.state, navigation) ??
      (document.language === "java"
        ? JavaSourceIndex.locate(view.state, navigation, definitionResolver)
        : null);
    if (!range) {
      return;
    }
    navigationFocus.reveal(view, range);
  }, [definitionResolver, navigation, navigationFocus, view]);

  /*
   * Back/Forward landing on a remembered caret. Line and column are clamped:
   * the document may have been re-decompiled with different output settings or
   * renamed symbols since the position was recorded.
   */
  useEffect(() => {
    if (!view || !positionRestore) {
      return;
    }
    if (positionRestore.descriptor !== document.descriptor) {
      return;
    }
    const doc = view.state.doc;
    const line = doc.line(Math.min(Math.max(positionRestore.line, 1), doc.lines));
    const offset = Math.min(
      line.from + Math.max(positionRestore.column - 1, 0),
      line.to,
    );
    navigationFocus.reveal(view, { from: offset, to: offset }, 1200);
  }, [document.descriptor, navigationFocus, positionRestore, view]);

  useEffect(() => {
    if (!view) {
      return;
    }
    const handleKeyDown = (event: KeyboardEvent) => {
      if (!eventTargetBelongsToEditor(event, view)) {
        return;
      }
      if (
        event.key.toLowerCase() === "f6" &&
        event.shiftKey &&
        !event.metaKey &&
        !event.ctrlKey &&
        !event.altKey &&
        !event.repeat
      ) {
        event.preventDefault();
        beginRename();
        return;
      }
      if (!event.metaKey && !event.ctrlKey && !event.altKey && !event.repeat) {
        const mode = INTEGER_DISPLAY_SHORTCUTS[event.key.toLowerCase()];
        const literal = mode
          ? JavaIntegerLiteral.at(view.state, view.state.selection.main.head)
          : null;
        if (literal && mode && setDisplayMode(literal, mode)) {
          event.preventDefault();
          return;
        }
      }
      definitionInteraction?.handleShortcut(event, view);
    };
    const isFocusedGroup = () =>
      useWorkspace.getState().editorLayout.focused === group;
    const handleMenuRename = () => {
      if (isFocusedGroup()) beginRename();
    };
    const handleDeclarationOrUsages = () => {
      if (!isFocusedGroup()) return;
      const symbol = definitionResolver?.resolveReferenceTarget(
        view.state,
        view.state.selection.main.head,
      );
      if (symbol) definitionInteraction?.activate(symbol, view);
    };
    const handleFindUsages = () => {
      if (!isFocusedGroup()) return;
      const symbol = definitionResolver?.resolveReferenceTarget(
        view.state,
        view.state.selection.main.head,
      );
      if (symbol) definitionInteraction?.findReferences(symbol, view);
    };
    window.document.addEventListener("keydown", handleKeyDown, true);
    window.addEventListener("dexdec:rename", handleMenuRename);
    window.addEventListener("dexdec:declaration-or-usages", handleDeclarationOrUsages);
    window.addEventListener("dexdec:find-usages", handleFindUsages);
    return () =>
      {
        window.document.removeEventListener("keydown", handleKeyDown, true);
        window.removeEventListener("dexdec:rename", handleMenuRename);
        window.removeEventListener("dexdec:declaration-or-usages", handleDeclarationOrUsages);
        window.removeEventListener("dexdec:find-usages", handleFindUsages);
      };
  }, [definitionInteraction, view, definitionResolver, group]);

  const contextEntries = (
    target: EditorContextTarget,
  ): ContextMenuEntry[] => {
    if (!view) {
      return [];
    }
    const entries: ContextMenuEntry[] = [];
    const copy = (text: string) => {
      void copyText(text);
      view.focus();
    };

    if (target.kind === "number" && target.integerLiteral) {
      const literal = target.integerLiteral;
      const currentMode =
        view.state.field(integerDisplays).get(integerDisplayKey(literal))?.mode ??
        "original";
      for (const option of INTEGER_DISPLAY_OPTIONS) {
        entries.push({
          id: `integer-${option.mode}`,
          icon:
            currentMode === option.mode ? (
              <Check size={14} />
            ) : (
              <Hash size={14} />
            ),
          label: t(option.label),
          shortcut: option.shortcut,
          disabled:
            currentMode === option.mode || !literal.supports(option.mode),
          onSelect: () => setDisplayMode(literal, option.mode),
        });
      }
      entries.push("separator", {
        id: "copy-number",
        icon: <Copy size={14} />,
        label: t("editor.copy"),
        shortcut: sc("mod+c"),
        onSelect: () => copy(literal.source),
      });
    } else if (
      target.kind === "symbol" &&
      target.symbol &&
      definitionInteraction
    ) {
      const declarationOrUsages =
        target.symbol.destination.kind !== "local" &&
        definitionResolver?.isDeclaration(view.state, target.symbol);
      entries.push({
        id: "rename",
        icon: <Pencil size={14} />,
        label: t("editor.rename"),
        shortcut: sc("shift+f6"),
        onSelect: () => beginRename(target.symbol!),
      });
      entries.push({
        id: "declaration-or-usages",
        icon: declarationOrUsages ? <Search size={14} /> : <CornerDownRight size={14} />,
        label: declarationOrUsages
          ? t("editor.findReferences")
          : target.symbol.destination.kind === "local"
            ? t("editor.goToDeclaration")
            : t("editor.goToDefinition"),
        shortcut: `${MOD_CLICK} / ${sc("mod+b")}`,
        onSelect: () => definitionInteraction.activate(target.symbol!, view),
      });
      if (target.symbol.destination.kind !== "local" && !declarationOrUsages) {
        entries.push({
          id: "references",
          icon: <Search size={14} />,
          label: t("editor.findReferences"),
          shortcut: sc("alt+f7"),
          onSelect: () =>
            definitionInteraction.findReferences(target.symbol!, view),
        });
      }
      entries.push(
        "separator",
        {
          id: "copy-symbol",
          icon: <Copy size={14} />,
          label: t("editor.copySymbol"),
          onSelect: () => copy(target.symbolText ?? ""),
        },
      );
    } else if (target.kind === "selection" && target.selectionText != null) {
      entries.push({
        id: "copy-selection",
        icon: <Copy size={14} />,
        label: t("editor.copy"),
        shortcut: sc("mod+c"),
        onSelect: () => copy(target.selectionText ?? ""),
      });
    } else {
      entries.push({
        id: "copy-line",
        icon: <Rows3 size={14} />,
        label: t("editor.copyLine"),
        onSelect: () => copy(target.lineText),
      });
    }

    entries.push({
      id: "select-all",
      icon: <ScanText size={14} />,
      label: t("editor.selectAll"),
      shortcut: sc("mod+a"),
      onSelect: () => {
        view.dispatch({
          selection: { anchor: 0, head: view.state.doc.length },
        });
        view.focus();
      },
    });
    entries.push(
      "separator",
      {
        id: "reveal",
        icon: <ListTree size={14} />,
        label: t("editor.revealInExplorer"),
        onSelect: () =>
          useWorkspace.getState().revealInExplorer(document.descriptor),
      },
      {
        id: "copy-qualified-name",
        icon: <Braces size={14} />,
        label: t("editor.copyQualifiedName"),
        onSelect: () => copy(document.outline.qualifiedName),
      },
      {
        id: "copy-descriptor",
        icon: <Hash size={14} />,
        label: t("editor.copyDescriptor"),
        onSelect: () => copy(document.descriptor),
      },
    );
    return entries;
  };

  return (
    <div
      ref={rootRef}
      className="relative h-full min-h-0"
      onFocusCapture={() => useWorkspace.getState().focusEditorGroup(group)}
      onContextMenu={(event) => {
        event.preventDefault();
        if (!view) {
          return;
        }
        setContextTarget(
          EditorContextTarget.capture(
            event.nativeEvent,
            view,
            definitionResolver,
          ),
        );
      }}
    >
      <CodeMirror
        value={document.source}
        height="100%"
        className="source-editor h-full"
        theme="none"
        extensions={extensions}
        readOnly={true}
        onCreateEditor={(editor) => {
          setView(editor);
          const head = editor.state.selection.main.head;
          const line = editor.state.doc.lineAt(head);
          const workspace = useWorkspace.getState();
          if (workspace.editorLayout.focused !== group) return;
          workspace.setCaret(
            { line: line.number, column: head - line.from + 1 },
            definitionResolver?.memberAtOffset?.(editor.state, head) ??
              (document.language === "java"
                ? JavaSourceIndex.memberAtOffset(editor.state, head)
                : null),
          );
        }}
        basicSetup={{
          autocompletion: false,
          bracketMatching: true,
          closeBrackets: false,
          foldGutter: codeFolding,
          highlightActiveLine: true,
          highlightActiveLineGutter: true,
          highlightSelectionMatches: true,
          lineNumbers: true,
          searchKeymap: true,
        }}
      />
      {rename ? (
        <div
          className="rename-editor"
          style={{
            left: rename.left,
            top: rename.top,
            width: rename.width,
          }}
        >
          <input
            ref={renameInputRef}
            className="rename-editor-input"
            value={rename.name}
            disabled={rename.pending}
            aria-label={t("editor.rename")}
            spellCheck={false}
            onChange={(event) =>
              setRename((current) =>
                current
                  ? {
                      ...current,
                      name: event.target.value,
                      issue: null,
                    }
                  : null,
              )
            }
            onKeyDown={(event) => {
              event.stopPropagation();
              if (event.key === "Enter") {
                event.preventDefault();
                void commitRename();
              } else if (event.key === "Escape") {
                event.preventDefault();
                setRename(null);
                view?.focus();
              }
            }}
            onBlur={() => {
              if (!rename.pending) {
                setRename(null);
              }
            }}
          />
          {rename.issue ? (
            <div className="rename-editor-error" role="alert">
              {t(RENAME_ISSUE_KEYS[rename.issue])}
            </div>
          ) : null}
        </div>
      ) : null}
      {contextTarget ? (
        <ContextMenu
          x={contextTarget.x}
          y={contextTarget.y}
          entries={contextEntries(contextTarget)}
          ariaLabel={t("editor.contextMenu")}
          onClose={() => setContextTarget(null)}
        />
      ) : null}
    </div>
  );
}

const INTEGER_DISPLAY_OPTIONS: ReadonlyArray<{
  mode: IntegerDisplayMode;
  label:
    | "editor.number.original"
    | "editor.number.hexadecimal"
    | "editor.number.decimal"
    | "editor.number.binary"
    | "editor.number.octal"
    | "editor.number.character";
  shortcut: string;
}> = [
  { mode: "hexadecimal", label: "editor.number.hexadecimal", shortcut: "H" },
  { mode: "decimal", label: "editor.number.decimal", shortcut: "D" },
  { mode: "binary", label: "editor.number.binary", shortcut: "B" },
  { mode: "octal", label: "editor.number.octal", shortcut: "O" },
  { mode: "character", label: "editor.number.character", shortcut: "C" },
  { mode: "original", label: "editor.number.original", shortcut: "R" },
];

const INTEGER_DISPLAY_SHORTCUTS: Readonly<
  Record<string, IntegerDisplayMode>
> = Object.fromEntries(
  INTEGER_DISPLAY_OPTIONS.map(({ mode, shortcut }) => [
    shortcut.toLowerCase(),
    mode,
  ]),
);

function eventTargetBelongsToEditor(
  event: KeyboardEvent,
  view: EditorView,
): boolean {
  const target = event.target;
  return (
    target === document.body ||
    target === document.documentElement ||
    (target instanceof Node && view.dom.contains(target))
  );
}
