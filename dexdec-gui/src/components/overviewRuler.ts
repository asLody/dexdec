import { SearchQuery, getSearchQuery, searchPanelOpen } from "@codemirror/search";
import type { EditorState } from "@codemirror/state";
import {
  EditorView,
  ViewPlugin,
  type PluginValue,
  type ViewUpdate,
} from "@codemirror/view";

/*
 * Overview ruler: a strip along the editor's right edge marking where the
 * search hits and the occurrences of the current selection sit in the whole
 * document, plus the caret. Purely indicative — it never swallows pointer
 * events, so the native scrollbar underneath still works.
 */

/** Above this the match scan is skipped; the ruler then shows only the caret. */
const SCAN_LIMIT = 1_500_000;
const MARK_LIMIT = 800;
/** Longest selection still treated as an occurrence probe. */
const SELECTION_LIMIT = 120;

type MarkKind = "match" | "selection";

export const overviewRuler = ViewPlugin.fromClass(
  class implements PluginValue {
    private readonly dom: HTMLElement;

    constructor(private readonly view: EditorView) {
      this.dom = document.createElement("div");
      this.dom.className = "cm-overview-ruler";
      this.dom.setAttribute("aria-hidden", "true");
      view.dom.appendChild(this.dom);
      this.render();
    }

    update(update: ViewUpdate) {
      if (update.docChanged || update.selectionSet || update.transactions.length) {
        this.render();
      }
    }

    destroy() {
      this.dom.remove();
    }

    private render() {
      const { state } = this.view;
      const lines = state.doc.lines;
      const parts: string[] = [];
      const { kind, positions } = collectMarks(state);
      for (const position of positions) {
        const line = state.doc.lineAt(position).number;
        parts.push(
          `<i class="cm-overview-mark is-${kind}" style="top:${percent(line, lines)}"></i>`,
        );
      }
      const caret = state.doc.lineAt(state.selection.main.head).number;
      parts.push(
        `<i class="cm-overview-mark is-caret" style="top:${percent(caret, lines)}"></i>`,
      );
      this.dom.innerHTML = parts.join("");
    }
  },
);

function percent(line: number, lines: number): string {
  return `${(((line - 0.5) / Math.max(lines, 1)) * 100).toFixed(3)}%`;
}

/*
 * Search hits win over selection occurrences: when the search panel is open the
 * ruler answers "where else does my query match", otherwise "where else does
 * the thing I just selected appear" — mirroring the in-editor highlights.
 */
function collectMarks(state: EditorState): {
  kind: MarkKind;
  positions: number[];
} {
  if (state.doc.length > SCAN_LIMIT) {
    return { kind: "match", positions: [] };
  }
  if (searchPanelOpen(state)) {
    const query = getSearchQuery(state);
    return {
      kind: "match",
      positions: query.valid ? scan(query, state) : [],
    };
  }
  const range = state.selection.main;
  if (range.empty || range.to - range.from > SELECTION_LIMIT) {
    return { kind: "selection", positions: [] };
  }
  const text = state.sliceDoc(range.from, range.to);
  if (!text.trim() || text.includes("\n")) {
    return { kind: "selection", positions: [] };
  }
  const query = new SearchQuery({
    search: text,
    caseSensitive: true,
    wholeWord: /^\w+$/.test(text),
  });
  return { kind: "selection", positions: query.valid ? scan(query, state) : [] };
}

function scan(query: SearchQuery, state: EditorState): number[] {
  const positions: number[] = [];
  const cursor = query.getCursor(state);
  for (let hit = cursor.next(); !hit.done; hit = cursor.next()) {
    positions.push(hit.value.from);
    if (positions.length >= MARK_LIMIT) {
      break;
    }
  }
  return positions;
}
