import { StateEffect, StateField } from "@codemirror/state";
import {
  Decoration,
  type DecorationSet,
  EditorView,
} from "@codemirror/view";

interface NavigationRange {
  from: number;
  to: number;
}

const setNavigationFocus = StateEffect.define<
  (NavigationRange & { lineFrom: number }) | null
>();

export const navigationFocusExtension = StateField.define<DecorationSet>({
  create: () => Decoration.none,
  update: (highlight, transaction) => {
    let next = highlight.map(transaction.changes);
    for (const effect of transaction.effects) {
      if (!effect.is(setNavigationFocus)) continue;
      next = effect.value
        ? Decoration.set(
            [
              Decoration.line({ class: "cm-navigation-focus-line" }).range(
                effect.value.lineFrom,
              ),
              ...(effect.value.to > effect.value.from
                ? [
                    Decoration.mark({
                      class: "cm-navigation-focus-token",
                    }).range(effect.value.from, effect.value.to),
                  ]
                : []),
            ],
            true,
          )
        : Decoration.none;
    }
    return next;
  },
  provide: (field) => EditorView.decorations.from(field),
});

export class EditorNavigationFocus {
  private timer: ReturnType<typeof setTimeout> | null = null;

  reveal(view: EditorView, range: NavigationRange, duration = 1800): void {
    this.cancelTimer();
    if (!this.contains(view, range)) return;

    const lineFrom = view.state.doc.lineAt(range.from).from;
    view.dispatch({
      selection: { anchor: range.from, head: range.to },
      effects: setNavigationFocus.of({ ...range, lineFrom }),
    });
    const block = view.lineBlockAt(range.from);
    view.scrollDOM.scrollTop = Math.max(
      0,
      block.top - (view.scrollDOM.clientHeight - block.height) / 2,
    );
    view.focus();
    this.timer = setTimeout(() => {
      if (view.dom.isConnected) {
        view.dispatch({ effects: setNavigationFocus.of(null) });
      }
      this.timer = null;
    }, duration);
  }

  dispose(): void {
    this.cancelTimer();
  }

  private cancelTimer(): void {
    if (this.timer) clearTimeout(this.timer);
    this.timer = null;
  }

  private contains(view: EditorView, range: NavigationRange): boolean {
    return (
      Number.isInteger(range.from) &&
      Number.isInteger(range.to) &&
      range.from >= 0 &&
      range.to >= range.from &&
      range.to <= view.state.doc.length
    );
  }
}
