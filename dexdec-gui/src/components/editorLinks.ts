import type { EditorState } from "@codemirror/state";
import { StateEffect, StateField } from "@codemirror/state";
import {
  Decoration,
  type DecorationSet,
  EditorView,
} from "@codemirror/view";

import { hasPrimaryModifier } from "../platform";

export interface EditorLink {
  range: { from: number; to: number };
}

export interface EditorLinkResolver<Link extends EditorLink> {
  resolve(state: EditorState, offset: number): Link | null;
}

const setEditorLink = StateEffect.define<EditorLink["range"] | null>();
const editorLinks = StateField.define<DecorationSet>({
  create: () => Decoration.none,
  update: (links, transaction) => {
    let next = links.map(transaction.changes);
    for (const effect of transaction.effects) {
      if (effect.is(setEditorLink)) {
        next = effect.value
          ? Decoration.set([
              Decoration.mark({ class: "cm-definition-link" }).range(
                effect.value.from,
                effect.value.to,
              ),
            ])
          : Decoration.none;
      }
    }
    return next;
  },
  provide: (field) => EditorView.decorations.from(field),
});

export class EditorLinkInteraction<Link extends EditorLink> {
  private hovered: Link | null = null;
  private pointer: { x: number; y: number } | null = null;
  private pressed: { x: number; y: number } | null = null;

  constructor(
    private readonly resolver: EditorLinkResolver<Link>,
    private readonly follow: (link: Link, view: EditorView) => void,
  ) {}

  extension() {
    return [
      editorLinks,
      EditorView.domEventHandlers({
        mousemove: (event, view) => {
          this.pointer = { x: event.clientX, y: event.clientY };
          this.updateHover(view, event);
        },
        mouseleave: (_event, view) => this.clear(view),
        keydown: (event, view) => this.updateHover(view, event),
        keyup: (event, view) => this.updateHover(view, event),
        blur: (_event, view) => this.clear(view),
        mousedown: (event, view) => {
          this.pressed = { x: event.clientX, y: event.clientY };
          if (event.button !== 0 || !hasPrimaryModifier(event)) {
            return false;
          }
          const link = this.linkAtPointer(view);
          if (!link) {
            return false;
          }
          event.preventDefault();
          this.follow(link, view);
          return true;
        },
        mouseup: (event, view) => {
          const pressed = this.pressed;
          this.pressed = null;
          if (
            event.button !== 0 ||
            event.detail > 1 ||
            hasPrimaryModifier(event) ||
            !pressed ||
            Math.hypot(event.clientX - pressed.x, event.clientY - pressed.y) > 3
          ) {
            return false;
          }
          const offset = view.posAtCoords({ x: event.clientX, y: event.clientY });
          if (offset === null) {
            return false;
          }
          event.preventDefault();
          view.dispatch({ selection: { anchor: offset } });
          view.focus();
          return true;
        },
      }),
    ];
  }

  private updateHover(
    view: EditorView,
    event: Pick<MouseEvent | KeyboardEvent, "metaKey" | "ctrlKey">,
  ): void {
    const next = hasPrimaryModifier(event) ? this.linkAtPointer(view) : null;
    if (
      next?.range.from === this.hovered?.range.from &&
      next?.range.to === this.hovered?.range.to
    ) {
      return;
    }
    this.hovered = next;
    view.dispatch({ effects: setEditorLink.of(next?.range ?? null) });
  }

  private linkAtPointer(view: EditorView): Link | null {
    if (!this.pointer) {
      return null;
    }
    const offset = view.posAtCoords(this.pointer);
    return offset == null ? null : this.resolver.resolve(view.state, offset);
  }

  private clear(view: EditorView): void {
    if (!this.hovered) {
      return;
    }
    this.hovered = null;
    view.dispatch({ effects: setEditorLink.of(null) });
  }
}
