import type { EditorGroup } from "../domain/editorLayout";

export interface EditorTabDrag {
  descriptor: string;
  group: EditorGroup;
}

export class EditorDragSession {
  private static value: EditorTabDrag | null = null;

  static begin(descriptor: string, group: EditorGroup): void {
    this.value = { descriptor, group };
  }

  static finish(): void {
    this.value = null;
  }

  static current(): EditorTabDrag | null {
    return this.value;
  }
}
