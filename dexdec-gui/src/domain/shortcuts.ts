import type { MessageKey } from "../i18n";

/*
 * Every keyboard affordance the app exposes, in one place, so the Keymap panel
 * and the tooltips can't drift apart. `combo` uses the declarative form that
 * platform.sc() renders (⌘⇧O on Apple, Ctrl+Shift+O elsewhere); `literal` is
 * for the handful that aren't a single chord (tab digits, modifier-click).
 */
export interface ShortcutEntry {
  label: MessageKey;
  combo?: string;
  literal?: "tab-digits" | "mod-click";
  /** Bound by the native application menu rather than the web layer. */
  menu?: boolean;
}

export interface ShortcutGroup {
  title: MessageKey;
  entries: ShortcutEntry[];
}

export const SHORTCUT_GROUPS: ShortcutGroup[] = [
  {
    title: "keymap.group.file",
    entries: [
      { label: "keymap.openArchive", combo: "mod+o", menu: true },
      { label: "keymap.save", combo: "mod+s", menu: true },
      { label: "keymap.saveAs", combo: "mod+shift+s", menu: true },
      { label: "keymap.closeEditor", combo: "mod+w", menu: true },
      { label: "keymap.reopenEditor", combo: "mod+shift+t", menu: true },
    ],
  },
  {
    title: "keymap.group.navigate",
    entries: [
      { label: "keymap.goToClass", combo: "mod+o", menu: true },
      { label: "keymap.goToMember", combo: "mod+f12", menu: true },
      { label: "keymap.searchSymbols", combo: "mod+alt+o", menu: true },
      { label: "keymap.goToDefinition", combo: "mod+b", menu: true },
      { label: "keymap.goToDefinition", literal: "mod-click" },
      { label: "keymap.findReferences", combo: "alt+f7", menu: true },
      { label: "keymap.back", combo: "mod+[", menu: true },
      { label: "keymap.forward", combo: "mod+]", menu: true },
    ],
  },
  {
    title: "keymap.group.view",
    entries: [
      { label: "keymap.toggleExplorer", combo: "mod+1", menu: true },
      { label: "keymap.toggleOutline", combo: "mod+7", menu: true },
      { label: "keymap.toggleProblems", combo: "mod+6", menu: true },
      { label: "keymap.settings", combo: "mod+,", menu: true },
    ],
  },
  {
    title: "keymap.group.edit",
    entries: [
      { label: "keymap.searchCode", combo: "mod+shift+f", menu: true },
      { label: "keymap.undoRename", combo: "mod+z" },
      { label: "keymap.redoRename", combo: "mod+shift+z" },
      { label: "keymap.rename", combo: "shift+f6", menu: true },
    ],
  },
  {
    title: "keymap.group.editor",
    entries: [
      { label: "keymap.find", combo: "mod+f" },
      { label: "keymap.findNext", combo: "mod+g" },
      { label: "keymap.findPrevious", combo: "mod+shift+g" },
      { label: "keymap.selectOccurrence", combo: "mod+d" },
      { label: "keymap.selectAll", combo: "mod+a" },
      { label: "keymap.copy", combo: "mod+c" },
    ],
  },
];
