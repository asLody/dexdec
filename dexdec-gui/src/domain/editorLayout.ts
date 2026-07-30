export type EditorGroup = string;

export const ROOT_EDITOR_GROUP = "group-1";

export type EditorSplitAxis = "horizontal" | "vertical";
export type EditorSplitSide = "before" | "after";

export type EditorLayoutNode =
  | { kind: "group"; id: EditorGroup }
  | {
      kind: "split";
      axis: EditorSplitAxis;
      first: EditorLayoutNode;
      second: EditorLayoutNode;
    };

export interface EditorLayoutState {
  root: EditorLayoutNode;
  focused: EditorGroup;
  tabs: Record<EditorGroup, string[]>;
  active: Record<EditorGroup, string | null>;
  preview: Record<EditorGroup, string | null>;
  nextGroup: number;
}

export interface OpenEditorOptions {
  group?: EditorGroup;
  preview?: boolean;
}

export interface EditorLayoutChange {
  state: EditorLayoutState;
  replacedPreview: string | null;
}

interface LegacyEditorLayoutState {
  split?: boolean;
  focused?: "primary" | "secondary";
  tabs?: Partial<Record<"primary" | "secondary", string[]>>;
  active?: Partial<Record<"primary" | "secondary", string | null>>;
  preview?: Partial<Record<"primary" | "secondary", string | null>>;
}

const leaf = (id: EditorGroup): EditorLayoutNode => ({ kind: "group", id });

function groupIds(node: EditorLayoutNode): EditorGroup[] {
  return node.kind === "group"
    ? [node.id]
    : [...groupIds(node.first), ...groupIds(node.second)];
}

function replaceNode(
  node: EditorLayoutNode,
  group: EditorGroup,
  replacement: EditorLayoutNode,
): EditorLayoutNode {
  if (node.kind === "group") return node.id === group ? replacement : node;
  return {
    ...node,
    first: replaceNode(node.first, group, replacement),
    second: replaceNode(node.second, group, replacement),
  };
}

function removeNode(
  node: EditorLayoutNode,
  group: EditorGroup,
): EditorLayoutNode | null {
  if (node.kind === "group") return node.id === group ? null : node;
  const first = removeNode(node.first, group);
  const second = removeNode(node.second, group);
  if (!first) return second;
  if (!second) return first;
  return { ...node, first, second };
}

export class EditorLayout {
  static empty(): EditorLayoutState {
    return {
      root: leaf(ROOT_EDITOR_GROUP),
      focused: ROOT_EDITOR_GROUP,
      tabs: { [ROOT_EDITOR_GROUP]: [] },
      active: { [ROOT_EDITOR_GROUP]: null },
      preview: { [ROOT_EDITOR_GROUP]: null },
      nextGroup: 2,
    };
  }

  static restore(value: unknown): EditorLayoutState {
    if (!value || typeof value !== "object") return EditorLayout.empty();
    const candidate = value as Partial<EditorLayoutState> & LegacyEditorLayoutState;
    if (candidate.root && candidate.tabs && candidate.active && candidate.preview) {
      const ids = groupIds(candidate.root);
      if (!ids.length) return EditorLayout.empty();
      const tabs: Record<string, string[]> = {};
      const active: Record<string, string | null> = {};
      const preview: Record<string, string | null> = {};
      for (const id of ids) {
        tabs[id] = [...(candidate.tabs[id] ?? [])];
        active[id] = candidate.active[id] ?? tabs[id].at(-1) ?? null;
        preview[id] = candidate.preview[id] ?? null;
      }
      return {
        root: candidate.root,
        focused: ids.includes(candidate.focused ?? "") ? candidate.focused! : ids[0],
        tabs,
        active,
        preview,
        nextGroup: Math.max(candidate.nextGroup ?? 2, ids.length + 1),
      };
    }

    const primary = ROOT_EDITOR_GROUP;
    const secondary = "group-2";
    const split = Boolean(candidate.split);
    const primaryTabs = [...(candidate.tabs?.primary ?? [])];
    const secondaryTabs = [...(candidate.tabs?.secondary ?? [])];
    return {
      root: split
        ? {
            kind: "split",
            axis: "horizontal",
            first: leaf(primary),
            second: leaf(secondary),
          }
        : leaf(primary),
      focused: split && candidate.focused === "secondary" ? secondary : primary,
      tabs: split
        ? { [primary]: primaryTabs, [secondary]: secondaryTabs }
        : { [primary]: primaryTabs },
      active: split
        ? {
            [primary]: candidate.active?.primary ?? primaryTabs.at(-1) ?? null,
            [secondary]: candidate.active?.secondary ?? secondaryTabs.at(-1) ?? null,
          }
        : { [primary]: candidate.active?.primary ?? primaryTabs.at(-1) ?? null },
      preview: split
        ? {
            [primary]: candidate.preview?.primary ?? null,
            [secondary]: candidate.preview?.secondary ?? null,
          }
        : { [primary]: candidate.preview?.primary ?? null },
      nextGroup: split ? 3 : 2,
    };
  }

  constructor(private readonly value: EditorLayoutState) {}

  groups(): readonly EditorGroup[] {
    return groupIds(this.value.root);
  }

  groupCount(): number {
    return this.groups().length;
  }

  has(group: EditorGroup): boolean {
    return Object.hasOwn(this.value.tabs, group);
  }

  tabsIn(group: EditorGroup): readonly string[] {
    return this.value.tabs[group] ?? [];
  }

  activeIn(group: EditorGroup): string | null {
    return this.value.active[group] ?? null;
  }

  previewIn(group: EditorGroup): string | null {
    return this.value.preview[group] ?? null;
  }

  contains(descriptor: string): boolean {
    return this.groups().some((group) => this.tabsIn(group).includes(descriptor));
  }

  groupOf(descriptor: string, preferred = this.value.focused): EditorGroup {
    if (this.tabsIn(preferred).includes(descriptor)) return preferred;
    return this.groups().find((group) => this.tabsIn(group).includes(descriptor))
      ?? preferred;
  }

  open(descriptor: string, options: OpenEditorOptions = {}): EditorLayoutChange {
    const group = this.has(options.group ?? "")
      ? options.group!
      : this.value.focused;
    const preview = options.preview ?? true;
    if (this.tabsIn(group).includes(descriptor)) {
      return {
        state: {
          ...this.value,
          focused: group,
          active: { ...this.value.active, [group]: descriptor },
          preview: {
            ...this.value.preview,
            [group]: preview === false && this.previewIn(group) === descriptor
              ? null
              : this.previewIn(group),
          },
        },
        replacedPreview: null,
      };
    }

    const replacedPreview = preview ? this.previewIn(group) : null;
    return {
      state: {
        ...this.value,
        focused: group,
        tabs: {
          ...this.value.tabs,
          [group]: [
            ...this.tabsIn(group).filter((candidate) => candidate !== replacedPreview),
            descriptor,
          ],
        },
        active: { ...this.value.active, [group]: descriptor },
        preview: { ...this.value.preview, [group]: preview ? descriptor : null },
      },
      replacedPreview,
    };
  }

  focus(group: EditorGroup, descriptor = this.activeIn(group)): EditorLayoutState {
    if (!this.has(group)) return this.value;
    return {
      ...this.value,
      focused: group,
      active: { ...this.value.active, [group]: descriptor },
    };
  }

  promote(descriptor: string, group = this.groupOf(descriptor)): EditorLayoutState {
    if (this.previewIn(group) !== descriptor) return this.value;
    return { ...this.value, preview: { ...this.value.preview, [group]: null } };
  }

  close(group: EditorGroup, descriptor: string): EditorLayoutState {
    const groupTabs = this.tabsIn(group);
    const index = groupTabs.indexOf(descriptor);
    if (index < 0) return this.value;
    const tabs = groupTabs.filter((candidate) => candidate !== descriptor);
    const fallback = tabs[Math.min(index, tabs.length - 1)] ?? null;
    const state = {
      ...this.value,
      tabs: { ...this.value.tabs, [group]: tabs },
      active: {
        ...this.value.active,
        [group]: this.activeIn(group) === descriptor ? fallback : this.activeIn(group),
      },
      preview: {
        ...this.value.preview,
        [group]: this.previewIn(group) === descriptor ? null : this.previewIn(group),
      },
    };
    return tabs.length === 0 && this.groupCount() > 1
      ? new EditorLayout(state).closeGroup(group)
      : state;
  }

  remove(group: EditorGroup, descriptors: ReadonlySet<string>): EditorLayoutState {
    let state = this.value;
    for (const descriptor of descriptors) {
      if (!new EditorLayout(state).has(group)) break;
      state = new EditorLayout(state).close(group, descriptor);
    }
    return state;
  }

  retain(descriptors: ReadonlySet<string>): EditorLayoutState {
    const tabs = { ...this.value.tabs };
    const active = { ...this.value.active };
    const preview = { ...this.value.preview };
    for (const group of this.groups()) {
      tabs[group] = this.tabsIn(group).filter((entry) => descriptors.has(entry));
      if (active[group] && !tabs[group].includes(active[group]!)) {
        active[group] = tabs[group].at(-1) ?? null;
      }
      if (preview[group] && !tabs[group].includes(preview[group]!)) {
        preview[group] = null;
      }
    }
    return { ...this.value, tabs, active, preview };
  }

  move(
    descriptor: string,
    source: EditorGroup,
    target: EditorGroup,
    before: string | null,
  ): EditorLayoutState {
    if (!this.tabsIn(source).includes(descriptor) || !this.has(target)) return this.value;
    const tabs = Object.fromEntries(
      this.groups().map((group) => [group, [...this.tabsIn(group)]]),
    );
    const sourceIndex = tabs[source].indexOf(descriptor);
    tabs[source].splice(sourceIndex, 1);
    const existing = tabs[target].indexOf(descriptor);
    if (existing >= 0) tabs[target].splice(existing, 1);
    const targetIndex = before ? tabs[target].indexOf(before) : -1;
    tabs[target].splice(targetIndex < 0 ? tabs[target].length : targetIndex, 0, descriptor);
    const active = { ...this.value.active, [target]: descriptor };
    if (source !== target && this.activeIn(source) === descriptor) {
      active[source] = tabs[source][Math.min(sourceIndex, tabs[source].length - 1)] ?? null;
    }
    const preview = { ...this.value.preview, [target]: null };
    if (this.previewIn(source) === descriptor) preview[source] = null;
    const state = { ...this.value, focused: target, tabs, active, preview };
    return source !== target && tabs[source].length === 0
      ? new EditorLayout(state).closeGroup(source)
      : state;
  }

  split(
    group: EditorGroup,
    descriptor: string | null,
    axis: EditorSplitAxis = "horizontal",
    side: EditorSplitSide = "after",
  ): EditorLayoutState {
    if (!this.has(group)) return this.value;
    const created = `group-${this.value.nextGroup}`;
    const existing = leaf(group);
    const addition = leaf(created);
    const replacement: EditorLayoutNode = {
      kind: "split",
      axis,
      first: side === "before" ? addition : existing,
      second: side === "before" ? existing : addition,
    };
    const state: EditorLayoutState = {
      ...this.value,
      root: replaceNode(this.value.root, group, replacement),
      focused: created,
      tabs: { ...this.value.tabs, [created]: [] },
      active: { ...this.value.active, [created]: null },
      preview: { ...this.value.preview, [created]: null },
      nextGroup: this.value.nextGroup + 1,
    };
    if (!descriptor) return state;
    return new EditorLayout(state).open(descriptor, {
      group: created,
      preview: false,
    }).state;
  }

  splitMove(
    descriptor: string,
    source: EditorGroup,
    target: EditorGroup,
    axis: EditorSplitAxis,
    side: EditorSplitSide,
  ): EditorLayoutState {
    const split = this.split(target, null, axis, side);
    const created = split.focused;
    return new EditorLayout(split).move(descriptor, source, created, null);
  }

  closeGroup(group: EditorGroup): EditorLayoutState {
    if (!this.has(group) || this.groupCount() === 1) return this.value;
    const root = removeNode(this.value.root, group);
    if (!root) return EditorLayout.empty();
    const tabs = { ...this.value.tabs };
    const active = { ...this.value.active };
    const preview = { ...this.value.preview };
    delete tabs[group];
    delete active[group];
    delete preview[group];
    const groups = groupIds(root);
    const focused = this.value.focused === group
      ? groups[Math.min(this.groups().indexOf(group), groups.length - 1)] ?? groups[0]
      : this.value.focused;
    return { ...this.value, root, focused, tabs, active, preview };
  }

  orderPinned(pinned: ReadonlySet<string>): EditorLayoutState {
    const tabs = Object.fromEntries(this.groups().map((group) => {
      const values = this.tabsIn(group);
      return [group, [
        ...values.filter((descriptor) => pinned.has(descriptor)),
        ...values.filter((descriptor) => !pinned.has(descriptor)),
      ]];
    }));
    return { ...this.value, tabs };
  }
}
