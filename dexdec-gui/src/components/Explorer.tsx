import { useVirtualizer } from "@tanstack/react-virtual";
import {
  Braces,
  ChevronDown,
  ChevronRight,
  Copy,
  CornerDownRight,
  Database,
  File,
  FileCode2,
  FileImage,
  Folder,
  FolderOpen,
  Library,
  ListTree,
  Package,
  PackageOpen,
  Pin,
  PinOff,
  Rows3,
  Search,
  X,
} from "lucide-react";
import { useDeferredValue, useEffect, useMemo, useRef, useState } from "react";

import {
  ProjectExplorerIndex,
  type ExplorerMode,
  type ProjectExplorerRow,
} from "../domain/explorer";
import { useTranslation } from "../i18n";
import { sc } from "../platform";
import { copyText } from "../services/clipboard";
import { useWorkspace } from "../state/workspace";
import { ContextMenu, type ContextMenuEntry } from "./ContextMenu";
import { EmptyState } from "./EmptyState";

interface ExplorerMenuState {
  x: number;
  y: number;
  row: ProjectExplorerRow | null;
}

export function Explorer() {
  const archive = useWorkspace((state) => state.archive);
  const activeDescriptor = useWorkspace((state) => state.activeDescriptor);
  const selectClass = useWorkspace((state) => state.selectClass);
  const openResource = useWorkspace((state) => state.openResource);
  const closeProject = useWorkspace((state) => state.closeProject);
  const activeResourcePath = useWorkspace((state) => state.resourceDocument?.path ?? null);
  const loadingResourcePath = useWorkspace((state) => state.loadingResourcePath);
  const pinned = useWorkspace((state) => state.pinned);
  const togglePin = useWorkspace((state) => state.togglePin);
  const findReferences = useWorkspace((state) => state.findReferences);
  const revealRequest = useWorkspace((state) => state.revealRequest);
  const { t } = useTranslation();
  const [query, setQuery] = useState("");
  const deferredQuery = useDeferredValue(query);
  const [mode, setMode] = useState<ExplorerMode>("tree");
  const [expandedNodes, setExpandedNodes] = useState<Set<string>>(new Set());
  const [focusIndex, setFocusIndex] = useState(-1);
  const [menu, setMenu] = useState<ExplorerMenuState | null>(null);
  const scrollRef = useRef<HTMLDivElement>(null);
  const pendingReveal = useRef<string | null>(null);
  const index = useMemo(
    () => new ProjectExplorerIndex(archive?.classes ?? [], archive?.resources ?? []),
    [archive?.classes, archive?.resources],
  );

  useEffect(() => {
    setExpandedNodes(index.initialExpansion(mode));
    setQuery("");
    setFocusIndex(-1);
  }, [archive?.sessionId, index, mode]);

  const rows = useMemo(
    () => index.rows(mode, expandedNodes, deferredQuery),
    [deferredQuery, expandedNodes, index, mode],
  );
  const virtualizer = useVirtualizer({
    count: rows.length,
    getScrollElement: () => scrollRef.current,
    estimateSize: () => 26,
    overscan: 16,
  });

  // "Reveal in Explorer" — expand the ancestor chain, then scroll to the
  // class row once the expanded rows have been recomputed.
  useEffect(() => {
    if (!revealRequest) {
      return;
    }
    const keys = index.expandPathTo(revealRequest.descriptor, mode);
    pendingReveal.current = revealRequest.descriptor;
    setQuery("");
    setExpandedNodes((current) => new Set([...current, ...keys]));
  }, [index, mode, revealRequest]);

  useEffect(() => {
    const descriptor = pendingReveal.current;
    if (!descriptor) {
      return;
    }
    const rowIndex = rows.findIndex(
      (row) => row.kind === "class" && row.classInfo.descriptor === descriptor,
    );
    if (rowIndex === -1) {
      return;
    }
    pendingReveal.current = null;
    setFocusIndex(rowIndex);
    virtualizer.scrollToIndex(rowIndex, { align: "center" });
  }, [rows, virtualizer]);

  const toggleNode = (key: string) => {
    setExpandedNodes((current) => {
      const next = new Set(current);
      if (next.has(key)) {
        next.delete(key);
      } else {
        next.add(key);
      }
      return next;
    });
  };

  const menuEntries = (row: ProjectExplorerRow | null): ContextMenuEntry[] => {
    const expansionEntries = (expanded: boolean, key: string): ContextMenuEntry[] => [
      {
        id: expanded ? "collapse" : "expand",
        icon: expanded ? <ChevronRight size={14} /> : <ChevronDown size={14} />,
        label: expanded ? t("explorer.collapse") : t("explorer.expand"),
        onSelect: () => toggleNode(key),
      },
      {
        id: "expand-all",
        icon: <ChevronDown size={14} />,
        label: t("explorer.expandAll"),
        onSelect: () => setExpandedNodes(index.allExpansion(mode)),
      },
      {
        id: "collapse-all",
        icon: <ChevronRight size={14} />,
        label: t("explorer.collapseAll"),
        onSelect: () => setExpandedNodes(new Set()),
      },
    ];

    if (!row) {
      if (!archive) {
        return [];
      }
      const entries: ContextMenuEntry[] = [
        {
          id: "expand-all",
          icon: <ChevronDown size={14} />,
          label: t("explorer.expandAll"),
          onSelect: () => setExpandedNodes(index.allExpansion(mode)),
        },
        {
          id: "collapse-all",
          icon: <ChevronRight size={14} />,
          label: t("explorer.collapseAll"),
          onSelect: () => setExpandedNodes(new Set()),
        },
        "separator",
        {
          id: "tree-mode",
          icon: <ListTree size={14} />,
          label: t("explorer.treeMode"),
          disabled: mode === "tree",
          onSelect: () => setMode("tree"),
        },
        {
          id: "flat-mode",
          icon: <Rows3 size={14} />,
          label: t("explorer.flatMode"),
          disabled: mode === "packages",
          onSelect: () => setMode("packages"),
        },
      ];
      entries.push(
        "separator",
        {
          id: "close-project",
          icon: <X size={14} />,
          label: t("explorer.closeProject"),
          shortcut: sc("mod+shift+w"),
          onSelect: () => void closeProject(),
        },
      );
      return entries;
    }

    if (row.kind === "section" || row.kind === "directory") {
      const entries = expansionEntries(row.expanded, row.key);
      if (row.kind === "directory") {
        entries.push(
          "separator",
          {
            id: "copy-resource-directory",
            icon: <Copy size={14} />,
            label: t("explorer.copyPath"),
            onSelect: () => void copyText(row.path),
          },
        );
      }
      return entries;
    }

    if (row.kind === "resource") {
      return [
        {
          id: "open-resource",
          icon: <CornerDownRight size={14} />,
          label: t("explorer.openResource"),
          onSelect: () => void openResource(row.entry.path),
        },
        "separator",
        {
          id: "copy-resource-path",
          icon: <Copy size={14} />,
          label: t("explorer.copyPath"),
          onSelect: () => void copyText(row.entry.path),
        },
      ];
    }

    if (row.kind === "package") {
      return [
        ...expansionEntries(row.expanded, row.key),
        "separator",
        {
          id: "filter-package",
          icon: <Search size={14} />,
          label: t("explorer.filterPackage"),
          disabled: row.qualifiedName === "<default>",
          onSelect: () => setQuery(row.qualifiedName),
        },
        {
          id: "copy-package",
          icon: <Copy size={14} />,
          label: t("explorer.copyPackageName"),
          onSelect: () => void copyText(row.qualifiedName),
        },
      ];
    }

    const descriptor = row.classInfo.descriptor;
    const isPinned = pinned.includes(descriptor);
    const entries: ContextMenuEntry[] = [
      {
        id: "open-class",
        icon: <CornerDownRight size={14} />,
        label: t("explorer.openClass"),
        onSelect: () => void selectClass(descriptor),
      },
      {
        id: "find-references",
        icon: <Search size={14} />,
        label: t("editor.findReferences"),
        shortcut: sc("alt+f7"),
        onSelect: () => void findReferences(
          { kind: "class", classDescriptor: descriptor },
          row.classInfo.displayName,
        ),
      },
      {
        id: "pin-class",
        icon: isPinned ? <PinOff size={14} /> : <Pin size={14} />,
        label: isPinned ? t("tabs.unpin") : t("tabs.pin"),
        onSelect: () => {
          if (isPinned) {
            togglePin(descriptor);
            return;
          }
          void selectClass(descriptor, { preview: false }).then(() => {
            const workspace = useWorkspace.getState();
            if (workspace.documents.some((entry) => entry.descriptor === descriptor)) {
              workspace.togglePin(descriptor);
            }
          });
        },
      },
    ];
    if (row.hasChildren) {
      entries.push("separator", ...expansionEntries(row.expanded, row.key));
    }
    entries.push(
      "separator",
      {
        id: "copy-qualified-name",
        icon: <Copy size={14} />,
        label: t("tabs.copyQualifiedName"),
        onSelect: () => void copyText(row.classInfo.qualifiedName),
      },
      {
        id: "copy-descriptor",
        icon: <Braces size={14} />,
        label: t("tabs.copyDescriptor"),
        onSelect: () => void copyText(descriptor),
      },
    );
    return entries;
  };

  const moveFocus = (next: number) => {
    const clamped = Math.max(0, Math.min(rows.length - 1, next));
    setFocusIndex(clamped);
    virtualizer.scrollToIndex(clamped, { align: "auto" });
  };

  const parentIndexOf = (from: number): number => {
    const depth = rows[from]?.depth ?? 0;
    if (!depth) {
      return -1;
    }
    for (let i = from - 1; i >= 0; i--) {
      if (rows[i].depth === depth - 1) {
        return i;
      }
    }
    return -1;
  };

  const onTreeKeyDown = (event: React.KeyboardEvent) => {
    if (!rows.length) {
      return;
    }
    const current = focusIndex >= 0 ? focusIndex : 0;
    const row = rows[current];
    switch (event.key) {
      case "ArrowDown":
        event.preventDefault();
        moveFocus(current + 1);
        break;
      case "ArrowUp":
        event.preventDefault();
        moveFocus(focusIndex > 0 ? current - 1 : 0);
        break;
      case "Home":
        event.preventDefault();
        moveFocus(0);
        break;
      case "End":
        event.preventDefault();
        moveFocus(rows.length - 1);
        break;
      case "PageDown":
        event.preventDefault();
        moveFocus(current + Math.max(1, Math.floor(virtualizer.getVirtualItems().length - 1)));
        break;
      case "PageUp":
        event.preventDefault();
        moveFocus(current - Math.max(1, Math.floor(virtualizer.getVirtualItems().length - 1)));
        break;
      case "ArrowRight": {
        event.preventDefault();
        if (!row) break;
        const expandable =
          row.kind === "section" ||
          row.kind === "directory" ||
          row.kind === "package" ||
          (row.kind === "class" && row.hasChildren);
        if (expandable && !row.expanded) {
          toggleNode(row.key);
        } else if (expandable) {
          moveFocus(current + 1);
        }
        break;
      }
      case "ArrowLeft": {
        event.preventDefault();
        if (!row) break;
        const expandable =
          row.kind === "section" ||
          row.kind === "directory" ||
          row.kind === "package" ||
          (row.kind === "class" && row.hasChildren);
        if (expandable && row.expanded) {
          toggleNode(row.key);
        } else {
          const parent = parentIndexOf(current);
          if (parent >= 0) {
            moveFocus(parent);
          }
        }
        break;
      }
      case "Enter": {
        event.preventDefault();
        if (!row) break;
        if (row.kind === "section" || row.kind === "directory" || row.kind === "package") {
          toggleNode(row.key);
        } else if (row.kind === "resource") {
          void openResource(row.entry.path);
        } else {
          void selectClass(row.classInfo.descriptor);
        }
        break;
      }
      default:
        break;
    }
  };

  const onSearchKeyDown = (event: React.KeyboardEvent) => {
    if (event.key === "Escape") {
      event.preventDefault();
      setQuery("");
      scrollRef.current?.focus();
    } else if (event.key === "Enter") {
      const firstOpenable = rows.find(
        (row) => row.kind === "class" || row.kind === "resource",
      );
      if (firstOpenable) {
        event.preventDefault();
        if (firstOpenable.kind === "class") {
          void selectClass(firstOpenable.classInfo.descriptor);
        } else {
          void openResource(firstOpenable.entry.path);
        }
      }
    }
  };

  return (
    <aside className="explorer-panel flex min-h-0 min-w-0 flex-col overflow-hidden border-r border-[var(--border)] bg-[var(--sidebar-surface)]">
      <div className="panel-header explorer-toolbar">
        <div className="explorer-search">
          <Search
            className="explorer-search-icon"
            size={12}
            aria-hidden="true"
          />
          <input
            className="search-input explorer-search-input"
            value={query}
            onChange={(event) => setQuery(event.target.value)}
            onKeyDown={onSearchKeyDown}
            placeholder={t("explorer.filter")}
            spellCheck={false}
            disabled={!archive}
            aria-label={t("explorer.filter")}
          />
          {query ? (
            <button
              type="button"
              title={t("explorer.clearFilter")}
              aria-label={t("explorer.clearFilter")}
              className="explorer-search-clear"
              onClick={() => setQuery("")}
            >
              <X size={11} />
            </button>
          ) : null}
        </div>
        <div className="seg-control">
          <button
            type="button"
            className={`seg-button ${mode === "tree" ? "seg-button-active" : ""}`}
            title={t("explorer.treeMode")}
            aria-label={t("explorer.treeMode")}
            aria-pressed={mode === "tree"}
            onClick={() => setMode("tree")}
          >
            <ListTree size={12} />
          </button>
          <button
            type="button"
            className={`seg-button ${mode === "packages" ? "seg-button-active" : ""}`}
            title={t("explorer.flatMode")}
            aria-label={t("explorer.flatMode")}
            aria-pressed={mode === "packages"}
            onClick={() => setMode("packages")}
          >
            <Rows3 size={12} />
          </button>
        </div>
      </div>

      <div
        ref={scrollRef}
        className="min-h-0 flex-1 overflow-auto outline-none"
        role="tree"
        aria-label={t("explorer.treeAria")}
        tabIndex={0}
        aria-activedescendant={
          focusIndex >= 0 && rows[focusIndex] ? `explorer-row-${focusIndex}` : undefined
        }
        onKeyDown={onTreeKeyDown}
        onContextMenu={(event) => {
          if (!archive) {
            return;
          }
          event.preventDefault();
          setMenu({ x: event.clientX, y: event.clientY, row: null });
        }}
      >
        {archive ? (
          rows.length ? (
            <div
              className="relative w-full"
              style={{ height: `${virtualizer.getTotalSize()}px` }}
            >
              {virtualizer.getVirtualItems().map((virtualRow) => {
                const row = rows[virtualRow.index];
                return (
                  <div
                    key={row.key}
                    id={`explorer-row-${virtualRow.index}`}
                    role="treeitem"
                    aria-level={row.depth + 1}
                    aria-selected={
                      (row.kind === "class" && row.classInfo.descriptor === activeDescriptor) ||
                      (row.kind === "resource" && row.entry.path === activeResourcePath)
                    }
                    aria-expanded={
                      row.kind === "section" ||
                      row.kind === "directory" ||
                      row.kind === "package" ||
                      (row.kind === "class" && row.hasChildren)
                        ? row.expanded
                        : undefined
                    }
                    className="absolute left-0 top-0 w-full"
                    style={{
                      height: `${virtualRow.size}px`,
                      transform: `translateY(${virtualRow.start}px)`,
                    }}
                  >
                    <ExplorerItem
                      row={row}
                      active={
                        (row.kind === "class" && row.classInfo.descriptor === activeDescriptor) ||
                        (row.kind === "resource" &&
                          (row.entry.path === activeResourcePath ||
                            row.entry.path === loadingResourcePath))
                      }
                      focused={virtualRow.index === focusIndex}
                      mode={mode}
                      onToggleNode={toggleNode}
                      onSelectClass={(descriptor) => {
                        setFocusIndex(virtualRow.index);
                        void selectClass(descriptor);
                      }}
                      onOpenClass={(descriptor) => {
                        setFocusIndex(virtualRow.index);
                        void selectClass(descriptor, { preview: false });
                      }}
                      onSelectResource={(path) => {
                        setFocusIndex(virtualRow.index);
                        void openResource(path);
                      }}
                      onFocusRow={() => setFocusIndex(virtualRow.index)}
                      onContextMenu={(event) => {
                        event.preventDefault();
                        event.stopPropagation();
                        setFocusIndex(virtualRow.index);
                        setMenu({
                          x: event.clientX,
                          y: event.clientY,
                          row,
                        });
                      }}
                    />
                  </div>
                );
              })}
            </div>
          ) : (
            <EmptyState compact icon={<Search size={16} />} title={t("explorer.empty")} />
          )
        ) : (
          <EmptyState compact icon={<FolderOpen size={17} />} title={t("explorer.noArchive")} />
        )}
      </div>
      {menu ? (
        <ContextMenu
          x={menu.x}
          y={menu.y}
          entries={menuEntries(menu.row)}
          ariaLabel={t("explorer.contextMenu")}
          onClose={() => setMenu(null)}
        />
      ) : null}
    </aside>
  );
}

interface ExplorerItemProps {
  row: ProjectExplorerRow;
  active: boolean;
  focused: boolean;
  mode: ExplorerMode;
  onToggleNode: (key: string) => void;
  onSelectClass: (descriptor: string) => void;
  onOpenClass: (descriptor: string) => void;
  onSelectResource: (path: string) => void;
  onFocusRow: () => void;
  onContextMenu: (event: React.MouseEvent) => void;
}

function ExplorerItem({
  row,
  active,
  focused,
  mode,
  onToggleNode,
  onSelectClass,
  onOpenClass,
  onSelectResource,
  onFocusRow,
  onContextMenu,
}: ExplorerItemProps) {
  const { t } = useTranslation();
  if (row.kind === "section") {
    return (
      <button
        type="button"
        tabIndex={-1}
        className={`tree-row font-medium ${focused ? "tree-row-focus" : ""}`}
        style={{ paddingLeft: `${6 + row.depth * 13}px` }}
        onClick={() => {
          onFocusRow();
          onToggleNode(row.key);
        }}
        onContextMenu={onContextMenu}
      >
        <span className="flex size-[14px] shrink-0 items-center justify-center">
          {row.expanded ? <ChevronDown size={12} /> : <ChevronRight size={12} />}
        </span>
        {row.section === "sources" ? (
          <Library size={13} className="shrink-0 text-[var(--glyph-class)]" />
        ) : (
          <FolderOpen size={13} className="shrink-0 text-[var(--glyph-package)]" />
        )}
        <span className="min-w-0 flex-1 truncate text-left">
          {t(row.section === "sources" ? "explorer.sources" : "explorer.resources")}
        </span>
        <span className="tree-count">{row.count}</span>
      </button>
    );
  }

  if (row.kind === "directory") {
    return (
      <button
        type="button"
        tabIndex={-1}
        className={`tree-row ${focused ? "tree-row-focus" : ""}`}
        style={{ paddingLeft: `${6 + row.depth * 13}px` }}
        title={row.path}
        onClick={() => {
          onFocusRow();
          onToggleNode(row.key);
        }}
        onContextMenu={onContextMenu}
      >
        <span className="flex size-[14px] shrink-0 items-center justify-center">
          {row.expanded ? <ChevronDown size={12} /> : <ChevronRight size={12} />}
        </span>
        {row.expanded ? (
          <FolderOpen size={13} className="shrink-0 text-[var(--glyph-package)]" />
        ) : (
          <Folder size={13} className="shrink-0 text-[var(--glyph-package)]" />
        )}
        <span className="min-w-0 flex-1 truncate text-left">{row.name}</span>
        <span className="tree-count">{row.fileCount}</span>
      </button>
    );
  }

  if (row.kind === "resource") {
    const icon =
      row.entry.kind === "xml" || row.entry.kind === "text" ? (
        <FileCode2 size={12} className="shrink-0 text-[var(--glyph-class)]" />
      ) : row.entry.kind === "image" ? (
        <FileImage size={12} className="shrink-0 text-[var(--glyph-package)]" />
      ) : row.entry.kind === "resourceTable" ? (
        <Database size={12} className="shrink-0 text-[var(--glyph-field)]" />
      ) : (
        <File size={12} className="shrink-0 text-[var(--text-muted)]" />
      );
    return (
      <button
        type="button"
        tabIndex={-1}
        className={`tree-row ${active ? "tree-row-active" : ""} ${
          focused ? "tree-row-focus" : ""
        }`}
        style={{ paddingLeft: `${20 + row.depth * 13}px` }}
        title={row.entry.path}
        onClick={() => onSelectResource(row.entry.path)}
        onContextMenu={onContextMenu}
      >
        {icon}
        <span className="min-w-0 flex-1 truncate text-left">
          {row.searchResult ? row.entry.path : row.name}
        </span>
      </button>
    );
  }

  if (row.kind === "package") {
    return (
      <button
        type="button"
        tabIndex={-1}
        className={`tree-row ${focused ? "tree-row-focus" : ""}`}
        style={{ paddingLeft: `${6 + row.depth * 13}px` }}
        title={row.qualifiedName}
        onClick={() => {
          onFocusRow();
          onToggleNode(row.key);
        }}
        onContextMenu={onContextMenu}
      >
        <span className="flex size-[14px] shrink-0 items-center justify-center">
          {row.expanded ? <ChevronDown size={12} /> : <ChevronRight size={12} />}
        </span>
        {row.expanded ? (
          <PackageOpen size={13} className="shrink-0 text-[var(--glyph-package)]" />
        ) : (
          <Package size={13} className="shrink-0 text-[var(--glyph-package)]" />
        )}
        <span className="min-w-0 flex-1 truncate text-left">{row.name}</span>
        <span className="tree-count">{row.classCount}</span>
      </button>
    );
  }

  const label = row.searchResult
    ? row.classInfo.qualifiedName
    : mode === "packages"
      ? row.classInfo.binaryName
      : row.classInfo.displayName;
  return (
    <div
      className={`tree-row ${active ? "tree-row-active" : ""} ${
        focused ? "tree-row-focus" : ""
      }`}
      style={{ paddingLeft: `${6 + row.depth * 13}px` }}
      onClick={() => onSelectClass(row.classInfo.descriptor)}
      onDoubleClick={() => onOpenClass(row.classInfo.descriptor)}
      onContextMenu={onContextMenu}
    >
      {row.hasChildren ? (
        <button
          type="button"
          tabIndex={-1}
          className="flex size-[14px] shrink-0 items-center justify-center"
          title={row.expanded ? t("explorer.collapseNested") : t("explorer.expandNested")}
          aria-label={row.expanded ? t("explorer.collapseNested") : t("explorer.expandNested")}
          onClick={(event) => {
            event.stopPropagation();
            onFocusRow();
            onToggleNode(row.key);
          }}
        >
          {row.expanded ? <ChevronDown size={12} /> : <ChevronRight size={12} />}
        </button>
      ) : (
        <span className={row.searchResult ? "w-0" : "w-[14px] shrink-0"} />
      )}
      <button
        type="button"
        tabIndex={-1}
        className="flex min-w-0 flex-1 items-center gap-1.5"
        onClick={(event) => {
          event.stopPropagation();
          onSelectClass(row.classInfo.descriptor);
        }}
        title={row.classInfo.qualifiedName}
      >
        <Braces size={12} className="shrink-0 text-[var(--glyph-class)]" />
        <span className="min-w-0 flex-1 truncate text-left">{label}</span>
      </button>
    </div>
  );
}
