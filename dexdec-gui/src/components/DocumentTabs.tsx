import {
  Braces,
  ChevronLeft,
  ChevronRight,
  File,
  FileCode2,
  FileImage,
  LoaderCircle,
  PanelRight,
  Pin,
  X,
} from "lucide-react";
import { useCallback, useEffect, useRef, useState } from "react";

import { useTranslation } from "../i18n";
import type { EditorGroup } from "../domain/editorLayout";
import { sc } from "../platform";
import { copyText } from "../services/clipboard";
import { EditorDragSession } from "../services/editorDrag";
import { useWorkspace } from "../state/workspace";
import { ContextMenu, type ContextMenuEntry } from "./ContextMenu";

export function DocumentTabs({ group }: { group: EditorGroup }) {
  const archive = useWorkspace((state) => state.archive);
  const documents = useWorkspace((state) => state.documents);
  const pinned = useWorkspace((state) => state.pinned);
  const editorLayout = useWorkspace((state) => state.editorLayout);
  const loadingDescriptor = useWorkspace((state) => state.loadingDescriptor);
  const resourceDocument = useWorkspace((state) => state.resourceDocument);
  const resourceGroup = useWorkspace((state) => state.resourceGroup);
  const loadingResourcePath = useWorkspace((state) => state.loadingResourcePath);
  const activateDocument = useWorkspace((state) => state.activateDocument);
  const closeDocument = useWorkspace((state) => state.closeDocument);
  const closeResource = useWorkspace((state) => state.closeResource);
  const openResource = useWorkspace((state) => state.openResource);
  const closeOtherDocuments = useWorkspace((state) => state.closeOtherDocuments);
  const closeAllDocuments = useWorkspace((state) => state.closeAllDocuments);
  const closeDocumentsToRight = useWorkspace((state) => state.closeDocumentsToRight);
  const reopenClosedTab = useWorkspace((state) => state.reopenClosedTab);
  const togglePin = useWorkspace((state) => state.togglePin);
  const promotePreview = useWorkspace((state) => state.promotePreview);
  const splitEditor = useWorkspace((state) => state.splitEditor);
  const closeEditorGroup = useWorkspace((state) => state.closeEditorGroup);
  const revealInExplorer = useWorkspace((state) => state.revealInExplorer);
  const stripRef = useRef<HTMLDivElement>(null);
  const { t } = useTranslation();
  const [menu, setMenu] = useState<{ x: number; y: number; descriptor: string } | null>(
    null,
  );
  const [overflow, setOverflow] = useState({ left: false, right: false });
  const [drag, setDrag] = useState<{ source: string; over: string } | null>(null);
  const moveDocument = useWorkspace((state) => state.moveDocument);
  const groupIds = Object.keys(editorLayout.tabs);
  const groupDocuments = (editorLayout.tabs[group] ?? [])
    .map((descriptor) =>
      documents.find((document) => document.descriptor === descriptor),
    )
    .filter((document): document is NonNullable<typeof document> => Boolean(document));
  const activeDescriptor = editorLayout.active[group] ?? null;
  const resourceHere = resourceGroup === group;

  const loadingClass =
    loadingDescriptor === activeDescriptor &&
    !documents.some((doc) => doc.descriptor === loadingDescriptor)
      ? archive?.classes.find((entry) => entry.descriptor === loadingDescriptor)
      : null;

  useEffect(() => {
    stripRef.current
      ?.querySelector(".document-tab-active")
      ?.scrollIntoView({ block: "nearest", inline: "nearest" });
  }, [activeDescriptor, documents.length, resourceDocument?.path, loadingResourcePath]);

  /* Which ends of the strip still have tabs hidden past the edge. */
  const syncOverflow = useCallback(() => {
    const strip = stripRef.current;
    if (!strip) {
      return;
    }
    const remaining = strip.scrollWidth - strip.clientWidth - strip.scrollLeft;
    setOverflow((current) => {
      const next = { left: strip.scrollLeft > 1, right: remaining > 1 };
      return current.left === next.left && current.right === next.right
        ? current
        : next;
    });
  }, []);

  useEffect(() => {
    const strip = stripRef.current;
    if (!strip) {
      return;
    }
    syncOverflow();
    const observer = new ResizeObserver(syncOverflow);
    observer.observe(strip);
    return () => observer.disconnect();
  }, [groupDocuments.length, loadingClass?.descriptor, loadingResourcePath, resourceDocument?.path, syncOverflow]);

  const scrollStrip = (direction: -1 | 1) => {
    const strip = stripRef.current;
    if (!strip) {
      return;
    }
    strip.scrollBy({
      left: direction * Math.max(160, strip.clientWidth * 0.75),
      behavior: "smooth",
    });
  };

  const onWheel = (event: React.WheelEvent<HTMLDivElement>) => {
    const strip = event.currentTarget;
    if (Math.abs(event.deltaY) > Math.abs(event.deltaX)) {
      strip.scrollLeft += event.deltaY;
      event.preventDefault();
    }
  };

  const menuEntries = (descriptor: string): ContextMenuEntry[] => {
    const document = documents.find((item) => item.descriptor === descriptor);
    const isPinned = pinned.includes(descriptor);
    const closable = groupDocuments.length > 1 || !isPinned;
    const index = groupDocuments.findIndex(
      (item) => item.descriptor === descriptor,
    );
    const hasClosableRight = groupDocuments
      .slice(index + 1)
      .some((item) => !pinned.includes(item.descriptor));
    const otherGroup = groupIds.find((candidate) => candidate !== group) ?? null;
    return [
      {
        label: isPinned ? t("tabs.unpin") : t("tabs.pin"),
        onSelect: () => togglePin(descriptor),
      },
      "separator",
      {
        label: t("tabs.closePlain"),
        shortcut: sc("mod+w"),
        onSelect: () => closeDocument(descriptor, group),
      },
      {
        label: t("tabs.closeOthers"),
        disabled: !closable,
        onSelect: () => closeOtherDocuments(descriptor, group),
      },
      {
        label: t("tabs.closeRight"),
        disabled: !hasClosableRight,
        onSelect: () => closeDocumentsToRight(descriptor, group),
      },
      {
        label: t("tabs.closeAll"),
        onSelect: () => closeAllDocuments(group),
      },
      {
        label: t("tabs.reopenClosed"),
        shortcut: sc("mod+shift+t"),
        disabled: !useWorkspace.getState().closedTabs.length,
        onSelect: reopenClosedTab,
      },
      "separator",
      {
        label: t("tabs.splitRight"),
        onSelect: () => splitEditor(descriptor, group, "horizontal", "after"),
      },
      ...(otherGroup
        ? [{
            label: t("tabs.moveToGroup", t("tabs.rightGroup")),
            onSelect: () => moveDocument(descriptor, null, group, otherGroup),
          } satisfies Exclude<ContextMenuEntry, "separator">]
        : []),
      ...(groupIds.length > 1
        ? [
            {
              label: t("tabs.closeGroup"),
              onSelect: () => closeEditorGroup(group),
            } satisfies Exclude<ContextMenuEntry, "separator">,
          ]
        : []),
      "separator",
      {
        label: t("tabs.revealInExplorer"),
        onSelect: () => revealInExplorer(descriptor),
      },
      {
        label: t("tabs.copyQualifiedName"),
        disabled: !document,
        onSelect: () => {
          if (document) {
            void copyText(document.outline.qualifiedName);
          }
        },
      },
      {
        label: t("tabs.copyDescriptor"),
        onSelect: () => void copyText(descriptor),
      },
    ];
  };

  if (
    groupIds.length === 1 &&
    !groupDocuments.length &&
    !loadingClass &&
    !(resourceHere && resourceDocument) &&
    !(resourceHere && loadingResourcePath)
  ) {
    return null;
  }

  const scrollable = overflow.left || overflow.right;
  const fade = scrollable
    ? overflow.left && overflow.right
      ? "both"
      : overflow.left
        ? "left"
        : "right"
    : "none";

  return (
    <div className="document-tabs">
      {scrollable ? (
        <button
          type="button"
          className="tab-scroll"
          title={t("tabs.scrollLeft")}
          aria-label={t("tabs.scrollLeft")}
          disabled={!overflow.left}
          onClick={() => scrollStrip(-1)}
        >
          <ChevronLeft size={14} />
        </button>
      ) : null}

      <div
        ref={stripRef}
        onWheel={onWheel}
        onScroll={syncOverflow}
        onDragOver={(event) => {
          if (!EditorDragSession.current()) return;
          event.preventDefault();
          event.stopPropagation();
          event.dataTransfer.dropEffect = "move";
        }}
        onDrop={(event) => {
          const source = EditorDragSession.current();
          if (!source) return;
          event.preventDefault();
          event.stopPropagation();
          moveDocument(source.descriptor, null, source.group, group);
          EditorDragSession.finish();
          setDrag(null);
        }}
        data-fade={fade}
        className="document-tab-strip"
      >
        {groupDocuments.map((document) => {
          const isPinned = pinned.includes(document.descriptor);
          const isPreview = editorLayout.preview[group] === document.descriptor;
          return (
            <div
              key={document.descriptor}
              draggable
              data-editor-tab={document.descriptor}
              className={`document-tab ${
                document.descriptor === activeDescriptor ? "document-tab-active" : ""
              } ${isPinned ? "document-tab-pinned" : ""} ${
                isPreview ? "document-tab-preview" : ""
              } ${
                drag?.source === document.descriptor ? "is-dragging" : ""
              } ${
                drag && drag.over === document.descriptor && drag.source !== drag.over
                  ? "is-drop-target"
                  : ""
              }`}
              onDragStart={(event) => {
                EditorDragSession.begin(document.descriptor, group);
                event.dataTransfer.effectAllowed = "move";
                event.dataTransfer.setData("text/plain", document.descriptor);
                setDrag({ source: document.descriptor, over: document.descriptor });
              }}
              onDragOver={(event) => {
                const source = EditorDragSession.current();
                if (!source) {
                  return;
                }
                event.preventDefault();
                event.stopPropagation();
                event.dataTransfer.dropEffect = "move";
                if (drag?.over !== document.descriptor) {
                  setDrag({ source: source.descriptor, over: document.descriptor });
                }
              }}
              onDrop={(event) => {
                event.preventDefault();
                event.stopPropagation();
                const source = EditorDragSession.current();
                if (source) {
                  moveDocument(
                    source.descriptor,
                    document.descriptor,
                    source.group,
                    group,
                  );
                }
                EditorDragSession.finish();
                setDrag(null);
              }}
              onDragEnd={() => {
                EditorDragSession.finish();
                setDrag(null);
              }}
              onMouseDown={(event) => {
                if (event.button === 1 && !isPinned) {
                  event.preventDefault();
                  closeDocument(document.descriptor, group);
                }
              }}
              onDoubleClick={() => promotePreview(document.descriptor, group)}
              onContextMenu={(event) => {
                event.preventDefault();
                setMenu({
                  x: event.clientX,
                  y: event.clientY,
                  descriptor: document.descriptor,
                });
              }}
            >
              <button
                type="button"
                className="flex min-w-0 flex-1 items-center gap-1.5"
                onClick={() => activateDocument(document.descriptor, group)}
                title={`${document.outline.qualifiedName}\n${
                  isPinned
                    ? t("tabs.pinnedHint")
                    : isPreview
                      ? t("tabs.previewHint")
                      : t("tabs.unpinnedHint")
                }`}
              >
                <Braces size={12} className="shrink-0 text-[var(--glyph-class)]" />
                <span className="truncate">
                  {document.outline.qualifiedName.split(".").at(-1)}
                </span>
              </button>
              {isPinned ? (
                <button
                  type="button"
                  className="tab-close tab-pin"
                  title={t("tabs.unpin")}
                  aria-label={`${t("tabs.unpin")} ${document.outline.qualifiedName}`}
                  onClick={() => togglePin(document.descriptor)}
                >
                  <Pin size={10} />
                </button>
              ) : (
                <button
                  type="button"
                  className="tab-close"
                  title={t("tabs.close", sc("mod+w"))}
                  aria-label={`${t("tabs.close", sc("mod+w"))} ${document.outline.qualifiedName}`}
                  onClick={() => closeDocument(document.descriptor, group)}
                >
                  <X size={11} />
                </button>
              )}
            </div>
          );
        })}
        {loadingClass ? (
          <div className="document-tab document-tab-active">
            <LoaderCircle
              size={12}
              className="shrink-0 animate-spin text-[var(--accent)]"
            />
            <span className="truncate">{loadingClass.binaryName}</span>
          </div>
        ) : null}
        {resourceHere && resourceDocument ? (
          <div className="document-tab document-tab-active">
            <button
              type="button"
              className="flex min-w-0 flex-1 items-center gap-1.5"
              title={resourceDocument.path}
              onClick={() => void openResource(resourceDocument.path)}
            >
              {resourceDocument.kind === "image" ? (
                <FileImage size={12} className="shrink-0 text-[var(--glyph-package)]" />
              ) : resourceDocument.text != null ? (
                <FileCode2 size={12} className="shrink-0 text-[var(--glyph-class)]" />
              ) : (
                <File size={12} className="shrink-0 text-[var(--text-muted)]" />
              )}
              <span className="truncate">{resourceDocument.path.split("/").at(-1)}</span>
            </button>
            <button
              type="button"
              className="tab-close"
              title={t("tabs.close", sc("mod+w"))}
              aria-label={`${t("tabs.closePlain")} ${resourceDocument.path}`}
              onClick={closeResource}
            >
              <X size={11} />
            </button>
          </div>
        ) : resourceHere && loadingResourcePath ? (
          <div className="document-tab document-tab-active">
            <LoaderCircle
              size={12}
              className="shrink-0 animate-spin text-[var(--accent)]"
            />
            <span className="truncate">{loadingResourcePath.split("/").at(-1)}</span>
          </div>
        ) : null}
      </div>

      {scrollable ? (
        <button
          type="button"
          className="tab-scroll"
          title={t("tabs.scrollRight")}
          aria-label={t("tabs.scrollRight")}
          disabled={!overflow.right}
          onClick={() => scrollStrip(1)}
        >
          <ChevronRight size={14} />
        </button>
      ) : null}

      <button
        type="button"
        className="tab-scroll"
        title={t("tabs.splitRight")}
        aria-label={t("tabs.splitRight")}
        onClick={() => splitEditor(undefined, group, "horizontal", "after")}
      >
        <PanelRight size={13} />
      </button>

      {menu ? (
        <ContextMenu
          x={menu.x}
          y={menu.y}
          entries={menuEntries(menu.descriptor)}
          onClose={() => setMenu(null)}
        />
      ) : null}
    </div>
  );
}
