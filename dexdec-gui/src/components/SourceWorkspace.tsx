import { LoaderCircle, PanelRight } from "lucide-react";
import { lazy, Suspense, useEffect, useRef, useState } from "react";

import type {
  EditorGroup,
  EditorLayoutNode,
  EditorSplitAxis,
  EditorSplitSide,
} from "../domain/editorLayout";
import type { SourceDocument } from "../domain/models";
import { useTranslation } from "../i18n";
import { EditorDragSession } from "../services/editorDrag";
import { useWorkspace } from "../state/workspace";
import { Breadcrumbs } from "./Breadcrumbs";
import { DocumentTabs } from "./DocumentTabs";
import { EmptyState } from "./EmptyState";
import { ProblemsPanel } from "./ProblemsPanel";
import { ReferencesPanel } from "./ReferencesPanel";
import { CodeSearchPanel } from "./CodeSearchPanel";
import { RecentProjects } from "./RecentProjects";

const CodeEditor = lazy(() => import("./CodeEditor"));
const PeekView = lazy(() => import("./PeekView"));
const ResourceViewer = lazy(() => import("./ResourceViewer"));

export function SourceWorkspace() {
  const root = useWorkspace((state) => state.editorLayout.root);
  const peek = useWorkspace((state) => state.peek);
  const problemsOpen = useWorkspace((state) => state.problemsOpen);
  const references = useWorkspace((state) => state.references);
  const codeSearchVisible = useWorkspace((state) => state.codeSearchVisible);
  return (
    <main className="source-workspace relative flex min-h-0 min-w-0 flex-1 flex-col overflow-hidden bg-[var(--workspace)]">
      <div className="flex min-h-0 min-w-0 flex-1">
        <EditorNode node={root} path="root" />
      </div>

      {peek ? (
        <Suspense fallback={null}>
          <PeekView />
        </Suspense>
      ) : null}
      {problemsOpen ? <ProblemsPanel /> : null}
      {references ? <ReferencesPanel /> : null}
      {codeSearchVisible ? <CodeSearchPanel /> : null}
    </main>
  );
}

function EditorNode({ node, path }: { node: EditorLayoutNode; path: string }) {
  if (node.kind === "group") return <EditorPane group={node.id} />;
  return <EditorSplit node={node} path={path} />;
}

function EditorSplit({
  node,
  path,
}: {
  node: Extract<EditorLayoutNode, { kind: "split" }>;
  path: string;
}) {
  const containerRef = useRef<HTMLDivElement>(null);
  const [ratio, setRatio] = useState(50);
  const horizontal = node.axis === "horizontal";

  const beginResize = (event: React.PointerEvent<HTMLDivElement>) => {
    event.preventDefault();
    let currentRatio = ratio;
    const move = (pointer: PointerEvent) => {
      const bounds = containerRef.current?.getBoundingClientRect();
      if (!bounds) return;
      const extent = horizontal ? bounds.width : bounds.height;
      if (!extent) return;
      const offset = horizontal
        ? pointer.clientX - bounds.left
        : pointer.clientY - bounds.top;
      currentRatio = Math.min(80, Math.max(20, (offset / extent) * 100));
      setRatio(currentRatio);
    };
    const finish = () => {
      window.removeEventListener("pointermove", move);
      window.removeEventListener("pointerup", finish);
      document.body.classList.remove(horizontal ? "col-resizing" : "row-resizing");
    };
    document.body.classList.add(horizontal ? "col-resizing" : "row-resizing");
    window.addEventListener("pointermove", move);
    window.addEventListener("pointerup", finish, { once: true });
  };

  return (
    <div
      ref={containerRef}
      className={`editor-split ${horizontal ? "is-horizontal" : "is-vertical"}`}
      style={horizontal
        ? { gridTemplateColumns: `${ratio}fr 5px ${100 - ratio}fr` }
        : { gridTemplateRows: `${ratio}fr 5px ${100 - ratio}fr` }}
    >
      <EditorNode node={node.first} path={`${path}.first`} />
      <div
        className="editor-split-handle"
        role="separator"
        aria-orientation={horizontal ? "vertical" : "horizontal"}
        onPointerDown={beginResize}
      />
      <EditorNode node={node.second} path={`${path}.second`} />
    </div>
  );
}

type EditorDropZone = "group" | "split-left" | "split-right" | "split-top" | "split-bottom";

function splitForZone(zone: EditorDropZone): {
  axis: EditorSplitAxis;
  side: EditorSplitSide;
} | null {
  switch (zone) {
    case "split-left": return { axis: "horizontal", side: "before" };
    case "split-right": return { axis: "horizontal", side: "after" };
    case "split-top": return { axis: "vertical", side: "before" };
    case "split-bottom": return { axis: "vertical", side: "after" };
    default: return null;
  }
}

function EditorPane({
  group,
}: {
  group: EditorGroup;
}) {
  const archive = useWorkspace((state) => state.archive);
  const documents = useWorkspace((state) => state.documents);
  const editorLayout = useWorkspace((state) => state.editorLayout);
  const loadingDescriptor = useWorkspace((state) => state.loadingDescriptor);
  const openingArchive = useWorkspace((state) => state.openingArchive);
  const resourceDocument = useWorkspace((state) => state.resourceDocument);
  const resourceNavigation = useWorkspace((state) => state.resourceNavigation);
  const resourceGroup = useWorkspace((state) => state.resourceGroup);
  const loadingResourcePath = useWorkspace((state) => state.loadingResourcePath);
  const navigation = useWorkspace((state) => state.navigation);
  const chooseArchive = useWorkspace((state) => state.chooseArchive);
  const selectClass = useWorkspace((state) => state.selectClass);
  const moveDocument = useWorkspace((state) => state.moveDocument);
  const splitDocument = useWorkspace((state) => state.splitDocument);
  const focusEditorGroup = useWorkspace((state) => state.focusEditorGroup);
  const [dropZone, setDropZone] = useState<EditorDropZone | null>(null);
  const activeDescriptor = editorLayout.active[group] ?? null;
  const otherActiveDescriptor = Object.entries(editorLayout.active)
    .find(([candidate, descriptor]) => candidate !== group && descriptor)?.[1] ?? null;
  const document =
    documents.find((item) => item.descriptor === activeDescriptor) ?? null;
  const resourceHere = resourceGroup === group;
  const loadingClass =
    loadingDescriptor && loadingDescriptor === activeDescriptor && archive
      ? archive.classes.find((entry) => entry.descriptor === loadingDescriptor)
      : null;
  const { t } = useTranslation();

  useEffect(() => {
    const clear = () => setDropZone(null);
    window.addEventListener("dragend", clear, true);
    return () => window.removeEventListener("dragend", clear, true);
  }, []);

  const zoneAt = (event: React.DragEvent<HTMLElement>) => {
    const bounds = event.currentTarget.getBoundingClientRect();
    const x = (event.clientX - bounds.left) / bounds.width;
    const y = (event.clientY - bounds.top) / bounds.height;
    const edge = 0.24;
    if (x < edge) return "split-left" as const;
    if (x > 1 - edge) return "split-right" as const;
    if (y < edge) return "split-top" as const;
    if (y > 1 - edge) return "split-bottom" as const;
    return "group" as const;
  };

  return (
    <section
      className={`editor-group min-h-0 min-w-0 flex-1 ${editorLayout.focused === group ? "is-focused" : ""}`}
      onPointerDownCapture={() => {
        if (editorLayout.focused !== group) focusEditorGroup(group);
      }}
      onDragOver={(event) => {
        if (!EditorDragSession.current()) return;
        event.preventDefault();
        event.dataTransfer.dropEffect = "move";
        setDropZone(zoneAt(event));
      }}
      onDragLeave={(event) => {
        if (
          event.relatedTarget instanceof Node &&
          event.currentTarget.contains(event.relatedTarget)
        ) {
          return;
        }
        setDropZone(null);
      }}
      onDrop={(event) => {
        const source = EditorDragSession.current();
        if (!source) return;
        event.preventDefault();
        const zone = zoneAt(event);
        const split = splitForZone(zone);
        if (split) {
          splitDocument(source.descriptor, source.group, group, split.axis, split.side);
        } else {
          moveDocument(source.descriptor, null, source.group, group);
        }
        EditorDragSession.finish();
        setDropZone(null);
      }}
    >
      {archive ? <DocumentTabs group={group} /> : null}
      {archive ? <Breadcrumbs group={group} /> : null}
      <div className="relative min-h-0 flex-1">
        {resourceHere && resourceDocument ? (
          <Suspense fallback={<CenteredLoading label={t("workspace.loadingResource")} />}>
            <ResourceViewer
              document={resourceDocument}
              navigation={
                resourceNavigation?.path === resourceDocument.path
                  ? resourceNavigation
                  : null
              }
            />
          </Suspense>
        ) : document ? (
          <SourceEditor
            group={group}
            document={document}
            navigation={
              navigation?.classDescriptor === document.descriptor ? navigation : null
            }
          />
        ) : openingArchive ? (
          <CenteredLoading label={t("workspace.indexing")} />
        ) : resourceHere && loadingResourcePath ? (
          <CenteredLoading label={t("workspace.loadingResource")} />
        ) : loadingClass ? (
          <CenteredLoading
            label={t(
              "workspace.decompilingClass",
              loadingClass.displayName ?? loadingDescriptor ?? "",
            )}
          />
        ) : archive ? (
          <EmptyEditor
            title={t("workspace.emptyEditorGroup")}
            action={
              otherActiveDescriptor ? (
                <button
                  type="button"
                  className="command-button"
                  onClick={() => void selectClass(otherActiveDescriptor, {
                    group,
                    preview: false,
                  })}
                >
                  <PanelRight size={13} />
                  {t("workspace.openInGroup")}
                </button>
              ) : null
            }
          />
        ) : (
          <RecentProjects />
        )}
        {document && (loadingDescriptor || openingArchive) ? (
          <div className="workspace-progress" aria-hidden="true" />
        ) : null}
      </div>
      {dropZone ? (
        <div className="editor-drop-overlay" data-zone={dropZone} aria-hidden="true" />
      ) : null}
    </section>
  );
}

function SourceEditor({
  group,
  document,
  navigation,
}: {
  group: EditorGroup;
  document: SourceDocument;
  navigation: import("../domain/models").MemberNavigation | null;
}) {
  const { t } = useTranslation();
  return (
    <Suspense
      fallback={
        <div className="flex h-full items-center justify-center text-[11.5px] text-[var(--text-faint)]">
          {t("workspace.loadingEditor")}
        </div>
      }
    >
      <CodeEditor group={group} document={document} navigation={navigation} />
    </Suspense>
  );
}

function EmptyEditor({
  title,
  action,
}: {
  title: string;
  action?: React.ReactNode;
}) {
  return <EmptyState title={title} action={action} />;
}

function CenteredLoading({ label }: { label: string }) {
  return (
    <div className="flex h-full flex-col items-center justify-center gap-3">
      <LoaderCircle size={17} className="animate-spin text-[var(--accent)]" />
      <span className="text-[12px] text-[var(--text-faint)]">{label}</span>
    </div>
  );
}
