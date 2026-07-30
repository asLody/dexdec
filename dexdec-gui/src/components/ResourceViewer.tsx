import { syntaxHighlighting } from "@codemirror/language";
import { EditorView } from "@codemirror/view";
import CodeMirror from "@uiw/react-codemirror";
import { Binary, Database, File, FileImage } from "lucide-react";
import { useEffect, useMemo, useState } from "react";

import type { ResourceDocument, ResourceNavigation } from "../domain/models";
import {
  AndroidProjectIndex,
  XmlElementLocator,
  XmlNavigationResolver,
} from "../domain/xmlNavigation";
import { useTranslation } from "../i18n";
import { useWorkspace } from "../state/workspace";
import { editorTheme, sourceHighlight } from "./CodeEditor";
import { EditorLinkInteraction } from "./editorLinks";
import {
  EditorNavigationFocus,
  navigationFocusExtension,
} from "./editorNavigationFocus";
import { resourceLanguages } from "./resourceLanguages";

export default function ResourceViewer({
  document,
  navigation,
}: {
  document: ResourceDocument;
  navigation: ResourceNavigation | null;
}) {
  if (document.dataUrl) {
    return <ImagePreview document={document} />;
  }
  if (document.text != null) {
    return <TextPreview document={document} navigation={navigation} />;
  }
  return <BinaryPreview document={document} />;
}

function TextPreview({
  document,
  navigation,
}: {
  document: ResourceDocument;
  navigation: ResourceNavigation | null;
}) {
  const archive = useWorkspace((state) => state.archive);
  const project = useMemo(
    () => (archive ? new AndroidProjectIndex(archive) : null),
    [archive],
  );
  const resolver = useMemo(
    () =>
      document.kind === "xml" && project
        ? new XmlNavigationResolver(document.path, document.text ?? "", project)
        : null,
    [document.kind, document.path, document.text, project],
  );
  const links = useMemo(
    () =>
      resolver
        ? new EditorLinkInteraction(resolver, (link, view) => {
            view.dispatch({
              selection: { anchor: link.range.from, head: link.range.to },
            });
            if (link.destination.kind === "local") {
              view.dispatch({
                selection: {
                  anchor: link.destination.from,
                  head: link.destination.to,
                },
                effects: EditorView.scrollIntoView(link.destination.from, {
                  y: "center",
                }),
              });
              view.focus();
            } else if (link.destination.kind === "class") {
              void useWorkspace.getState().selectClass(link.destination.descriptor);
            } else {
              void useWorkspace.getState().openResource(link.destination.path);
            }
          })
        : null,
    [resolver],
  );
  const focus = useMemo(() => new EditorNavigationFocus(), []);
  const [view, setView] = useState<EditorView | null>(null);
  const extensions = useMemo(() => {
    const language = resourceLanguages.extensionFor(document.textFormat);
    return [
      editorTheme,
      syntaxHighlighting(sourceHighlight),
      navigationFocusExtension,
      ...(language ? [language] : []),
      ...(links ? links.extension() : []),
    ];
  }, [document.textFormat, links]);

  useEffect(() => () => focus.dispose(), [focus]);

  useEffect(() => {
    if (!view || !navigation || document.kind !== "xml") return;
    const range = new XmlElementLocator(view.state.doc.toString()).locate(
      navigation.target,
    );
    if (range) focus.reveal(view, range);
  }, [document.kind, focus, navigation, view]);

  return (
    <CodeMirror
      value={document.text ?? ""}
      height="100%"
      className="source-editor h-full"
      theme="none"
      extensions={extensions}
      onCreateEditor={setView}
      readOnly
      basicSetup={{
        autocompletion: false,
        bracketMatching: true,
        closeBrackets: false,
        foldGutter: false,
        highlightActiveLine: true,
        highlightActiveLineGutter: true,
        highlightSelectionMatches: true,
        lineNumbers: true,
        searchKeymap: true,
      }}
    />
  );
}

function ImagePreview({ document }: { document: ResourceDocument }) {
  const { t } = useTranslation();
  return (
    <div className="flex h-full min-h-0 flex-col bg-[var(--editor-background)]">
      <ResourceHeader document={document} label={t("resource.imagePreview")} />
      <div className="resource-image-canvas min-h-0 flex-1 overflow-auto p-8">
        <img
          src={document.dataUrl ?? undefined}
          alt={document.path}
          className="m-auto block max-h-full max-w-full object-contain"
        />
      </div>
    </div>
  );
}

function BinaryPreview({ document }: { document: ResourceDocument }) {
  const { t } = useTranslation();
  const Icon =
    document.kind === "resourceTable"
      ? Database
      : document.kind === "image"
        ? FileImage
        : document.kind === "binary"
          ? Binary
          : File;
  return (
    <div className="flex h-full flex-col items-center justify-center gap-3 bg-[var(--editor-background)] px-8 text-center">
      <div className="flex size-11 items-center justify-center rounded-[7px] border border-[var(--border)] bg-[var(--panel)] text-[var(--text-muted)]">
        <Icon size={20} strokeWidth={1.5} />
      </div>
      <div className="max-w-xl truncate text-[13px] font-medium text-[var(--text)]">
        {document.path.split("/").at(-1)}
      </div>
      <div className="max-w-xl truncate text-[11.5px] text-[var(--text-faint)]">
        {document.path} · {formatBytes(document.size)}
      </div>
      <div className="mt-1 text-[11.5px] text-[var(--text-muted)]">
        {document.message ?? t("resource.binaryPreviewUnavailable")}
      </div>
    </div>
  );
}

function ResourceHeader({
  document,
  label,
}: {
  document: ResourceDocument;
  label: string;
}) {
  return (
    <div className="flex h-8 shrink-0 items-center gap-2 border-b border-[var(--border)] px-3 text-[11px] text-[var(--text-muted)]">
      <span className="min-w-0 flex-1 truncate">{document.path}</span>
      <span className="shrink-0 text-[var(--text-faint)]">
        {label} · {formatBytes(document.size)}
      </span>
    </div>
  );
}

function formatBytes(size: number): string {
  if (size < 1024) return `${size} B`;
  if (size < 1024 * 1024) return `${(size / 1024).toFixed(1)} KiB`;
  return `${(size / (1024 * 1024)).toFixed(1)} MiB`;
}
