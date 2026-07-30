import { StreamLanguage, syntaxHighlighting } from "@codemirror/language";
import { java } from "@codemirror/lang-java";
import { kotlin } from "@codemirror/legacy-modes/mode/clike";
import { EditorView } from "@codemirror/view";
import CodeMirror from "@uiw/react-codemirror";
import { ExternalLink, FunctionSquare, LoaderCircle, X } from "lucide-react";
import { useMemo } from "react";

import { useTranslation } from "../i18n";
import { useAppearance } from "../state/appearance";
import { useWorkspace } from "../state/workspace";
import { editorTheme, sourceHighlight } from "./CodeEditor";

/*
 * Docked peek panel showing a single decompiled method (via the
 * decompile_method IPC) without replacing the active document. Lazy-loaded
 * together with the editor chunk, so it costs nothing until first used.
 */
export default function PeekView() {
  const peek = useWorkspace((state) => state.peek);
  const closePeek = useWorkspace((state) => state.closePeek);
  const selectClass = useWorkspace((state) => state.selectClass);
  const navigateToMember = useWorkspace((state) => state.navigateToMember);
  const wordWrap = useAppearance((state) => state.wordWrap);

  const { t } = useTranslation();
  const extensions = useMemo(
    () => [
      peek?.language === "java"
        ? java()
        : StreamLanguage.define(kotlin),
      wordWrap ? EditorView.lineWrapping : [],
      editorTheme,
      syntaxHighlighting(sourceHighlight),
    ],
    [peek?.language, wordWrap],
  );

  if (!peek) {
    return null;
  }

  const shortClass = peek.classDescriptor
    .replace(/^L|;$/g, "")
    .split("/")
    .pop();

  const openInEditor = () => {
    const { classDescriptor, name, descriptor } = peek;
    closePeek();
    void selectClass(classDescriptor).then(() =>
      navigateToMember({ classDescriptor, kind: "method", name, descriptor }),
    );
  };

  return (
    <div className="absolute inset-x-0 bottom-0 z-20 flex h-[248px] flex-col border-t border-[var(--border-strong)] bg-[var(--chrome)] shadow-[0_-10px_32px_rgba(0,0,0,0.4)]">
      <div className="flex h-8 shrink-0 items-center gap-2 border-b border-[var(--border)] px-3">
        <FunctionSquare size={12} className="shrink-0 text-[var(--glyph-method)]" />
        <span
          className="min-w-0 flex-1 truncate text-[12px] text-[var(--text)]"
          title={peek.displaySignature}
        >
          {peek.displaySignature}
        </span>
        <span className="shrink-0 text-[10.5px] text-[var(--text-faint)]">
          {shortClass}
        </span>
        {peek.state === "ready" && peek.elapsedMs != null ? (
          <span className="shrink-0 text-[10.5px] tabular-nums text-[var(--text-faint)]">
            {peek.elapsedMs} ms
          </span>
        ) : null}
        <button
          type="button"
          className="icon-button !h-[22px] !w-[22px]"
          title={t("peek.openInEditor")}
          aria-label={t("peek.openInEditor")}
          onClick={openInEditor}
        >
          <ExternalLink size={12} />
        </button>
        <button
          type="button"
          className="icon-button !h-[22px] !w-[22px]"
          title={t("peek.close")}
          aria-label={t("peek.close")}
          onClick={closePeek}
        >
          <X size={12} />
        </button>
      </div>

      <div className="min-h-0 flex-1">
        {peek.state === "loading" ? (
          <div className="flex h-full items-center justify-center gap-2 text-[11.5px] text-[var(--text-faint)]">
            <LoaderCircle size={13} className="animate-spin text-[var(--accent)]" />
            {t("peek.loading")}
          </div>
        ) : peek.state === "error" ? (
          <div className="flex h-full items-center justify-center px-6 text-center text-[11.5px] text-[var(--danger)]">
            {peek.error ?? t("peek.failed")}
          </div>
        ) : (
          <CodeMirror
            value={peek.source ?? ""}
            height="100%"
            className="source-editor h-full"
            theme="none"
            extensions={extensions}
            editable={false}
            basicSetup={{
              autocompletion: false,
              bracketMatching: true,
              closeBrackets: false,
              foldGutter: false,
              highlightActiveLine: false,
              highlightActiveLineGutter: false,
              highlightSelectionMatches: false,
              lineNumbers: false,
              searchKeymap: false,
            }}
          />
        )}
      </div>
    </div>
  );
}
