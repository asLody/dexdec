import { CircleAlert, LoaderCircle, X } from "lucide-react";

import { useTranslation } from "../i18n";
import { useWorkspace } from "../state/workspace";
import { useActivity } from "../state/activity";

export function StatusBar() {
  const archive = useWorkspace((state) => state.archive);
  const documents = useWorkspace((state) => state.documents);
  const activeDescriptor = useWorkspace((state) => state.activeDescriptor);
  const caret = useWorkspace((state) => state.caret);
  const error = useWorkspace((state) => state.error);
  const clearError = useWorkspace((state) => state.clearError);
  const problems = useWorkspace((state) => state.problems);
  const problemsOpen = useWorkspace((state) => state.problemsOpen);
  const setProblemsOpen = useWorkspace((state) => state.setProblemsOpen);
  const tasks = useActivity((state) => state.tasks);
  const setActivityOpen = useActivity((state) => state.setOpen);
  const { t } = useTranslation();
  const document = documents.find((item) => item.descriptor === activeDescriptor);
  const running = tasks.filter((task) => task.status === "running");

  return (
    <footer className="status-bar flex h-[22px] shrink-0 items-center border-t border-[var(--border)] bg-[var(--chrome)] px-3 text-[10.5px] text-[var(--text-faint)]">
      {error ? (
        <div className="flex min-w-0 flex-1 items-center gap-2 text-[var(--danger)]">
          <CircleAlert size={12} className="shrink-0" />
          <span className="truncate">{error}</span>
          <button
            type="button"
            className="ml-auto flex size-4 shrink-0 items-center justify-center rounded-[3px] hover:text-[var(--text)]"
            title={t("status.dismiss")}
            aria-label={t("status.dismiss")}
            onClick={clearError}
          >
            <X size={11} />
          </button>
        </div>
      ) : (
        <>
          {running.length ? (
            <button
              type="button"
              className="status-activity"
              title={running.map((task) => task.title).join("\n")}
              onClick={() => setActivityOpen(true)}
            >
              <LoaderCircle size={11} className="animate-spin text-[var(--accent)]" />
              <span>{running.length === 1 ? running[0].title : t("activity.running", running.length)}</span>
            </button>
          ) : null}
          {problems.length ? (
            <button
              type="button"
              className={`mr-2 flex shrink-0 items-center gap-1 rounded-[3px] px-1 text-[var(--danger)] ${
                problemsOpen ? "bg-[var(--raised)]" : ""
              }`}
              title={`${problems.length} ${t("problems.title")} — ${problemsOpen ? t("status.hideProblems") : t("status.showProblems")}`}
              onClick={() => setProblemsOpen(!problemsOpen)}
            >
              <CircleAlert size={11} />
              <span className="tabular-nums">{problems.length}</span>
            </button>
          ) : null}
          <div className="min-w-0 flex-1 truncate">
            {document ? (
              <span className="font-mono text-[10.5px]">{document.outline.qualifiedName}</span>
            ) : archive ? (
              <span>{archive.name}</span>
            ) : (
              <span>{t("status.ready")}</span>
            )}
          </div>
          <div className="flex shrink-0 items-center gap-3.5 tabular-nums">
            {document && caret ? (
              <span>{t("status.line", caret.line.toLocaleString(), caret.column)}</span>
            ) : null}
            {document ? <span>{t("status.methods", document.methodCount)}</span> : null}
            {document ? <span>{formatDuration(document.elapsedMs)}</span> : null}
            {archive ? <span>{t("status.classes", archive.classCount.toLocaleString())}</span> : null}
          </div>
        </>
      )}
    </footer>
  );
}

function formatDuration(milliseconds: number): string {
  return milliseconds < 1000
    ? `${milliseconds} ms`
    : `${(milliseconds / 1000).toFixed(2)} s`;
}
