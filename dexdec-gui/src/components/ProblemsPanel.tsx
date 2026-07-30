import { Braces, Check, CircleAlert, Trash2, X } from "lucide-react";

import { useTranslation } from "../i18n";
import { useWorkspace } from "../state/workspace";
import { EmptyState } from "./EmptyState";

/*
 * Docked list of decompile failures collected while browsing. Clicking a row
 * re-attempts the class — primarily a decompiler-development instrument, so
 * it lives above the editor, next to the peek dock.
 */
export function ProblemsPanel() {
  const problems = useWorkspace((state) => state.problems);
  const setOpen = useWorkspace((state) => state.setProblemsOpen);
  const clearProblems = useWorkspace((state) => state.clearProblems);
  const selectClass = useWorkspace((state) => state.selectClass);
  const { t } = useTranslation();

  return (
    <div className="absolute inset-x-0 bottom-0 z-20 flex max-h-[40%] flex-col border-t border-[var(--border-strong)] bg-[var(--chrome)] shadow-[0_-10px_32px_rgba(0,0,0,0.4)]">
      <div className="flex h-8 shrink-0 items-center gap-2 border-b border-[var(--border)] px-3">
        <CircleAlert size={12} className="shrink-0 text-[var(--danger)]" />
        <span className="text-[12px] font-medium text-[var(--text)]">{t("problems.title")}</span>
        <span className="text-[10.5px] tabular-nums text-[var(--text-faint)]">
          {problems.length}
        </span>
        <div className="ml-auto flex items-center gap-0.5">
          <button
            type="button"
            className="icon-button !h-[22px] !w-[22px]"
            title={t("problems.clear")}
            aria-label={t("problems.clear")}
            onClick={clearProblems}
          >
            <Trash2 size={12} />
          </button>
          <button
            type="button"
            className="icon-button !h-[22px] !w-[22px]"
            title={t("problems.close")}
            aria-label={t("problems.close")}
            onClick={() => setOpen(false)}
          >
            <X size={12} />
          </button>
        </div>
      </div>

      <div className="min-h-0 flex-1 overflow-auto py-1">
        {problems.length ? (
          [...problems].reverse().map((problem) => (
            <button
              key={problem.id}
              type="button"
              className="problem-row"
              title={`${problem.descriptor}\n${problem.message}`}
              onClick={() => void selectClass(problem.descriptor)}
            >
              <Braces size={11} className="mt-[2px] shrink-0 text-[var(--glyph-class)]" />
              <span className="shrink-0 text-[11.5px] font-medium text-[var(--text)]">
                {problem.descriptor.replace(/^L|;$/g, "").split("/").pop()}
              </span>
              <span className="min-w-0 flex-1 truncate text-left text-[11.5px] text-[var(--text-faint)]">
                {problem.message}
              </span>
              <span className="shrink-0 text-[10px] tabular-nums text-[var(--text-faint)]">
                {formatTime(problem.at)}
              </span>
            </button>
          ))
        ) : (
          <EmptyState compact icon={<Check size={17} />} title={t("problems.empty")} />
        )}
      </div>
    </div>
  );
}

function formatTime(at: number): string {
  const date = new Date(at);
  const pad = (value: number) => String(value).padStart(2, "0");
  return `${pad(date.getHours())}:${pad(date.getMinutes())}:${pad(date.getSeconds())}`;
}
