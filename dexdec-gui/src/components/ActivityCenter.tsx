import {
  Check,
  CircleAlert,
  LoaderCircle,
  ListChecks,
  Trash2,
  X,
} from "lucide-react";
import { useEffect, useMemo, useRef, useState } from "react";

import { useTranslation } from "../i18n";
import { useActivity, type ActivityTask } from "../state/activity";

export function ActivityCenter() {
  const tasks = useActivity((state) => state.tasks);
  const open = useActivity((state) => state.open);
  const setOpen = useActivity((state) => state.setOpen);
  const cancel = useActivity((state) => state.cancel);
  const dismiss = useActivity((state) => state.dismiss);
  const clearFinished = useActivity((state) => state.clearFinished);
  const panelRef = useRef<HTMLDivElement>(null);
  const [, setClock] = useState(0);
  const { t } = useTranslation();
  const ordered = useMemo(
    () => [...tasks].sort((left, right) =>
      Number(right.status === "running") - Number(left.status === "running") ||
      right.startedAt - left.startedAt),
    [tasks],
  );
  const running = tasks.filter((task) => task.status === "running").length;

  useEffect(() => {
    if (!open || !running) return;
    const timer = window.setInterval(() => setClock((value) => value + 1), 1_000);
    return () => window.clearInterval(timer);
  }, [open, running]);

  useEffect(() => {
    if (!open) return;
    const onPointerDown = (event: PointerEvent) => {
      if (!panelRef.current?.contains(event.target as Node)) setOpen(false);
    };
    const onKeyDown = (event: KeyboardEvent) => {
      if (event.key === "Escape") {
        event.preventDefault();
        setOpen(false);
      }
    };
    window.addEventListener("pointerdown", onPointerDown, true);
    window.addEventListener("keydown", onKeyDown, true);
    return () => {
      window.removeEventListener("pointerdown", onPointerDown, true);
      window.removeEventListener("keydown", onKeyDown, true);
    };
  }, [open, setOpen]);

  if (!open) return null;

  return (
    <div ref={panelRef} className="activity-center" role="dialog" aria-label={t("activity.title")}>
      <header className="activity-header">
        <ListChecks size={14} className="text-[var(--accent)]" />
        <span>{t("activity.title")}</span>
        {running ? <span className="activity-count">{running}</span> : null}
        <button
          type="button"
          className="icon-button ml-auto !h-[24px] !w-[24px]"
          title={t("activity.clearFinished")}
          aria-label={t("activity.clearFinished")}
          disabled={!tasks.some((task) => task.status !== "running")}
          onClick={clearFinished}
        >
          <Trash2 size={12} />
        </button>
        <button
          type="button"
          className="icon-button !h-[24px] !w-[24px]"
          title={t("activity.close")}
          aria-label={t("activity.close")}
          onClick={() => setOpen(false)}
        >
          <X size={12} />
        </button>
      </header>

      <div className="activity-list">
        {ordered.length ? ordered.map((task) => (
          <ActivityRow
            key={task.id}
            task={task}
            onCancel={() => cancel(task.id)}
            onDismiss={() => dismiss(task.id)}
          />
        )) : (
          <div className="activity-empty">
            <Check size={18} />
            <span>{t("activity.empty")}</span>
          </div>
        )}
      </div>
    </div>
  );
}

function ActivityRow({
  task,
  onCancel,
  onDismiss,
}: {
  task: ActivityTask;
  onCancel: () => void;
  onDismiss: () => void;
}) {
  const { t } = useTranslation();
  const elapsed = (task.finishedAt ?? Date.now()) - task.startedAt;
  return (
    <div className={`activity-row is-${task.status}`}>
      <div className="activity-status" aria-hidden="true">
        {task.status === "running" ? (
          <LoaderCircle size={13} className="animate-spin" />
        ) : task.status === "failed" ? (
          <CircleAlert size={13} />
        ) : task.status === "completed" ? (
          <Check size={13} />
        ) : (
          <X size={13} />
        )}
      </div>
      <div className="min-w-0 flex-1">
        <div className="flex items-center gap-2">
          <span className="activity-name">{task.title}</span>
          <span className="activity-duration">{formatElapsed(elapsed)}</span>
        </div>
        {task.error ? (
          <div className="activity-error" title={task.error}>{task.error}</div>
        ) : task.detail ? (
          <div className="activity-detail" title={task.detail}>{task.detail}</div>
        ) : null}
        {task.status === "running" ? (
          <div className="activity-progress" aria-hidden="true">
            <div
              className={task.progress == null ? "is-indeterminate" : ""}
              style={task.progress == null ? undefined : { width: `${task.progress * 100}%` }}
            />
          </div>
        ) : null}
      </div>
      {task.status === "running" && task.cancellable ? (
        <button type="button" className="activity-action" onClick={onCancel}>
          {t("activity.cancel")}
        </button>
      ) : task.status !== "running" ? (
        <button
          type="button"
          className="activity-dismiss"
          title={t("activity.dismiss")}
          aria-label={t("activity.dismiss")}
          onClick={onDismiss}
        >
          <X size={11} />
        </button>
      ) : null}
    </div>
  );
}

function formatElapsed(milliseconds: number): string {
  if (milliseconds < 1_000) return `${milliseconds} ms`;
  if (milliseconds < 60_000) return `${(milliseconds / 1_000).toFixed(1)} s`;
  const minutes = Math.floor(milliseconds / 60_000);
  return `${minutes}m ${Math.floor((milliseconds % 60_000) / 1_000)}s`;
}
