import { create } from "zustand";

export type ActivityKind =
  | "archive"
  | "references";

export type ActivityStatus = "running" | "completed" | "failed" | "cancelled";

export interface ActivityTask {
  id: string;
  kind: ActivityKind;
  title: string;
  detail: string | null;
  status: ActivityStatus;
  progress: number | null;
  cancellable: boolean;
  startedAt: number;
  finishedAt: number | null;
  error: string | null;
}

export interface Notice {
  id: string;
  message: string;
  tone: "info" | "success" | "error";
}

interface ActivityState {
  tasks: ActivityTask[];
  notices: Notice[];
  open: boolean;
  setOpen: (open: boolean) => void;
  cancel: (id: string) => void;
  dismiss: (id: string) => void;
  clearFinished: () => void;
  dismissNotice: (id: string) => void;
}

interface ActivitySpec {
  kind: ActivityKind;
  title: string;
  detail?: string;
  scope?: string;
  cancellable?: boolean;
  onCancel?: () => void;
}

const HISTORY_LIMIT = 24;

export const useActivity = create<ActivityState>((set) => ({
  tasks: [],
  notices: [],
  open: false,
  setOpen: (open) => set({ open }),
  cancel: (id) => ActivityCenter.cancel(id),
  dismiss: (id) => set((state) => ({
    tasks: state.tasks.filter((task) => task.id !== id || task.status === "running"),
  })),
  clearFinished: () => set((state) => ({
    tasks: state.tasks.filter((task) => task.status === "running"),
  })),
  dismissNotice: (id) => set((state) => ({
    notices: state.notices.filter((notice) => notice.id !== id),
  })),
}));

export class ActivityHandle {
  constructor(readonly id: string) {}

  detail(detail: string): this {
    ActivityCenter.patch(this.id, { detail });
    return this;
  }

  progress(progress: number | null): this {
    ActivityCenter.patch(this.id, {
      progress: progress == null ? null : Math.max(0, Math.min(1, progress)),
    });
    return this;
  }

  complete(detail?: string): void {
    ActivityCenter.finish(this.id, "completed", detail);
  }

  fail(error: unknown): void {
    ActivityCenter.finish(
      this.id,
      "failed",
      undefined,
      error instanceof Error ? error.message : String(error),
    );
  }

  cancel(): void {
    ActivityCenter.cancel(this.id);
  }
}

export class ActivityCenter {
  private static sequence = 0;
  private static readonly cancellations = new Map<string, () => void>();
  private static readonly scopes = new Map<string, string>();

  static begin(spec: ActivitySpec): ActivityHandle {
    if (spec.scope) {
      const previous = this.scopes.get(spec.scope);
      if (previous) {
        const task = useActivity.getState().tasks.find((entry) => entry.id === previous);
        if (task?.cancellable) this.cancel(previous);
        else this.finish(previous, "cancelled");
      }
    }
    const id = `activity-${++this.sequence}`;
    const task: ActivityTask = {
      id,
      kind: spec.kind,
      title: spec.title,
      detail: spec.detail ?? null,
      status: "running",
      progress: null,
      cancellable: Boolean(spec.cancellable),
      startedAt: Date.now(),
      finishedAt: null,
      error: null,
    };
    if (spec.onCancel) this.cancellations.set(id, spec.onCancel);
    if (spec.scope) this.scopes.set(spec.scope, id);
    useActivity.setState((state) => ({
      tasks: [...state.tasks.filter((entry) => entry.id !== id), task].slice(-HISTORY_LIMIT),
    }));
    return new ActivityHandle(id);
  }

  static cancel(id: string): void {
    const task = useActivity.getState().tasks.find((entry) => entry.id === id);
    if (!task || task.status !== "running" || !task.cancellable) return;
    this.cancellations.get(id)?.();
    this.finish(id, "cancelled");
  }

  static cancelScope(scope: string): void {
    const id = this.scopes.get(scope);
    if (id) this.cancel(id);
  }

  static notify(
    message: string,
    tone: Notice["tone"] = "info",
    duration = 2_200,
  ): void {
    const id = `notice-${++this.sequence}`;
    useActivity.setState((state) => ({
      notices: [...state.notices, { id, message, tone }].slice(-4),
    }));
    window.setTimeout(() => useActivity.getState().dismissNotice(id), duration);
  }

  static patch(id: string, patch: Partial<ActivityTask>): void {
    useActivity.setState((state) => ({
      tasks: state.tasks.map((task) => task.id === id ? { ...task, ...patch } : task),
    }));
  }

  static finish(
    id: string,
    status: Exclude<ActivityStatus, "running">,
    detail?: string,
    error?: string,
  ): void {
    const current = useActivity.getState().tasks.find((task) => task.id === id);
    if (!current || current.status !== "running") return;
    this.cancellations.delete(id);
    for (const [scope, taskId] of this.scopes) {
      if (taskId === id) this.scopes.delete(scope);
    }
    this.patch(id, {
      status,
      detail: detail ?? current.detail,
      finishedAt: Date.now(),
      progress: status === "completed" ? 1 : null,
      cancellable: false,
      error: error ?? null,
    });
  }
}

if (import.meta.env.DEV) {
  (window as unknown as Record<string, unknown>).__dexdecActivity = useActivity;
}
