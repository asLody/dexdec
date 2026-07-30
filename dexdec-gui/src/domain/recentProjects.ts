export type RecentProjectKind = "apk" | "dex" | "database";

export interface RecentProject {
  path: string;
  name: string;
  parent: string;
  kind: RecentProjectKind;
  openedAt: number;
  iconData?: string | null;
}

export class RecentProjectHistory {
  private static readonly storageKey = "dexdec.recentProjects";
  private static readonly limit = 12;

  load(): RecentProject[] {
    try {
      const raw = localStorage.getItem(RecentProjectHistory.storageKey);
      if (!raw) return [];
      const values: unknown = JSON.parse(raw);
      if (!Array.isArray(values)) return [];
      return values
        .filter(RecentProjectHistory.isEntry)
        .sort((left, right) => right.openedAt - left.openedAt)
        .slice(0, RecentProjectHistory.limit);
    } catch {
      return [];
    }
  }

  remember(path: string): RecentProject[] {
    const entry = RecentProjectHistory.fromPath(path);
    const entries = [
      entry,
      ...this.load().filter((candidate) => !this.samePath(candidate.path, path)),
    ].slice(0, RecentProjectHistory.limit);
    this.store(entries);
    return entries;
  }

  remove(path: string): RecentProject[] {
    const entries = this.load().filter(
      (candidate) => !this.samePath(candidate.path, path),
    );
    this.store(entries);
    return entries;
  }

  clear(): RecentProject[] {
    try {
      localStorage.removeItem(RecentProjectHistory.storageKey);
    } catch {
      /* storage unavailable */
    }
    return [];
  }

  setIcon(path: string, iconData: string): RecentProject[] {
    if (!iconData.startsWith("data:image/")) return this.load();
    const entries = this.load().map((entry) =>
      this.samePath(entry.path, path) ? { ...entry, iconData } : entry,
    );
    this.store(entries);
    return entries;
  }

  private store(entries: RecentProject[]): void {
    try {
      localStorage.setItem(
        RecentProjectHistory.storageKey,
        JSON.stringify(entries),
      );
    } catch {
      /* storage unavailable */
    }
  }

  private samePath(left: string, right: string): boolean {
    const windowsPath = /^[a-z]:[\\/]/i;
    return windowsPath.test(left) || windowsPath.test(right)
      ? left.localeCompare(right, undefined, { sensitivity: "accent" }) === 0
      : left === right;
  }

  private static fromPath(path: string): RecentProject {
    const parts = path.split(/[\\/]/);
    const name = parts.pop() || path;
    const parent = parts.join(path.includes("\\") ? "\\" : "/");
    const lower = name.toLocaleLowerCase();
    const kind = lower.endsWith(".dexdb")
      ? "database"
      : lower.endsWith(".dex")
        ? "dex"
        : "apk";
    return { path, name, parent, kind, openedAt: Date.now(), iconData: null };
  }

  private static isEntry(value: unknown): value is RecentProject {
    if (!value || typeof value !== "object") return false;
    const entry = value as Partial<RecentProject>;
    return (
      typeof entry.path === "string" &&
      entry.path.length > 0 &&
      typeof entry.name === "string" &&
      typeof entry.parent === "string" &&
      (entry.kind === "apk" ||
        entry.kind === "dex" ||
        entry.kind === "database") &&
      typeof entry.openedAt === "number" &&
      Number.isFinite(entry.openedAt) &&
      (entry.iconData === undefined ||
        entry.iconData === null ||
        (typeof entry.iconData === "string" &&
          entry.iconData.startsWith("data:image/")))
    );
  }
}

export const recentProjectHistory = new RecentProjectHistory();
