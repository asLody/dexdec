import type {
  ProjectRename,
  ProjectRenameDto,
  ProjectSnapshot,
  RenameTarget,
} from "./models";

class RenameIdentity {
  static key(target: RenameTarget): string {
    switch (target.kind) {
      case "class":
        return `class\u0000${target.classDescriptor}`;
      case "field":
      case "method":
        return [
          target.kind,
          target.classDescriptor,
          target.originalName,
          target.descriptor,
        ].join("\u0000");
      case "local":
      case "label":
        return [
          target.kind,
          target.classDescriptor,
          target.localOrdinal,
        ].join("\u0000");
    }
  }
}

class RenameCommand {
  constructor(
    readonly key: string,
    readonly before: ProjectRename | null,
    readonly after: ProjectRename | null,
  ) {}

  apply(records: Map<string, ProjectRename>): void {
    this.write(records, this.after);
  }

  revert(records: Map<string, ProjectRename>): void {
    this.write(records, this.before);
  }

  private write(
    records: Map<string, ProjectRename>,
    value: ProjectRename | null,
  ): void {
    if (value) {
      records.set(this.key, value);
    } else {
      records.delete(this.key);
    }
  }
}

class CommandHistory {
  private commands: RenameCommand[] = [];
  private cursor = 0;

  execute(command: RenameCommand, records: Map<string, ProjectRename>): void {
    this.commands.splice(this.cursor);
    command.apply(records);
    this.commands.push(command);
    this.cursor = this.commands.length;
  }

  undo(records: Map<string, ProjectRename>): boolean {
    if (!this.canUndo) {
      return false;
    }
    this.commands[--this.cursor].revert(records);
    return true;
  }

  redo(records: Map<string, ProjectRename>): boolean {
    if (!this.canRedo) {
      return false;
    }
    this.commands[this.cursor++].apply(records);
    return true;
  }

  clear(): void {
    this.commands = [];
    this.cursor = 0;
  }

  get canUndo(): boolean {
    return this.cursor > 0;
  }

  get canRedo(): boolean {
    return this.cursor < this.commands.length;
  }
}

/**
 * In-memory DexDec project state. Mutations are commands; the dexdb save point
 * is an immutable snapshot and no edit writes to disk implicitly.
 */
export class ProjectSession {
  private archivePathValue: string | null = null;
  private databasePathValue: string | null = null;
  private readonly recordsByKey = new Map<string, ProjectRename>();
  private readonly history = new CommandHistory();
  private savedSignature = "";

  activateArchive(archivePath: string): void {
    this.activate(archivePath, null, []);
  }

  activateSnapshot(snapshot: ProjectSnapshot): void {
    this.activate(
      snapshot.archivePath,
      snapshot.databasePath,
      snapshot.renames.map(ProjectSession.fromDto),
    );
  }

  close(): void {
    this.archivePathValue = null;
    this.databasePathValue = null;
    this.recordsByKey.clear();
    this.history.clear();
    this.savedSignature = "";
  }

  rename(target: RenameTarget, alias: string): boolean {
    const key = RenameIdentity.key(target);
    const before = this.recordsByKey.get(key) ?? null;
    const after =
      alias === target.originalName
        ? null
        : { target: ProjectSession.cloneTarget(target), alias };
    if (before?.alias === after?.alias || (!before && !after)) {
      return false;
    }
    this.history.execute(new RenameCommand(key, before, after), this.recordsByKey);
    return true;
  }

  undo(): boolean {
    return this.history.undo(this.recordsByKey);
  }

  redo(): boolean {
    return this.history.redo(this.recordsByKey);
  }

  markSaved(databasePath: string): void {
    this.databasePathValue = databasePath;
    this.savedSignature = this.signature();
  }

  snapshot(): ProjectSnapshot {
    if (!this.archivePathValue) {
      throw new Error("no archive is open");
    }
    return {
      databasePath: this.databasePathValue,
      archivePath: this.archivePathValue,
      renames: this.records.map(ProjectSession.toDto),
    };
  }

  renameFor(target: RenameTarget): ProjectRename | null {
    return this.recordsByKey.get(RenameIdentity.key(target)) ?? null;
  }

  get records(): ProjectRename[] {
    return [...this.recordsByKey.values()];
  }

  get archivePath(): string | null {
    return this.archivePathValue;
  }

  get databasePath(): string | null {
    return this.databasePathValue;
  }

  get dirty(): boolean {
    return this.archivePathValue !== null && this.signature() !== this.savedSignature;
  }

  get canUndo(): boolean {
    return this.history.canUndo;
  }

  get canRedo(): boolean {
    return this.history.canRedo;
  }

  private activate(
    archivePath: string,
    databasePath: string | null,
    records: ProjectRename[],
  ): void {
    this.archivePathValue = archivePath;
    this.databasePathValue = databasePath;
    this.recordsByKey.clear();
    for (const record of records) {
      this.recordsByKey.set(RenameIdentity.key(record.target), record);
    }
    this.history.clear();
    this.savedSignature = this.signature();
  }

  private signature(): string {
    return JSON.stringify(
      this.records.map(ProjectSession.toDto).sort((left, right) =>
        ProjectSession.dtoKey(left).localeCompare(ProjectSession.dtoKey(right)),
      ),
    );
  }

  private static fromDto(dto: ProjectRenameDto): ProjectRename {
    const common = {
      classDescriptor: dto.classDescriptor,
      originalName: dto.originalName,
    };
    const target: RenameTarget =
      dto.kind === "class"
        ? { kind: "class", ...common }
        : dto.kind === "local" || dto.kind === "label"
          ? {
              kind: dto.kind,
              ...common,
              localOrdinal: dto.localOrdinal,
            }
          : {
              kind: dto.kind,
              ...common,
              descriptor: dto.descriptor,
            };
    return { target, alias: dto.alias };
  }

  private static toDto(rename: ProjectRename): ProjectRenameDto {
    const target = rename.target;
    return {
      kind: target.kind,
      classDescriptor: target.classDescriptor,
      originalName: target.originalName,
      descriptor:
        target.kind === "field" || target.kind === "method"
          ? target.descriptor
          : "",
      localOrdinal:
        target.kind === "local" || target.kind === "label"
          ? target.localOrdinal
          : -1,
      alias: rename.alias,
    };
  }

  private static dtoKey(rename: ProjectRenameDto): string {
    return [
      rename.kind,
      rename.classDescriptor,
      rename.originalName,
      rename.descriptor,
      rename.localOrdinal,
    ].join("\u0000");
  }

  private static cloneTarget(target: RenameTarget): RenameTarget {
    return { ...target };
  }
}
