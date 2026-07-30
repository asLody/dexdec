import type { ClassSummary, ResourceEntry } from "./models";

export type ExplorerMode = "tree" | "packages";

export type ExplorerRow =
  | {
      kind: "package";
      key: string;
      name: string;
      qualifiedName: string;
      classCount: number;
      depth: number;
      expanded: boolean;
    }
  | {
      kind: "class";
      key: string;
      classInfo: ClassSummary;
      depth: number;
      expanded: boolean;
      hasChildren: boolean;
      searchResult: boolean;
    };

export type ProjectExplorerRow =
  | ExplorerRow
  | {
      kind: "section";
      key: string;
      section: "sources" | "resources";
      count: number;
      depth: number;
      expanded: boolean;
    }
  | {
      kind: "directory";
      key: string;
      name: string;
      path: string;
      fileCount: number;
      depth: number;
      expanded: boolean;
    }
  | {
      kind: "resource";
      key: string;
      name: string;
      entry: ResourceEntry;
      depth: number;
      expanded: false;
      hasChildren: false;
      searchResult: boolean;
    };

interface ClassNode {
  classInfo: ClassSummary;
  children: ClassNode[];
}

interface PackageNode {
  segment: string;
  qualifiedName: string;
  children: PackageNode[];
  classes: ClassNode[];
  classCount: number;
}

interface FlatPackage {
  name: string;
  classes: ClassSummary[];
}

export class ExplorerIndex {
  private readonly allClasses: ClassSummary[];
  private readonly classMap: Map<string, ClassSummary>;
  private readonly packageRoots: PackageNode[];
  private readonly flatPackages: FlatPackage[];

  constructor(classes: ClassSummary[]) {
    this.allClasses = [...classes].sort((left, right) =>
      left.qualifiedName.localeCompare(right.qualifiedName),
    );
    this.classMap = new Map(
      this.allClasses.map((classInfo) => [classInfo.descriptor, classInfo]),
    );
    const classNodes = new Map<string, ClassNode>(
      this.allClasses.map(
        (classInfo): [string, ClassNode] => [
          classInfo.descriptor,
          { classInfo, children: [] },
        ],
      ),
    );
    const topLevelClasses: ClassNode[] = [];
    for (const node of classNodes.values()) {
      const parent = node.classInfo.parentDescriptor
        ? classNodes.get(node.classInfo.parentDescriptor)
        : undefined;
      if (parent && !this.hasOwnershipCycle(node.classInfo.descriptor, classNodes)) {
        parent.children.push(node);
      } else {
        topLevelClasses.push(node);
      }
    }
    for (const node of classNodes.values()) {
      node.children.sort((left, right) =>
        left.classInfo.displayName.localeCompare(right.classInfo.displayName),
      );
    }
    this.packageRoots = this.buildPackageTree(topLevelClasses);
    this.flatPackages = this.buildFlatPackages(this.allClasses);
  }

  rows(
    mode: ExplorerMode,
    expandedNodes: ReadonlySet<string>,
    query: string,
  ): ExplorerRow[] {
    const normalizedQuery = query.trim().toLocaleLowerCase();
    if (normalizedQuery) {
      return this.allClasses
        .filter((classInfo) =>
          classInfo.qualifiedName.toLocaleLowerCase().includes(normalizedQuery),
        )
        .map((classInfo) => ({
          kind: "class" as const,
          key: `search:${classInfo.descriptor}`,
          classInfo,
          depth: 0,
          expanded: false,
          hasChildren: false,
          searchResult: true,
        }));
    }
    return mode === "tree"
      ? this.treeRows(expandedNodes)
      : this.packageRows(expandedNodes);
  }

  initialExpansion(mode: ExplorerMode): Set<string> {
    const firstKey =
      mode === "tree"
        ? this.packageRoots[0] && this.treePackageKey(this.packageRoots[0])
        : this.flatPackages[0] && this.flatPackageKey(this.flatPackages[0].name);
    return firstKey ? new Set([firstKey]) : new Set();
  }

  allExpansion(mode: ExplorerMode): Set<string> {
    if (mode === "packages") {
      return new Set(this.flatPackages.map((group) => this.flatPackageKey(group.name)));
    }
    const keys = new Set<string>();
    const visitClass = (node: ClassNode): void => {
      if (node.children.length) keys.add(this.classKey(node.classInfo.descriptor));
      node.children.forEach(visitClass);
    };
    const visitPackage = (node: PackageNode): void => {
      keys.add(this.treePackageKey(node));
      node.children.forEach(visitPackage);
      node.classes.forEach(visitClass);
    };
    this.packageRoots.forEach(visitPackage);
    return keys;
  }

  /**
   * Expansion keys needed to make a class visible: every ancestor package
   * plus (in tree mode) every enclosing outer class.
   */
  expandPathTo(descriptor: string, mode: ExplorerMode): string[] {
    const classInfo = this.classMap.get(descriptor);
    if (!classInfo) {
      return [];
    }
    const packageName = classInfo.package || "<default>";
    if (mode === "packages") {
      return [this.flatPackageKey(packageName)];
    }
    const keys: string[] = [];
    if (packageName === "<default>") {
      keys.push("tree-package:<default>");
    } else {
      let qualified = "";
      for (const segment of packageName.split(".")) {
        qualified = qualified ? `${qualified}.${segment}` : segment;
        keys.push(`tree-package:${qualified}`);
      }
    }
    const guard = new Set<string>([descriptor]);
    let parent = classInfo.parentDescriptor;
    while (parent && !guard.has(parent)) {
      guard.add(parent);
      keys.push(this.classKey(parent));
      parent = this.classMap.get(parent)?.parentDescriptor ?? null;
    }
    return keys;
  }

  private treeRows(expandedNodes: ReadonlySet<string>): ExplorerRow[] {
    const rows: ExplorerRow[] = [];
    const visitPackage = (node: PackageNode, depth: number): void => {
      const key = this.treePackageKey(node);
      const expanded = expandedNodes.has(key);
      rows.push({
        kind: "package",
        key,
        name: node.segment,
        qualifiedName: node.qualifiedName,
        classCount: node.classCount,
        depth,
        expanded,
      });
      if (!expanded) return;
      for (const child of node.children) visitPackage(child, depth + 1);
      for (const classNode of node.classes) visitClass(classNode, depth + 1);
    };
    const visitClass = (node: ClassNode, depth: number): void => {
      const key = this.classKey(node.classInfo.descriptor);
      const expanded = expandedNodes.has(key);
      rows.push({
        kind: "class",
        key,
        classInfo: node.classInfo,
        depth,
        expanded,
        hasChildren: node.children.length > 0,
        searchResult: false,
      });
      if (expanded) {
        for (const child of node.children) visitClass(child, depth + 1);
      }
    };
    for (const root of this.packageRoots) visitPackage(root, 0);
    return rows;
  }

  private packageRows(expandedNodes: ReadonlySet<string>): ExplorerRow[] {
    const rows: ExplorerRow[] = [];
    for (const group of this.flatPackages) {
      const key = this.flatPackageKey(group.name);
      const expanded = expandedNodes.has(key);
      rows.push({
        kind: "package",
        key,
        name: group.name,
        qualifiedName: group.name,
        classCount: group.classes.length,
        depth: 0,
        expanded,
      });
      if (!expanded) continue;
      rows.push(
        ...group.classes.map((classInfo) => ({
          kind: "class" as const,
          key: `flat:${classInfo.descriptor}`,
          classInfo,
          depth: 1,
          expanded: false,
          hasChildren: false,
          searchResult: false,
        })),
      );
    }
    return rows;
  }

  private buildPackageTree(classes: ClassNode[]): PackageNode[] {
    interface MutablePackage {
      segment: string;
      qualifiedName: string;
      children: Map<string, MutablePackage>;
      classes: ClassNode[];
    }
    const roots = new Map<string, MutablePackage>();
    for (const classNode of classes) {
      const packageName = classNode.classInfo.package;
      const segments = packageName ? packageName.split(".") : ["<default>"];
      let children = roots;
      let qualifiedName = "";
      let leaf: MutablePackage | null = null;
      for (const segment of segments) {
        qualifiedName =
          segment === "<default>"
            ? "<default>"
            : qualifiedName
              ? `${qualifiedName}.${segment}`
              : segment;
        leaf = children.get(segment) ?? {
          segment,
          qualifiedName,
          children: new Map(),
          classes: [],
        };
        children.set(segment, leaf);
        children = leaf.children;
      }
      leaf!.classes.push(classNode);
    }

    const freeze = (node: MutablePackage): PackageNode => {
      const children = [...node.children.values()]
        .map(freeze)
        .sort((left, right) => left.segment.localeCompare(right.segment));
      const packageClasses = node.classes.sort((left, right) =>
        left.classInfo.displayName.localeCompare(right.classInfo.displayName),
      );
      return {
        segment: node.segment,
        qualifiedName: node.qualifiedName,
        children,
        classes: packageClasses,
        classCount:
          children.reduce((total, child) => total + child.classCount, 0) +
          packageClasses.reduce((total, child) => total + this.classCount(child), 0),
      };
    };
    return [...roots.values()]
      .map(freeze)
      .sort((left, right) => left.segment.localeCompare(right.segment));
  }

  private buildFlatPackages(classes: ClassSummary[]): FlatPackage[] {
    const groups = new Map<string, ClassSummary[]>();
    for (const classInfo of classes) {
      const packageName = classInfo.package || "<default>";
      const packageClasses = groups.get(packageName);
      if (packageClasses) packageClasses.push(classInfo);
      else groups.set(packageName, [classInfo]);
    }
    return [...groups.entries()]
      .sort(([left], [right]) => left.localeCompare(right))
      .map(([name, packageClasses]) => ({
        name,
        classes: packageClasses.sort((left, right) =>
          left.binaryName.localeCompare(right.binaryName),
        ),
      }));
  }

  private classCount(node: ClassNode): number {
    return 1 + node.children.reduce((total, child) => total + this.classCount(child), 0);
  }

  private hasOwnershipCycle(
    descriptor: string,
    classes: ReadonlyMap<string, ClassNode>,
  ): boolean {
    const visited = new Set([descriptor]);
    let parent = classes.get(descriptor)?.classInfo.parentDescriptor;
    while (parent && classes.has(parent)) {
      if (visited.has(parent)) return true;
      visited.add(parent);
      parent = classes.get(parent)?.classInfo.parentDescriptor;
    }
    return false;
  }

  private treePackageKey(node: PackageNode): string {
    return `tree-package:${node.qualifiedName}`;
  }

  private flatPackageKey(name: string): string {
    return `flat-package:${name}`;
  }

  private classKey(descriptor: string): string {
    return `tree-class:${descriptor}`;
  }
}

interface ResourceDirectory {
  name: string;
  path: string;
  directories: Map<string, ResourceDirectory>;
  files: ResourceEntry[];
  fileCount: number;
}

export class ProjectExplorerIndex {
  private readonly sources: ExplorerIndex;
  private readonly manifest: ResourceEntry | null;
  private readonly resources: ResourceEntry[];
  private readonly resourceRoot: ResourceDirectory;
  private readonly sourceCount: number;

  constructor(classes: ClassSummary[], resources: ResourceEntry[]) {
    this.sources = new ExplorerIndex(classes);
    this.sourceCount = classes.length;
    this.manifest = resources.find((entry) => entry.path === "AndroidManifest.xml") ?? null;
    this.resources = resources.filter((entry) => entry !== this.manifest);
    this.resourceRoot = this.buildResourceTree(this.resources);
  }

  rows(
    mode: ExplorerMode,
    expanded: ReadonlySet<string>,
    query: string,
  ): ProjectExplorerRow[] {
    const normalizedQuery = query.trim().toLocaleLowerCase();
    const sourceRows = this.sources.rows(mode, expanded, query);
    const resourceRows = this.resourceRows(expanded, normalizedQuery);
    const rows: ProjectExplorerRow[] = [];
    if (
      this.manifest &&
      (!normalizedQuery || this.manifest.path.toLocaleLowerCase().includes(normalizedQuery))
    ) {
      rows.push(this.resourceRow(this.manifest, 0, Boolean(normalizedQuery)));
    }
    const sourcesOpen = expanded.has("section:sources");
    rows.push({
      kind: "section",
      key: "section:sources",
      section: "sources",
      count: normalizedQuery
        ? sourceRows.filter((row) => row.kind === "class").length
        : this.sourceCount,
      depth: 0,
      expanded: sourcesOpen,
    });
    if (sourcesOpen) {
      rows.push(...sourceRows.map((row) => ({ ...row, depth: row.depth + 1 })));
    }
    if (this.resources.length) {
      const resourcesOpen = expanded.has("section:resources");
      rows.push({
        kind: "section",
        key: "section:resources",
        section: "resources",
        count: normalizedQuery ? resourceRows.length : this.resources.length,
        depth: 0,
        expanded: resourcesOpen,
      });
      if (resourcesOpen) rows.push(...resourceRows);
    }
    return rows;
  }

  initialExpansion(mode: ExplorerMode): Set<string> {
    return new Set([
      "section:sources",
      "section:resources",
      ...this.sources.initialExpansion(mode),
    ]);
  }

  allExpansion(mode: ExplorerMode): Set<string> {
    const expanded = new Set([
      "section:sources",
      "section:resources",
      ...this.sources.allExpansion(mode),
    ]);
    const visit = (directory: ResourceDirectory): void => {
      for (const child of directory.directories.values()) {
        expanded.add(this.directoryKey(child.path));
        visit(child);
      }
    };
    visit(this.resourceRoot);
    return expanded;
  }

  expandPathTo(descriptor: string, mode: ExplorerMode): string[] {
    return ["section:sources", ...this.sources.expandPathTo(descriptor, mode)];
  }

  private resourceRows(
    expanded: ReadonlySet<string>,
    query: string,
  ): ProjectExplorerRow[] {
    if (query) {
      return this.resources
        .filter((entry) => entry.path.toLocaleLowerCase().includes(query))
        .map((entry) => this.resourceRow(entry, 1, true));
    }
    const rows: ProjectExplorerRow[] = [];
    const visit = (directory: ResourceDirectory, depth: number): void => {
      const key = this.directoryKey(directory.path);
      const open = expanded.has(key);
      rows.push({
        kind: "directory",
        key,
        name: directory.name,
        path: directory.path,
        fileCount: directory.fileCount,
        depth,
        expanded: open,
      });
      if (!open) return;
      [...directory.directories.values()]
        .sort((left, right) => left.name.localeCompare(right.name))
        .forEach((child) => visit(child, depth + 1));
      directory.files
        .sort((left, right) => left.path.localeCompare(right.path))
        .forEach((entry) => rows.push(this.resourceRow(entry, depth + 1, false)));
    };
    [...this.resourceRoot.directories.values()]
      .sort((left, right) => left.name.localeCompare(right.name))
      .forEach((directory) => visit(directory, 1));
    this.resourceRoot.files
      .sort((left, right) => left.path.localeCompare(right.path))
      .forEach((entry) => rows.push(this.resourceRow(entry, 1, false)));
    return rows;
  }

  private resourceRow(
    entry: ResourceEntry,
    depth: number,
    searchResult: boolean,
  ): Extract<ProjectExplorerRow, { kind: "resource" }> {
    return {
      kind: "resource",
      key: `resource:${entry.path}`,
      name: entry.path.split("/").at(-1) ?? entry.path,
      entry,
      depth,
      expanded: false,
      hasChildren: false,
      searchResult,
    };
  }

  private buildResourceTree(resources: ResourceEntry[]): ResourceDirectory {
    const root: ResourceDirectory = {
      name: "",
      path: "",
      directories: new Map(),
      files: [],
      fileCount: resources.length,
    };
    for (const entry of resources) {
      const parts = entry.path.split("/").filter(Boolean);
      let directory = root;
      let path = "";
      for (const segment of parts.slice(0, -1)) {
        path = path ? `${path}/${segment}` : segment;
        let child = directory.directories.get(segment);
        if (!child) {
          child = {
            name: segment,
            path,
            directories: new Map(),
            files: [],
            fileCount: 0,
          };
          directory.directories.set(segment, child);
        }
        child.fileCount += 1;
        directory = child;
      }
      directory.files.push(entry);
    }
    return root;
  }

  private directoryKey(path: string): string {
    return `resource-directory:${path}`;
  }
}
