import type { EditorState } from "@codemirror/state";

import type {
  Archive,
  ClassSummary,
  ResourceEntry,
  ResourceNavigationTarget,
} from "./models";
import type { EditorLink, EditorLinkResolver } from "../components/editorLinks";

export type XmlNavigationDestination =
  | { kind: "class"; descriptor: string }
  | { kind: "resource"; path: string }
  | { kind: "local"; from: number; to: number };

export interface XmlNavigationLink extends EditorLink {
  destination: XmlNavigationDestination;
}

interface ResourceCandidate {
  entry: ResourceEntry;
  qualifier: string;
}

interface XmlAttributeRange {
  name: string;
  value: string;
  from: number;
  to: number;
}

interface XmlStartTag {
  name: string;
  nameFrom: number;
  nameTo: number;
  attributes: XmlAttributeRange[];
}

/** Locates semantic XML targets while retaining offsets in the displayed source. */
export class XmlElementLocator {
  constructor(private readonly source: string) {}

  locate(target: ResourceNavigationTarget): { from: number; to: number } | null {
    const names = new Set(target.names);
    for (const tag of this.startTags()) {
      if (!names.has(tag.name)) continue;
      if (!target.attribute) {
        return { from: tag.nameFrom, to: tag.nameTo };
      }
      const attribute = tag.attributes.find(
        (candidate) =>
          candidate.name === target.attribute?.name &&
          candidate.value === target.attribute.value,
      );
      if (attribute) return { from: attribute.from, to: attribute.to };
    }
    return null;
  }

  private *startTags(): Generator<XmlStartTag> {
    let cursor = 0;
    while (cursor < this.source.length) {
      const open = this.source.indexOf("<", cursor);
      if (open < 0) return;
      if (
        this.source.startsWith("</", open) ||
        this.source.startsWith("<?", open) ||
        this.source.startsWith("<!", open)
      ) {
        cursor = this.tagEnd(open + 2) + 1;
        continue;
      }
      const end = this.tagEnd(open + 1);
      if (end <= open) return;
      const tag = this.parseStartTag(open, end);
      if (tag) yield tag;
      cursor = end + 1;
    }
  }

  private tagEnd(from: number): number {
    let quote: '"' | "'" | null = null;
    for (let index = from; index < this.source.length; index += 1) {
      const character = this.source[index];
      if (quote) {
        if (character === quote) quote = null;
      } else if (character === '"' || character === "'") {
        quote = character;
      } else if (character === ">") {
        return index;
      }
    }
    return this.source.length;
  }

  private parseStartTag(open: number, end: number): XmlStartTag | null {
    let cursor = open + 1;
    while (cursor < end && /\s/.test(this.source[cursor])) cursor += 1;
    const nameFrom = cursor;
    while (cursor < end && !/[\s/>]/.test(this.source[cursor])) cursor += 1;
    if (cursor === nameFrom) return null;
    const nameTo = cursor;
    const attributes: XmlAttributeRange[] = [];
    while (cursor < end) {
      while (cursor < end && /[\s/]/.test(this.source[cursor])) cursor += 1;
      const attributeNameFrom = cursor;
      while (cursor < end && !/[\s=/>]/.test(this.source[cursor])) cursor += 1;
      if (cursor === attributeNameFrom) break;
      const attributeName = this.source.slice(attributeNameFrom, cursor);
      while (cursor < end && /\s/.test(this.source[cursor])) cursor += 1;
      if (this.source[cursor] !== "=") continue;
      cursor += 1;
      while (cursor < end && /\s/.test(this.source[cursor])) cursor += 1;
      const quote = this.source[cursor];
      if (quote !== '"' && quote !== "'") continue;
      const valueFrom = ++cursor;
      while (cursor < end && this.source[cursor] !== quote) cursor += 1;
      const valueTo = cursor;
      attributes.push({
        name: attributeName,
        value: this.source.slice(valueFrom, valueTo),
        from: valueFrom,
        to: valueTo,
      });
      cursor += 1;
    }
    return {
      name: this.source.slice(nameFrom, nameTo),
      nameFrom,
      nameTo,
      attributes,
    };
  }
}

/** Resolves Android resource names and DEX classes without loading resource bodies. */
export class AndroidProjectIndex {
  private readonly resources = new Map<string, ResourceCandidate[]>();
  private readonly classes = new Map<string, ClassSummary>();
  private readonly packageName: string | null;

  constructor(archive: Archive) {
    this.packageName = archive.overview?.packageName ?? null;
    archive.resources.forEach((entry) => this.indexResource(entry));
    archive.classes.forEach((classInfo) => this.indexClass(classInfo));
  }

  resource(reference: string, sourcePath: string): ResourceEntry | null {
    const parsed = this.parseReference(reference);
    if (
      !parsed ||
      (parsed.namespace &&
        parsed.namespace !== "app" &&
        parsed.namespace !== this.packageName)
    ) {
      return null;
    }
    const candidates = this.resources.get(`${parsed.type}/${parsed.name}`);
    if (!candidates?.length) {
      return null;
    }
    const sourceQualifier = this.sourceQualifier(sourcePath);
    return [...candidates].sort((left, right) => {
      const rank = (candidate: ResourceCandidate): number =>
        candidate.qualifier === sourceQualifier
          ? 0
          : candidate.qualifier === ""
            ? 1
            : 2;
      return rank(left) - rank(right) || left.entry.path.localeCompare(right.entry.path);
    })[0].entry;
  }

  class(name: string, manifestPackage: string | null): ClassSummary | null {
    const normalized = name.startsWith("/") ? name.slice(1) : name;
    const candidates = [
      normalized,
      normalized.startsWith(".") && manifestPackage
        ? `${manifestPackage}${normalized}`
        : null,
      !normalized.includes(".") && manifestPackage
        ? `${manifestPackage}.${normalized}`
        : null,
    ];
    for (const candidate of candidates) {
      if (!candidate) continue;
      const classInfo = this.classes.get(candidate);
      if (classInfo) return classInfo;
    }
    return null;
  }

  private indexResource(entry: ResourceEntry): void {
    const match = /^res\/([a-z][a-z0-9_]*)(-[^/]+)?\/([^/]+)$/i.exec(entry.path);
    if (!match) return;
    const type = match[1];
    const qualifier = match[2] ?? "";
    const fileName = match[3];
    const name = fileName.endsWith(".9.png")
      ? fileName.slice(0, -6)
      : fileName.includes(".")
        ? fileName.slice(0, fileName.indexOf("."))
        : fileName;
    const key = `${type}/${name}`;
    const candidates = this.resources.get(key) ?? [];
    candidates.push({ entry, qualifier });
    this.resources.set(key, candidates);
  }

  private indexClass(classInfo: ClassSummary): void {
    this.classes.set(classInfo.qualifiedName, classInfo);
    this.classes.set(classInfo.qualifiedName.replace(/\$/g, "."), classInfo);
  }

  private parseReference(reference: string): {
    namespace: string | null;
    type: string;
    name: string;
  } | null {
    const match = /^@\+?(?:([A-Za-z_][\w.]*):)?([A-Za-z_][\w]*)\/([A-Za-z0-9_.]+)$/.exec(
      reference,
    );
    return match
      ? { namespace: match[1] ?? null, type: match[2], name: match[3] }
      : null;
  }

  private sourceQualifier(path: string): string {
    const directory = /^res\/[a-z][a-z0-9_]*(-[^/]+)?\//i.exec(path);
    return directory?.[1] ?? "";
  }
}

/** Finds navigable Android resource references and class names on the current XML line. */
export class XmlNavigationResolver
  implements EditorLinkResolver<XmlNavigationLink>
{
  private readonly manifestPackage: string | null;
  private readonly localIds = new Map<string, { from: number; to: number }>();

  constructor(
    private readonly sourcePath: string,
    source: string,
    private readonly project: AndroidProjectIndex,
  ) {
    this.manifestPackage =
      /<manifest\b[^>]*\bpackage\s*=\s*["']([^"']+)["']/i.exec(source)?.[1] ?? null;
    for (const declaration of source.matchAll(/@\+id\/([A-Za-z0-9_.]+)/g)) {
      this.localIds.set(declaration[1], {
        from: declaration.index,
        to: declaration.index + declaration[0].length,
      });
    }
  }

  resolve(state: EditorState, offset: number): XmlNavigationLink | null {
    const line = state.doc.lineAt(Math.min(offset, state.doc.length));
    const localOffset = offset - line.from;
    const resource = this.matchAt(
      line.text,
      localOffset,
      /@\+?(?:[A-Za-z_][\w.]*:)?[A-Za-z_][\w]*\/[A-Za-z0-9_.]+/g,
    );
    if (resource) {
      const entry = this.project.resource(resource.text, this.sourcePath);
      if (entry) {
        return {
          range: { from: line.from + resource.from, to: line.from + resource.to },
          destination: { kind: "resource", path: entry.path },
        };
      }
      const localId = /^@id\/([A-Za-z0-9_.]+)$/.exec(resource.text)?.[1];
      const declaration = localId ? this.localIds.get(localId) : null;
      if (declaration) {
        return {
          range: { from: line.from + resource.from, to: line.from + resource.to },
          destination: { kind: "local", ...declaration },
        };
      }
    }

    const className = this.matchAt(
      line.text,
      localOffset,
      /\.?[A-Za-z_$][\w$]*(?:\.[A-Za-z_$][\w$]*)*/g,
    );
    if (!className) return null;
    const classInfo = this.project.class(className.text, this.manifestPackage);
    return classInfo
      ? {
          range: { from: line.from + className.from, to: line.from + className.to },
          destination: { kind: "class", descriptor: classInfo.descriptor },
        }
      : null;
  }

  private matchAt(
    line: string,
    offset: number,
    pattern: RegExp,
  ): { text: string; from: number; to: number } | null {
    for (const match of line.matchAll(pattern)) {
      const from = match.index;
      const to = from + match[0].length;
      if (from <= offset && offset <= to) {
        return { text: match[0], from, to };
      }
    }
    return null;
  }
}
