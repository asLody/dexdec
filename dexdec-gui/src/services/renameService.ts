import { EditorState } from "@codemirror/state";

import {
  createSourceDefinitionResolver,
  type ResolvedSymbol,
  type SourceDefinitionResolver,
} from "../domain/sourceDefinitionResolver";
import type {
  Archive,
  ClassOutline,
  ClassSummary,
  ProjectRename,
  ReferenceLocation,
  ReferenceTarget,
  RenameTarget,
  SourceDocument,
  SourceSymbolSpan,
  SymbolDestination,
} from "../domain/models";
import { ProjectSession } from "../domain/projectSession";
import { ArchiveMemberResolver } from "./archiveMemberResolver";

export type RenameIssue =
  | "invalid"
  | "keyword"
  | "conflict"
  | "unresolved";

export interface PreparedRename {
  target: RenameTarget;
  currentName: string;
  symbol: ResolvedSymbol;
  resolver: SourceDefinitionResolver;
}

export interface PresentedWorkspace {
  archive: Archive;
  documents: SourceDocument[];
}

class JavaIdentifier {
  private static readonly pattern =
    /^[$_\p{ID_Start}][$\u200c\u200d\p{ID_Continue}]*$/u;

  private static readonly keywords = new Set([
    "abstract", "assert", "boolean", "break", "byte", "case", "catch",
    "char", "class", "const", "continue", "default", "do", "double",
    "else", "enum", "extends", "final", "finally", "float", "for", "goto",
    "if", "implements", "import", "instanceof", "int", "interface", "long",
    "native", "new", "package", "private", "protected", "public", "return",
    "short", "static", "strictfp", "super", "switch", "synchronized",
    "this", "throw", "throws", "transient", "try", "void", "volatile",
    "while", "_", "true", "false", "null", "record", "sealed", "permits",
    "yield", "var",
  ]);

  static issue(name: string): RenameIssue | null {
    if (!this.pattern.test(name)) {
      return "invalid";
    }
    return this.keywords.has(name) ? "keyword" : null;
  }
}

class RenameLookup {
  private readonly classes = new Map<string, ProjectRename>();
  private readonly members = new Map<string, ProjectRename>();
  private readonly locals = new Map<string, ProjectRename>();
  private readonly memberNames = new Set<string>();
  private readonly memberOwnerDescriptors = new Set<string>();
  private readonly memberOutlines = new Map<string, ClassOutline>();

  constructor(records: ProjectRename[]) {
    for (const record of records) {
      const target = record.target;
      if (target.kind === "class") {
        this.classes.set(target.classDescriptor, record);
      } else if (target.kind === "field" || target.kind === "method") {
        this.members.set(RenameLookup.memberKey(target), record);
        const nameKey = `${target.kind}\u0000${target.originalName}`;
        this.memberNames.add(nameKey);
        this.memberOwnerDescriptors.add(target.classDescriptor);
      } else {
        this.locals.set(RenameLookup.localKey(target), record);
      }
    }
  }

  classAlias(descriptor: string): string | null {
    return this.classes.get(descriptor)?.alias ?? null;
  }

  memberAlias(target: Extract<RenameTarget, { kind: "field" | "method" }>): string | null {
    return this.members.get(RenameLookup.memberKey(target))?.alias ?? null;
  }

  localAlias(
    kind: "local" | "label",
    classDescriptor: string,
    ordinal: number,
    originalName: string,
  ): string | null {
    const record = this.locals.get(
      RenameLookup.localKey({
        kind,
        classDescriptor,
        originalName: "",
        localOrdinal: ordinal,
      }),
    );
    return record?.target.originalName === originalName
      ? record.alias
      : null;
  }

  mightRenameMember(kind: "field" | "method", name: string): boolean {
    return this.memberNames.has(`${kind}\u0000${name}`);
  }

  directMember(
    destination: Extract<SymbolDestination, { kind: "member" }>,
    documentOutline: ClassOutline,
  ): ProjectRename | null {
    const outline =
      this.memberOutlines.get(destination.classDescriptor) ??
      (documentOutline.descriptor === destination.classDescriptor
        ? documentOutline
        : null);
    if (!outline) {
      return null;
    }
    if (destination.classDescriptor !== outline.descriptor) {
      return null;
    }
    if (destination.memberKind === "field") {
      const fields = outline.fields.filter(
        (field) => (field.originalName ?? field.name) === destination.name,
      );
      if (fields.length !== 1) {
        return null;
      }
      return this.members.get(
        RenameLookup.memberKey({
          kind: "field",
          classDescriptor: outline.descriptor,
          originalName: destination.name,
          descriptor: fields[0].descriptor,
        }),
      ) ?? null;
    }
    const methods = outline.methods.filter((method) => {
      if ((method.originalName ?? method.name) !== destination.name) {
        return false;
      }
      const parameters = JvmDescriptor.parameters(method.descriptor);
      if (
        !parameters ||
        (destination.arity != null && parameters.length !== destination.arity)
      ) {
        return false;
      }
      return (
        !destination.parameterDescriptors ||
        destination.parameterDescriptors.every(
          (argument, index) =>
            argument == null || argument === parameters[index],
        )
      );
    });
    if (methods.length !== 1) {
      return null;
    }
    return this.members.get(
      RenameLookup.memberKey({
        kind: "method",
        classDescriptor: outline.descriptor,
        originalName: destination.name,
        descriptor: methods[0].descriptor,
      }),
    ) ?? null;
  }

  get memberOwners(): string[] {
    return [...this.memberOwnerDescriptors];
  }

  indexMemberOutline(outline: ClassOutline): void {
    this.memberOutlines.set(outline.descriptor, outline);
  }

  private static memberKey(
    target: Extract<RenameTarget, { kind: "field" | "method" }>,
  ): string {
    return [
      target.kind,
      target.classDescriptor,
      target.originalName,
      target.descriptor,
    ].join("\u0000");
  }

  private static localKey(
    target: Extract<RenameTarget, { kind: "local" | "label" }>,
  ): string {
    return [
      target.kind,
      target.classDescriptor,
      target.localOrdinal,
    ].join("\u0000");
  }
}

class JvmDescriptor {
  static parameters(descriptor: string): string[] | null {
    if (!descriptor.startsWith("(")) {
      return null;
    }
    const parameters: string[] = [];
    let index = 1;
    while (index < descriptor.length && descriptor[index] !== ")") {
      const start = index;
      while (descriptor[index] === "[") {
        index += 1;
      }
      if (descriptor[index] === "L") {
        const end = descriptor.indexOf(";", index);
        if (end < 0) {
          return null;
        }
        index = end + 1;
      } else {
        index += 1;
      }
      parameters.push(descriptor.slice(start, index));
    }
    return descriptor[index] === ")" ? parameters : null;
  }
}

class ArchivePresenter {
  private readonly sourceByDescriptor: Map<string, ClassSummary>;
  private readonly presentedByDescriptor = new Map<string, ClassSummary>();

  constructor(
    private readonly source: Archive,
    private readonly aliases: RenameLookup,
  ) {
    this.sourceByDescriptor = new Map(
      source.classes.map((entry) => [entry.descriptor, entry]),
    );
  }

  archive(): Archive {
    return {
      ...this.source,
      classes: this.source.classes.map((entry) => this.class(entry.descriptor)!),
    };
  }

  outline(outline: ClassOutline): ClassOutline {
    const classInfo = this.class(outline.descriptor);
    const originalClass = this.sourceByDescriptor.get(outline.descriptor);
    const classAlias = classInfo?.displayName ?? originalClass?.displayName;
    const originalClassName = originalClass?.displayName ?? "";
    return {
      ...outline,
      qualifiedName: classInfo?.qualifiedName ?? outline.qualifiedName,
      fields: outline.fields.map((field) => {
        const alias = this.aliases.memberAlias({
          kind: "field",
          classDescriptor: outline.descriptor,
          originalName: field.originalName ?? field.name,
          descriptor: field.descriptor,
        });
        return {
          ...field,
          originalName: field.originalName ?? field.name,
          name: alias ?? field.originalName ?? field.name,
        };
      }),
      methods: outline.methods.map((method) => {
        const originalName = method.originalName ?? method.name;
        const alias = method.constructor
          ? null
          : this.aliases.memberAlias({
              kind: "method",
              classDescriptor: outline.descriptor,
              originalName,
              descriptor: method.descriptor,
            });
        const displayName = method.constructor
          ? classAlias ?? originalClassName
          : alias ?? originalName;
        const signatureName = method.constructor ? originalClassName : originalName;
        return {
          ...method,
          originalName,
          name: method.constructor ? method.name : displayName,
          displaySignature: ArchivePresenter.renameSignature(
            method.displaySignature,
            signatureName,
            displayName,
          ),
        };
      }),
    };
  }

  private class(descriptor: string): ClassSummary | null {
    const cached = this.presentedByDescriptor.get(descriptor);
    if (cached) {
      return cached;
    }
    const source = this.sourceByDescriptor.get(descriptor);
    if (!source) {
      return null;
    }
    const parent = source.parentDescriptor
      ? this.class(source.parentDescriptor)
      : null;
    const displayName = this.aliases.classAlias(descriptor) ?? source.displayName;
    const binaryName = parent
      ? `${parent.binaryName}$${displayName}`
      : ArchivePresenter.replaceLastBinarySegment(source.binaryName, displayName);
    const qualifiedName = source.package
      ? `${source.package}.${binaryName}`
      : binaryName;
    const presented = {
      ...source,
      displayName,
      binaryName,
      qualifiedName,
    };
    this.presentedByDescriptor.set(descriptor, presented);
    return presented;
  }

  private static replaceLastBinarySegment(binaryName: string, name: string): string {
    const separator = binaryName.lastIndexOf("$");
    return separator < 0 ? name : `${binaryName.slice(0, separator + 1)}${name}`;
  }

  private static renameSignature(
    signature: string,
    originalName: string,
    alias: string,
  ): string {
    if (!originalName || originalName === alias) {
      return signature;
    }
    const marker = `${originalName}(`;
    const index = signature.lastIndexOf(marker);
    return index < 0
      ? signature
      : `${signature.slice(0, index)}${alias}${signature.slice(index + originalName.length)}`;
  }
}

class MemberBindingIndex {
  private readonly resolutions = new Map<string, Promise<ReferenceTarget | null>>();

  constructor(
    private readonly sessionId: number,
    private readonly documents: SourceDocument[],
    private readonly resolver: ArchiveMemberResolver,
  ) {}

  resolve(
    destination: Extract<SymbolDestination, { kind: "member" }>,
  ): Promise<ReferenceTarget | null> {
    if (destination.descriptor) {
      return Promise.resolve({
        kind: destination.memberKind,
        classDescriptor: destination.classDescriptor,
        name: destination.name,
        descriptor: destination.descriptor,
      });
    }
    const key = JSON.stringify([
      destination.memberKind,
      destination.classDescriptor,
      destination.name,
      destination.arity,
      destination.parameterDescriptors ?? null,
    ]);
    let resolution = this.resolutions.get(key);
    if (!resolution) {
      resolution = this.resolver.referenceTarget(
        this.sessionId,
        destination,
        this.documents,
      );
      this.resolutions.set(key, resolution);
    }
    return resolution;
  }
}

interface SymbolPresentation {
  symbol: ResolvedSymbol;
  replacement: string | null;
  destination: SymbolDestination;
}

class SourceAnalysis {
  readonly symbols: ResolvedSymbol[];
  private readonly localOrdinals = new Map<string, number>();
  private readonly localKinds = new Map<string, "local" | "label">();
  private readonly localNames = new Map<string, string>();

  constructor(
    readonly source: string,
    document: SourceDocument,
    archive: Archive,
  ) {
    const state = EditorState.create({ doc: source });
    const resolver = createSourceDefinitionResolver(document, archive);
    this.symbols = resolver.symbols(state);
    let nextLocal = 0;
    for (const symbol of this.symbols) {
      if (
        symbol.destination.kind === "local" &&
        symbol.range.from === symbol.destination.from &&
        symbol.range.to === symbol.destination.to
      ) {
        const key = SourceAnalysis.rangeKey(symbol.destination);
        this.localOrdinals.set(key, nextLocal++);
        this.localKinds.set(key, resolver.localKind(state, symbol.destination));
        this.localNames.set(
          key,
          state.doc.sliceString(symbol.range.from, symbol.range.to),
        );
      }
    }
  }

  local(
    destination: Extract<SymbolDestination, { kind: "local" }>,
  ): {
    ordinal: number;
    kind: "local" | "label";
    originalName: string;
  } | null {
    const key = SourceAnalysis.rangeKey(destination);
    const ordinal = this.localOrdinals.get(key);
    return ordinal == null
      ? null
      : {
          ordinal,
          kind: this.localKinds.get(key) ?? "local",
          originalName: this.localNames.get(key) ?? "",
        };
  }

  private static rangeKey(range: { from: number; to: number }): string {
    return `${range.from}:${range.to}`;
  }
}

class SourceComposer {
  static compose(
    source: string,
    presentations: SymbolPresentation[],
  ): { source: string; spans: SourceSymbolSpan[] } {
    const ordered = [...presentations].sort(
      (left, right) =>
        left.symbol.range.from - right.symbol.range.from ||
        left.symbol.range.to - right.symbol.range.to,
    );
    const chunks: string[] = [];
    const provisional: {
      original: { from: number; to: number };
      rendered: SourceSymbolSpan;
    }[] = [];
    let sourceCursor = 0;
    let outputLength = 0;

    for (const entry of ordered) {
      const { from, to } = entry.symbol.range;
      if (from < sourceCursor) {
        continue;
      }
      const prefix = source.slice(sourceCursor, from);
      const text = entry.replacement ?? source.slice(from, to);
      chunks.push(prefix, text);
      outputLength += prefix.length;
      const rendered = {
        from: outputLength,
        to: outputLength + text.length,
        destination: entry.destination,
      };
      provisional.push({
        original: { from, to },
        rendered,
      });
      outputLength += text.length;
      sourceCursor = to;
    }
    chunks.push(source.slice(sourceCursor));

    const renderedDeclarations = new Map(
      provisional.map((entry) => [
        SourceComposer.rangeKey(entry.original),
        { from: entry.rendered.from, to: entry.rendered.to },
      ]),
    );
    const spans = provisional.map(({ rendered }) => {
      const destination = rendered.destination;
      if (destination.kind !== "local") {
        return rendered;
      }
      const declaration = renderedDeclarations.get(
        SourceComposer.rangeKey(destination),
      );
      return {
        ...rendered,
        destination: declaration
          ? { ...destination, ...declaration }
          : destination,
      };
    });
    return { source: chunks.join(""), spans };
  }

  private static rangeKey(range: { from: number; to: number }): string {
    return `${range.from}:${range.to}`;
  }
}

class SourcePresenter {
  constructor(
    private readonly archive: Archive,
    private readonly aliases: RenameLookup,
    private readonly archivePresenter: ArchivePresenter,
    private readonly bindings: MemberBindingIndex,
  ) {}

  async present(
    document: SourceDocument,
    analysis: SourceAnalysis,
  ): Promise<SourceDocument> {
    const presentations = await Promise.all(
      analysis.symbols.map(async (symbol): Promise<SymbolPresentation> => {
        const destination = symbol.destination;
        if (destination.kind === "local") {
          const local = analysis.local(destination);
          return {
            symbol,
            replacement:
              !local
                ? null
                : this.aliases.localAlias(
                    local.kind,
                    document.descriptor,
                    local.ordinal,
                    local.originalName,
                  ),
            destination: local
              ? {
                  ...destination,
                  localOrdinal: local.ordinal,
                  localKind: local.kind,
                  originalName: local.originalName,
                }
              : destination,
          };
        }
        if (destination.kind === "class") {
          return {
            symbol,
            replacement: this.aliases.classAlias(destination.classDescriptor),
            destination,
          };
        }
        if (destination.name === "<init>") {
          return {
            symbol,
            replacement: this.aliases.classAlias(destination.classDescriptor),
            destination,
          };
        }
        if (
          !this.aliases.mightRenameMember(
            destination.memberKind,
            destination.name,
          )
        ) {
          return { symbol, replacement: null, destination };
        }
        const direct = this.aliases.directMember(destination, document.outline);
        if (direct) {
          const target = direct.target;
          if (target.kind === "field" || target.kind === "method") {
            return {
              symbol,
              replacement: direct.alias,
              destination: {
                ...destination,
                classDescriptor: target.classDescriptor,
                memberKind: target.kind,
                name: target.originalName,
                descriptor: target.descriptor,
              },
            };
          }
        }
        const exact = await this.bindings.resolve(destination);
        if (!exact || exact.kind === "class") {
          return { symbol, replacement: null, destination };
        }
        const exactTarget: Extract<RenameTarget, { kind: "field" | "method" }> = {
          kind: exact.kind,
          classDescriptor: exact.classDescriptor,
          originalName: exact.name,
          descriptor: exact.descriptor,
        };
        return {
          symbol,
          replacement: this.aliases.memberAlias(exactTarget),
          destination: {
            ...destination,
            classDescriptor: exact.classDescriptor,
            memberKind: exact.kind,
            name: exact.name,
            descriptor: exact.descriptor,
          },
        };
      }),
    );
    const composed = SourceComposer.compose(document.source, presentations);
    return {
      ...document,
      source: composed.source,
      outline: this.archivePresenter.outline(document.outline),
      symbolSpans: composed.spans,
    };
  }
}

/**
 * Produces aliased source while retaining canonical DEX identities.
 * Parsing and member resolution happen once per document revision; the editor
 * then resolves renamed tokens by binary-searching the generated sidecar.
 */
export class RenameService {
  private baseArchive: Archive | null = null;
  private presentedArchive: {
    classSignature: string;
    archive: Archive;
  } | null = null;
  private readonly analyses = new Map<
    string,
    { source: string; analysis: SourceAnalysis }
  >();

  constructor(
    private readonly project: ProjectSession,
    private readonly members: ArchiveMemberResolver,
  ) {}

  activateArchive(archive: Archive): Archive {
    this.baseArchive = structuredClone(archive);
    this.presentedArchive = null;
    this.analyses.clear();
    return this.presentArchive();
  }

  closeArchive(): void {
    this.baseArchive = null;
    this.presentedArchive = null;
    this.analyses.clear();
    this.members.closeArchive();
  }

  presentArchive(): Archive {
    if (!this.baseArchive) {
      throw new Error("no archive is open");
    }
    const classRenames = this.project.records
      .filter((record) => record.target.kind === "class")
      .sort((left, right) =>
        left.target.classDescriptor.localeCompare(
          right.target.classDescriptor,
        ),
      );
    const classSignature = JSON.stringify(
      classRenames.map((record) => [
        record.target.classDescriptor,
        record.alias,
      ]),
    );
    if (this.presentedArchive?.classSignature === classSignature) {
      return this.presentedArchive.archive;
    }
    const archive = classRenames.length
      ? new ArchivePresenter(
          this.baseArchive,
          new RenameLookup(this.project.records),
        ).archive()
      : this.baseArchive;
    this.presentedArchive = { classSignature, archive };
    return archive;
  }

  async presentDocument(
    sessionId: number,
    document: SourceDocument,
    documents: SourceDocument[],
  ): Promise<SourceDocument> {
    const [presented] = await this.presentDocuments(sessionId, [
      ...documents,
      document,
    ], document.descriptor);
    return presented;
  }

  async presentWorkspace(
    sessionId: number,
    documents: SourceDocument[],
  ): Promise<PresentedWorkspace> {
    const archive = this.presentArchive();
    const presented = await this.presentDocuments(sessionId, documents);
    return { archive, documents: presented };
  }

  presentReferenceLocations(
    locations: ReferenceLocation[],
  ): ReferenceLocation[] {
    const classes = new Map(
      this.presentArchive().classes.map((entry) => [
        entry.descriptor,
        entry.qualifiedName,
      ]),
    );
    const aliases = new RenameLookup(this.project.records);
    return locations.map((location) => ({
      ...location,
      displayClassName: classes.get(location.classDescriptor),
      displayMethodName:
        aliases.memberAlias({
          kind: "method",
          classDescriptor: location.classDescriptor,
          originalName: location.method,
          descriptor: location.descriptor,
        }) ?? location.method,
    }));
  }

  async prepare(
    sessionId: number,
    document: SourceDocument,
    archive: Archive,
    documents: SourceDocument[],
    state: EditorState,
    symbol: ResolvedSymbol,
    resolver: SourceDefinitionResolver,
  ): Promise<PreparedRename | null> {
    const currentName = state.doc.sliceString(symbol.range.from, symbol.range.to);
    const destination = symbol.destination;
    if (destination.kind === "local") {
      const localOrdinal =
        destination.localOrdinal ??
        resolver.localOrdinal(state, destination);
      if (localOrdinal == null) {
        return null;
      }
      const tentative: RenameTarget = {
        kind:
          destination.localKind ??
          resolver.localKind(state, destination),
        classDescriptor: document.descriptor,
        originalName: destination.originalName ?? currentName,
        localOrdinal,
      };
      return {
        target: tentative,
        currentName,
        symbol,
        resolver,
      };
    }
    if (destination.kind === "class" || destination.name === "<init>") {
      const descriptor =
        destination.kind === "class"
          ? destination.classDescriptor
          : destination.classDescriptor;
      const sourceClass = this.baseArchive?.classes.find(
        (entry) => entry.descriptor === descriptor,
      );
      return sourceClass
        ? {
            target: {
              kind: "class",
              classDescriptor: descriptor,
              originalName: sourceClass.displayName,
            },
            currentName,
            symbol,
            resolver,
          }
        : null;
    }

    const exact = destination.descriptor
      ? {
          kind: destination.memberKind,
          classDescriptor: destination.classDescriptor,
          name: destination.name,
          descriptor: destination.descriptor,
        } satisfies ReferenceTarget
      : await this.members.referenceTarget(sessionId, destination, documents);
    if (!exact || exact.kind === "class") {
      return null;
    }
    return {
      target: {
        kind: exact.kind,
        classDescriptor: exact.classDescriptor,
        originalName: exact.name,
        descriptor: exact.descriptor,
      },
      currentName,
      symbol,
      resolver,
    };
  }

  async validate(
    sessionId: number,
    prepared: PreparedRename,
    name: string,
    document: SourceDocument,
    archive: Archive,
    documents: SourceDocument[],
    state: EditorState,
  ): Promise<RenameIssue | null> {
    const syntaxIssue = JavaIdentifier.issue(name);
    if (syntaxIssue) {
      return syntaxIssue;
    }
    if (name === prepared.currentName) {
      return null;
    }
    const target = prepared.target;
    if (target.kind === "class") {
      const selected = archive.classes.find(
        (entry) => entry.descriptor === target.classDescriptor,
      );
      const conflict = archive.classes.some(
        (entry) =>
          entry.descriptor !== target.classDescriptor &&
          entry.parentDescriptor === selected?.parentDescriptor &&
          entry.package === selected?.package &&
          entry.displayName === name,
      );
      return conflict ? "conflict" : null;
    }
    if (target.kind === "field" || target.kind === "method") {
      const outline = await this.members.classOutline(
        sessionId,
        target.classDescriptor,
        documents,
      );
      if (!outline) {
        return "unresolved";
      }
      if (target.kind === "field") {
        const conflict = outline.fields.some(
          (field) => {
            const originalName = field.originalName ?? field.name;
            const candidate: Extract<RenameTarget, { kind: "field" }> = {
              kind: "field",
              classDescriptor: target.classDescriptor,
              originalName,
              descriptor: field.descriptor,
            };
            return (
              (originalName !== target.originalName ||
                field.descriptor !== target.descriptor) &&
              (this.project.renameFor(candidate)?.alias ?? originalName) === name
            );
          },
        );
        return conflict ? "conflict" : null;
      }
      const parameters = RenameService.parameterSignature(target.descriptor);
      const conflict = outline.methods.some(
        (method) => {
          if (method.constructor) {
            return false;
          }
          const originalName = method.originalName ?? method.name;
          const candidate: Extract<RenameTarget, { kind: "method" }> = {
            kind: "method",
            classDescriptor: target.classDescriptor,
            originalName,
            descriptor: method.descriptor,
          };
          return (
            (originalName !== target.originalName ||
              method.descriptor !== target.descriptor) &&
            (this.project.renameFor(candidate)?.alias ?? originalName) === name &&
            RenameService.parameterSignature(method.descriptor) === parameters
          );
        },
      );
      return conflict ? "conflict" : null;
    }

    const resolver = prepared.resolver;
    const selectedDestination = prepared.symbol.destination;
    if (selectedDestination.kind !== "local") {
      return "unresolved";
    }
    const selectedRange = resolver.localBindingRange(state, selectedDestination);
    const selectedOrdinal = target.localOrdinal;
    for (const symbol of resolver.symbols(state)) {
      if (
        symbol.destination.kind !== "local" ||
        symbol.range.from !== symbol.destination.from ||
        symbol.range.to !== symbol.destination.to ||
        resolver.localKind(state, symbol.destination) !== target.kind ||
        state.doc.sliceString(symbol.range.from, symbol.range.to) !== name
      ) {
        continue;
      }
      const ordinal = resolver.localOrdinal(state, symbol.destination);
      if (ordinal === selectedOrdinal) {
        continue;
      }
      const range = resolver.localBindingRange(state, symbol.destination);
      if (
        !selectedRange ||
        !range ||
        (selectedRange.from <= range.to && range.from <= selectedRange.to)
      ) {
        return "conflict";
      }
    }
    return null;
  }

  private async presentDocuments(
    sessionId: number,
    documents: SourceDocument[],
    onlyDescriptor?: string,
  ): Promise<SourceDocument[]> {
    if (!this.baseArchive) {
      throw new Error("no archive is open");
    }
    const unique = new Map<string, SourceDocument>();
    for (const document of documents) {
      unique.set(document.descriptor, RenameService.baseDocument(document));
    }
    const baseDocuments = [...unique.values()];
    const aliases = new RenameLookup(this.project.records);
    if (!this.project.records.length) {
      const selected = onlyDescriptor
        ? baseDocuments.filter((entry) => entry.descriptor === onlyDescriptor)
        : baseDocuments;
      return selected;
    }
    const baseOutlines = new Map(
      baseDocuments.map((document) => [
        document.descriptor,
        document.outline,
      ]),
    );
    await Promise.all(
      aliases.memberOwners.map(async (descriptor) => {
        const outline =
          baseOutlines.get(descriptor) ??
          await this.members.classOutline(
            sessionId,
            descriptor,
            baseDocuments,
          );
        if (outline) {
          aliases.indexMemberOutline(outline);
        }
      }),
    );
    const archivePresenter = new ArchivePresenter(this.baseArchive, aliases);
    const bindings = new MemberBindingIndex(
      sessionId,
      baseDocuments,
      this.members,
    );
    const presenter = new SourcePresenter(
      this.baseArchive,
      aliases,
      archivePresenter,
      bindings,
    );
    const selected = onlyDescriptor
      ? baseDocuments.filter((entry) => entry.descriptor === onlyDescriptor)
      : baseDocuments;
    return Promise.all(
      selected.map((document) =>
        presenter.present(document, this.analysis(document)),
      ),
    );
  }

  private static baseDocument(document: SourceDocument): SourceDocument {
    const originalSource = document.originalSource ?? document.source;
    const originalOutline = document.originalOutline ?? document.outline;
    return {
      ...document,
      source: originalSource,
      outline: structuredClone(originalOutline),
      originalSource,
      originalOutline: structuredClone(originalOutline),
      symbolSpans: undefined,
    };
  }

  private analysis(document: SourceDocument): SourceAnalysis {
    if (!this.baseArchive) {
      throw new Error("no archive is open");
    }
    const cached = this.analyses.get(document.descriptor);
    if (cached?.source === document.source) {
      return cached.analysis;
    }
    const analysis = new SourceAnalysis(
      document.source,
      document,
      this.baseArchive,
    );
    this.analyses.set(document.descriptor, {
      source: document.source,
      analysis,
    });
    return analysis;
  }

  private static parameterSignature(descriptor: string): string {
    const end = descriptor.indexOf(")");
    return end < 0 ? descriptor : descriptor.slice(0, end + 1);
  }
}
