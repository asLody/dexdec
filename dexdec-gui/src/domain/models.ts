export interface Archive {
  sessionId: number;
  path: string;
  name: string;
  classCount: number;
  classes: ClassSummary[];
  resources: ResourceEntry[];
  overview: ApkOverview | null;
}

export interface ApkOverview {
  packageName: string | null;
  applicationLabel: string | null;
  applicationIcon: string | null;
  versionName: string | null;
  versionCode: string | null;
  minSdk: string | null;
  targetSdk: string | null;
  debuggable: boolean | null;
  allowBackup: boolean | null;
  usesCleartextTraffic: boolean | null;
  permissions: string[];
  components: {
    activities: number;
    services: number;
    receivers: number;
    providers: number;
    explicitlyExported: number;
    launcherActivities: number;
  };
  dexFileCount: number;
  resourceCount: number;
  nativeLibraryCount: number;
  nativeAbis: string[];
  signatureCount: number;
}

export type ResourceKind =
  | "xml"
  | "image"
  | "text"
  | "font"
  | "nativeLibrary"
  | "resourceTable"
  | "signature"
  | "binary";

export interface ResourceEntry {
  path: string;
  kind: ResourceKind;
  size: number;
  compressedSize: number;
}

export interface ResourceDocument {
  path: string;
  kind: ResourceKind;
  mimeType: string | null;
  textFormat: ResourceTextFormat | null;
  size: number;
  text: string | null;
  dataUrl: string | null;
  message: string | null;
}

export type ResourceTextFormat =
  | "plain"
  | "xml"
  | "json"
  | "html"
  | "css"
  | "javascript"
  | "typescript"
  | "java"
  | "kotlin"
  | "aidl"
  | "smali"
  | "properties"
  | "markdown"
  | "yaml"
  | "toml"
  | "sql"
  | "shell"
  | "c"
  | "cpp"
  | "proto"
  | "gradle";

export interface ResourceNavigationTarget {
  kind: "xmlElement";
  names: string[];
  attribute?: {
    name: string;
    value: string;
  };
}

export interface ResourceNavigation {
  sequence: number;
  path: string;
  target: ResourceNavigationTarget;
}

export interface SymbolSearchResult {
  kind: "class" | "field" | "method" | "resource";
  name: string;
  detail: string;
  classDescriptor: string | null;
  descriptor: string | null;
  resourcePath: string | null;
}

export interface CodeSearchRequest {
  query: string;
  matchCase: boolean;
  wholeWord: boolean;
  useRegex: boolean;
  maxResults: number;
}

export interface CodeSearchMatch {
  classDescriptor: string;
  sourcePath: string;
  line: number;
  column: number;
  matchLength: number;
  excerpt: string;
  excerptMatchStart: number;
}

export type CodeSearchEvent =
  | {
      type: "results";
      items: CodeSearchMatch[];
    }
  | {
      type: "progress";
      scannedClasses: number;
      totalClasses: number;
      failedClasses: number;
      matches: number;
    };

export interface CodeSearchSummary {
  scannedClasses: number;
  totalClasses: number;
  failedClasses: number;
  matches: number;
  truncated: boolean;
  elapsedMs: number;
}

export interface ClassSummary {
  descriptor: string;
  qualifiedName: string;
  package: string;
  binaryName: string;
  displayName: string;
  parentDescriptor: string | null;
  sourcePath: string;
}

export type ClassKind = "class" | "interface" | "annotation" | "enum";

export interface ClassOutline {
  descriptor: string;
  qualifiedName: string;
  kind: ClassKind;
  accessFlags: number;
  superClass: string | null;
  interfaces: string[];
  sourceFile: string | null;
  parentClass: string | null;
  nestedClasses: string[];
  fields: FieldOutline[];
  methods: MethodOutline[];
}

export interface FieldOutline {
  name: string;
  originalName?: string;
  descriptor: string;
  displayType: string;
  accessFlags: number;
}

export interface MethodOutline {
  name: string;
  originalName?: string;
  descriptor: string;
  displaySignature: string;
  accessFlags: number;
  hasCode: boolean;
  constructor: boolean;
}

export type SourceLanguage = "java" | "kotlin";

/**
 * What to read a class as: one language for everything, or `auto` to read each
 * class as whatever it was written in.
 */
export type LanguagePreference = SourceLanguage | "auto";

export interface SourceDocument {
  descriptor: string;
  language: SourceLanguage;
  sourcePath: string;
  source: string;
  methodCount: number;
  elapsedMs: number;
  outline: ClassOutline;
  /** Immutable decompiler output used to derive renamed presentations. */
  originalSource?: string;
  originalOutline?: ClassOutline;
  /** Semantic identities for identifiers after presentation aliases are applied. */
  symbolSpans?: SourceSymbolSpan[];
}

export interface MethodRequest {
  class: string;
  method: string;
  descriptor?: string;
}

export interface MethodDocument {
  class: string;
  method: string;
  descriptor: string | null;
  language: SourceLanguage;
  source: string | null;
  elapsedMs: number;
}

export interface MemberNavigation {
  sequence: number;
  classDescriptor: string;
  kind: "field" | "method";
  /** Canonical DEX name. Presentation aliases never enter navigation state. */
  name: string;
  descriptor: string;
}

/** A source-level definition candidate resolved from the Java syntax tree. */
export type SymbolDestination =
  | {
      kind: "local";
      from: number;
      to: number;
      localOrdinal?: number;
      localKind?: "local" | "label";
      originalName?: string;
    }
  | {
      kind: "class";
      classDescriptor: string;
    }
  | {
      kind: "member";
      classDescriptor: string;
      memberKind: "field" | "method";
      name: string;
      arity: number | null;
      parameterDescriptors?: (string | null)[];
      descriptor?: string;
    };

export interface SourceSymbolSpan {
  from: number;
  to: number;
  destination: SymbolDestination;
}

export type ReferenceTarget =
  | {
      kind: "class";
      classDescriptor: string;
    }
  | {
      kind: "field";
      classDescriptor: string;
      name: string;
      descriptor: string;
    }
  | {
      kind: "method";
      classDescriptor: string;
      name: string;
      descriptor: string;
    };

export interface ReferenceLocation {
  classDescriptor: string;
  method: string;
  descriptor: string;
  offset: number;
  /** Presentation-only aliases; DEX lookup continues to use the fields above. */
  displayClassName?: string;
  displayMethodName?: string;
}

export interface ReferenceResults {
  locations: ReferenceLocation[];
  elapsedMs: number;
}

export type RenameTarget =
  | {
      kind: "class";
      classDescriptor: string;
      originalName: string;
    }
  | {
      kind: "field";
      classDescriptor: string;
      originalName: string;
      descriptor: string;
    }
  | {
      kind: "method";
      classDescriptor: string;
      originalName: string;
      descriptor: string;
    }
  | {
      kind: "local";
      classDescriptor: string;
      originalName: string;
      localOrdinal: number;
    }
  | {
      kind: "label";
      classDescriptor: string;
      originalName: string;
      localOrdinal: number;
    };

export interface ProjectRename {
  target: RenameTarget;
  alias: string;
}

export interface ProjectSnapshot {
  databasePath: string | null;
  archivePath: string;
  renames: ProjectRenameDto[];
}

/** Flat wire representation stored in the versioned dexdb schema. */
export interface ProjectRenameDto {
  kind: RenameTarget["kind"];
  classDescriptor: string;
  originalName: string;
  descriptor: string;
  localOrdinal: number;
  alias: string;
}
