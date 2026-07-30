import type { EditorState } from "@codemirror/state";

import type {
  Archive,
  MemberNavigation,
  SourceDocument,
  SymbolDestination,
} from "./models";
import { JavaDefinitionResolver } from "./javaDefinitionResolver";
import { KotlinDefinitionResolver } from "./kotlinDefinitionResolver";

export interface ResolvedSymbol {
  range: { from: number; to: number };
  destination: SymbolDestination;
}

export interface SemanticToken {
  from: number;
  to: number;
  kind: "type" | "function" | "property" | "variable" | "annotation" | "label";
}

export interface MemberAtOffset {
  kind: "field" | "method";
  name: string;
  arity: number | null;
}

export interface SourceDefinitionResolver {
  resolve(state: EditorState, offset: number): ResolvedSymbol | null;
  resolveReferenceTarget(state: EditorState, offset: number): ResolvedSymbol | null;
  isDeclaration(state: EditorState, symbol: ResolvedSymbol): boolean;
  isNavigable(destination: SymbolDestination): boolean;
  symbols(state: EditorState): ResolvedSymbol[];
  localOrdinal(
    state: EditorState,
    destination: Extract<SymbolDestination, { kind: "local" }>,
  ): number | null;
  localKind(
    state: EditorState,
    destination: Extract<SymbolDestination, { kind: "local" }>,
  ): "local" | "label";
  localBindingRange(
    state: EditorState,
    destination: Extract<SymbolDestination, { kind: "local" }>,
  ): { from: number; to: number } | null;
  locateMember?(
    state: EditorState,
    target: MemberNavigation,
  ): { from: number; to: number } | null;
  memberAtOffset?(state: EditorState, offset: number): MemberAtOffset | null;
  semanticTokens?(): SemanticToken[];
}

export function createSourceDefinitionResolver(
  document: SourceDocument,
  archive: Archive,
): SourceDefinitionResolver {
  return document.language === "kotlin"
    ? new KotlinDefinitionResolver(document, archive)
    : new JavaDefinitionResolver(document, archive);
}
