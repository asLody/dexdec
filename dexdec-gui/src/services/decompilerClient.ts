import { Channel, invoke } from "@tauri-apps/api/core";
import { open } from "@tauri-apps/plugin-dialog";

import type { DecompileOptions } from "../state/decompileOptions";
import type {
  Archive,
  ClassOutline,
  CodeSearchEvent,
  CodeSearchRequest,
  CodeSearchSummary,
  MethodDocument,
  LanguagePreference,
  MethodRequest,
  ReferenceResults,
  ReferenceTarget,
  ResourceDocument,
  SourceDocument,
  SymbolSearchResult,
} from "../domain/models";

export interface DecompilerClient {
  chooseArchive(): Promise<string | null>;
  openArchive(path: string): Promise<Archive>;
  closeArchive(sessionId: number): Promise<void>;
  inspectClass(sessionId: number, descriptor: string): Promise<ClassOutline>;
  decompileClass(
    sessionId: number,
    requestId: number,
    descriptor: string,
    language: LanguagePreference,
    options: DecompileOptions,
  ): Promise<SourceDocument>;
  decompileMethod(
    sessionId: number,
    requestId: number,
    request: MethodRequest,
    language: LanguagePreference,
    options: DecompileOptions,
  ): Promise<MethodDocument>;
  cancelRequest(sessionId: number, requestId: number): Promise<void>;
  findReferences(
    sessionId: number,
    requestId: number,
    target: ReferenceTarget,
  ): Promise<ReferenceResults>;
  readResource(sessionId: number, path: string): Promise<ResourceDocument>;
  searchSymbols(
    sessionId: number,
    query: string,
    limit?: number,
  ): Promise<SymbolSearchResult[]>;
  searchCode(
    sessionId: number,
    requestId: number,
    search: CodeSearchRequest,
    language: LanguagePreference,
    options: DecompileOptions,
    onEvent: (event: CodeSearchEvent) => void,
  ): Promise<CodeSearchSummary>;
  cancelCodeSearch(sessionId: number, requestId: number): Promise<void>;
}

export class TauriDecompilerClient implements DecompilerClient {
  async chooseArchive(): Promise<string | null> {
    const selected = await open({
      title: "Open APK, DEX, or DexDec Database",
      multiple: false,
      directory: false,
      filters: [
        { name: "DexDec database", extensions: ["dexdb"] },
        { name: "Android bytecode", extensions: ["apk", "dex"] },
        { name: "All files", extensions: ["*"] },
      ],
    });
    return typeof selected === "string" ? selected : null;
  }

  openArchive(path: string): Promise<Archive> {
    return invoke<Archive>("open_archive", { path });
  }

  closeArchive(sessionId: number): Promise<void> {
    return invoke<void>("close_archive", { sessionId });
  }

  inspectClass(sessionId: number, descriptor: string): Promise<ClassOutline> {
    return invoke<ClassOutline>("inspect_class", { sessionId, descriptor });
  }

  decompileClass(
    sessionId: number,
    requestId: number,
    descriptor: string,
    language: LanguagePreference,
    options: DecompileOptions,
  ): Promise<SourceDocument> {
    return invoke<SourceDocument>("decompile_class", {
      sessionId,
      requestId,
      descriptor,
      language,
      options,
    });
  }

  decompileMethod(
    sessionId: number,
    requestId: number,
    request: MethodRequest,
    language: LanguagePreference,
    options: DecompileOptions,
  ): Promise<MethodDocument> {
    return invoke<MethodDocument>("decompile_method", {
      sessionId,
      requestId,
      request,
      language,
      options,
    });
  }

  cancelRequest(sessionId: number, requestId: number): Promise<void> {
    return invoke<void>("cancel_decompile_request", { sessionId, requestId });
  }

  findReferences(
    sessionId: number,
    requestId: number,
    target: ReferenceTarget,
  ): Promise<ReferenceResults> {
    return invoke<ReferenceResults>("find_references", { sessionId, requestId, target });
  }

  readResource(sessionId: number, path: string): Promise<ResourceDocument> {
    return invoke<ResourceDocument>("read_resource", { sessionId, path });
  }

  searchSymbols(
    sessionId: number,
    query: string,
    limit = 200,
  ): Promise<SymbolSearchResult[]> {
    return invoke<SymbolSearchResult[]>("search_symbols", {
      sessionId,
      query,
      limit,
    });
  }

  searchCode(
    sessionId: number,
    requestId: number,
    search: CodeSearchRequest,
    language: LanguagePreference,
    options: DecompileOptions,
    onEvent: (event: CodeSearchEvent) => void,
  ): Promise<CodeSearchSummary> {
    const channel = new Channel<CodeSearchEvent>();
    channel.onmessage = onEvent;
    return invoke<CodeSearchSummary>("search_code", {
      sessionId,
      requestId,
      search,
      language,
      options,
      onEvent: channel,
    });
  }

  cancelCodeSearch(sessionId: number, requestId: number): Promise<void> {
    return invoke<void>("cancel_code_search", { sessionId, requestId });
  }
}

export const decompilerClient: DecompilerClient = new TauriDecompilerClient();
