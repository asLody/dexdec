import { useVirtualizer } from "@tanstack/react-virtual";
import {
  Braces,
  CircleDot,
  FileCode2,
  FunctionSquare,
  LoaderCircle,
  Search,
} from "lucide-react";
import { useEffect, useRef, useState } from "react";

import type { SymbolSearchResult } from "../domain/models";
import { useTranslation } from "../i18n";
import { decompilerClient } from "../services/decompilerClient";
import { useWorkspace } from "../state/workspace";

export function GlobalSearch() {
  const archive = useWorkspace((state) => state.archive);
  const selectClass = useWorkspace((state) => state.selectClass);
  const openResource = useWorkspace((state) => state.openResource);
  const navigateToMember = useWorkspace((state) => state.navigateToMember);
  const setVisible = useWorkspace((state) => state.setGlobalSearchVisible);
  const [query, setQuery] = useState("");
  const [results, setResults] = useState<SymbolSearchResult[]>([]);
  const [activeIndex, setActiveIndex] = useState(0);
  const [loading, setLoading] = useState(false);
  const requestSequence = useRef(0);
  const inputRef = useRef<HTMLInputElement>(null);
  const scrollRef = useRef<HTMLDivElement>(null);
  const { t } = useTranslation();

  useEffect(() => {
    inputRef.current?.focus();
  }, []);

  useEffect(() => {
    const term = query.trim();
    const sequence = ++requestSequence.current;
    setActiveIndex(0);
    if (!archive || !term) {
      setResults([]);
      setLoading(false);
      return;
    }
    setLoading(true);
    const timer = window.setTimeout(() => {
      void decompilerClient
        .searchSymbols(archive.sessionId, term)
        .then((next) => {
          if (requestSequence.current === sequence) setResults(next);
        })
        .catch((error) => {
          if (requestSequence.current === sequence) {
            useWorkspace.getState().reportError(String(error));
          }
        })
        .finally(() => {
          if (requestSequence.current === sequence) setLoading(false);
        });
    }, 90);
    return () => window.clearTimeout(timer);
  }, [archive, query]);

  const virtualizer = useVirtualizer({
    count: results.length,
    getScrollElement: () => scrollRef.current,
    estimateSize: () => 36,
    overscan: 10,
  });

  const close = () => setVisible(false);
  const openResult = async (result: SymbolSearchResult | undefined) => {
    if (!result) return;
    close();
    if (result.kind === "resource" && result.resourcePath) {
      await openResource(result.resourcePath);
      return;
    }
    if (!result.classDescriptor) return;
    await selectClass(result.classDescriptor);
    if ((result.kind === "field" || result.kind === "method") && result.descriptor) {
      navigateToMember({
        classDescriptor: result.classDescriptor,
        kind: result.kind,
        name: result.name,
        descriptor: result.descriptor,
      });
    }
  };

  const onKeyDown = (event: React.KeyboardEvent) => {
    if (event.key === "ArrowDown" || event.key === "ArrowUp") {
      event.preventDefault();
      if (!results.length) return;
      const delta = event.key === "ArrowDown" ? 1 : -1;
      setActiveIndex((current) => {
        const next = (current + delta + results.length) % results.length;
        virtualizer.scrollToIndex(next, { align: "auto" });
        return next;
      });
    } else if (event.key === "Enter") {
      event.preventDefault();
      void openResult(results[activeIndex] ?? results[0]);
    } else if (event.key === "Escape") {
      event.preventDefault();
      close();
    }
  };

  return (
    <div
      className="palette-backdrop palette-backdrop-quick"
      onMouseDown={(event) => {
        if (event.target === event.currentTarget) close();
      }}
    >
      <div role="dialog" aria-label={t("search.title")} className="palette">
        <div className="palette-search">
          {loading ? (
            <LoaderCircle size={14} className="palette-search-icon animate-spin" />
          ) : (
            <Search size={14} className="palette-search-icon" />
          )}
          <input
            ref={inputRef}
            value={query}
            onChange={(event) => setQuery(event.target.value)}
            onKeyDown={onKeyDown}
            placeholder={t("search.placeholder")}
            spellCheck={false}
            className="palette-input"
          />
          {query ? <span className="palette-count">{results.length}</span> : null}
        </div>
        <div ref={scrollRef} className="palette-list">
          {results.length ? (
            <div className="relative w-full" style={{ height: virtualizer.getTotalSize() }}>
              {virtualizer.getVirtualItems().map((row) => {
                const result = results[row.index];
                return (
                  <button
                    type="button"
                    key={`${result.kind}:${result.classDescriptor}:${result.name}:${result.descriptor}:${result.resourcePath}`}
                    className={`quick-open-row absolute top-0 ${row.index === activeIndex ? "quick-open-row-active" : ""}`}
                    style={{ height: row.size, transform: `translateY(${row.start}px)` }}
                    onMouseMove={() => setActiveIndex(row.index)}
                    onClick={() => void openResult(result)}
                  >
                    <ResultIcon kind={result.kind} />
                    <span className="min-w-0 shrink truncate text-[12.5px] text-[var(--text)]">
                      {result.name}
                    </span>
                    <span className="min-w-0 flex-1 truncate text-right font-mono text-[10.5px] text-[var(--text-faint)]">
                      {result.detail}
                    </span>
                  </button>
                );
              })}
            </div>
          ) : (
            <div className="palette-empty">
              {loading
                ? t("search.indexing")
                : query.trim()
                  ? t("search.empty")
                  : t("search.hint")}
            </div>
          )}
        </div>
        <div className="palette-footer">
          <span className="palette-footer-item"><kbd className="kbd">↑↓</kbd> {t("palette.navigate")}</span>
          <span className="palette-footer-item"><kbd className="kbd">↵</kbd> {t("palette.open")}</span>
          <span className="palette-footer-item"><kbd className="kbd">esc</kbd> {t("palette.dismiss")}</span>
        </div>
      </div>
    </div>
  );
}

function ResultIcon({ kind }: { kind: SymbolSearchResult["kind"] }) {
  switch (kind) {
    case "class":
      return <Braces size={12} className="shrink-0 text-[var(--glyph-class)]" />;
    case "field":
      return <CircleDot size={11} className="shrink-0 text-[var(--glyph-field)]" />;
    case "method":
      return <FunctionSquare size={11} className="shrink-0 text-[var(--glyph-method)]" />;
    case "resource":
      return <FileCode2 size={12} className="shrink-0 text-[var(--glyph-package)]" />;
  }
}
