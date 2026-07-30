import { useVirtualizer } from "@tanstack/react-virtual";
import {
  CaseSensitive,
  FileCode2,
  LoaderCircle,
  Regex,
  Search,
  Square,
  WholeWord,
  X,
} from "lucide-react";
import { useEffect, useMemo, useRef, useState } from "react";

import type {
  CodeSearchEvent,
  CodeSearchMatch,
  CodeSearchSummary,
} from "../domain/models";
import { useTranslation } from "../i18n";
import { decompilerClient } from "../services/decompilerClient";
import { useWorkspace } from "../state/workspace";
import { EmptyState } from "./EmptyState";

interface SearchProgress {
  scannedClasses: number;
  totalClasses: number;
  failedClasses: number;
  matches: number;
}

interface ActiveSearch {
  sessionId: number;
  requestId: number;
  cancelled: boolean;
}

const EMPTY_PROGRESS: SearchProgress = {
  scannedClasses: 0,
  totalClasses: 0,
  failedClasses: 0,
  matches: 0,
};

export function CodeSearchPanel() {
  const archive = useWorkspace((state) => state.archive);
  const language = useWorkspace((state) => state.sourceLanguage);
  const decompileOptions = useWorkspace((state) => state.decompileOptions);
  const selectClass = useWorkspace((state) => state.selectClass);
  const restorePosition = useWorkspace((state) => state.restorePosition);
  const setVisible = useWorkspace((state) => state.setCodeSearchVisible);
  const { t } = useTranslation();
  const [query, setQuery] = useState("");
  const [matchCase, setMatchCase] = useState(false);
  const [wholeWord, setWholeWord] = useState(false);
  const [useRegex, setUseRegex] = useState(false);
  const [results, setResults] = useState<CodeSearchMatch[]>([]);
  const [progress, setProgress] = useState<SearchProgress>(EMPTY_PROGRESS);
  const [summary, setSummary] = useState<CodeSearchSummary | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [running, setRunning] = useState(false);
  const [activeIndex, setActiveIndex] = useState(0);
  const inputRef = useRef<HTMLInputElement>(null);
  const listRef = useRef<HTMLDivElement>(null);
  const sequenceRef = useRef(0);
  const activeSearchRef = useRef<ActiveSearch | null>(null);
  const classNames = useMemo(
    () => new Map(archive?.classes.map((entry) => [entry.descriptor, entry.qualifiedName])),
    [archive],
  );
  const virtualizer = useVirtualizer({
    count: results.length,
    getScrollElement: () => listRef.current,
    estimateSize: () => 46,
    overscan: 18,
  });

  useEffect(() => {
    inputRef.current?.focus();
  }, []);

  useEffect(() => {
    return () => cancelActiveSearch(activeSearchRef);
  }, []);

  useEffect(() => {
    cancelActiveSearch(activeSearchRef);
    setResults([]);
    setSummary(null);
    setError(null);
    setProgress(EMPTY_PROGRESS);
    setRunning(false);
  }, [
    archive?.sessionId,
    language,
    decompileOptions.indentWidth,
    decompileOptions.includeNested,
  ]);

  const handleEvent = (requestId: number, event: CodeSearchEvent) => {
    if (activeSearchRef.current?.requestId !== requestId) return;
    if (event.type === "results") {
      setResults((current) => [...current, ...event.items]);
      return;
    }
    setProgress(event);
  };

  const start = async () => {
    const term = query.trim();
    if (!archive || !term) return;
    cancelActiveSearch(activeSearchRef);
    const requestId = ++sequenceRef.current;
    activeSearchRef.current = {
      sessionId: archive.sessionId,
      requestId,
      cancelled: false,
    };
    setResults([]);
    setProgress(EMPTY_PROGRESS);
    setSummary(null);
    setError(null);
    setActiveIndex(0);
    setRunning(true);
    try {
      const nextSummary = await decompilerClient.searchCode(
        archive.sessionId,
        requestId,
        {
          query: term,
          matchCase,
          wholeWord,
          useRegex,
          maxResults: 10_000,
        },
        language,
        decompileOptions,
        (event) => handleEvent(requestId, event),
      );
      if (activeSearchRef.current?.requestId !== requestId) return;
      setSummary(nextSummary);
    } catch (reason) {
      const active = activeSearchRef.current;
      if (active?.requestId === requestId && !active.cancelled) {
        setError(reason instanceof Error ? reason.message : String(reason));
      }
    } finally {
      if (activeSearchRef.current?.requestId === requestId) {
        activeSearchRef.current = null;
        setRunning(false);
      }
    }
  };

  const stop = () => {
    cancelActiveSearch(activeSearchRef);
    setRunning(false);
  };

  const close = () => {
    stop();
    setVisible(false);
  };

  const open = async (result: CodeSearchMatch | undefined) => {
    if (!result) return;
    if (running) stop();
    await selectClass(result.classDescriptor);
    if (useWorkspace.getState().activeDescriptor !== result.classDescriptor) return;
    restorePosition(result.classDescriptor, {
      line: result.line,
      column: result.column,
    });
  };

  const move = (index: number) => {
    if (!results.length) return;
    const next = Math.max(0, Math.min(results.length - 1, index));
    setActiveIndex(next);
    virtualizer.scrollToIndex(next, { align: "auto" });
  };

  const onKeyDown = (event: React.KeyboardEvent) => {
    if (event.key === "Escape") {
      event.preventDefault();
      close();
    } else if (event.key === "Enter") {
      event.preventDefault();
      if (event.currentTarget === listRef.current && results.length) {
        void open(results[activeIndex]);
      } else if (!running) {
        void start();
      }
    } else if (event.key === "ArrowDown" || event.key === "ArrowUp") {
      if (!results.length) return;
      event.preventDefault();
      move(activeIndex + (event.key === "ArrowDown" ? 1 : -1));
      listRef.current?.focus();
    }
  };

  const percent = progress.totalClasses
    ? Math.min(100, (progress.scannedClasses / progress.totalClasses) * 100)
    : 0;

  return (
    <section className="absolute inset-x-0 bottom-0 z-30 flex h-[350px] max-h-[58%] flex-col border-t border-[var(--border-strong)] bg-[var(--chrome)] shadow-[0_-10px_32px_rgba(0,0,0,0.4)]">
      <header className="flex h-8 shrink-0 items-center gap-2 border-b border-[var(--border)] px-3">
        <Search size={12} className="shrink-0 text-[var(--accent)]" />
        <span className="text-[12px] font-medium text-[var(--text)]">
          {t("codeSearch.title")}
        </span>
        {running ? <LoaderCircle size={11} className="animate-spin text-[var(--text-faint)]" /> : null}
        {results.length ? (
          <span className="text-[10.5px] tabular-nums text-[var(--text-faint)]">
            {t("codeSearch.resultCount", results.length)}
          </span>
        ) : null}
        {summary ? (
          <span className="text-[10px] tabular-nums text-[var(--text-faint)]">
            {summary.elapsedMs} ms
          </span>
        ) : null}
        <button
          type="button"
          className="icon-button ml-auto !h-[22px] !w-[22px]"
          title={t("codeSearch.close")}
          aria-label={t("codeSearch.close")}
          onClick={close}
        >
          <X size={12} />
        </button>
      </header>

      <div className="flex h-10 shrink-0 items-center gap-1.5 border-b border-[var(--border)] px-3">
        <div className="relative min-w-[220px] max-w-[720px] flex-1">
          <Search size={12} className="pointer-events-none absolute left-2.5 top-1/2 -translate-y-1/2 text-[var(--text-faint)]" />
          <input
            ref={inputRef}
            value={query}
            onChange={(event) => setQuery(event.target.value)}
            onKeyDown={onKeyDown}
            className="h-7 w-full rounded-[5px] border border-[var(--border-strong)] bg-[var(--input)] pl-8 pr-2 text-[12px] text-[var(--text)] outline-none focus:border-[var(--accent)]"
            placeholder={t("codeSearch.placeholder")}
            spellCheck={false}
          />
        </div>
        <SearchOption
          active={matchCase}
          label={t("codeSearch.matchCase")}
          onClick={() => setMatchCase((value) => !value)}
        >
          <CaseSensitive size={14} />
        </SearchOption>
        <SearchOption
          active={wholeWord}
          label={t("codeSearch.wholeWord")}
          onClick={() => setWholeWord((value) => !value)}
        >
          <WholeWord size={14} />
        </SearchOption>
        <SearchOption
          active={useRegex}
          label={t("codeSearch.regex")}
          onClick={() => setUseRegex((value) => !value)}
        >
          <Regex size={13} />
        </SearchOption>
        <button
          type="button"
          className="ml-1 flex h-7 items-center gap-1.5 rounded-[5px] border border-[var(--border-strong)] bg-[var(--raised)] px-2.5 text-[11.5px] text-[var(--text)] hover:bg-[var(--hover)] disabled:opacity-45"
          disabled={!query.trim()}
          onClick={running ? stop : () => void start()}
        >
          {running ? <Square size={10} fill="currentColor" /> : <Search size={11} />}
          {running ? t("codeSearch.stop") : t("codeSearch.start")}
        </button>
      </div>

      {running ? (
        <div className="h-[2px] shrink-0 bg-[var(--border)]">
          <div
            className="h-full bg-[var(--accent)] transition-[width] duration-150"
            style={{ width: `${percent}%` }}
          />
        </div>
      ) : null}

      <div
        ref={listRef}
        className="min-h-0 flex-1 overflow-auto py-1 outline-none"
        tabIndex={0}
        role="listbox"
        aria-activedescendant={results[activeIndex] ? `code-search-row-${activeIndex}` : undefined}
        onKeyDown={onKeyDown}
      >
        {error ? (
          <PanelMessage danger>{error}</PanelMessage>
        ) : results.length ? (
          <div className="relative w-full" style={{ height: virtualizer.getTotalSize() }}>
            {virtualizer.getVirtualItems().map((row) => {
              const result = results[row.index];
              const className = classNames.get(result.classDescriptor) ?? result.classDescriptor;
              return (
                <button
                  key={`${result.classDescriptor}:${result.line}:${result.column}:${row.index}`}
                  id={`code-search-row-${row.index}`}
                  type="button"
                  role="option"
                  aria-selected={row.index === activeIndex}
                  className={`absolute left-0 top-0 flex w-full min-w-0 items-center gap-2 border-l-2 px-3 text-left ${row.index === activeIndex ? "border-[var(--accent)] bg-[var(--active)]" : "border-transparent hover:bg-[var(--hover)]"}`}
                  style={{ height: row.size, transform: `translateY(${row.start}px)` }}
                  onMouseMove={() => setActiveIndex(row.index)}
                  onClick={() => void open(result)}
                >
                  <FileCode2 size={12} className="shrink-0 text-[var(--glyph-class)]" />
                  <span className="min-w-0 flex-1">
                    <span className="flex min-w-0 items-center gap-2 text-[10.5px] text-[var(--text-faint)]">
                      <span className="truncate">{className}</span>
                      <span className="shrink-0 font-mono tabular-nums">:{result.line}</span>
                    </span>
                    <span className="block min-w-0 truncate whitespace-pre font-mono text-[11.5px] leading-5 text-[var(--text-muted)]">
                      <HighlightedExcerpt result={result} />
                    </span>
                  </span>
                </button>
              );
            })}
          </div>
        ) : running ? (
          <PanelMessage>
            {t(
              "codeSearch.progress",
              progress.scannedClasses,
              progress.totalClasses,
              progress.matches,
            )}
          </PanelMessage>
        ) : summary ? (
          <EmptyState compact icon={<Search size={17} />} title={t("codeSearch.empty")} />
        ) : (
          <EmptyState compact icon={<Search size={17} />} title={t("codeSearch.hint")} />
        )}
      </div>

      {(running || summary) ? (
        <footer className="flex h-6 shrink-0 items-center gap-3 border-t border-[var(--border)] px-3 text-[10px] tabular-nums text-[var(--text-faint)]">
          <span>
            {t("codeSearch.scanned", progress.scannedClasses, progress.totalClasses)}
          </span>
          {progress.failedClasses ? (
            <span className="text-[var(--warning)]">
              {t("codeSearch.failed", progress.failedClasses)}
            </span>
          ) : null}
          {summary?.truncated ? <span>{t("codeSearch.truncated")}</span> : null}
        </footer>
      ) : null}
    </section>
  );
}

function SearchOption({
  active,
  label,
  onClick,
  children,
}: {
  active: boolean;
  label: string;
  onClick: () => void;
  children: React.ReactNode;
}) {
  return (
    <button
      type="button"
      aria-pressed={active}
      aria-label={label}
      title={label}
      className={`icon-button !h-7 !w-7 ${active ? "!border-[var(--accent)] !bg-[var(--active)] !text-[var(--accent)]" : ""}`}
      onClick={onClick}
    >
      {children}
    </button>
  );
}

function HighlightedExcerpt({ result }: { result: CodeSearchMatch }) {
  const characters = Array.from(result.excerpt);
  const start = result.excerptMatchStart;
  const end = start + result.matchLength;
  return (
    <>
      {characters.slice(0, start).join("")}
      <mark className="rounded-[2px] bg-[color-mix(in_srgb,var(--accent)_24%,transparent)] px-px text-[var(--text)]">
        {characters.slice(start, end).join("")}
      </mark>
      {characters.slice(end).join("")}
    </>
  );
}

function PanelMessage({
  children,
  danger = false,
}: {
  children: React.ReactNode;
  danger?: boolean;
}) {
  return (
    <div className={`flex h-full items-center justify-center px-8 text-center text-[11.5px] ${danger ? "text-[var(--danger)]" : "text-[var(--text-faint)]"}`}>
      {children}
    </div>
  );
}

function cancelActiveSearch(reference: React.MutableRefObject<ActiveSearch | null>) {
  const active = reference.current;
  if (!active) return;
  active.cancelled = true;
  void decompilerClient
    .cancelCodeSearch(active.sessionId, active.requestId)
    .catch(() => {
      /* The archive may already have been closed. */
    });
  reference.current = null;
}
