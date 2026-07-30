import { useVirtualizer } from "@tanstack/react-virtual";
import { Braces, Search } from "lucide-react";
import {
  useDeferredValue,
  useEffect,
  useMemo,
  useRef,
  useState,
} from "react";

import { useTranslation } from "../i18n";
import type { ClassSummary } from "../domain/models";
import { fuzzyMatch } from "../domain/fuzzy";
import { useWorkspace } from "../state/workspace";

interface Match {
  classInfo: ClassSummary;
  score: number;
  indices: number[];
}

const RESULT_LIMIT = 400;

export function QuickOpen() {
  const archive = useWorkspace((state) => state.archive);
  const activeDescriptor = useWorkspace((state) => state.activeDescriptor);
  const selectClass = useWorkspace((state) => state.selectClass);
  const setVisible = useWorkspace((state) => state.setQuickOpenVisible);
  const [query, setQuery] = useState("");
  const deferredQuery = useDeferredValue(query);
  const [activeIndex, setActiveIndex] = useState(0);
  const inputRef = useRef<HTMLInputElement>(null);
  const { t } = useTranslation();
  const scrollRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    inputRef.current?.focus();
    inputRef.current?.select();
  }, []);

  const matches = useMemo(() => {
    if (!archive) {
      return [];
    }
    const term = deferredQuery.trim();
    if (!term) {
      const active = archive.classes.find(
        (entry) => entry.descriptor === activeDescriptor,
      );
      const rest = archive.classes
        .filter((entry) => entry.descriptor !== activeDescriptor)
        .slice(0, 60);
      return [active, ...rest]
        .filter((entry): entry is ClassSummary => Boolean(entry))
        .map((classInfo) => ({ classInfo, score: 0, indices: [] }));
    }
    const scored: Match[] = [];
    for (const classInfo of archive.classes) {
      const result = fuzzyMatch(term, classInfo.qualifiedName);
      if (result) {
        scored.push({ classInfo, ...result });
      }
    }
    scored.sort(
      (left, right) =>
        right.score - left.score ||
        left.classInfo.qualifiedName.localeCompare(right.classInfo.qualifiedName),
    );
    return scored.slice(0, RESULT_LIMIT);
  }, [archive, activeDescriptor, deferredQuery]);

  useEffect(() => {
    setActiveIndex(0);
  }, [deferredQuery]);

  const virtualizer = useVirtualizer({
    count: matches.length,
    getScrollElement: () => scrollRef.current,
    estimateSize: () => 32,
    overscan: 8,
  });

  const close = () => setVisible(false);
  const openMatch = (match: Match | undefined) => {
    if (!match) {
      return;
    }
    close();
    void selectClass(match.classInfo.descriptor);
  };

  const onKeyDown = (event: React.KeyboardEvent) => {
    if (event.key === "ArrowDown" || event.key === "ArrowUp") {
      event.preventDefault();
      if (!matches.length) {
        return;
      }
      const delta = event.key === "ArrowDown" ? 1 : -1;
      setActiveIndex((current) => {
        const next = (current + delta + matches.length) % matches.length;
        virtualizer.scrollToIndex(next, { align: "auto" });
        return next;
      });
    } else if (event.key === "Home" || event.key === "End") {
      event.preventDefault();
      const next = event.key === "Home" ? 0 : matches.length - 1;
      if (next >= 0) {
        setActiveIndex(next);
        virtualizer.scrollToIndex(next, { align: "auto" });
      }
    } else if (event.key === "Enter") {
      event.preventDefault();
      openMatch(matches[activeIndex] ?? matches[0]);
    } else if (event.key === "Escape") {
      event.preventDefault();
      close();
    }
  };

  return (
    <div
      className="palette-backdrop palette-backdrop-quick"
      onMouseDown={(event) => {
        if (event.target === event.currentTarget) {
          close();
        }
      }}
    >
      <div
        role="dialog"
        aria-label={t("toolbar.goToClassPlaceholder")}
        className="palette"
      >
        <div className="palette-search">
          <Search size={14} className="palette-search-icon" strokeWidth={2} />
          <input
            ref={inputRef}
            value={query}
            onChange={(event) => setQuery(event.target.value)}
            onKeyDown={onKeyDown}
            placeholder={t("quickopen.placeholder")}
            spellCheck={false}
            role="combobox"
            aria-expanded="true"
            aria-controls="quick-open-list"
            aria-activedescendant={`quick-open-row-${activeIndex}`}
            className="palette-input"
          />
          {archive ? (
            <span className="palette-count">
              {matches.length.toLocaleString()}
            </span>
          ) : null}
        </div>

        <div ref={scrollRef} className="palette-list">
          {matches.length ? (
            <div
              id="quick-open-list"
              role="listbox"
              className="relative w-full"
              style={{ height: `${virtualizer.getTotalSize()}px` }}
            >
              {virtualizer.getVirtualItems().map((virtualRow) => {
                const match = matches[virtualRow.index];
                return (
                  <div
                    key={match.classInfo.descriptor}
                    id={`quick-open-row-${virtualRow.index}`}
                    role="option"
                    aria-selected={virtualRow.index === activeIndex}
                    className={`quick-open-row absolute top-0 ${
                      virtualRow.index === activeIndex ? "quick-open-row-active" : ""
                    }`}
                    style={{
                      height: `${virtualRow.size}px`,
                      transform: `translateY(${virtualRow.start}px)`,
                    }}
                    onMouseMove={() => setActiveIndex(virtualRow.index)}
                    onMouseDown={(event) => {
                      event.preventDefault();
                      openMatch(match);
                    }}
                  >
                    <Braces size={12} className="shrink-0 text-[var(--glyph-class)]" />
                    <span className="min-w-0 shrink truncate text-[12.5px] text-[var(--text)]">
                      <HighlightedName
                        name={match.classInfo.displayName}
                        qualifiedName={match.classInfo.qualifiedName}
                        indices={match.indices}
                      />
                    </span>
                    <span className="min-w-0 flex-1 truncate text-right text-[11px] text-[var(--text-faint)]">
                      {match.classInfo.package || "<default>"}
                    </span>
                  </div>
                );
              })}
            </div>
          ) : (
            <div className="palette-empty">{t("quickopen.empty")}</div>
          )}
        </div>

        <div className="palette-footer">
          <span className="palette-footer-item">
            <kbd className="kbd">↑↓</kbd> {t("palette.navigate")}
          </span>
          <span className="palette-footer-item">
            <kbd className="kbd">↵</kbd> {t("palette.open")}
          </span>
          <span className="palette-footer-item">
            <kbd className="kbd">esc</kbd> {t("palette.dismiss")}
          </span>
        </div>
      </div>
    </div>
  );
}

/*
 * Renders the class display name with matched characters emphasized. Match
 * indices refer to the qualified name, so only those falling inside the
 * display-name suffix are used.
 */
function HighlightedName({
  name,
  qualifiedName,
  indices,
}: {
  name: string;
  qualifiedName: string;
  indices: number[];
}) {
  if (!indices.length) {
    return <>{name}</>;
  }
  const offset = qualifiedName.length - name.length;
  const local = new Set(
    indices.filter((index) => index >= offset).map((index) => index - offset),
  );
  if (!local.size) {
    return <>{name}</>;
  }
  return (
    <>
      {[...name].map((char, index) =>
        local.has(index) ? (
          <span key={index} className="font-semibold text-[var(--accent-strong)]">
            {char}
          </span>
        ) : (
          <span key={index}>{char}</span>
        ),
      )}
    </>
  );
}
