import { useVirtualizer } from "@tanstack/react-virtual";
import { CircleDot, FunctionSquare, Search } from "lucide-react";
import {
  useDeferredValue,
  useEffect,
  useMemo,
  useRef,
  useState,
} from "react";

import { parametersOf } from "../domain/descriptors";
import { useTranslation } from "../i18n";
import { fuzzyMatch } from "../domain/fuzzy";
import { useWorkspace } from "../state/workspace";

interface MemberItem {
  kind: "field" | "method";
  name: string;
  displayName: string;
  detail: string;
  descriptor: string;
  hasCode: boolean;
}

/*
 * "Go to member" palette (⌘⇧O): fuzzy jump across the active document's
 * fields and methods, jumping through the same Java-AST navigation the
 * Outline uses.
 */
export function MemberOpen() {
  const documents = useWorkspace((state) => state.documents);
  const activeDescriptor = useWorkspace((state) => state.activeDescriptor);
  const navigateToMember = useWorkspace((state) => state.navigateToMember);
  const setVisible = useWorkspace((state) => state.setMemberOpenVisible);
  const document = documents.find((item) => item.descriptor === activeDescriptor);
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

  const members = useMemo<MemberItem[]>(() => {
    if (!document) {
      return [];
    }
    const { outline } = document;
    return [
      ...outline.fields.map((field) => ({
        kind: "field" as const,
        name: field.originalName ?? field.name,
        displayName: field.name,
        detail: field.displayType,
        descriptor: field.descriptor,
        hasCode: true,
      })),
      ...outline.methods.map((method) => ({
        kind: "method" as const,
        name: method.originalName ?? method.name,
        displayName: method.constructor ? "<init>" : method.name,
        detail: parametersOf(method.descriptor),
        descriptor: method.descriptor,
        hasCode: method.hasCode,
      })),
    ];
  }, [document]);

  const matches = useMemo(() => {
    const term = deferredQuery.trim();
    if (!term) {
      return members.map((member) => ({ member, indices: [] as number[] }));
    }
    return members
      .map((member) => {
        const result = fuzzyMatch(term, member.displayName);
        return result ? { member, indices: result.indices, score: result.score } : null;
      })
      .filter(
        (entry): entry is { member: MemberItem; indices: number[]; score: number } =>
          entry !== null,
      )
      .sort(
        (left, right) =>
          right.score - left.score ||
          left.member.displayName.localeCompare(right.member.displayName),
      );
  }, [deferredQuery, members]);

  useEffect(() => {
    setActiveIndex(0);
  }, [deferredQuery]);

  const virtualizer = useVirtualizer({
    count: matches.length,
    getScrollElement: () => scrollRef.current,
    estimateSize: () => 30,
    overscan: 8,
  });

  const close = () => setVisible(false);
  const openMember = (item: MemberItem | undefined) => {
    if (!item || !document) {
      return;
    }
    close();
    navigateToMember({
      classDescriptor: document.descriptor,
      kind: item.kind,
      name: item.name,
      descriptor: item.descriptor,
    });
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
    } else if (event.key === "Enter") {
      event.preventDefault();
      openMember(matches[activeIndex]?.member ?? matches[0]?.member);
    } else if (event.key === "Escape") {
      event.preventDefault();
      close();
    }
  };

  return (
    <div
      className="palette-backdrop palette-backdrop-member"
      onMouseDown={(event) => {
        if (event.target === event.currentTarget) {
          close();
        }
      }}
    >
      <div
        role="dialog"
        aria-label={t("memberopen.jump")}
        className="palette palette-narrow"
      >
        <div className="palette-search">
          <Search size={14} className="palette-search-icon" strokeWidth={2} />
          <input
            ref={inputRef}
            value={query}
            onChange={(event) => setQuery(event.target.value)}
            onKeyDown={onKeyDown}
            placeholder={t("memberopen.placeholder", document?.outline.qualifiedName.split(".").at(-1) ?? "")}
            spellCheck={false}
            role="combobox"
            aria-expanded="true"
            aria-controls="member-open-list"
            aria-activedescendant={`member-open-row-${activeIndex}`}
            className="palette-input"
          />
          <span className="palette-count">{matches.length}</span>
        </div>

        <div ref={scrollRef} className="palette-list palette-list-compact">
          {matches.length ? (
            <div
              id="member-open-list"
              role="listbox"
              className="relative w-full"
              style={{ height: `${virtualizer.getTotalSize()}px` }}
            >
              {virtualizer.getVirtualItems().map((virtualRow) => {
                const { member, indices } = matches[virtualRow.index];
                return (
                  <div
                    key={`${member.kind}:${member.name}:${member.descriptor}`}
                    id={`member-open-row-${virtualRow.index}`}
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
                      openMember(member);
                    }}
                  >
                    {member.kind === "field" ? (
                      <CircleDot
                        size={11}
                        className="shrink-0 text-[var(--glyph-field)]"
                      />
                    ) : (
                      <FunctionSquare
                        size={11}
                        className={`shrink-0 ${
                          member.hasCode
                            ? "text-[var(--glyph-method)]"
                            : "text-[var(--text-faint)]"
                        }`}
                      />
                    )}
                    <span
                      className={`min-w-0 shrink truncate text-[12.5px] ${
                        member.hasCode ? "text-[var(--text)]" : "text-[var(--text-faint)]"
                      }`}
                    >
                      <HighlightedText text={member.displayName} indices={indices} />
                    </span>
                    <span className="min-w-0 flex-1 truncate text-right font-mono text-[10.5px] text-[var(--text-faint)]">
                      {member.detail}
                    </span>
                  </div>
                );
              })}
            </div>
          ) : (
            <div className="palette-empty">{t("memberopen.empty")}</div>
          )}
        </div>

        <div className="palette-footer">
          <span className="palette-footer-item">
            <kbd className="kbd">↑↓</kbd> {t("palette.navigate")}
          </span>
          <span className="palette-footer-item">
            <kbd className="kbd">↵</kbd> {t("memberopen.jump")}
          </span>
          <span className="palette-footer-item">
            <kbd className="kbd">esc</kbd> {t("palette.dismiss")}
          </span>
        </div>
      </div>
    </div>
  );
}

function HighlightedText({ text, indices }: { text: string; indices: number[] }) {
  if (!indices.length) {
    return <>{text}</>;
  }
  const marked = new Set(indices);
  return (
    <>
      {[...text].map((char, index) =>
        marked.has(index) ? (
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
