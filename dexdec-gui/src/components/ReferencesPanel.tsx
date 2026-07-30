import { useVirtualizer } from "@tanstack/react-virtual";
import {
  Braces,
  FunctionSquare,
  LoaderCircle,
  SearchCode,
  X,
} from "lucide-react";
import { useEffect, useRef, useState } from "react";

import type { ReferenceLocation } from "../domain/models";
import { useTranslation } from "../i18n";
import { useWorkspace } from "../state/workspace";
import { EmptyState } from "./EmptyState";

export function ReferencesPanel() {
  const references = useWorkspace((state) => state.references);
  const close = useWorkspace((state) => state.closeReferences);
  const selectClass = useWorkspace((state) => state.selectClass);
  const { t } = useTranslation();
  const scrollRef = useRef<HTMLDivElement>(null);
  const headerScrollRef = useRef<HTMLDivElement>(null);
  const columnsRef = useRef<HTMLDivElement>(null);
  const [activeIndex, setActiveIndex] = useState(0);
  const [columns, setColumns] = useState(() => ReferenceColumnLayout.restore());
  const columnsValueRef = useRef(columns);
  const resizeRef = useRef<ColumnResize | null>(null);
  const locations = references?.locations ?? [];
  const virtualizer = useVirtualizer({
    count: locations.length,
    getScrollElement: () => scrollRef.current,
    estimateSize: () => 25,
    overscan: 16,
  });

  useEffect(() => setActiveIndex(0), [references?.sequence]);
  useEffect(() => {
    columnsValueRef.current = columns;
  }, [columns]);
  useEffect(
    () => () => document.documentElement.classList.remove("reference-column-resizing"),
    [],
  );

  if (!references) {
    return null;
  }

  const open = async (location: ReferenceLocation) => {
    await selectClass(location.classDescriptor, { recordHistory: false });
    const state = useWorkspace.getState();
    if (state.activeDescriptor !== location.classDescriptor) {
      return;
    }
    state.navigateToMember({
      classDescriptor: location.classDescriptor,
      kind: "method",
      name: location.method,
      descriptor: location.descriptor,
    });
  };

  const move = (index: number) => {
    const next = Math.max(0, Math.min(locations.length - 1, index));
    setActiveIndex(next);
    virtualizer.scrollToIndex(next, { align: "auto" });
  };

  const onKeyDown = (event: React.KeyboardEvent) => {
    if (!locations.length) return;
    if (event.key === "ArrowDown" || event.key === "ArrowUp") {
      event.preventDefault();
      move(activeIndex + (event.key === "ArrowDown" ? 1 : -1));
    } else if (event.key === "Home" || event.key === "End") {
      event.preventDefault();
      move(event.key === "Home" ? 0 : locations.length - 1);
    } else if (event.key === "Enter") {
      event.preventDefault();
      void open(locations[activeIndex]);
    }
  };

  const startColumnResize = (
    column: ReferenceColumnIndex,
    event: React.PointerEvent<HTMLDivElement>,
  ) => {
    const startWidth = event.currentTarget.parentElement?.clientWidth ?? 0;
    if (!startWidth) return;
    event.preventDefault();
    event.currentTarget.setPointerCapture(event.pointerId);
    resizeRef.current = {
      column,
      pointerId: event.pointerId,
      startX: event.clientX,
      startWidth,
      columns: columnsValueRef.current,
    };
    document.documentElement.classList.add("reference-column-resizing");
  };

  const updateColumnResize = (event: React.PointerEvent<HTMLDivElement>) => {
    const resize = resizeRef.current;
    if (!resize || resize.pointerId !== event.pointerId) return;
    const next = resize.columns.resize(
      resize.column,
      resize.startWidth + event.clientX - resize.startX,
    );
    columnsValueRef.current = next;
    setColumns(next);
  };

  const finishColumnResize = (event: React.PointerEvent<HTMLDivElement>) => {
    if (resizeRef.current?.pointerId !== event.pointerId) return;
    resizeRef.current = null;
    document.documentElement.classList.remove("reference-column-resizing");
    columnsValueRef.current.persist();
  };

  const nudgeColumn = (
    column: ReferenceColumnIndex,
    pixels: number,
  ) => {
    const width = columnsRef.current?.children.item(column)?.clientWidth ?? 0;
    if (!width) return;
    const next = columnsValueRef.current.resize(column, width + pixels);
    columnsValueRef.current = next;
    setColumns(next);
    next.persist();
  };

  const resetColumns = () => {
    const next = ReferenceColumnLayout.defaults();
    columnsValueRef.current = next;
    setColumns(next);
    next.persist();
  };

  const gridStyle = { gridTemplateColumns: columns.gridTemplate };
  const tableStyle = { minWidth: `${columns.minimumWidth}px` };

  return (
    <div className="absolute inset-x-0 bottom-0 z-30 flex h-[280px] max-h-[48%] flex-col border-t border-[var(--border-strong)] bg-[var(--chrome)] shadow-[0_-10px_32px_rgba(0,0,0,0.4)]">
      <div className="flex h-8 shrink-0 items-center gap-2 border-b border-[var(--border)] px-3">
        <SearchCode size={12} className="shrink-0 text-[var(--accent)]" />
        <span className="text-[12px] font-medium text-[var(--text)]">
          {t("references.title", references.label)}
        </span>
        {references.state === "loading" ? (
          <LoaderCircle
            size={11}
            className="animate-spin text-[var(--text-faint)]"
          />
        ) : (
          <span className="text-[10.5px] tabular-nums text-[var(--text-faint)]">
            {references.locations.length}
          </span>
        )}
        {references.elapsedMs != null ? (
          <span className="text-[10px] tabular-nums text-[var(--text-faint)]">
            {references.elapsedMs} ms
          </span>
        ) : null}
        <button
          type="button"
          className="icon-button ml-auto !h-[22px] !w-[22px]"
          title={t("references.close")}
          aria-label={t("references.close")}
          onClick={close}
        >
          <X size={12} />
        </button>
      </div>

      {references.state === "ready" && locations.length ? (
        <div ref={headerScrollRef} className="reference-columns-viewport">
          <div
            ref={columnsRef}
            className="reference-columns"
            style={{ ...gridStyle, ...tableStyle }}
          >
            <ReferenceColumnHeader
              label={t("references.class")}
              column={0}
              onPointerDown={startColumnResize}
              onPointerMove={updateColumnResize}
              onPointerEnd={finishColumnResize}
              onNudge={nudgeColumn}
              onReset={resetColumns}
            />
            <ReferenceColumnHeader
              label={t("references.method")}
              column={1}
              onPointerDown={startColumnResize}
              onPointerMove={updateColumnResize}
              onPointerEnd={finishColumnResize}
              onNudge={nudgeColumn}
              onReset={resetColumns}
            />
          </div>
        </div>
      ) : null}

      <div
        ref={scrollRef}
        className="min-h-0 flex-1 overflow-auto py-1 outline-none"
        role="listbox"
        tabIndex={0}
        aria-activedescendant={locations[activeIndex] ? `reference-row-${activeIndex}` : undefined}
        onKeyDown={onKeyDown}
        onScroll={(event) => {
          if (headerScrollRef.current) {
            headerScrollRef.current.scrollLeft = event.currentTarget.scrollLeft;
          }
        }}
      >
        {references.state === "loading" ? (
          <PanelMessage>{t("references.loading")}</PanelMessage>
        ) : references.state === "error" ? (
          <PanelMessage danger>
            {references.error ?? t("references.failed")}
          </PanelMessage>
        ) : references.locations.length ? (
          <div
            className="relative w-full"
            style={{ height: virtualizer.getTotalSize(), ...tableStyle }}
          >
            {virtualizer.getVirtualItems().map((row) => {
              const location = locations[row.index];
              return (
                <button
                  key={`${location.classDescriptor}:${location.method}${location.descriptor}:${location.offset}`}
                  type="button"
                  id={`reference-row-${row.index}`}
                  role="option"
                  aria-selected={row.index === activeIndex}
                  tabIndex={-1}
                  className={`reference-row absolute left-0 top-0 ${row.index === activeIndex ? "is-focused" : ""}`}
                  style={{
                    height: row.size,
                    transform: `translateY(${row.start}px)`,
                    ...gridStyle,
                  }}
                  title={`${location.classDescriptor}->${location.method}${location.descriptor}`}
                  onFocus={() => setActiveIndex(row.index)}
                  onClick={() => {
                    setActiveIndex(row.index);
                    void open(location);
                  }}
                >
                  <span className="reference-cell">
                    <Braces
                      size={11}
                      className="shrink-0 text-[var(--glyph-class)]"
                    />
                    <span className="min-w-0 truncate text-left text-[11.5px] text-[var(--text)]">
                      {location.displayClassName ?? shortClassName(location.classDescriptor)}
                    </span>
                  </span>
                  <span className="reference-cell">
                    <FunctionSquare
                      size={11}
                      className="shrink-0 text-[var(--glyph-method)]"
                    />
                    <span className="min-w-0 truncate text-left font-mono text-[11px] text-[var(--text-muted)]">
                      {location.displayMethodName ?? location.method}
                      {location.descriptor}
                    </span>
                  </span>
                </button>
              );
            })}
          </div>
        ) : (
          <EmptyState compact icon={<SearchCode size={17} />} title={t("references.empty")} />
        )}
      </div>
    </div>
  );
}

type ReferenceColumnIndex = 0 | 1;

interface ColumnResize {
  column: ReferenceColumnIndex;
  pointerId: number;
  startX: number;
  startWidth: number;
  columns: ReferenceColumnLayout;
}

const REFERENCE_COLUMN_STORAGE = "dexdec.references.columns.v2";
const REFERENCE_COLUMN_MINIMUMS = [150, 240] as const;

class ReferenceColumnLayout {
  private constructor(private readonly widths: readonly [number, number]) {}

  static defaults(): ReferenceColumnLayout {
    return new ReferenceColumnLayout([360, 720]);
  }

  static restore(): ReferenceColumnLayout {
    try {
      const value = JSON.parse(localStorage.getItem(REFERENCE_COLUMN_STORAGE) ?? "null");
      if (
        Array.isArray(value) &&
        value.length === 2 &&
        value.every(
          (part) =>
            typeof part === "number" &&
            Number.isFinite(part) &&
            part > 0 &&
            part < 50_000,
        )
      ) {
        return new ReferenceColumnLayout([value[0], value[1]]);
      }
    } catch {
      // Ignore malformed preferences and return the balanced default.
    }
    return ReferenceColumnLayout.defaults();
  }

  get gridTemplate(): string {
    return `${this.widths[0]}px minmax(${this.widths[1]}px, 1fr)`;
  }

  get minimumWidth(): number {
    return this.widths[0] + this.widths[1];
  }

  resize(column: ReferenceColumnIndex, width: number): ReferenceColumnLayout {
    const next = [...this.widths] as [number, number];
    next[column] = Math.max(REFERENCE_COLUMN_MINIMUMS[column], Math.round(width));
    return new ReferenceColumnLayout(next);
  }

  persist(): void {
    localStorage.setItem(REFERENCE_COLUMN_STORAGE, JSON.stringify(this.widths));
  }
}

function ReferenceColumnHeader({
  label,
  column,
  onPointerDown,
  onPointerMove,
  onPointerEnd,
  onNudge,
  onReset,
}: {
  label: string;
  column: ReferenceColumnIndex;
  onPointerDown: (
    column: ReferenceColumnIndex,
    event: React.PointerEvent<HTMLDivElement>,
  ) => void;
  onPointerMove: (event: React.PointerEvent<HTMLDivElement>) => void;
  onPointerEnd: (event: React.PointerEvent<HTMLDivElement>) => void;
  onNudge: (column: ReferenceColumnIndex, pixels: number) => void;
  onReset: () => void;
}) {
  const { t } = useTranslation();
  return (
    <div className="reference-column">
      <span className="truncate">{label}</span>
      <div
        className="reference-column-resizer"
        role="separator"
        aria-label={t("references.resizeColumn", label)}
        aria-orientation="vertical"
        tabIndex={0}
        onPointerDown={(event) => onPointerDown(column, event)}
        onPointerMove={onPointerMove}
        onPointerUp={onPointerEnd}
        onPointerCancel={onPointerEnd}
        onDoubleClick={onReset}
        onKeyDown={(event) => {
          if (event.key !== "ArrowLeft" && event.key !== "ArrowRight") return;
          event.preventDefault();
          onNudge(column, event.key === "ArrowLeft" ? -8 : 8);
        }}
      />
    </div>
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
    <div
      className={`flex h-20 items-center justify-center px-6 text-center text-[11.5px] ${
        danger ? "text-[var(--danger)]" : "text-[var(--text-faint)]"
      }`}
    >
      {children}
    </div>
  );
}

function shortClassName(descriptor: string): string {
  return descriptor.replace(/^L|;$/g, "").replaceAll("/", ".");
}
