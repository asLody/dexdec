import {
  type CSSProperties,
  type ReactNode,
  useCallback,
  useEffect,
  useLayoutEffect,
  useRef,
  useState,
} from "react";
import { createPortal } from "react-dom";

export interface ContextMenuItem {
  id?: string;
  icon?: ReactNode;
  label: string;
  shortcut?: string;
  disabled?: boolean;
  danger?: boolean;
  onSelect: () => void;
}

export type ContextMenuEntry = ContextMenuItem | "separator";

interface ContextMenuProps {
  x: number;
  y: number;
  entries: ContextMenuEntry[];
  ariaLabel?: string;
  onClose: () => void;
}

const MENU_WIDTH = 244;
const ITEM_HEIGHT = 28;

/*
 * Native-feeling context menu: portaled (escapes overflow-clipped parents),
 * viewport-clamped, closes on outside click / Esc / scroll / blur, with
 * roving arrow-key selection.
 */
export function ContextMenu({
  x,
  y,
  entries,
  ariaLabel,
  onClose,
}: ContextMenuProps) {
  const menuRef = useRef<HTMLDivElement>(null);
  const closeTimerRef = useRef<number | null>(null);
  const [position, setPosition] = useState<{
    left: number;
    top: number;
    originX: "left" | "right";
    originY: "top" | "bottom";
    side: "left" | "right";
  }>({
    left: x,
    top: y,
    originX: "left",
    originY: "top",
    side: "right",
  });
  const [activeIndex, setActiveIndex] = useState<number | null>(null);
  const [closing, setClosing] = useState(false);
  const selectableIndices = entries.flatMap((entry, index) =>
    entry !== "separator" && !entry.disabled ? [index] : [],
  );
  const requestClose = useCallback(
    (action?: () => void) => {
      if (closing) {
        return;
      }
      setClosing(true);
      action?.();
      const reducedMotion = window.matchMedia(
        "(prefers-reduced-motion: reduce)",
      ).matches;
      closeTimerRef.current = window.setTimeout(onClose, reducedMotion ? 0 : 150);
    },
    [closing, onClose],
  );

  useEffect(
    () => () => {
      if (closeTimerRef.current != null) {
        window.clearTimeout(closeTimerRef.current);
      }
    },
    [],
  );

  useLayoutEffect(() => {
    const menu = menuRef.current;
    if (!menu) {
      return;
    }
    const rect = menu.getBoundingClientRect();
    const left = Math.max(4, Math.min(x, window.innerWidth - rect.width - 4));
    const top = Math.max(4, Math.min(y, window.innerHeight - rect.height - 4));
    setPosition({
      left,
      top,
      originX: x > left + rect.width / 2 ? "right" : "left",
      originY: y > top + rect.height / 2 ? "bottom" : "top",
      side: x > left + rect.width / 2 ? "left" : "right",
    });
    menu.focus({ preventScroll: true });
  }, [x, y]);

  useEffect(() => {
    const onMouseDown = (event: MouseEvent) => {
      if (!menuRef.current?.contains(event.target as Node)) {
        requestClose();
      }
    };
    const onKeyDown = (event: KeyboardEvent) => {
      if (event.key === "Escape") {
        event.preventDefault();
        requestClose();
        return;
      }
      if (event.key === "ArrowDown" || event.key === "ArrowUp") {
        event.preventDefault();
        if (!selectableIndices.length) {
          return;
        }
        const current = activeIndex == null
          ? -1
          : selectableIndices.indexOf(activeIndex);
        const delta = event.key === "ArrowDown" ? 1 : -1;
        const next =
          current === -1 && delta < 0
            ? selectableIndices.length - 1
            : (current + delta + selectableIndices.length) %
              selectableIndices.length;
        setActiveIndex(selectableIndices[next]);
      } else if (event.key === "Home" || event.key === "End") {
        event.preventDefault();
        if (selectableIndices.length) {
          setActiveIndex(
            event.key === "Home"
              ? selectableIndices[0]
              : selectableIndices[selectableIndices.length - 1],
          );
        }
      } else if (event.key === "Enter" && activeIndex != null) {
        const entry = entries[activeIndex];
        if (entry === "separator" || entry.disabled) {
          return;
        }
        event.preventDefault();
        requestClose(entry.onSelect);
      }
    };
    const onScroll = () => requestClose();
    window.addEventListener("mousedown", onMouseDown, true);
    window.addEventListener("keydown", onKeyDown, true);
    window.addEventListener("wheel", onScroll, true);
    window.addEventListener("blur", onScroll);
    return () => {
      window.removeEventListener("mousedown", onMouseDown, true);
      window.removeEventListener("keydown", onKeyDown, true);
      window.removeEventListener("wheel", onScroll, true);
      window.removeEventListener("blur", onScroll);
    };
  }, [activeIndex, entries, requestClose, selectableIndices]);

  return createPortal(
    <div
      ref={menuRef}
      role="menu"
      data-state={closing ? "closed" : "open"}
      data-side={position.side}
      aria-label={ariaLabel}
      tabIndex={-1}
      className="context-menu"
      style={
        {
          left: position.left,
          top: position.top,
          width: MENU_WIDTH,
          "--context-origin-x": position.originX,
          "--context-origin-y": position.originY,
        } as CSSProperties
      }
      onContextMenu={(event) => event.preventDefault()}
    >
      {entries.map((entry, index) =>
        entry === "separator" ? (
          <div
            key={`sep-${index}`}
            role="separator"
            className="context-menu-separator"
          />
        ) : (
          <button
            key={entry.id ?? `${entry.label}-${index}`}
            type="button"
            role="menuitem"
            disabled={entry.disabled}
            className={`context-menu-item ${
              activeIndex === index ? "context-menu-item-active" : ""
            } ${entry.danger ? "context-menu-item-danger" : ""}`}
            onMouseEnter={() => {
              if (!entry.disabled) {
                setActiveIndex(index);
              }
            }}
            onClick={() => {
              requestClose(entry.onSelect);
            }}
          >
            {entry.icon ? (
              <span className="context-menu-icon" aria-hidden="true">
                {entry.icon}
              </span>
            ) : null}
            <span className="truncate">{entry.label}</span>
            {entry.shortcut ? (
              <span className="context-menu-shortcut">
                {entry.shortcut}
              </span>
            ) : null}
          </button>
        ),
      )}
    </div>,
    document.body,
  );
}

export function estimateMenuHeight(entries: ContextMenuEntry[]): number {
  return (
    entries.reduce(
      (total, entry) => total + (entry === "separator" ? 9 : ITEM_HEIGHT),
      8,
    )
  );
}
