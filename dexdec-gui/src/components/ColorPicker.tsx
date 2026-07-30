import { useEffect, useRef, useState } from "react";
import { createPortal } from "react-dom";

import { useTranslation } from "../i18n";
import { normalizeColor, type BackgroundPreset } from "../state/appearance";

/*
 * In-app colour picker popover: saturation/value field, hue rail, hex field and
 * the curated presets. Replaces the system colour panel, which ignored the
 * app's design language and offered far more than picking a background needs.
 *
 * Rendered through a portal on document.body: the settings dialog carries a
 * backdrop-filter, which makes it the containing block for position: fixed, so
 * viewport coordinates resolved against the dialog instead and pushed the
 * popover off its right edge. HSV is held locally: round-tripping through hex
 * would drop the hue of greys mid-drag.
 */

interface Hsv {
  h: number;
  s: number;
  v: number;
}

const WIDTH = 212;

export function ColorPicker({
  value,
  presets,
  anchor,
  defaultColor,
  defaultLabel,
  onChange,
  onClose,
}: {
  /** Current colour as #rrggbb. */
  value: string;
  presets: BackgroundPreset[];
  /** Trigger rect the popover hangs from. */
  anchor: DOMRect;
  /** The built-in surface the null preset falls back to. */
  defaultColor: string;
  /** Shown on the preset that clears the override. */
  defaultLabel: string;
  onChange: (color: string | null) => void;
  onClose: () => void;
}) {
  const { t } = useTranslation();
  const [hsv, setHsv] = useState<Hsv>(() => hexToHsv(value));
  const [draft, setDraft] = useState(value);
  const areaRef = useRef<HTMLDivElement>(null);
  const hueRef = useRef<HTMLDivElement>(null);

  /* Follow external changes (preset clicks) without fighting a live drag. */
  useEffect(() => {
    if (hsvToHex(hsv) !== value) {
      setHsv(hexToHsv(value));
      setDraft(value);
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [value]);

  useEffect(() => {
    const onKeyDown = (event: KeyboardEvent) => {
      if (event.key === "Escape") {
        event.preventDefault();
        event.stopPropagation();
        onClose();
      }
    };
    window.addEventListener("keydown", onKeyDown, true);
    return () => window.removeEventListener("keydown", onKeyDown, true);
  }, [onClose]);

  const apply = (next: Hsv) => {
    setHsv(next);
    const hex = hsvToHex(next);
    setDraft(hex);
    onChange(hex);
  };

  const trackPointer = (
    event: React.PointerEvent<HTMLDivElement>,
    element: HTMLDivElement | null,
    update: (x: number, y: number) => void,
  ) => {
    if (!element) {
      return;
    }
    element.setPointerCapture(event.pointerId);
    const read = (clientX: number, clientY: number) => {
      const rect = element.getBoundingClientRect();
      update(
        clamp((clientX - rect.left) / rect.width),
        clamp((clientY - rect.top) / rect.height),
      );
    };
    read(event.clientX, event.clientY);
    const onMove = (move: PointerEvent) => read(move.clientX, move.clientY);
    const onUp = () => {
      element.removeEventListener("pointermove", onMove);
      element.removeEventListener("pointerup", onUp);
    };
    element.addEventListener("pointermove", onMove);
    element.addEventListener("pointerup", onUp);
  };

  const onAreaKeyDown = (event: React.KeyboardEvent) => {
    const step = event.shiftKey ? 0.1 : 0.02;
    const moves: Record<string, Partial<Hsv>> = {
      ArrowLeft: { s: clamp(hsv.s - step) },
      ArrowRight: { s: clamp(hsv.s + step) },
      ArrowUp: { v: clamp(hsv.v + step) },
      ArrowDown: { v: clamp(hsv.v - step) },
    };
    const move = moves[event.key];
    if (move) {
      event.preventDefault();
      apply({ ...hsv, ...move });
    }
  };

  const onHueKeyDown = (event: React.KeyboardEvent) => {
    const step = event.shiftKey ? 30 : 4;
    const delta =
      event.key === "ArrowLeft" ? -step : event.key === "ArrowRight" ? step : 0;
    if (delta) {
      event.preventDefault();
      apply({ ...hsv, h: (hsv.h + delta + 360) % 360 });
    }
  };

  const left = Math.max(
    12,
    Math.min(anchor.right - WIDTH, window.innerWidth - WIDTH - 12),
  );
  const top = Math.min(anchor.bottom + 7, window.innerHeight - 250);

  return createPortal(
    <>
      <div
        className="color-popover-shield"
        onMouseDown={(event) => {
          event.preventDefault();
          event.stopPropagation();
          onClose();
        }}
      />
      <div
        className="color-popover"
        data-color-popover=""
        style={{ left, top, width: WIDTH }}
        onMouseDown={(event) => event.stopPropagation()}
      >
        <div
          ref={areaRef}
          className="color-popover-area"
          role="slider"
          tabIndex={0}
          aria-label={t("color.field")}
          aria-valuetext={hsvToHex(hsv)}
          style={{ background: `hsl(${hsv.h} 100% 50%)` }}
          onKeyDown={onAreaKeyDown}
          onPointerDown={(event) =>
            trackPointer(event, areaRef.current, (x, y) =>
              apply({ ...hsv, s: x, v: 1 - y }),
            )
          }
        >
          <span
            className="color-popover-knob"
            style={{
              left: `${hsv.s * 100}%`,
              top: `${(1 - hsv.v) * 100}%`,
              background: hsvToHex(hsv),
            }}
          />
        </div>

        <div
          ref={hueRef}
          className="color-popover-hue"
          role="slider"
          tabIndex={0}
          aria-label={t("color.hue")}
          aria-valuemin={0}
          aria-valuemax={360}
          aria-valuenow={Math.round(hsv.h)}
          onKeyDown={onHueKeyDown}
          onPointerDown={(event) =>
            trackPointer(event, hueRef.current, (x) =>
              apply({ ...hsv, h: x * 360 }),
            )
          }
        >
          <span
            className="color-popover-knob"
            style={{
              left: `${(hsv.h / 360) * 100}%`,
              top: "50%",
              background: `hsl(${hsv.h} 100% 50%)`,
            }}
          />
        </div>

        <input
          className={`color-popover-hex ${
            normalizeColor(draft) ? "" : "is-invalid"
          }`}
          value={draft}
          maxLength={7}
          spellCheck={false}
          aria-label={t("color.hex")}
          aria-invalid={!normalizeColor(draft)}
          onChange={(event) => {
            setDraft(event.target.value);
            const color = normalizeColor(event.target.value);
            if (color) {
              setHsv(hexToHsv(color));
              onChange(color);
            }
          }}
          onBlur={() => setDraft(value)}
        />

        <div className="color-popover-presets">
          {presets.map((preset) => (
            <button
              key={preset.label}
              type="button"
              className={`color-preset ${
                (preset.value ?? defaultColor) === value ? "is-active" : ""
              }`}
              style={{ background: preset.value ?? defaultColor }}
              title={
                preset.value
                  ? `${preset.label} · ${preset.value}`
                  : `${preset.label} · ${defaultLabel}`
              }
              aria-label={preset.label}
              onClick={() => onChange(preset.value)}
            />
          ))}
        </div>
      </div>
    </>,
    document.body,
  );
}

function clamp(value: number): number {
  return Math.min(1, Math.max(0, value));
}

function hexToHsv(hex: string): Hsv {
  const r = parseInt(hex.slice(1, 3), 16) / 255;
  const g = parseInt(hex.slice(3, 5), 16) / 255;
  const b = parseInt(hex.slice(5, 7), 16) / 255;
  const max = Math.max(r, g, b);
  const span = max - Math.min(r, g, b);
  let h = 0;
  if (span) {
    if (max === r) {
      h = ((g - b) / span) % 6;
    } else if (max === g) {
      h = (b - r) / span + 2;
    } else {
      h = (r - g) / span + 4;
    }
    h = (h * 60 + 360) % 360;
  }
  return { h, s: max ? span / max : 0, v: max };
}

function hsvToHex({ h, s, v }: Hsv): string {
  const channel = (n: number) => {
    const k = (n + h / 60) % 6;
    const value = v - v * s * Math.max(0, Math.min(k, 4 - k, 1));
    return Math.round(value * 255)
      .toString(16)
      .padStart(2, "0");
  };
  return `#${channel(5)}${channel(3)}${channel(1)}`;
}
