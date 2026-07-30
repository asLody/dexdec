/* Platform detection and declarative shortcut formatting. */
export const IS_MACOS = /mac|iphone|ipad/i.test(
  navigator.userAgent + " " + (navigator.platform ?? ""),
);

const MAC_GLYPHS: Record<string, string> = {
  ctrl: "⌃",
  alt: "⌥",
  shift: "⇧",
  mod: "⌘",
};

const WIN_LABELS: Record<string, string> = {
  ctrl: "Ctrl",
  alt: "Alt",
  shift: "Shift",
  mod: "Ctrl",
};

/** Canonical macOS modifier order: ⌃ ⌥ ⇧ ⌘. */
const MAC_ORDER = ["ctrl", "alt", "shift", "mod"];

/**
 * Formats a declarative combo like "mod+shift+o" for the current platform:
 * "⌘⇧O" on macOS, "Ctrl+Shift+O" elsewhere.
 */
export function sc(combo: string): string {
  const parts = combo.toLowerCase().split("+");
  const key = parts[parts.length - 1];
  const modifiers = parts.slice(0, -1);
  if (IS_MACOS) {
    const ordered = MAC_ORDER.filter((modifier) => modifiers.includes(modifier));
    const glyphs = ordered.map((modifier) => MAC_GLYPHS[modifier]).join("");
    return glyphs + (key.length === 1 ? key.toUpperCase() : key);
  }
  const labels = modifiers.map((modifier) => WIN_LABELS[modifier] ?? modifier);
  return [...labels, key.length === 1 ? key.toUpperCase() : key[0].toUpperCase() + key.slice(1)].join("+");
}

/** Modifier-click affordance, e.g. for peek: "⌘Click" / "Ctrl+Click". */
export const MOD_CLICK = IS_MACOS ? "⌘Click" : "Ctrl+Click";

/** The platform's primary command modifier: Command on Apple, Control elsewhere. */
export function hasPrimaryModifier(event: Pick<MouseEvent | KeyboardEvent, "metaKey" | "ctrlKey">) {
  return IS_MACOS ? event.metaKey : event.ctrlKey;
}
