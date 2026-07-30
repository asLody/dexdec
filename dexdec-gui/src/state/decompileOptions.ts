/*
 * Output settings sent with every decompile request. They live outside the
 * workspace store so the IPC client can depend on the shape without importing
 * the store itself.
 */
export interface DecompileOptions {
  /** Spaces per indentation level, 2–8. */
  indentWidth: number;
  /** Emit nested classes inside their outer class instead of on their own. */
  includeNested: boolean;
}

export const DECOMPILE_DEFAULTS: DecompileOptions = {
  indentWidth: 4,
  includeNested: true,
};

export const INDENT_WIDTHS = [2, 4, 8] as const;

const STORAGE_KEY = "dexdec.decompileOptions";

export function loadDecompileOptions(): DecompileOptions {
  try {
    const saved = JSON.parse(
      localStorage.getItem(STORAGE_KEY) ?? "null",
    ) as Partial<DecompileOptions> | null;
    return {
      indentWidth: INDENT_WIDTHS.includes(saved?.indentWidth as never)
        ? saved!.indentWidth!
        : DECOMPILE_DEFAULTS.indentWidth,
      includeNested: saved?.includeNested !== false,
    };
  } catch {
    return DECOMPILE_DEFAULTS;
  }
}

export function saveDecompileOptions(options: DecompileOptions): void {
  try {
    localStorage.setItem(STORAGE_KEY, JSON.stringify(options));
  } catch {
    /* storage unavailable */
  }
}
