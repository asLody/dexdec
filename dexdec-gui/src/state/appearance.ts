import { create } from "zustand";

export type AppearanceMode = "system" | "light" | "dark";
export type CodeThemeId =
  | "aurora"
  | "github"
  | "dracula"
  | "nord"
  | "solarized"
  | "tokyo-night"
  | "catppuccin"
  | "one"
  | "everforest";
export type EditorFontId =
  | "sf-mono"
  | "jetbrains-mono"
  | "menlo"
  | "cascadia-code"
  | "fira-code";

export interface CodeThemeOption {
  id: CodeThemeId;
  label: string;
  palettes: Record<"light" | "dark", CodeThemePalette>;
}

export interface CodeThemePalette {
  foreground: string;
  keyword: string;
  string: string;
  character: string;
  constant: string;
  type: string;
  function: string;
  property: string;
  variable: string;
  annotation: string;
  label: string;
  comment: string;
  operator: string;
  punctuation: string;
}

export interface EditorFontOption {
  id: EditorFontId;
  label: string;
  stack: string;
}

export const CODE_THEMES: CodeThemeOption[] = [
  {
    id: "aurora",
    label: "Aurora",
    palettes: {
      light: {
        foreground: "#242a33",
        keyword: "#7847a8",
        string: "#49782d",
        character: "#9b6418",
        constant: "#b04f28",
        type: "#087f79",
        function: "#275fa5",
        property: "#4f5865",
        variable: "#242a33",
        annotation: "#9b6418",
        label: "#87508c",
        comment: "#626b76",
        operator: "#596270",
        punctuation: "#747d88",
      },
      dark: {
        foreground: "#d9dce3",
        keyword: "#c2a6e8",
        string: "#a9cb8c",
        character: "#e4b66f",
        constant: "#e39a6b",
        type: "#72c6b5",
        function: "#8db7ef",
        property: "#c1c7d0",
        variable: "#d9dce3",
        annotation: "#e0aa68",
        label: "#c99fcf",
        comment: "#687282",
        operator: "#a3aab6",
        punctuation: "#838c99",
      },
    },
  },
  {
    id: "github",
    label: "GitHub",
    palettes: {
      light: {
        foreground: "#24292f",
        keyword: "#cf222e",
        string: "#0a3069",
        character: "#953800",
        constant: "#0550ae",
        type: "#116329",
        function: "#8250df",
        property: "#24292f",
        variable: "#953800",
        annotation: "#953800",
        label: "#8250df",
        comment: "#555f6a",
        operator: "#cf222e",
        punctuation: "#57606a",
      },
      dark: {
        foreground: "#c9d1d9",
        keyword: "#ff7b72",
        string: "#a5d6ff",
        character: "#ffa657",
        constant: "#79c0ff",
        type: "#7ee787",
        function: "#d2a8ff",
        property: "#c9d1d9",
        variable: "#ffa657",
        annotation: "#ffa657",
        label: "#d2a8ff",
        comment: "#8b949e",
        operator: "#ff7b72",
        punctuation: "#8b949e",
      },
    },
  },
  {
    id: "dracula",
    label: "Dracula",
    palettes: {
      light: {
        foreground: "#282a36",
        keyword: "#8f0075",
        string: "#14710a",
        character: "#985400",
        constant: "#6f42c1",
        type: "#006d77",
        function: "#005cc5",
        property: "#383a46",
        variable: "#282a36",
        annotation: "#b35c00",
        label: "#8f0075",
        comment: "#727785",
        operator: "#8f0075",
        punctuation: "#626673",
      },
      dark: {
        foreground: "#f8f8f2",
        keyword: "#ff79c6",
        string: "#f1fa8c",
        character: "#f1fa8c",
        constant: "#bd93f9",
        type: "#8be9fd",
        function: "#50fa7b",
        property: "#f8f8f2",
        variable: "#f8f8f2",
        annotation: "#ffb86c",
        label: "#ff79c6",
        comment: "#6272a4",
        operator: "#ff79c6",
        punctuation: "#b7b7c2",
      },
    },
  },
  {
    id: "nord",
    label: "Nord",
    palettes: {
      light: {
        foreground: "#2e3440",
        keyword: "#5e81ac",
        string: "#4f6f3c",
        character: "#9a6a28",
        constant: "#8a517d",
        type: "#3f7d78",
        function: "#397a91",
        property: "#3b4252",
        variable: "#2e3440",
        annotation: "#a44d36",
        label: "#8a517d",
        comment: "#7b8494",
        operator: "#5e81ac",
        punctuation: "#6c7481",
      },
      dark: {
        foreground: "#d8dee9",
        keyword: "#81a1c1",
        string: "#a3be8c",
        character: "#ebcb8b",
        constant: "#b48ead",
        type: "#8fbcbb",
        function: "#88c0d0",
        property: "#d8dee9",
        variable: "#d8dee9",
        annotation: "#d08770",
        label: "#b48ead",
        comment: "#616e88",
        operator: "#81a1c1",
        punctuation: "#8b95a5",
      },
    },
  },
  {
    id: "solarized",
    label: "Solarized",
    palettes: {
      light: {
        foreground: "#586e75",
        keyword: "#859900",
        string: "#2aa198",
        character: "#b58900",
        constant: "#d33682",
        type: "#268bd2",
        function: "#b58900",
        property: "#657b83",
        variable: "#586e75",
        annotation: "#cb4b16",
        label: "#6c71c4",
        comment: "#93a1a1",
        operator: "#859900",
        punctuation: "#839496",
      },
      dark: {
        foreground: "#93a1a1",
        keyword: "#859900",
        string: "#2aa198",
        character: "#b58900",
        constant: "#d33682",
        type: "#268bd2",
        function: "#b58900",
        property: "#93a1a1",
        variable: "#839496",
        annotation: "#cb4b16",
        label: "#6c71c4",
        comment: "#586e75",
        operator: "#859900",
        punctuation: "#657b83",
      },
    },
  },
  {
    id: "tokyo-night",
    label: "Tokyo Night",
    palettes: {
      light: {
        foreground: "#343b58",
        keyword: "#9854f1",
        string: "#587539",
        character: "#8c6c3e",
        constant: "#b15c00",
        type: "#007197",
        function: "#2e7de9",
        property: "#188092",
        variable: "#343b58",
        annotation: "#8c6c3e",
        label: "#f52a65",
        comment: "#848cb5",
        operator: "#007197",
        punctuation: "#6172b0",
      },
      dark: {
        foreground: "#c0caf5",
        keyword: "#bb9af7",
        string: "#9ece6a",
        character: "#e0af68",
        constant: "#ff9e64",
        type: "#2ac3de",
        function: "#7aa2f7",
        property: "#73daca",
        variable: "#c0caf5",
        annotation: "#e0af68",
        label: "#f7768e",
        comment: "#565f89",
        operator: "#89ddff",
        punctuation: "#9aa5ce",
      },
    },
  },
  {
    id: "catppuccin",
    label: "Catppuccin",
    palettes: {
      light: {
        foreground: "#4c4f69",
        keyword: "#8839ef",
        string: "#40a02b",
        character: "#df8e1d",
        constant: "#fe640b",
        type: "#04a5e5",
        function: "#1e66f5",
        property: "#179299",
        variable: "#4c4f69",
        annotation: "#df8e1d",
        label: "#d20f39",
        comment: "#8c8fa1",
        operator: "#04a5e5",
        punctuation: "#6c6f85",
      },
      dark: {
        foreground: "#cdd6f4",
        keyword: "#cba6f7",
        string: "#a6e3a1",
        character: "#f9e2af",
        constant: "#fab387",
        type: "#89dceb",
        function: "#89b4fa",
        property: "#94e2d5",
        variable: "#cdd6f4",
        annotation: "#f9e2af",
        label: "#f38ba8",
        comment: "#6c7086",
        operator: "#89dceb",
        punctuation: "#9399b2",
      },
    },
  },
  {
    id: "one",
    label: "One",
    palettes: {
      light: {
        foreground: "#383a42",
        keyword: "#a626a4",
        string: "#50a14f",
        character: "#c18401",
        constant: "#986801",
        type: "#0184bc",
        function: "#4078f2",
        property: "#e45649",
        variable: "#383a42",
        annotation: "#c18401",
        label: "#a626a4",
        comment: "#a0a1a7",
        operator: "#0184bc",
        punctuation: "#696c77",
      },
      dark: {
        foreground: "#abb2bf",
        keyword: "#c678dd",
        string: "#98c379",
        character: "#e5c07b",
        constant: "#d19a66",
        type: "#56b6c2",
        function: "#61afef",
        property: "#e06c75",
        variable: "#abb2bf",
        annotation: "#e5c07b",
        label: "#c678dd",
        comment: "#5c6370",
        operator: "#56b6c2",
        punctuation: "#7f848e",
      },
    },
  },
  {
    id: "everforest",
    label: "Everforest",
    palettes: {
      light: {
        foreground: "#5c6a72",
        keyword: "#b16286",
        string: "#6f8f00",
        character: "#b77900",
        constant: "#d94f4f",
        type: "#248f68",
        function: "#327da8",
        property: "#5c6a72",
        variable: "#5c6a72",
        annotation: "#b77900",
        label: "#b16286",
        comment: "#829181",
        operator: "#d94f4f",
        punctuation: "#78867e",
      },
      dark: {
        foreground: "#d3c6aa",
        keyword: "#d699b6",
        string: "#a7c080",
        character: "#dbbc7f",
        constant: "#e69875",
        type: "#83c092",
        function: "#7fbbb3",
        property: "#d3c6aa",
        variable: "#d3c6aa",
        annotation: "#dbbc7f",
        label: "#d699b6",
        comment: "#859289",
        operator: "#e67e80",
        punctuation: "#9da9a0",
      },
    },
  },
];

export const EDITOR_FONTS: EditorFontOption[] = [
  {
    id: "sf-mono",
    label: "SF Mono",
    stack:
      '"SF Mono", SFMono-Regular, ui-monospace, Menlo, Monaco, Consolas, monospace',
  },
  {
    id: "jetbrains-mono",
    label: "JetBrains Mono",
    stack:
      '"JetBrains Mono", "SF Mono", SFMono-Regular, Menlo, Consolas, monospace',
  },
  {
    id: "menlo",
    label: "Menlo",
    stack: 'Menlo, Monaco, "SF Mono", Consolas, monospace',
  },
  {
    id: "cascadia-code",
    label: "Cascadia Code",
    stack:
      '"Cascadia Code", "Cascadia Mono", "SF Mono", Menlo, Consolas, monospace',
  },
  {
    id: "fira-code",
    label: "Fira Code",
    stack:
      '"Fira Code", "SF Mono", SFMono-Regular, Menlo, Consolas, monospace',
  },
];

interface AppearancePreferences {
  mode: AppearanceMode;
  codeTheme: CodeThemeId;
  editorFont: EditorFontId;
  editorFontSize: number;
  codeFolding: boolean;
  wordWrap: boolean;
  /** Editor background overrides per scheme; null keeps the built-in surface. */
  backgroundLight: string | null;
  backgroundDark: string | null;
}

interface AppearanceState extends AppearancePreferences {
  systemDark: boolean;
  settingsOpen: boolean;
  setMode: (mode: AppearanceMode) => void;
  setCodeTheme: (theme: CodeThemeId) => void;
  setEditorFont: (font: EditorFontId) => void;
  setEditorFontSize: (size: number) => void;
  setCodeFolding: (enabled: boolean) => void;
  setWordWrap: (enabled: boolean) => void;
  setBackground: (scheme: "light" | "dark", color: string | null) => void;
  setSettingsOpen: (open: boolean) => void;
  reset: () => void;
}

const STORAGE_KEY = "dexdec.appearance";
const DEFAULTS: AppearancePreferences = {
  mode: "system",
  codeTheme: "aurora",
  editorFont: "sf-mono",
  editorFontSize: 13,
  codeFolding: true,
  wordWrap: false,
  backgroundLight: null,
  backgroundDark: null,
};

/* The built-in editor surfaces, mirroring the :root defaults in styles.css. */
export const EDITOR_SURFACES: Record<"light" | "dark", string> = {
  light: "#e1e4e7",
  dark: "#111113",
};

/*
 * Curated editor backgrounds per scheme. The first entry is the built-in
 * surface and stores `null`, so picking it clears the override rather than
 * pinning the current default. The rest are the grounds people already read
 * code on, named after where they come from.
 */
export interface BackgroundPreset {
  /** null selects the built-in surface for the scheme. */
  value: string | null;
  label: string;
}

export const EDITOR_BACKGROUNDS: Record<"light" | "dark", BackgroundPreset[]> = {
  light: [
    { value: null, label: "Soft Gray" },
    { value: "#fafafa", label: "Ash" },
    { value: "#f4f4f5", label: "Fog" },
    { value: "#f6f8fa", label: "GitHub" },
    { value: "#eff1f5", label: "Latte" },
    { value: "#eceff4", label: "Snow Storm" },
    { value: "#fdf6e3", label: "Solarized" },
    { value: "#f2e5bc", label: "Gruvbox" },
  ],
  dark: [
    { value: null, label: "Graphite" },
    { value: "#0a0a0b", label: "Void" },
    { value: "#16181d", label: "Slate" },
    { value: "#1a1b26", label: "Tokyo Night" },
    { value: "#1e1e2e", label: "Catppuccin" },
    { value: "#282a36", label: "Dracula" },
    { value: "#2e3440", label: "Nord" },
    { value: "#002b36", label: "Solarized" },
  ],
};

const HEX_COLOR = /^#[0-9a-f]{6}$/i;

/** Accepts #abc / #aabbcc, with or without the hash. */
export function normalizeColor(input: string): string | null {
  const value = input.trim().replace(/^#*/, "");
  const hex =
    value.length === 3
      ? value.replace(/./g, (digit) => digit + digit)
      : value;
  return HEX_COLOR.test(`#${hex}`) ? `#${hex.toLowerCase()}` : null;
}

function storedColor(value: unknown): string | null {
  return typeof value === "string" && HEX_COLOR.test(value) ? value : null;
}

const PALETTE_PROPERTIES: Record<keyof CodeThemePalette, string> = {
  foreground: "--editor-foreground",
  keyword: "--syntax-keyword",
  string: "--syntax-string",
  character: "--syntax-character",
  constant: "--syntax-constant",
  type: "--syntax-type",
  function: "--syntax-function",
  property: "--syntax-property",
  variable: "--syntax-variable",
  annotation: "--syntax-annotation",
  label: "--syntax-label",
  comment: "--syntax-comment",
  operator: "--syntax-operator",
  punctuation: "--syntax-punctuation",
};

function systemPrefersDark(): boolean {
  return window.matchMedia?.("(prefers-color-scheme: dark)").matches ?? true;
}

function loadPreferences(): AppearancePreferences {
  try {
    const saved = JSON.parse(
      localStorage.getItem(STORAGE_KEY) ?? "null",
    ) as Partial<AppearancePreferences> | null;
    return {
      mode:
        saved?.mode === "light" ||
        saved?.mode === "dark" ||
        saved?.mode === "system"
          ? saved.mode
          : DEFAULTS.mode,
      codeTheme: CODE_THEMES.some((theme) => theme.id === saved?.codeTheme)
        ? saved!.codeTheme!
        : DEFAULTS.codeTheme,
      editorFont: EDITOR_FONTS.some((font) => font.id === saved?.editorFont)
        ? saved!.editorFont!
        : DEFAULTS.editorFont,
      editorFontSize:
        typeof saved?.editorFontSize === "number"
          ? clampFontSize(saved.editorFontSize)
          : DEFAULTS.editorFontSize,
      codeFolding: saved?.codeFolding !== false,
      wordWrap: saved?.wordWrap === true,
      backgroundLight: storedColor(saved?.backgroundLight),
      backgroundDark: storedColor(saved?.backgroundDark),
    };
  } catch {
    return DEFAULTS;
  }
}

function clampFontSize(size: number): number {
  return Math.round(Math.min(22, Math.max(10, size)) * 2) / 2;
}

const initial = loadPreferences();

export const useAppearance = create<AppearanceState>((set) => ({
  ...initial,
  systemDark: systemPrefersDark(),
  settingsOpen: false,
  setMode: (mode) => set({ mode }),
  setCodeTheme: (codeTheme) => set({ codeTheme }),
  setEditorFont: (editorFont) => set({ editorFont }),
  setEditorFontSize: (editorFontSize) =>
    set({ editorFontSize: clampFontSize(editorFontSize) }),
  setCodeFolding: (codeFolding) => set({ codeFolding }),
  setWordWrap: (wordWrap) => set({ wordWrap }),
  setBackground: (scheme, color) =>
    set(
      scheme === "light"
        ? { backgroundLight: storedColor(color) }
        : { backgroundDark: storedColor(color) },
    ),
  setSettingsOpen: (settingsOpen) => set({ settingsOpen }),
  reset: () => set(DEFAULTS),
}));

function syncAppearance(state: AppearanceState): void {
  const effectiveMode =
    state.mode === "system"
      ? state.systemDark
        ? "dark"
        : "light"
      : state.mode;
  const font =
    EDITOR_FONTS.find((candidate) => candidate.id === state.editorFont) ??
    EDITOR_FONTS[0];
  const theme =
    CODE_THEMES.find((candidate) => candidate.id === state.codeTheme) ??
    CODE_THEMES[0];
  const root = document.documentElement;
  root.dataset.colorScheme = effectiveMode;
  root.dataset.codeTheme = state.codeTheme;
  root.style.removeProperty("--editor-background");
  for (const scheme of ["light", "dark"] as const) {
    const override =
      scheme === "light" ? state.backgroundLight : state.backgroundDark;
    const property = `--editor-surface-${scheme}`;
    if (override) {
      root.style.setProperty(property, override);
    } else {
      root.style.removeProperty(property);
    }
  }
  const palette = theme.palettes[effectiveMode];
  for (const property of Object.keys(PALETTE_PROPERTIES) as Array<
    keyof CodeThemePalette
  >) {
    root.style.setProperty(PALETTE_PROPERTIES[property], palette[property]);
  }
  root.style.setProperty("--editor-font-family", font.stack);
  root.style.setProperty("--editor-font-size", `${state.editorFontSize}px`);
  try {
    localStorage.setItem(
      STORAGE_KEY,
      JSON.stringify({
        mode: state.mode,
        codeTheme: state.codeTheme,
        editorFont: state.editorFont,
        editorFontSize: state.editorFontSize,
        codeFolding: state.codeFolding,
        wordWrap: state.wordWrap,
        backgroundLight: state.backgroundLight,
        backgroundDark: state.backgroundDark,
      } satisfies AppearancePreferences),
    );
  } catch {
    /* appearance remains active when storage is unavailable */
  }
}

syncAppearance(useAppearance.getState());
useAppearance.subscribe(syncAppearance);

const colorScheme = window.matchMedia?.("(prefers-color-scheme: dark)");
colorScheme?.addEventListener("change", (event) => {
  useAppearance.setState({ systemDark: event.matches });
});
