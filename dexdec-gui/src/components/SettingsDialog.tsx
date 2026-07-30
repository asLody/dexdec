import { getVersion } from "@tauri-apps/api/app";
import {
  Cable,
  Check,
  Copy,
  Info,
  Keyboard,
  Minus,
  Monitor,
  Moon,
  Palette,
  Plus,
  RefreshCw,
  RotateCcw,
  Search,
  SlidersHorizontal,
  Sun,
  Type,
  X,
} from "lucide-react";
import { useEffect, useRef, useState } from "react";

import appIcon from "../assets/dexdec-app-icon.png";
import { SHORTCUT_GROUPS, type ShortcutEntry } from "../domain/shortcuts";
import {
  LOCALES,
  useTranslation,
  type LocalePreference,
  type MessageKey,
} from "../i18n";
import { MOD_CLICK, sc } from "../platform";
import { copyText } from "../services/clipboard";
import {
  mcpConfigurationClient,
  type AgentMcpIntegration,
  type McpConfigurationDocument,
} from "../services/mcpClient";
import { INDENT_WIDTHS } from "../state/decompileOptions";
import { useWorkspace } from "../state/workspace";
import { ColorPicker } from "./ColorPicker";
import {
  CODE_THEMES,
  EDITOR_BACKGROUNDS,
  EDITOR_FONTS,
  EDITOR_SURFACES,
  type AppearanceMode,
  type CodeThemePalette,
  useAppearance,
} from "../state/appearance";

/*
 * The snippet each theme swatch renders, as [text, palette slot] runs. Short
 * enough to stay legible at 10px, wide enough to show the tokens that actually
 * distinguish one theme from another: comment, keyword, type, literal, string.
 */
const THEME_PREVIEW: [string, keyof CodeThemePalette][][] = [
  [["// dexdec", "comment"]],
  [["class ", "keyword"], ["Main", "type"], [" {", "punctuation"]],
  [
    ["  int ", "keyword"],
    ["id", "variable"],
    [" = ", "operator"],
    ["42", "constant"],
    [";", "punctuation"],
  ],
  [
    ["  String ", "type"],
    ["s", "variable"],
    [" = ", "operator"],
    ['"dex"', "string"],
    [";", "punctuation"],
  ],
  [["}", "punctuation"]],
];

const APPEARANCE_MODES: {
  id: AppearanceMode;
  icon: typeof Monitor;
  label: "settings.mode.system" | "settings.mode.light" | "settings.mode.dark";
}[] = [
  { id: "system", icon: Monitor, label: "settings.mode.system" },
  { id: "light", icon: Sun, label: "settings.mode.light" },
  { id: "dark", icon: Moon, label: "settings.mode.dark" },
];

type SettingsTab =
  | "appearance"
  | "editor"
  | "decompiler"
  | "mcp"
  | "keymap"
  | "about";

const SETTINGS_TABS: {
  id: SettingsTab;
  icon: typeof Monitor;
  label: MessageKey;
}[] = [
  { id: "appearance", icon: Palette, label: "settings.tab.appearance" },
  { id: "editor", icon: Type, label: "settings.tab.editor" },
  { id: "decompiler", icon: SlidersHorizontal, label: "settings.tab.decompiler" },
  { id: "mcp", icon: Cable, label: "settings.tab.mcp" },
  { id: "keymap", icon: Keyboard, label: "settings.tab.keymap" },
  { id: "about", icon: Info, label: "settings.tab.about" },
];

export function SettingsDialog() {
  const open = useAppearance((state) => state.settingsOpen);
  const mode = useAppearance((state) => state.mode);
  const systemDark = useAppearance((state) => state.systemDark);
  const codeTheme = useAppearance((state) => state.codeTheme);
  const editorFont = useAppearance((state) => state.editorFont);
  const editorFontSize = useAppearance((state) => state.editorFontSize);
  const codeFolding = useAppearance((state) => state.codeFolding);
  const wordWrap = useAppearance((state) => state.wordWrap);
  const setMode = useAppearance((state) => state.setMode);
  const setCodeTheme = useAppearance((state) => state.setCodeTheme);
  const setEditorFont = useAppearance((state) => state.setEditorFont);
  const setEditorFontSize = useAppearance((state) => state.setEditorFontSize);
  const setCodeFolding = useAppearance((state) => state.setCodeFolding);
  const setWordWrap = useAppearance((state) => state.setWordWrap);
  const setOpen = useAppearance((state) => state.setSettingsOpen);
  const reset = useAppearance((state) => state.reset);
  const { t, localePreference, setLocalePreference } = useTranslation();
  const dialogRef = useRef<HTMLDivElement>(null);
  const [tab, setTab] = useState<SettingsTab>("appearance");
  const effectiveScheme =
    mode === "system" ? (systemDark ? "dark" : "light") : mode;

  useEffect(() => {
    if (!open) {
      return;
    }
    const previous = document.activeElement as HTMLElement | null;
    const onKeyDown = (event: KeyboardEvent) => {
      if (event.key === "Escape") {
        // An open colour popover closes itself first.
        if (document.querySelector("[data-color-popover]")) {
          return;
        }
        event.preventDefault();
        setOpen(false);
        return;
      }
      if (event.key !== "Tab" || !dialogRef.current) {
        return;
      }
      // While the colour popover is open it owns the focus cycle; it lives in a
      // portal outside the dialog, so trap within whichever is on top.
      const container =
        document.querySelector<HTMLElement>("[data-color-popover]") ??
        dialogRef.current;
      const focusable = [
        ...container.querySelectorAll<HTMLElement>(
          'button:not(:disabled), select:not(:disabled), input:not(:disabled)',
        ),
      ];
      if (!focusable.length) {
        return;
      }
      const first = focusable[0];
      const last = focusable.at(-1)!;
      if (event.shiftKey && document.activeElement === first) {
        event.preventDefault();
        last.focus();
      } else if (!event.shiftKey && document.activeElement === last) {
        event.preventDefault();
        first.focus();
      }
    };
    window.addEventListener("keydown", onKeyDown, true);
    requestAnimationFrame(() =>
      dialogRef.current?.querySelector<HTMLElement>("button")?.focus(),
    );
    return () => {
      window.removeEventListener("keydown", onKeyDown, true);
      previous?.focus();
    };
  }, [open, setOpen]);

  if (!open) {
    return null;
  }

  /* Roving arrow-key navigation across the vertical tab rail. */
  const onTabKeyDown = (event: React.KeyboardEvent<HTMLDivElement>) => {
    const step =
      event.key === "ArrowDown" ? 1 : event.key === "ArrowUp" ? -1 : 0;
    if (!step) {
      return;
    }
    event.preventDefault();
    const index = SETTINGS_TABS.findIndex((option) => option.id === tab);
    const next =
      SETTINGS_TABS[(index + step + SETTINGS_TABS.length) % SETTINGS_TABS.length];
    setTab(next.id);
    event.currentTarget
      .querySelector<HTMLElement>(`#settings-tab-${next.id}`)
      ?.focus();
  };

  return (
    <div
      className="settings-backdrop"
      onMouseDown={(event) => {
        if (event.target === event.currentTarget) {
          setOpen(false);
        }
      }}
    >
      <div
        ref={dialogRef}
        className="settings-dialog"
        role="dialog"
        aria-modal="true"
        aria-labelledby="settings-title"
      >
        <nav className="settings-nav">
          <h2 id="settings-title" className="settings-nav-title">
            {t("settings.title")}
          </h2>
          <div
            className="settings-nav-list"
            role="tablist"
            aria-orientation="vertical"
            aria-label={t("settings.title")}
            onKeyDown={onTabKeyDown}
          >
            {SETTINGS_TABS.map((option) => {
              const Icon = option.icon;
              const active = tab === option.id;
              return (
                <button
                  key={option.id}
                  id={`settings-tab-${option.id}`}
                  type="button"
                  role="tab"
                  className={`settings-nav-item ${active ? "is-active" : ""}`}
                  aria-selected={active}
                  aria-controls={`settings-panel-${option.id}`}
                  tabIndex={active ? 0 : -1}
                  onClick={() => setTab(option.id)}
                >
                  <Icon size={14} />
                  <span>{t(option.label)}</span>
                </button>
              );
            })}
          </div>
        </nav>

        <div className="settings-main">
          <header className="settings-header">
            <h3>{t(SETTINGS_TABS.find((item) => item.id === tab)!.label)}</h3>
            <button
              type="button"
              className="icon-button"
              title={t("settings.close")}
              aria-label={t("settings.close")}
              onClick={() => setOpen(false)}
            >
              <X size={15} />
            </button>
          </header>

          <div
            className={`settings-content ${tab === "about" ? "is-about" : ""}`}
            role="tabpanel"
            id={`settings-panel-${tab}`}
            aria-labelledby={`settings-tab-${tab}`}
          >
            {tab === "appearance" ? (
              <>
                <SettingGroup title={t("settings.group.general")}>
                  <SettingRow label={t("settings.language")} htmlFor="settings-language">
                    <select
                      id="settings-language"
                      className="settings-select"
                      value={localePreference}
                      onChange={(event) =>
                        setLocalePreference(event.target.value as LocalePreference)
                      }
                    >
                      <option value="system">{t("settings.language.system")}</option>
                      {LOCALES.map((option) => (
                        <option key={option.id} value={option.id}>
                          {option.label}
                        </option>
                      ))}
                    </select>
                  </SettingRow>

                  <SettingRow label={t("settings.interface")}>
                    <div className="settings-segmented">
                      {APPEARANCE_MODES.map((option) => {
                        const Icon = option.icon;
                        return (
                          <button
                            key={option.id}
                            type="button"
                            className={mode === option.id ? "is-active" : ""}
                            aria-pressed={mode === option.id}
                            onClick={() => setMode(option.id)}
                          >
                            <Icon size={13} />
                            <span>{t(option.label)}</span>
                          </button>
                        );
                      })}
                    </div>
                  </SettingRow>
                </SettingGroup>

                <SettingGroup title={t("settings.background")}>
                  <SettingRow
                    label={t("settings.background.color")}
                    hint={t(
                      effectiveScheme === "dark"
                        ? "settings.background.hintDark"
                        : "settings.background.hintLight",
                    )}
                  >
                    <BackgroundPicker scheme={effectiveScheme} />
                  </SettingRow>
                </SettingGroup>

                <SettingGroup title={t("settings.codeTheme")} plain>
                  <div className="code-theme-grid">
                    {CODE_THEMES.map((theme) => {
                      const palette = theme.palettes[effectiveScheme];
                      const active = codeTheme === theme.id;
                      return (
                        <button
                          key={theme.id}
                          type="button"
                          className={`code-theme-card ${active ? "is-active" : ""}`}
                          aria-pressed={active}
                          onClick={() => setCodeTheme(theme.id)}
                        >
                          <span
                            className="code-theme-canvas"
                            data-scheme={effectiveScheme}
                            style={{ color: palette.foreground }}
                            aria-hidden="true"
                          >
                            {THEME_PREVIEW.map((line, index) => (
                              <span className="code-theme-line" key={index}>
                                {line.map(([text, slot], run) => (
                                  <span key={run} style={{ color: palette[slot] }}>
                                    {text}
                                  </span>
                                ))}
                              </span>
                            ))}
                          </span>
                          <span className="code-theme-label">
                            <span className="code-theme-name">{theme.label}</span>
                            {active ? (
                              <Check size={12} className="code-theme-check" />
                            ) : null}
                          </span>
                        </button>
                      );
                    })}
                  </div>
                </SettingGroup>
              </>
            ) : null}

            {tab === "editor" ? (
              <>
                <SettingGroup title={t("settings.group.typography")}>
                  <SettingRow label={t("settings.font")} htmlFor="editor-font">
                    <select
                      id="editor-font"
                      className="settings-select"
                      value={editorFont}
                      onChange={(event) =>
                        setEditorFont(event.target.value as typeof editorFont)
                      }
                    >
                      {EDITOR_FONTS.map((font) => (
                        <option key={font.id} value={font.id}>
                          {font.label}
                        </option>
                      ))}
                    </select>
                  </SettingRow>

                  <SettingRow
                    label={t("settings.fontSize")}
                    htmlFor="editor-font-size"
                  >
                    <div className="settings-stepper">
                      <button
                        type="button"
                        title={t("settings.decreaseFont")}
                        aria-label={t("settings.decreaseFont")}
                        onClick={() => setEditorFontSize(editorFontSize - 0.5)}
                        disabled={editorFontSize <= 10}
                      >
                        <Minus size={13} />
                      </button>
                      <input
                        id="editor-font-size"
                        type="range"
                        min="10"
                        max="22"
                        step="0.5"
                        value={editorFontSize}
                        onChange={(event) =>
                          setEditorFontSize(Number(event.target.value))
                        }
                      />
                      <output>{editorFontSize}px</output>
                      <button
                        type="button"
                        title={t("settings.increaseFont")}
                        aria-label={t("settings.increaseFont")}
                        onClick={() => setEditorFontSize(editorFontSize + 0.5)}
                        disabled={editorFontSize >= 22}
                      >
                        <Plus size={13} />
                      </button>
                    </div>
                  </SettingRow>
                </SettingGroup>

                <SettingGroup title={t("settings.group.behavior")}>
                  <SettingRow
                    label={t("settings.codeFolding")}
                    hint={t("settings.codeFolding.hint")}
                  >
                    <Switch
                      id="editor-code-folding"
                      checked={codeFolding}
                      label={t("settings.codeFolding")}
                      onChange={setCodeFolding}
                    />
                  </SettingRow>

                  <SettingRow
                    label={t("settings.wordWrap")}
                    hint={t("settings.wordWrap.hint")}
                  >
                    <Switch
                      id="editor-word-wrap"
                      checked={wordWrap}
                      label={t("settings.wordWrap")}
                      onChange={setWordWrap}
                    />
                  </SettingRow>
                </SettingGroup>

                <SettingGroup title={t("settings.preview")} plain>
                  <div
                    className="settings-code-sample"
                    style={{
                      fontFamily: EDITOR_FONTS.find(
                        (font) => font.id === editorFont,
                      )?.stack,
                      fontSize: editorFontSize,
                    }}
                  >
                    <span className="sample-keyword">public</span>{" "}
                    <span className="sample-type">String</span>{" "}
                    <span className="sample-method">decompile</span>
                    <span className="sample-punctuation">()</span>{" "}
                    <span className="sample-punctuation">{"{"}</span>
                    <br />
                    {"    "}
                    <span className="sample-keyword">return</span>{" "}
                    <span className="sample-string">"source"</span>
                    <span className="sample-punctuation">;</span>
                    <br />
                    <span className="sample-punctuation">{"}"}</span>
                  </div>
                </SettingGroup>
              </>
            ) : null}

            {tab === "decompiler" ? <DecompilerPanel /> : null}
            {tab === "mcp" ? <McpPanel /> : null}
            {tab === "keymap" ? <KeymapPanel /> : null}
            {tab === "about" ? <AboutPanel /> : null}
          </div>

          <footer className="settings-footer">
            {tab === "about" || tab === "keymap" || tab === "mcp" ? (
              <span />
            ) : (
              <button type="button" className="settings-reset" onClick={reset}>
                <RotateCcw size={13} />
                <span>{t("settings.reset")}</span>
              </button>
            )}
            <button
              type="button"
              className="settings-done"
              onClick={() => setOpen(false)}
            >
              {t("settings.done")}
            </button>
          </footer>
        </div>
      </div>
    </div>
  );
}

function McpPanel() {
  const { t } = useTranslation();
  const [configuration, setConfiguration] =
    useState<McpConfigurationDocument | null>(null);
  const [integrations, setIntegrations] = useState<AgentMcpIntegration[]>([]);
  const [loadingIntegrations, setLoadingIntegrations] = useState(true);
  const [configuring, setConfiguring] = useState<string | null>(null);
  const [integrationError, setIntegrationError] = useState<string | null>(null);
  const [configurationError, setConfigurationError] = useState<string | null>(
    null,
  );
  const [copied, setCopied] = useState(false);

  useEffect(() => {
    let cancelled = false;
    setConfiguration(null);
    setIntegrations([]);
    setLoadingIntegrations(true);
    setIntegrationError(null);
    setConfigurationError(null);
    setCopied(false);
    void mcpConfigurationClient
      .configuration()
      .then((nextConfiguration) => {
        if (!cancelled) {
          setConfiguration(nextConfiguration);
        }
      })
      .catch((reason) => {
        if (!cancelled) {
          setConfigurationError(
            reason instanceof Error ? reason.message : String(reason),
          );
        }
      });
    void mcpConfigurationClient
      .integrations()
      .then((nextIntegrations) => {
        if (!cancelled) {
          setIntegrations(nextIntegrations);
          setLoadingIntegrations(false);
        }
      })
      .catch((reason) => {
        if (!cancelled) {
          setLoadingIntegrations(false);
          setIntegrationError(
            reason instanceof Error ? reason.message : String(reason),
          );
        }
      });
    return () => {
      cancelled = true;
    };
  }, []);

  const copyConfiguration = async () => {
    if (!configuration) return;
    if (await copyText(configuration.json)) {
      setCopied(true);
      window.setTimeout(() => setCopied(false), 1600);
    }
  };

  const configureAgent = async (agentId: string) => {
    if (configuring) return;
    setConfiguring(agentId);
    setIntegrationError(null);
    try {
      const updated = await mcpConfigurationClient.configureAgent(agentId);
      setIntegrations((current) =>
        current.map((integration) =>
          integration.id === updated.id ? updated : integration,
        ),
      );
    } catch (reason) {
      setIntegrationError(
        reason instanceof Error ? reason.message : String(reason),
      );
    } finally {
      setConfiguring(null);
    }
  };

  const configureAll = async () => {
    if (configuring) return;
    setConfiguring("all");
    setIntegrationError(null);
    try {
      setIntegrations(await mcpConfigurationClient.configureAll());
    } catch (reason) {
      setIntegrationError(
        reason instanceof Error ? reason.message : String(reason),
      );
    } finally {
      setConfiguring(null);
    }
  };

  const unconfigureAgent = async (agentId: string) => {
    if (configuring) return;
    setConfiguring(agentId);
    setIntegrationError(null);
    try {
      const updated = await mcpConfigurationClient.unconfigureAgent(agentId);
      setIntegrations((current) =>
        current.map((integration) =>
          integration.id === updated.id ? updated : integration,
        ),
      );
    } catch (reason) {
      setIntegrationError(
        reason instanceof Error ? reason.message : String(reason),
      );
    } finally {
      setConfiguring(null);
    }
  };

  const availableIntegrations = integrations.filter(
    (integration) => integration.available,
  );
  const pendingIntegrations = availableIntegrations.filter(
    (integration) => !integration.configured,
  );

  return (
    <>
      <SettingGroup title={t("settings.mcp.agents")} plain>
        <div className="settings-agent-toolbar">
          <p>{t("settings.mcp.agents.hint")}</p>
          <button
            type="button"
            className="settings-agent-configure-all"
            disabled={configuring !== null || pendingIntegrations.length === 0}
            onClick={() => void configureAll()}
          >
            <RefreshCw
              size={13}
              className={configuring === "all" ? "is-spinning" : undefined}
            />
            <span>
              {configuring === "all"
                ? t("settings.mcp.configuring")
                : t("settings.mcp.configureAll")}
            </span>
          </button>
        </div>
        <div className="settings-card settings-agent-list">
          {loadingIntegrations ? (
            <div className="settings-agent-empty">
              {t("settings.mcp.detecting")}
            </div>
          ) : (
            integrations.map((integration) => {
              const active = configuring === integration.id;
              const removing =
                integration.configured ||
                (!integration.available && integration.needsUpdate);
              const status = !integration.available
                ? t("settings.mcp.notInstalled")
                : integration.configured
                  ? t("settings.mcp.configured")
                  : integration.needsUpdate
                    ? t("settings.mcp.updateRequired")
                    : t("settings.mcp.notConfigured");
              return (
                <div className="settings-agent-row" key={integration.id}>
                  <div className="settings-agent-details">
                    <div className="settings-agent-heading">
                      <span>{integration.name}</span>
                      <small
                        className={
                          integration.configured
                            ? "is-configured"
                            : integration.needsUpdate
                              ? "is-stale"
                              : undefined
                        }
                      >
                        {status}
                      </small>
                    </div>
                    <span
                      className="settings-agent-path"
                      title={integration.message ?? integration.configPath}
                    >
                      {integration.message ?? integration.configPath}
                    </span>
                  </div>
                  <button
                    type="button"
                    className="settings-agent-action"
                    disabled={
                      (!integration.available && !removing) || configuring !== null
                    }
                    onClick={() =>
                      void (removing
                        ? unconfigureAgent(integration.id)
                        : configureAgent(integration.id))
                    }
                  >
                    {active ? (
                      <RefreshCw size={12} className="is-spinning" />
                    ) : null}
                    <span>
                      {active
                        ? removing
                          ? t("settings.mcp.unconfiguring")
                          : t("settings.mcp.configuring")
                        : removing
                          ? t("settings.mcp.unconfigure")
                          : integration.needsUpdate
                          ? t("settings.mcp.reconfigure")
                          : t("settings.mcp.configure")}
                    </span>
                  </button>
                </div>
              );
            })
          )}
        </div>
        {integrationError ? (
          <p className="settings-agent-error">{integrationError}</p>
        ) : null}
      </SettingGroup>

      <SettingGroup title={t("settings.mcp.otherClients")}>
        <SettingRow
          label={t("settings.mcp.copy")}
          hint={configurationError ?? t("settings.mcp.copy.hint")}
        >
          <button
            type="button"
            className="settings-agent-action"
            title={t("settings.mcp.copy")}
            disabled={!configuration}
            onClick={() => void copyConfiguration()}
          >
            {copied ? <Check size={13} /> : <Copy size={13} />}
            <span>
              {copied ? t("settings.mcp.copied") : t("settings.mcp.copyAction")}
            </span>
          </button>
        </SettingRow>
      </SettingGroup>
    </>
  );
}

/*
 * Output settings that reach the Rust decompiler. Changing one marks the open
 * documents stale, so the active tab re-decompiles immediately and the others
 * when they are next activated.
 */
function DecompilerPanel() {
  const { t } = useTranslation();
  const options = useWorkspace((state) => state.decompileOptions);
  const setOptions = useWorkspace((state) => state.setDecompileOptions);

  return (
    <>
      <SettingGroup title={t("settings.group.output")}>
        <SettingRow
          label={t("settings.indentWidth")}
          hint={t("settings.indentWidth.hint")}
        >
          <div className="settings-segmented is-compact">
            {INDENT_WIDTHS.map((width) => (
              <button
                key={width}
                type="button"
                className={options.indentWidth === width ? "is-active" : ""}
                aria-pressed={options.indentWidth === width}
                onClick={() => setOptions({ indentWidth: width })}
              >
                <span>{width}</span>
              </button>
            ))}
          </div>
        </SettingRow>

        <SettingRow
          label={t("settings.includeNested")}
          hint={t("settings.includeNested.hint")}
        >
          <Switch
            id="decompiler-include-nested"
            checked={options.includeNested}
            label={t("settings.includeNested")}
            onChange={(includeNested) => setOptions({ includeNested })}
          />
        </SettingRow>
      </SettingGroup>

      <p className="settings-hint">{t("settings.decompiler.note")}</p>
    </>
  );
}

/*
 * The background control: a swatch that opens the in-app picker, plus a reset.
 * Light and dark keep separate values, so it always edits the scheme currently
 * on screen.
 */
function BackgroundPicker({ scheme }: { scheme: "light" | "dark" }) {
  const { t } = useTranslation();
  const override = useAppearance((state) =>
    scheme === "light" ? state.backgroundLight : state.backgroundDark,
  );
  const setBackground = useAppearance((state) => state.setBackground);
  const swatchRef = useRef<HTMLButtonElement>(null);
  const [anchor, setAnchor] = useState<DOMRect | null>(null);
  const current = override ?? EDITOR_SURFACES[scheme];

  return (
    <div className="settings-color">
      <button
        ref={swatchRef}
        id="editor-background"
        type="button"
        className={`settings-color-swatch ${anchor ? "is-open" : ""}`}
        style={{ background: current }}
        title={current}
        aria-label={t("settings.background.color")}
        aria-expanded={Boolean(anchor)}
        onClick={() =>
          setAnchor((open) =>
            open ? null : (swatchRef.current?.getBoundingClientRect() ?? null),
          )
        }
      />
      <button
        type="button"
        className="settings-color-reset"
        title={t("settings.background.reset")}
        aria-label={t("settings.background.reset")}
        disabled={!override}
        onClick={() => setBackground(scheme, null)}
      >
        <RotateCcw size={12} />
      </button>

      {anchor ? (
        <ColorPicker
          value={current}
          presets={EDITOR_BACKGROUNDS[scheme]}
          anchor={anchor}
          defaultColor={EDITOR_SURFACES[scheme]}
          defaultLabel={t("settings.background.default")}
          onChange={(color) =>
            setBackground(
              scheme,
              color === EDITOR_SURFACES[scheme] ? null : color,
            )
          }
          onClose={() => setAnchor(null)}
        />
      ) : null}
    </div>
  );
}

/** Renders a shortcut entry for the current platform. */
function comboText(entry: ShortcutEntry): string {
  if (entry.combo) {
    return sc(entry.combo);
  }
  if (entry.literal === "tab-digits") {
    return `${sc("mod+1")} … ${sc("mod+9")}`;
  }
  return MOD_CLICK;
}

function KeymapPanel() {
  const { t } = useTranslation();
  const [query, setQuery] = useState("");

  const normalized = query.trim().toLocaleLowerCase();
  const groups = SHORTCUT_GROUPS.map((group) => ({
    title: group.title,
    entries: normalized
      ? group.entries.filter(
          (entry) =>
            t(entry.label).toLocaleLowerCase().includes(normalized) ||
            comboText(entry).toLocaleLowerCase().includes(normalized),
        )
      : group.entries,
  })).filter((group) => group.entries.length);

  return (
    <div className="settings-keymap">
      <div className="settings-search">
        <Search size={12} aria-hidden="true" />
        <input
          className="search-input"
          value={query}
          placeholder={t("keymap.filter")}
          aria-label={t("keymap.filter")}
          spellCheck={false}
          onChange={(event) => setQuery(event.target.value)}
          onKeyDown={(event) => {
            if (event.key === "Escape" && query) {
              event.preventDefault();
              setQuery("");
            }
          }}
        />
      </div>

      {groups.map((group) => (
        <SettingGroup key={group.title} title={t(group.title)}>
          {group.entries.map((entry) => (
            <div
              className="settings-row"
              key={`${entry.label}:${entry.combo ?? entry.literal ?? ""}`}
            >
              <div className="settings-row-label">
                <span>{t(entry.label)}</span>
              </div>
              <div className="settings-row-control">
                <kbd className="kbd">{comboText(entry)}</kbd>
              </div>
            </div>
          ))}
        </SettingGroup>
      ))}

      {groups.length ? null : (
        <p className="settings-hint">{t("keymap.empty")}</p>
      )}
    </div>
  );
}

/*
 * Product panel. The version comes from the Tauri runtime, so it stays blank in a
 * plain browser session rather than showing a stale hard-coded number.
 */
function AboutPanel() {
  const { t } = useTranslation();
  const [version, setVersion] = useState<string | null>(null);

  useEffect(() => {
    let cancelled = false;
    void getVersion()
      .then((appVersion) => {
        if (!cancelled) {
          setVersion(appVersion);
        }
      })
      .catch(() => undefined);
    return () => {
      cancelled = true;
    };
  }, []);

  return (
    <div className="settings-about">
      <div className="settings-about-mark" aria-hidden="true">
        <img src={appIcon} alt="" />
      </div>
      <h4>DexDec</h4>
      <p className="settings-about-tagline">{t("settings.about.tagline")}</p>
      {version ? (
        <span className="settings-about-version">
          {t("settings.about.version", version)}
        </span>
      ) : null}
    </div>
  );
}

function SettingGroup({
  title,
  plain,
  children,
}: {
  title: string;
  /** Renders the body bare, for content that carries its own frame. */
  plain?: boolean;
  children: React.ReactNode;
}) {
  return (
    <section className="settings-group">
      <h4 className="settings-group-title">{title}</h4>
      {plain ? children : <div className="settings-card">{children}</div>}
    </section>
  );
}

function SettingRow({
  label,
  hint,
  htmlFor,
  children,
}: {
  label: string;
  hint?: string;
  htmlFor?: string;
  children: React.ReactNode;
}) {
  return (
    <div className="settings-row">
      <div className="settings-row-label">
        {htmlFor ? (
          <label htmlFor={htmlFor}>{label}</label>
        ) : (
          <span>{label}</span>
        )}
        {hint ? <small>{hint}</small> : null}
      </div>
      <div className="settings-row-control">{children}</div>
    </div>
  );
}

function Switch({
  id,
  checked,
  label,
  onChange,
}: {
  id: string;
  checked: boolean;
  label: string;
  onChange: (value: boolean) => void;
}) {
  return (
    <button
      id={id}
      type="button"
      role="switch"
      className="settings-switch"
      aria-checked={checked}
      aria-label={label}
      onClick={() => onChange(!checked)}
    >
      <span aria-hidden="true" />
    </button>
  );
}
