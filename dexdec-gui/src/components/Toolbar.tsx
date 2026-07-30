import {
  ChevronLeft,
  ChevronRight,
  FolderOpen,
  LoaderCircle,
  ListChecks,
  PanelLeftClose,
  PanelLeftOpen,
  PanelRightClose,
  PanelRightOpen,
  Redo2,
  Save,
  Search,
  Settings,
  Undo2,
} from "lucide-react";

import { useTranslation } from "../i18n";
import { sc } from "../platform";
import { useWorkspace } from "../state/workspace";
import { useAppearance } from "../state/appearance";
import { useActivity } from "../state/activity";

const LANGUAGE_CHOICES = [
  { value: "java", label: "Java" },
  { value: "kotlin", label: "Kotlin" },
] as const;

interface IconButtonProps {
  label: string;
  onClick: () => void;
  disabled?: boolean;
  children: React.ReactNode;
}

function IconButton({ label, onClick, disabled, children }: IconButtonProps) {
  return (
    <button
      type="button"
      className="icon-button"
      title={label}
      aria-label={label}
      disabled={disabled}
      onClick={onClick}
    >
      {children}
    </button>
  );
}

export function Toolbar() {
  const archive = useWorkspace((state) => state.archive);
  const openingArchive = useWorkspace((state) => state.openingArchive);
  const sourceLanguage = useWorkspace((state) => state.sourceLanguage);
  const setSourceLanguage = useWorkspace((state) => state.setSourceLanguage);
  const explorerVisible = useWorkspace((state) => state.explorerVisible);
  const outlineVisible = useWorkspace((state) => state.outlineVisible);
  const chooseArchive = useWorkspace((state) => state.chooseArchive);
  const saveProject = useWorkspace((state) => state.saveProject);
  const savingProject = useWorkspace((state) => state.savingProject);
  const projectDirty = useWorkspace((state) => state.projectDirty);
  const canUndo = useWorkspace((state) => state.canUndo);
  const canRedo = useWorkspace((state) => state.canRedo);
  const undo = useWorkspace((state) => state.undo);
  const redo = useWorkspace((state) => state.redo);
  const toggleExplorer = useWorkspace((state) => state.toggleExplorer);
  const toggleOutline = useWorkspace((state) => state.toggleOutline);
  const setQuickOpenVisible = useWorkspace((state) => state.setQuickOpenVisible);
  const canGoBack = useWorkspace((state) => state.historyIndex > 0);
  const canGoForward = useWorkspace(
    (state) => state.historyIndex < state.history.length - 1,
  );
  const goBack = useWorkspace((state) => state.goBack);
  const goForward = useWorkspace((state) => state.goForward);
  const setSettingsOpen = useAppearance((state) => state.setSettingsOpen);
  const tasks = useActivity((state) => state.tasks);
  const activityOpen = useActivity((state) => state.open);
  const setActivityOpen = useActivity((state) => state.setOpen);
  const runningTasks = tasks.filter((task) => task.status === "running");
  const { t } = useTranslation();

  return (
    <header
      className="app-toolbar grid h-9 shrink-0 grid-cols-[minmax(0,1fr)_auto_minmax(0,1fr)] items-center border-b border-[var(--border)] bg-[var(--chrome)] px-2"
      data-tauri-drag-region
    >
      {/* left: panel + navigation + archive action */}
      <div className="flex min-w-0 items-center gap-1" data-tauri-drag-region>
        <IconButton
          label={
            explorerVisible
              ? t("toolbar.hideExplorer", sc("mod+1"))
              : t("toolbar.showExplorer", sc("mod+1"))
          }
          onClick={toggleExplorer}
        >
          {explorerVisible ? <PanelLeftClose size={15} /> : <PanelLeftOpen size={15} />}
        </IconButton>

        <div className="flex items-center">
          <IconButton
            label={t("toolbar.goBack", sc("mod+["))}
            onClick={goBack}
            disabled={!canGoBack}
          >
            <ChevronLeft size={15} />
          </IconButton>
          <IconButton
            label={t("toolbar.goForward", sc("mod+]"))}
            onClick={goForward}
            disabled={!canGoForward}
          >
            <ChevronRight size={15} />
          </IconButton>
        </div>

        <div className="mx-0.5 h-3.5 w-px bg-[var(--border-strong)]" />

        <button
          type="button"
          className="toolbar-button"
          onClick={() => void chooseArchive()}
          disabled={openingArchive}
          title={t("toolbar.openArchive", sc("mod+o"))}
        >
          {openingArchive ? (
            <LoaderCircle className="animate-spin" size={13} />
          ) : (
            <FolderOpen size={13} />
          )}
          <span>{t("toolbar.open")}</span>
        </button>

        <div className="mx-0.5 h-3.5 w-px bg-[var(--border-strong)]" />

        <IconButton
          label={t("toolbar.save", sc("mod+s"))}
          onClick={() => void saveProject()}
          disabled={!archive || savingProject}
        >
          {savingProject ? (
            <LoaderCircle className="animate-spin" size={14} />
          ) : (
            <Save
              size={14}
              className={projectDirty ? "text-[var(--accent)]" : undefined}
            />
          )}
        </IconButton>
        <IconButton
          label={t("toolbar.undo", sc("mod+z"))}
          onClick={undo}
          disabled={!canUndo}
        >
          <Undo2 size={14} />
        </IconButton>
        <IconButton
          label={t("toolbar.redo", sc("mod+shift+z"))}
          onClick={redo}
          disabled={!canRedo}
        >
          <Redo2 size={14} />
        </IconButton>
      </div>

      {/* center: quick open, centered on the window */}
      <div className="flex justify-center px-3" data-tauri-drag-region>
        <button
          type="button"
          className="quick-open-trigger"
          onClick={() => setQuickOpenVisible(true)}
          disabled={!archive}
          title={t("toolbar.goToClass", sc("mod+o"))}
        >
          <Search size={12} className="shrink-0 text-[var(--text-faint)]" />
          <span className="min-w-0 flex-1 truncate text-left">
            {archive ? t("toolbar.goToClassPlaceholder") : t("toolbar.openFirst")}
          </span>
          <kbd className="kbd shrink-0">{sc("mod+o")}</kbd>
        </button>
      </div>

      {/* right: activity, archive context, outline panel */}
      <div className="flex min-w-0 items-center justify-end gap-1" data-tauri-drag-region>
        {archive ? (
          <>
            <div
              className="source-language-switch"
              role="group"
              aria-label="Source language"
            >
              {LANGUAGE_CHOICES.map(({ value, label }) => (
                <button
                  key={value}
                  type="button"
                  className={sourceLanguage === value ? "is-active" : undefined}
                  aria-pressed={sourceLanguage === value}
                  onClick={() => setSourceLanguage(value)}
                  title={t("toolbar.languageFixedHint", label)}
                >
                  {label}
                </button>
              ))}
            </div>

            <div className="mx-0.5 h-3.5 w-px bg-[var(--border-strong)]" />
          </>
        ) : null}

        <button
          type="button"
          className={`icon-button relative ${activityOpen ? "icon-button-active" : ""}`}
          title={t("activity.open")}
          aria-label={t("activity.open")}
          aria-expanded={activityOpen}
          onClick={() => setActivityOpen(!activityOpen)}
        >
          {runningTasks.length ? (
            <LoaderCircle className="animate-spin text-[var(--accent)]" size={14} />
          ) : (
            <ListChecks size={14} />
          )}
          {runningTasks.length > 1 ? (
            <span className="activity-badge">{runningTasks.length}</span>
          ) : null}
        </button>

        <IconButton
          label={
            outlineVisible
              ? t("toolbar.hideOutline", sc("mod+7"))
              : t("toolbar.showOutline", sc("mod+7"))
          }
          onClick={toggleOutline}
        >
          {outlineVisible ? <PanelRightClose size={15} /> : <PanelRightOpen size={15} />}
        </IconButton>

        <div className="mx-0.5 h-3.5 w-px bg-[var(--border-strong)]" />

        <IconButton
          label={t("toolbar.settings", sc("mod+,"))}
          onClick={() => setSettingsOpen(true)}
        >
          <Settings size={15} />
        </IconButton>
      </div>
    </header>
  );
}
