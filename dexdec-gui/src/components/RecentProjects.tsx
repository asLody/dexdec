import { Binary, Database, FolderOpen, Package, Trash2, X } from "lucide-react";

import type { RecentProject } from "../domain/recentProjects";
import { useTranslation } from "../i18n";
import { sc } from "../platform";
import { useWorkspace } from "../state/workspace";

class RecentProjectPresentation {
  constructor(
    private readonly project: RecentProject,
    private readonly locale: string,
  ) {}

  date(): string {
    return new Intl.DateTimeFormat(this.locale, {
      dateStyle: "medium",
      timeStyle: "short",
    }).format(this.project.openedAt);
  }

  kind(): string {
    return this.project.kind === "database"
      ? "DexDB"
      : this.project.kind.toUpperCase();
  }
}

export function RecentProjects() {
  const projects = useWorkspace((state) => state.recentProjects);
  const opening = useWorkspace((state) => state.openingArchive);
  const openArchive = useWorkspace((state) => state.openArchive);
  const chooseArchive = useWorkspace((state) => state.chooseArchive);
  const remove = useWorkspace((state) => state.removeRecentProject);
  const clear = useWorkspace((state) => state.clearRecentProjects);
  const { locale, t } = useTranslation();

  return (
    <div className="recent-projects-scroll">
      <div className={`project-welcome ${projects.length ? "has-recent" : ""}`}>
        <div className="project-welcome-entry">
          <span>{t("workspace.openToBegin")}</span>
          <div className="project-welcome-action">
            <kbd className="kbd">{sc("mod+o")}</kbd>
          <button
            type="button"
              className="command-button"
            onClick={() => void chooseArchive()}
            disabled={opening}
          >
              <FolderOpen size={13} />
              {t("workspace.openButton")}
          </button>
          </div>
        </div>

        {projects.length ? (
        <section className="recent-projects" aria-labelledby="recent-projects-title">
          <header className="recent-projects-header">
            <h2 id="recent-projects-title">{t("recent.title")}</h2>
            <div className="recent-projects-actions">
              <button
                type="button"
                className="recent-projects-clear"
                onClick={clear}
                title={t("recent.clear")}
                aria-label={t("recent.clear")}
              >
                <Trash2 size={13} />
              </button>
            </div>
          </header>

          <div className="recent-project-list">
            {projects.map((project) => {
              const presentation = new RecentProjectPresentation(project, locale);
              const ProjectIcon = project.kind === "database"
                ? Database
                : project.kind === "dex"
                  ? Binary
                  : Package;
              return (
                <div className="recent-project-row" key={project.path}>
                  <button
                    type="button"
                    className="recent-project-open"
                    onClick={() => void openArchive(project.path)}
                    disabled={opening}
                    title={project.path}
                  >
                    <span className="recent-project-icon" aria-hidden="true">
                      {project.iconData ? (
                        <img src={project.iconData} alt="" />
                      ) : (
                        <ProjectIcon size={17} />
                      )}
                    </span>
                    <span className="recent-project-identity">
                      <strong>{project.name}</strong>
                      <span>{project.parent}</span>
                    </span>
                    <span className="recent-project-meta">
                      <span>{presentation.kind()}</span>
                      <time dateTime={new Date(project.openedAt).toISOString()}>
                        {presentation.date()}
                      </time>
                    </span>
                  </button>
                  <button
                    type="button"
                    className="recent-project-remove"
                    onClick={() => remove(project.path)}
                    aria-label={t("recent.remove", project.name)}
                    title={t("recent.remove", project.name)}
                  >
                    <X size={13} />
                  </button>
                </div>
              );
            })}
          </div>
        </section>
        ) : null}
      </div>
    </div>
  );
}
