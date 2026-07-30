import {
  Activity,
  AlertTriangle,
  ArchiveRestore,
  Box,
  Bug,
  ChevronDown,
  ChevronRight,
  ChevronUp,
  Copy,
  Cpu,
  Database,
  FileArchive,
  FileCode2,
  Fingerprint,
  Globe2,
  KeyRound,
  Package,
  Radio,
  Search,
  Server,
  ShieldCheck,
  Smartphone,
  SquareArrowOutUpRight,
  X,
} from "lucide-react";
import { useEffect, useMemo, useState } from "react";

import type {
  ApkOverview as ApkOverviewData,
  Archive,
  ResourceNavigationTarget,
} from "../domain/models";
import { useTranslation } from "../i18n";
import { ApplicationIconService } from "../services/applicationIcon";
import { copyText } from "../services/clipboard";
import { useWorkspace } from "../state/workspace";

type PermissionScope = "all" | "android" | "application";

interface ComponentFact {
  id: "activities" | "services" | "receivers" | "providers";
  count: number;
  icon: React.ReactNode;
  elementNames: string[];
}

class OverviewModel {
  constructor(
    readonly archive: Archive,
    readonly overview: ApkOverviewData | null,
  ) {}

  get hasManifest(): boolean {
    return this.archive.resources.some(
      (entry) => entry.path === "AndroidManifest.xml",
    );
  }

  get permissions(): string[] {
    return this.overview?.permissions ?? [];
  }

  get version(): string | null {
    const name = this.overview?.versionName;
    const code = this.overview?.versionCode;
    if (name && code) return `${name} (${code})`;
    return name ?? code ?? null;
  }

  get androidPermissionCount(): number {
    return this.permissions.filter((permission) =>
      permission.startsWith("android.permission."),
    ).length;
  }

  get applicationPermissionCount(): number {
    return this.permissions.length - this.androidPermissionCount;
  }

  get components(): ComponentFact[] {
    return [
      {
        id: "activities",
        count: this.overview?.components.activities ?? 0,
        icon: <Activity size={16} />,
        elementNames: ["activity", "activity-alias"],
      },
      {
        id: "services",
        count: this.overview?.components.services ?? 0,
        icon: <Server size={16} />,
        elementNames: ["service"],
      },
      {
        id: "receivers",
        count: this.overview?.components.receivers ?? 0,
        icon: <Radio size={16} />,
        elementNames: ["receiver"],
      },
      {
        id: "providers",
        count: this.overview?.components.providers ?? 0,
        icon: <Database size={16} />,
        elementNames: ["provider"],
      },
    ];
  }

  filteredPermissions(scope: PermissionScope, query: string): string[] {
    const normalized = query.trim().toLocaleLowerCase();
    return this.permissions.filter((permission) => {
      const android = permission.startsWith("android.permission.");
      if (scope === "android" && !android) return false;
      if (scope === "application" && android) return false;
      return !normalized || permission.toLocaleLowerCase().includes(normalized);
    });
  }
}

export default function ApkOverview({ archive }: { archive: Archive }) {
  const overview = archive.overview;
  const model = useMemo(
    () => new OverviewModel(archive, overview),
    [archive, overview],
  );
  const openResource = useWorkspace((state) => state.openResource);
  const { t } = useTranslation();
  const iconData = useApplicationIcon(archive);
  const fallbackName = archive.name.replace(/\.(apk|dex)$/i, "");
  const applicationName =
    overview?.applicationLabel && !overview.applicationLabel.startsWith("@")
      ? overview.applicationLabel
      : fallbackName;

  const openManifest = (target?: ResourceNavigationTarget) => {
    if (model.hasManifest) void openResource("AndroidManifest.xml", target);
  };

  return (
    <div className="apk-overview-scroll">
      <div className="apk-overview-content">
        <ApplicationIdentity
          name={applicationName}
          packageName={overview?.packageName ?? archive.name}
          iconData={iconData}
          manifestAvailable={model.hasManifest}
          onOpenManifest={() => openManifest()}
        />

        <div className="overview-metrics" aria-label={t("overview.projectSummary")}>
          <Metric
            icon={<FileCode2 size={15} />}
            value={archive.classCount}
            label={t("overview.classes")}
          />
          <Metric
            icon={<Database size={15} />}
            value={overview?.resourceCount ?? archive.resources.length}
            label={t("overview.resources")}
          />
          <Metric
            icon={<Box size={15} />}
            value={overview?.dexFileCount ?? 1}
            label={t("overview.dexFiles")}
          />
          <Metric
            icon={<Cpu size={15} />}
            value={overview?.nativeLibraryCount ?? 0}
            label={t("overview.nativeLibraries")}
          />
        </div>

        <div className="overview-main-grid">
          <main className="overview-primary-column">
            <OverviewSection title={t("overview.components")}>
              <div className="overview-component-grid">
                {model.components.map((component) => (
                  <ComponentLink
                    key={component.id}
                    icon={component.icon}
                    label={t(`overview.${component.id}`)}
                    count={component.count}
                    enabled={model.hasManifest}
                    onClick={() =>
                      openManifest({
                        kind: "xmlElement",
                        names: component.elementNames,
                      })
                    }
                  />
                ))}
              </div>
            </OverviewSection>

            <PermissionBrowser model={model} />
          </main>

          <aside className="overview-secondary-column">
            <PackageDetails model={model} />
            <AnalysisSignals model={model} />
            <NativeSection overview={overview} />
          </aside>
        </div>
      </div>
    </div>
  );
}

function useApplicationIcon(archive: Archive): string | null {
  const service = useMemo(() => new ApplicationIconService(archive), [archive]);
  const [iconData, setIconData] = useState<string | null>(null);

  useEffect(() => {
    let current = true;
    setIconData(null);
    void service
      .load()
      .then((data) => {
        if (current) setIconData(data);
      })
      .catch(() => {});
    return () => {
      current = false;
    };
  }, [service]);

  return iconData;
}

function ApplicationIdentity({
  name,
  packageName,
  iconData,
  manifestAvailable,
  onOpenManifest,
}: {
  name: string;
  packageName: string;
  iconData: string | null;
  manifestAvailable: boolean;
  onOpenManifest: () => void;
}) {
  const { t } = useTranslation();
  return (
    <header className="overview-identity">
      <div className="overview-app-icon">
        {iconData ? (
          <img src={iconData} alt="" className="size-full object-cover" />
        ) : (
          <Package size={27} strokeWidth={1.4} aria-hidden="true" />
        )}
      </div>
      <div className="min-w-0 flex-1">
        <h1 className="overview-app-name">{name}</h1>
        <div className="overview-package-name" title={packageName}>
          {packageName}
        </div>
      </div>
      {manifestAvailable ? (
        <button
          type="button"
          className="command-button overview-manifest-button"
          onClick={onOpenManifest}
        >
          <FileCode2 size={14} />
          {t("overview.openManifest")}
        </button>
      ) : null}
    </header>
  );
}

function Metric({
  icon,
  value,
  label,
}: {
  icon: React.ReactNode;
  value: number;
  label: string;
}) {
  return (
    <div className="overview-metric">
      <span className="overview-metric-icon">{icon}</span>
      <span className="overview-metric-value">{value.toLocaleString()}</span>
      <span className="overview-metric-label">{label}</span>
    </div>
  );
}

function OverviewSection({
  title,
  trailing,
  children,
  className = "",
}: {
  title: string;
  trailing?: React.ReactNode;
  children: React.ReactNode;
  className?: string;
}) {
  return (
    <section className={`overview-section ${className}`}>
      <header className="overview-section-header">
        <h2>{title}</h2>
        {trailing}
      </header>
      {children}
    </section>
  );
}

function ComponentLink({
  icon,
  label,
  count,
  enabled,
  onClick,
}: {
  icon: React.ReactNode;
  label: string;
  count: number;
  enabled: boolean;
  onClick: () => void;
}) {
  const { t } = useTranslation();
  return (
    <button
      type="button"
      className="overview-component"
      onClick={onClick}
      disabled={!enabled}
      title={enabled ? t("overview.openComponentDeclarations") : undefined}
    >
      <span className="overview-component-icon">{icon}</span>
      <span className="overview-component-copy">
        <span className="overview-component-label">{label}</span>
        <span className="overview-component-source">AndroidManifest.xml</span>
      </span>
      <span className="overview-component-count">{count.toLocaleString()}</span>
      <ChevronRight size={14} className="overview-component-arrow" />
    </button>
  );
}

function PermissionBrowser({ model }: { model: OverviewModel }) {
  const { t } = useTranslation();
  const [scope, setScope] = useState<PermissionScope>("all");
  const [query, setQuery] = useState("");
  const [expanded, setExpanded] = useState(false);
  const filtered = useMemo(
    () => model.filteredPermissions(scope, query),
    [model, query, scope],
  );
  const visible = expanded || query ? filtered : filtered.slice(0, 12);
  const canToggle = !query && filtered.length > 12;

  useEffect(() => setExpanded(false), [scope]);

  return (
    <OverviewSection
      title={t("overview.permissions")}
      className="overview-permissions-section"
      trailing={
        <span className="overview-section-count">
          {filtered.length.toLocaleString()}
        </span>
      }
    >
      <div className="overview-permission-tools">
        <div className="overview-permission-search">
          <Search size={13} aria-hidden="true" />
          <input
            value={query}
            onChange={(event) => setQuery(event.target.value)}
            placeholder={t("overview.filterPermissions")}
            aria-label={t("overview.filterPermissions")}
            spellCheck={false}
          />
          {query ? (
            <button
              type="button"
              onClick={() => setQuery("")}
              aria-label={t("overview.clearPermissionFilter")}
              title={t("overview.clearPermissionFilter")}
            >
              <X size={12} />
            </button>
          ) : null}
        </div>
        <div className="overview-permission-scope" role="group">
          <ScopeButton
            active={scope === "all"}
            label={t("overview.permissionAll")}
            count={model.permissions.length}
            onClick={() => setScope("all")}
          />
          <ScopeButton
            active={scope === "android"}
            label={t("overview.permissionAndroid")}
            count={model.androidPermissionCount}
            onClick={() => setScope("android")}
          />
          <ScopeButton
            active={scope === "application"}
            label={t("overview.permissionApplication")}
            count={model.applicationPermissionCount}
            onClick={() => setScope("application")}
          />
        </div>
      </div>

      {visible.length ? (
        <div className="overview-permission-list">
          {visible.map((permission) => (
            <PermissionRow
              key={permission}
              permission={permission}
              manifestAvailable={model.hasManifest}
            />
          ))}
        </div>
      ) : (
        <div className="overview-empty-value">{t("overview.noPermissions")}</div>
      )}

      {canToggle ? (
        <button
          type="button"
          className="overview-show-permissions"
          onClick={() => setExpanded((current) => !current)}
        >
          {expanded ? <ChevronUp size={13} /> : <ChevronDown size={13} />}
          {expanded
            ? t("overview.showFewerPermissions")
            : t("overview.showAllPermissions", filtered.length)}
        </button>
      ) : null}
    </OverviewSection>
  );
}

function ScopeButton({
  active,
  label,
  count,
  onClick,
}: {
  active: boolean;
  label: string;
  count: number;
  onClick: () => void;
}) {
  return (
    <button
      type="button"
      className={active ? "is-active" : ""}
      aria-pressed={active}
      onClick={onClick}
    >
      {label}
      <span>{count.toLocaleString()}</span>
    </button>
  );
}

function PermissionRow({
  permission,
  manifestAvailable,
}: {
  permission: string;
  manifestAvailable: boolean;
}) {
  const { t } = useTranslation();
  const openResource = useWorkspace((state) => state.openResource);
  const separator = permission.lastIndexOf(".");
  const namespace = separator >= 0 ? permission.slice(0, separator + 1) : "";
  const name = separator >= 0 ? permission.slice(separator + 1) : permission;
  const openDeclaration = () => {
    if (!manifestAvailable) return;
    void openResource("AndroidManifest.xml", {
      kind: "xmlElement",
      names: ["uses-permission", "uses-permission-sdk-23"],
      attribute: { name: "android:name", value: permission },
    });
  };
  return (
    <div className="overview-permission-row">
      <button
        type="button"
        className="overview-permission-open"
        onClick={openDeclaration}
        disabled={!manifestAvailable}
        title={
          manifestAvailable ? t("overview.openPermissionDeclaration") : permission
        }
      >
        <ShieldCheck size={13} aria-hidden="true" />
        <span className="overview-permission-name">
          <span>{namespace}</span>
          <strong>{name}</strong>
        </span>
      </button>
      <button
        type="button"
        className="overview-permission-copy"
        onClick={() => void copyText(permission)}
        aria-label={t("overview.copyPermission")}
        title={t("overview.copyPermission")}
      >
        <Copy size={12} />
      </button>
    </div>
  );
}

function PackageDetails({ model }: { model: OverviewModel }) {
  const { t } = useTranslation();
  const overview = model.overview;
  return (
    <OverviewSection title={t("overview.packageProfile")}>
      <dl className="overview-definition-list">
        <Definition
          icon={<Package size={14} />}
          label={t("overview.packageName")}
          value={overview?.packageName}
          mono
        />
        <Definition
          icon={<FileArchive size={14} />}
          label={t("overview.version")}
          value={model.version}
          mono
        />
        <Definition
          icon={<Smartphone size={14} />}
          label={t("overview.minSdk")}
          value={overview?.minSdk}
        />
        <Definition
          icon={<Smartphone size={14} />}
          label={t("overview.targetSdk")}
          value={overview?.targetSdk}
        />
        <Definition
          icon={<KeyRound size={14} />}
          label={t("overview.v1SignerCertificates")}
          value={String(overview?.signatureCount ?? 0)}
        />
        <Definition
          icon={<Bug size={14} />}
          label={t("overview.debuggable")}
          value={
            overview?.debuggable == null
              ? null
              : overview.debuggable
                ? t("overview.yes")
                : t("overview.no")
          }
          tone={overview?.debuggable ? "danger" : "success"}
        />
      </dl>
    </OverviewSection>
  );
}

function AnalysisSignals({ model }: { model: OverviewModel }) {
  const { t } = useTranslation();
  const overview = model.overview;
  return (
    <OverviewSection title={t("overview.analysis")}>
      <div className="overview-signal-list">
        {overview?.debuggable ? (
          <Signal
            icon={<AlertTriangle size={15} />}
            title={t("overview.debugBuild")}
            detail={t("overview.debugBuildDetail")}
            tone="danger"
          />
        ) : (
          <Signal
            icon={<ShieldCheck size={15} />}
            title={t("overview.debuggingDisabled")}
            detail={t("overview.debuggingDisabledDetail")}
            tone="success"
          />
        )}
        <Signal
          icon={<SquareArrowOutUpRight size={15} />}
          title={t(
            "overview.exportedProfile",
            overview?.components.explicitlyExported ?? 0,
          )}
          detail={t(
            "overview.launcherProfile",
            overview?.components.launcherActivities ?? 0,
          )}
        />
        {overview?.usesCleartextTraffic != null ? (
          <Signal
            icon={<Globe2 size={15} />}
            title={
              overview.usesCleartextTraffic
                ? t("overview.cleartextEnabled")
                : t("overview.cleartextDisabled")
            }
            detail={t("overview.cleartextDetail")}
            tone={overview.usesCleartextTraffic ? "danger" : "success"}
          />
        ) : null}
        {overview?.allowBackup != null ? (
          <Signal
            icon={<ArchiveRestore size={15} />}
            title={
              overview.allowBackup
                ? t("overview.backupEnabled")
                : t("overview.backupDisabled")
            }
            detail={t("overview.backupDetail")}
            tone={overview.allowBackup ? "neutral" : "success"}
          />
        ) : null}
        <Signal
          icon={<Fingerprint size={15} />}
          title={t("overview.permissionProfile", model.permissions.length)}
          detail={t(
            "overview.permissionProfileDetail",
            model.androidPermissionCount,
            model.applicationPermissionCount,
          )}
        />
      </div>
    </OverviewSection>
  );
}

function Signal({
  icon,
  title,
  detail,
  tone = "neutral",
}: {
  icon: React.ReactNode;
  title: string;
  detail: string;
  tone?: "neutral" | "danger" | "success";
}) {
  return (
    <div className={`overview-signal is-${tone}`}>
      <span className="overview-signal-icon">{icon}</span>
      <span>
        <strong>{title}</strong>
        <small>{detail}</small>
      </span>
    </div>
  );
}

function NativeSection({ overview }: { overview: ApkOverviewData | null }) {
  const { t } = useTranslation();
  return (
    <OverviewSection
      title={t("overview.nativeAbis")}
      trailing={
        <span className="overview-section-count">
          {(overview?.nativeLibraryCount ?? 0).toLocaleString()} {t("overview.files")}
        </span>
      }
    >
      {overview?.nativeAbis.length ? (
        <div className="overview-abi-list">
          {overview.nativeAbis.map((abi) => (
            <span key={abi}>{abi}</span>
          ))}
        </div>
      ) : (
        <div className="overview-empty-value">{t("overview.noNativeCode")}</div>
      )}
    </OverviewSection>
  );
}

function Definition({
  icon,
  label,
  value,
  mono = false,
  tone,
}: {
  icon: React.ReactNode;
  label: string;
  value: string | null | undefined;
  mono?: boolean;
  tone?: "danger" | "success";
}) {
  return (
    <div className="overview-definition">
      <span className="overview-definition-icon">{icon}</span>
      <dt>{label}</dt>
      <dd
        className={`${mono ? "is-mono" : ""} ${tone ? `is-${tone}` : ""}`}
        title={value ?? undefined}
      >
        {value ?? "—"}
      </dd>
    </div>
  );
}
