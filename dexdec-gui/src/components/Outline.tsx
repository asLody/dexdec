import {
  ArrowDownAZ,
  CircleDot,
  FileCode2,
  FunctionSquare,
  Search,
  X,
} from "lucide-react";
import { useEffect, useMemo, useRef, useState } from "react";

import { parametersOf, arityOf } from "../domain/descriptors";
import { useTranslation } from "../i18n";
import { hasPrimaryModifier, MOD_CLICK } from "../platform";
import type {
  ClassOutline,
  FieldOutline,
  MethodOutline,
} from "../domain/models";
import { useWorkspace, type CaretMember } from "../state/workspace";
import { EmptyState } from "./EmptyState";

export function Outline() {
  const documents = useWorkspace((state) => state.documents);
  const activeDescriptor = useWorkspace((state) => state.activeDescriptor);
  const navigateToMember = useWorkspace((state) => state.navigateToMember);
  const findReferences = useWorkspace((state) => state.findReferences);
  const caretMember = useWorkspace((state) => state.caretMember);
  const document = documents.find((item) => item.descriptor === activeDescriptor);

  const { t } = useTranslation();
  const [query, setQuery] = useState("");
  const [codeOnly, setCodeOnly] = useState(false);
  const [sortAZ, setSortAZ] = useState(false);

  return (
    <aside className="outline-panel flex min-h-0 min-w-0 flex-col overflow-hidden border-l border-[var(--border)] bg-[var(--panel)]">
      <div className="panel-header outline-toolbar">
        <div className="outline-search">
          <Search className="outline-search-icon" size={12} aria-hidden="true" />
          <input
            className="search-input outline-search-input"
            value={query}
            onChange={(event) => setQuery(event.target.value)}
            onKeyDown={(event) => {
              if (event.key === "Escape" && query) {
                event.preventDefault();
                setQuery("");
              }
            }}
            placeholder={t("outline.filter")}
            spellCheck={false}
            disabled={!document}
            aria-label={t("outline.filter")}
          />
          {query ? (
            <button
              type="button"
              title={t("outline.clearFilter")}
              aria-label={t("outline.clearFilter")}
              className="outline-search-clear"
              onClick={() => setQuery("")}
            >
              <X size={11} />
            </button>
          ) : null}
        </div>
        <div className="outline-tools">
          <button
            type="button"
            className={`outline-tool ${codeOnly ? "outline-tool-active" : ""}`}
            title={t("outline.hideNoCode")}
            aria-label={t("outline.hideNoCode")}
            aria-pressed={codeOnly}
            onClick={() => setCodeOnly((value) => !value)}
          >
            <FileCode2 size={13} />
          </button>
          <button
            type="button"
            className={`outline-tool ${sortAZ ? "outline-tool-active" : ""}`}
            title={sortAZ ? t("outline.declarationOrder") : t("outline.sortAZ")}
            aria-label={
              sortAZ ? t("outline.declarationOrder") : t("outline.sortAZ")
            }
            aria-pressed={sortAZ}
            onClick={() => setSortAZ((value) => !value)}
          >
            <ArrowDownAZ size={13} />
          </button>
        </div>
      </div>

      {document ? (
        <OutlineContent
          outline={document.outline}
          sourcePath={document.sourcePath}
          caretMember={caretMember}
          query={query}
          codeOnly={codeOnly}
          sortAZ={sortAZ}
          onField={(field) =>
            navigateToMember({
              classDescriptor: document.descriptor,
              kind: "field",
              name: field.originalName ?? field.name,
              descriptor: field.descriptor,
            })
          }
          onFindField={(field) =>
            void findReferences(
              {
                kind: "member",
                classDescriptor: document.descriptor,
                memberKind: "field",
                name: field.originalName ?? field.name,
                arity: null,
                descriptor: field.descriptor,
              },
              field.name,
            )
          }
          onMethod={(method) =>
            navigateToMember({
              classDescriptor: document.descriptor,
              kind: "method",
              name: method.originalName ?? method.name,
              descriptor: method.descriptor,
            })
          }
          onFindMethod={(method) =>
            void findReferences(
              {
                kind: "member",
                classDescriptor: document.descriptor,
                memberKind: "method",
                name: method.originalName ?? method.name,
                arity: arityOf(method.descriptor),
                descriptor: method.descriptor,
              },
              method.constructor ? "<init>" : method.name,
            )
          }
        />
      ) : (
        <EmptyState icon={<FileCode2 size={18} />} title={t("outline.noClass")} />
      )}
    </aside>
  );
}

function OutlineContent({
  outline,
  sourcePath,
  caretMember,
  query,
  codeOnly,
  sortAZ,
  onField,
  onFindField,
  onMethod,
  onFindMethod,
}: {
  outline: ClassOutline;
  sourcePath: string;
  caretMember: CaretMember | null;
  query: string;
  codeOnly: boolean;
  sortAZ: boolean;
  onField: (field: FieldOutline) => void;
  onFindField: (field: FieldOutline) => void;
  onMethod: (method: MethodOutline) => void;
  onFindMethod: (method: MethodOutline) => void;
}) {
  const { t } = useTranslation();
  const scrollRef = useRef<HTMLDivElement>(null);
  const [focusIndex, setFocusIndex] = useState(0);

  const normalized = query.trim().toLocaleLowerCase();
  const fields = useMemo(() => {
    let list = outline.fields;
    if (normalized) {
      list = list.filter((field) =>
        field.name.toLocaleLowerCase().includes(normalized),
      );
    }
    if (sortAZ) {
      list = [...list].sort((left, right) => left.name.localeCompare(right.name));
    }
    return list;
  }, [normalized, outline.fields, sortAZ]);

  const methods = useMemo(() => {
    let list = outline.methods;
    if (codeOnly) {
      list = list.filter((method) => method.hasCode);
    }
    if (normalized) {
      list = list.filter((method) =>
        (method.constructor ? "<init>" : method.name)
          .toLocaleLowerCase()
          .includes(normalized),
      );
    }
    if (sortAZ) {
      list = [...list].sort((left, right) =>
        (left.constructor ? "<init>" : left.name).localeCompare(
          right.constructor ? "<init>" : right.name,
        ),
      );
    }
    return list;
  }, [codeOnly, normalized, outline.methods, sortAZ]);
  const memberCount = fields.length + methods.length;

  useEffect(() => {
    setFocusIndex((index) => Math.max(0, Math.min(memberCount - 1, index)));
  }, [memberCount]);

  const moveFocus = (index: number) => {
    const next = Math.max(0, Math.min(memberCount - 1, index));
    setFocusIndex(next);
    scrollRef.current
      ?.querySelector(`#outline-member-${next}`)
      ?.scrollIntoView({ block: "nearest" });
  };

  const openFocused = () => {
    if (focusIndex < fields.length) onField(fields[focusIndex]);
    else if (methods[focusIndex - fields.length]) onMethod(methods[focusIndex - fields.length]);
  };

  const onKeyDown = (event: React.KeyboardEvent) => {
    if (!memberCount) return;
    if (event.key === "ArrowDown" || event.key === "ArrowUp") {
      event.preventDefault();
      moveFocus(focusIndex + (event.key === "ArrowDown" ? 1 : -1));
    } else if (event.key === "Home" || event.key === "End") {
      event.preventDefault();
      moveFocus(event.key === "Home" ? 0 : memberCount - 1);
    } else if (event.key === "Enter") {
      event.preventDefault();
      openFocused();
    }
  };

  const isCurrent = (
    kind: "field" | "method",
    name: string,
    descriptor: string,
  ) => {
    if (!caretMember || caretMember.kind !== kind || caretMember.name !== name) {
      return false;
    }
    if (kind === "field" || name === "<clinit>") {
      return true;
    }
    return arityOf(descriptor) === caretMember.arity;
  };

  useEffect(() => {
    if (!caretMember) {
      return;
    }
    scrollRef.current
      ?.querySelector('[data-caret-current="true"]')
      ?.scrollIntoView({ block: "nearest" });
  }, [caretMember]);

  const filtering = Boolean(normalized) || codeOnly;
  const packageName =
    outline.qualifiedName.split(".").slice(0, -1).join(".") || "<default>";
  const simpleName =
    outline.qualifiedName.split(".").at(-1) ?? outline.qualifiedName;

  return (
    <div
      ref={scrollRef}
      className="outline-body outline-none"
      tabIndex={0}
      aria-label={t("outline.members")}
      aria-activedescendant={memberCount ? `outline-member-${focusIndex}` : undefined}
      onKeyDown={onKeyDown}
    >
      <header
        className="outline-identity"
        title={`${outline.qualifiedName}\n${sourcePath}`}
      >
        <div className="outline-identity-name">{simpleName}</div>
        <div className="outline-identity-package">{packageName}</div>
      </header>

      {fields.length ? (
        <OutlineSection
          title={t("outline.fields")}
          count={
            filtering ? `${fields.length}/${outline.fields.length}` : fields.length
          }
        >
          {fields.map((field, index) => (
            <FieldRow
              key={`${field.name}:${field.descriptor}`}
              field={field}
              current={isCurrent("field", field.name, field.descriptor)}
              id={`outline-member-${index}`}
              focused={focusIndex === index}
              onClick={() => {
                setFocusIndex(index);
                onField(field);
              }}
              onFind={() => onFindField(field)}
            />
          ))}
        </OutlineSection>
      ) : null}

      {methods.length ? (
        <OutlineSection
          title={t("outline.methods")}
          count={
            filtering
              ? `${methods.length}/${outline.methods.length}`
              : methods.length
          }
        >
          {methods.map((method, index) => {
            const memberIndex = fields.length + index;
            return (
            <MethodRow
              key={`${method.name}${method.descriptor}`}
              method={method}
              current={isCurrent("method", method.name, method.descriptor)}
              id={`outline-member-${memberIndex}`}
              focused={focusIndex === memberIndex}
              onClick={() => {
                setFocusIndex(memberIndex);
                onMethod(method);
              }}
              onFind={() => onFindMethod(method)}
            />
            );
          })}
        </OutlineSection>
      ) : null}

      {filtering && !fields.length && !methods.length ? (
        <EmptyState compact icon={<Search size={16} />} title={t("outline.noMatch")} />
      ) : null}
    </div>
  );
}

function OutlineSection({
  title,
  count,
  children,
}: {
  title: string;
  count: number | string;
  children: React.ReactNode;
}) {
  return (
    <section className="outline-section">
      <div className="outline-section-title">
        <span>{title}</span>
        <span className="outline-section-count">{count}</span>
      </div>
      <div className="outline-section-list">{children}</div>
    </section>
  );
}

function FieldRow({
  field,
  current,
  id,
  focused,
  onClick,
  onFind,
}: {
  field: FieldOutline;
  current: boolean;
  id: string;
  focused: boolean;
  onClick: () => void;
  onFind: () => void;
}) {
  const flags = memberFlags(field.accessFlags);
  return (
    <button
      id={id}
      type="button"
      tabIndex={-1}
      className={`outline-row ${current ? "outline-row-current" : ""} ${focused ? "is-focused" : ""}`}
      data-caret-current={current || undefined}
      title={`${flags.visibility}${flags.static ? " static" : ""} ${field.displayType} ${field.name}`}
      onClick={(event) => {
        if (hasPrimaryModifier(event)) onFind();
        else onClick();
      }}
    >
      <CircleDot
        size={11}
        className="outline-row-icon is-field"
        aria-hidden="true"
      />
      <span className="outline-row-main">
        <span className="outline-row-name">{field.name}</span>
        <span className="outline-row-sig">: {field.displayType}</span>
      </span>
      {flags.static ? <span className="outline-row-tag">static</span> : null}
    </button>
  );
}

function MethodRow({
  method,
  current,
  id,
  focused,
  onClick,
  onFind,
}: {
  method: MethodOutline;
  current: boolean;
  id: string;
  focused: boolean;
  onClick: () => void;
  onFind: () => void;
}) {
  const { t } = useTranslation();
  const flags = memberFlags(method.accessFlags);
  const name = method.constructor ? "<init>" : method.name;
  const params = parametersOf(method.descriptor);
  const noCodeTag =
    !method.hasCode
      ? flags.native
        ? "native"
        : flags.abstract
          ? "abstract"
          : "no-code"
      : null;

  return (
    <button
      id={id}
      type="button"
      tabIndex={-1}
      className={`outline-row ${current ? "outline-row-current" : ""} ${
        method.hasCode ? "" : "is-no-code"
      } ${focused ? "is-focused" : ""}`}
      data-caret-current={current || undefined}
      title={`${method.displaySignature}\n${t("editor.findReferences")} (${MOD_CLICK})`}
      onClick={(event) => {
        if (hasPrimaryModifier(event)) onFind();
        else onClick();
      }}
    >
      <FunctionSquare
        size={12}
        className={`outline-row-icon is-method ${
          method.hasCode ? "" : "is-muted"
        }`}
        aria-hidden="true"
      />
      <span className="outline-row-main">
        <span className="outline-row-name">{name}</span>
        <span className="outline-row-sig">{params}</span>
      </span>
      <span className="outline-row-tags">
        {flags.static ? <span className="outline-row-tag">static</span> : null}
        {noCodeTag ? (
          <span className="outline-row-tag is-muted">{noCodeTag}</span>
        ) : null}
      </span>
    </button>
  );
}

function visibility(flags: number): string {
  if (flags & 0x0001) return "public";
  if (flags & 0x0002) return "private";
  if (flags & 0x0004) return "protected";
  return "package";
}

function memberFlags(flags: number): {
  visibility: string;
  static: boolean;
  abstract: boolean;
  native: boolean;
} {
  return {
    visibility: visibility(flags),
    static: (flags & 0x0008) !== 0,
    abstract: (flags & 0x0400) !== 0,
    native: (flags & 0x0100) !== 0,
  };
}
