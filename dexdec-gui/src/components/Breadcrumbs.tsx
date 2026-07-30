import { ChevronRight, CircleDot, FunctionSquare, Package } from "lucide-react";
import { useMemo } from "react";

import { arityOf, parametersOf } from "../domain/descriptors";
import type { EditorGroup } from "../domain/editorLayout";
import type { ClassOutline } from "../domain/models";
import { useTranslation } from "../i18n";
import { sc } from "../platform";
import { useWorkspace, type CaretMember } from "../state/workspace";

interface ResolvedMember {
  kind: "field" | "method";
  /** Canonical DEX name used by navigation. */
  name: string;
  displayName: string;
  descriptor: string;
  /** Parameter list for methods, empty for fields. */
  params: string;
  title: string;
}

/*
 * Path bar under the tab strip: package › enclosing classes › member at the
 * caret. Every segment is a jump — the outer classes open, the class segment
 * opens the member palette, the member scrolls back to its declaration.
 */
export function Breadcrumbs({ group }: { group: EditorGroup }) {
  const archive = useWorkspace((state) => state.archive);
  const documents = useWorkspace((state) => state.documents);
  const editorLayout = useWorkspace((state) => state.editorLayout);
  const caretMember = useWorkspace((state) =>
    state.editorLayout.focused === group ? state.caretMember : null,
  );
  const selectClass = useWorkspace((state) => state.selectClass);
  const revealInExplorer = useWorkspace((state) => state.revealInExplorer);
  const navigateToMember = useWorkspace((state) => state.navigateToMember);
  const setMemberOpenVisible = useWorkspace((state) => state.setMemberOpenVisible);
  const focusEditorGroup = useWorkspace((state) => state.focusEditorGroup);
  const { t } = useTranslation();

  const document =
    documents.find((item) => item.descriptor === editorLayout.active[group]) ?? null;

  const member = useMemo(
    () => resolveMember(document?.outline ?? null, caretMember),
    [caretMember, document?.outline],
  );

  const chain = useMemo(
    () => classChain(document?.descriptor ?? ""),
    [document?.descriptor],
  );

  if (!document) {
    return null;
  }

  const qualified = document.outline.qualifiedName;
  const dot = qualified.lastIndexOf(".");
  const packageName = dot > 0 ? qualified.slice(0, dot) : "";

  return (
    <nav className="breadcrumbs" aria-label={t("breadcrumb.aria")}>
      {packageName ? (
        <>
          <button
            type="button"
            className="breadcrumb-item is-package"
            title={`${packageName}\n${t("tabs.revealInExplorer")}`}
            onClick={() => revealInExplorer(document.descriptor)}
          >
            <Package size={11} aria-hidden="true" />
            <span>{packageName}</span>
          </button>
          <ChevronRight className="breadcrumb-sep" size={11} aria-hidden="true" />
        </>
      ) : null}

      {chain.map((entry, index) => {
        const last = index === chain.length - 1;
        const known =
          !last && archive?.classes.some((item) => item.descriptor === entry.descriptor);
        return (
          <span className="breadcrumb-cell" key={entry.descriptor}>
            <button
              type="button"
              className={`breadcrumb-item ${last ? "is-current" : ""}`}
              disabled={!last && !known}
              title={
                last
                  ? `${qualified}\n${t("breadcrumb.goToMember", sc("mod+f12"))}`
                  : t("breadcrumb.openClass", entry.name)
              }
              onClick={() => {
                if (last) {
                  focusEditorGroup(group);
                  setMemberOpenVisible(true);
                } else {
                  void selectClass(entry.descriptor, { group });
                }
              }}
            >
              <span>{entry.name}</span>
            </button>
            {last && !member ? null : (
              <ChevronRight className="breadcrumb-sep" size={11} aria-hidden="true" />
            )}
          </span>
        );
      })}

      {member ? (
        <button
          type="button"
          className="breadcrumb-item is-member"
          title={`${member.title}\n${t("breadcrumb.jumpToDeclaration")}`}
          onClick={() => {
            focusEditorGroup(group);
            navigateToMember({
              classDescriptor: document.descriptor,
              kind: member.kind,
              name: member.name,
              descriptor: member.descriptor,
            });
          }}
        >
          {member.kind === "method" ? (
            <FunctionSquare
              size={11}
              className="breadcrumb-icon is-method"
              aria-hidden="true"
            />
          ) : (
            <CircleDot
              size={11}
              className="breadcrumb-icon is-field"
              aria-hidden="true"
            />
          )}
          <span>{member.displayName}</span>
          {member.params ? (
            <span className="breadcrumb-params">{member.params}</span>
          ) : null}
        </button>
      ) : null}
    </nav>
  );
}

/*
 * Splits `Lorg/example/Outer$Inner;` into the enclosing class chain, keeping a
 * loadable descriptor for each link so outer classes stay one click away.
 */
function classChain(
  descriptor: string,
): { name: string; descriptor: string }[] {
  const internal = descriptor.replace(/^L|;$/g, "");
  if (!internal) {
    return [];
  }
  const slash = internal.lastIndexOf("/");
  const prefix = slash < 0 ? "" : internal.slice(0, slash + 1);
  const parts = internal.slice(slash + 1).split("$");
  return parts.map((name, index) => ({
    name,
    descriptor: `L${prefix}${parts.slice(0, index + 1).join("$")};`,
  }));
}

/** Matches the caret's member against the outline, mirroring the outline rows. */
function resolveMember(
  outline: ClassOutline | null,
  caret: CaretMember | null,
): ResolvedMember | null {
  if (!outline || !caret) {
    return null;
  }
  if (caret.kind === "field") {
    const field = outline.fields.find((entry) => entry.name === caret.name);
    return field
      ? {
          kind: "field",
          name: field.originalName ?? field.name,
          displayName: field.name,
          descriptor: field.descriptor,
          params: "",
          title: `${field.displayType} ${field.name}`,
        }
      : null;
  }
  const candidates = outline.methods.filter((entry) => entry.name === caret.name);
  const method =
    candidates.length === 1
      ? candidates[0]
      : (candidates.find((entry) => arityOf(entry.descriptor) === caret.arity) ??
        candidates[0]);
  return method
    ? {
        kind: "method",
        name: method.originalName ?? method.name,
        displayName: method.name,
        descriptor: method.descriptor,
        params: parametersOf(method.descriptor),
        title: method.displaySignature,
      }
    : null;
}
