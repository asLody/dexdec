import type { EditorState } from "@codemirror/state";
import { javaLanguage } from "@codemirror/lang-java";
import type { SyntaxNode, Tree } from "@lezer/common";

import type { MemberNavigation } from "./models";
import type { SourceDefinitionResolver } from "./sourceDefinitionResolver";

export interface SourceRange {
  from: number;
  to: number;
}

/** Identifies the member enclosing a document offset, for caret sync. */
export interface MemberAtOffset {
  kind: "field" | "method";
  name: string;
  arity: number | null;
}

const TYPE_BODY_NAMES = new Set([
  "ClassBody",
  "InterfaceBody",
  "EnumBody",
  "AnnotationTypeBody",
]);

const MEMBER_DECLARATIONS = new Set([
  "FieldDeclaration",
  "MethodDeclaration",
  "ConstructorDeclaration",
  "StaticInitializer",
]);

export class JavaSourceIndex {
  private static readonly trees = new WeakMap<object, Tree>();

  static locate(
    state: EditorState,
    target: MemberNavigation,
    resolver: SourceDefinitionResolver,
  ): SourceRange | null {
    const tree = this.tree(state);
    const typeBody = this.firstTypeBody(tree.topNode);
    if (!typeBody) {
      return null;
    }

    const desiredParameters =
      target.kind === "method"
        ? JvmMethodDescriptor.parameters(target.descriptor)
        : null;
    const candidates: MethodSourceCandidate[] = [];
    let fieldMatch: SourceRange | null = null;
    tree.iterate({
      enter: (cursor) => {
        if (fieldMatch || !this.belongsTo(typeBody, cursor.node)) {
          return;
        }
        const declaration = cursor.node;
        if (target.kind === "field" && declaration.name === "FieldDeclaration") {
          for (const definition of this.definitions(state, declaration)) {
            const destination = resolver.resolve(state, definition.from)?.destination;
            if (
              (destination?.kind === "member" &&
                destination.memberKind === "field" &&
                destination.classDescriptor === target.classDescriptor &&
                destination.name === target.name &&
                destination.descriptor === target.descriptor) ||
              ((destination?.kind !== "member" || !destination.descriptor) &&
                this.text(state, definition) === target.name)
            ) {
              fieldMatch = this.range(definition);
              break;
            }
          }
          return false;
        }
        if (target.kind !== "method") {
          return;
        }
        if (target.name === "<clinit>" && declaration.name === "StaticInitializer") {
          candidates.push({
            range: this.range(declaration),
            name: "<clinit>",
            parameters: [],
            descriptor: null,
          });
          return false;
        }
        const declarationKind =
          target.name === "<init>" ? "ConstructorDeclaration" : "MethodDeclaration";
        if (declaration.name !== declarationKind) {
          return;
        }
        const definition = declaration.getChild("Definition");
        const destination = definition
          ? resolver.resolve(state, definition.from)?.destination
          : null;
        if (
          definition &&
          (target.name === "<init>" ||
            this.text(state, definition) === target.name ||
            (destination?.kind === "member" &&
              destination.name === target.name &&
              destination.descriptor === target.descriptor)) &&
          this.parameterCount(declaration) === desiredParameters?.length
        ) {
          candidates.push({
            range: this.range(definition),
            descriptor:
              destination?.kind === "member"
                ? destination.descriptor ?? null
                : null,
            name:
              destination?.kind === "member"
                ? destination.name
                : null,
            parameters:
              destination?.kind === "member" &&
              destination.memberKind === "method"
                ? destination.parameterDescriptors ?? null
                : null,
          });
        }
        return false;
      },
    });
    if (target.kind === "field") {
      return fieldMatch;
    }
    if (!desiredParameters) {
      return null;
    }
    const exact = candidates.filter(
      (candidate) =>
        candidate.name === target.name &&
        candidate.descriptor === target.descriptor,
    );
    if (exact.length === 1) {
      return exact[0].range;
    }
    const constrained = candidates.filter(
      (candidate) =>
        candidate.parameters?.length === desiredParameters.length &&
        candidate.parameters.every(
          (parameter, index) =>
            parameter === null || parameter === desiredParameters[index],
        ),
    );
    if (constrained.length === 1) {
      return constrained[0].range;
    }
    return candidates.length === 1 ? candidates[0].range : null;
  }

  /**
   * Finds the top-level member whose declaration range contains `offset`.
   * Used to highlight the outline row for the current caret position.
   */
  static memberAtOffset(state: EditorState, offset: number): MemberAtOffset | null {
    const typeBody = this.firstTypeBody(this.tree(state).topNode);
    if (!typeBody) {
      return null;
    }
    for (let member = typeBody.firstChild; member; member = member.nextSibling) {
      if (!MEMBER_DECLARATIONS.has(member.name)) {
        continue;
      }
      if (offset < member.from || offset > member.to) {
        continue;
      }
      if (member.name === "FieldDeclaration") {
        // `long b, c;` — pick the declared variable under the caret.
        let fallback: string | null = null;
        const stack: SyntaxNode[] = [member];
        while (stack.length) {
          const node = stack.pop()!;
          if (node.name === "Definition") {
            const text = this.text(state, node);
            fallback ??= text;
            if (offset >= node.from && offset <= node.to) {
              return { kind: "field", name: text, arity: null };
            }
          }
          for (let child = node.firstChild; child; child = child.nextSibling) {
            stack.push(child);
          }
        }
        return fallback ? { kind: "field", name: fallback, arity: null } : null;
      }
      if (member.name === "StaticInitializer") {
        return { kind: "method", name: "<clinit>", arity: 0 };
      }
      if (member.name === "ConstructorDeclaration") {
        return { kind: "method", name: "<init>", arity: this.parameterCount(member) };
      }
      const definition = member.getChild("Definition");
      if (!definition) {
        return null;
      }
      return {
        kind: "method",
        name: this.text(state, definition),
        arity: this.parameterCount(member),
      };
    }
    return null;
  }

  private static firstTypeBody(root: SyntaxNode): SyntaxNode | null {
    let body: SyntaxNode | null = null;
    const visit = (node: SyntaxNode): void => {
      if (body) return;
      if (TYPE_BODY_NAMES.has(node.name)) {
        body = node;
        return;
      }
      for (let child = node.firstChild; child; child = child.nextSibling) {
        visit(child);
      }
    };
    visit(root);
    return body;
  }

  private static tree(state: EditorState): Tree {
    const document = state.doc as object;
    let tree = this.trees.get(document);
    if (!tree) {
      tree = javaLanguage.parser.parse(state.doc.toString());
      this.trees.set(document, tree);
    }
    return tree;
  }

  private static belongsTo(typeBody: SyntaxNode, node: SyntaxNode): boolean {
    for (let parent = node.parent; parent; parent = parent.parent) {
      if (TYPE_BODY_NAMES.has(parent.name)) {
        return (
          parent.name === typeBody.name &&
          parent.from === typeBody.from &&
          parent.to === typeBody.to
        );
      }
    }
    return false;
  }

  private static definitions(
    state: EditorState,
    declaration: SyntaxNode,
  ): SyntaxNode[] {
    const definitions: SyntaxNode[] = [];
    const stack = [declaration];
    while (stack.length) {
      const node = stack.pop()!;
      if (node.name === "Definition") {
        definitions.push(node);
      }
      for (let child = node.lastChild; child; child = child.prevSibling) {
        stack.push(child);
      }
    }
    return definitions;
  }

  private static parameterCount(declaration: SyntaxNode): number {
    const parameters = declaration.getChild("FormalParameters");
    if (!parameters) {
      return 0;
    }
    let count = 0;
    const stack = [parameters];
    while (stack.length) {
      const node = stack.pop()!;
      if (node.name === "FormalParameter" || node.name === "SpreadParameter") {
        count += 1;
        continue;
      }
      for (let child = node.lastChild; child; child = child.prevSibling) {
        stack.push(child);
      }
    }
    return count;
  }

  private static text(state: EditorState, node: SyntaxNode): string {
    return state.doc.sliceString(node.from, node.to);
  }

  private static range(node: SyntaxNode): SourceRange {
    return { from: node.from, to: node.to };
  }
}

interface MethodSourceCandidate {
  range: SourceRange;
  name: string | null;
  descriptor: string | null;
  parameters: (string | null)[] | null;
}

class JvmMethodDescriptor {
  static parameters(descriptor: string): string[] | null {
    if (!descriptor.startsWith("(")) {
      return null;
    }
    let index = 1;
    const parameters: string[] = [];
    while (index < descriptor.length && descriptor[index] !== ")") {
      const start = index;
      while (descriptor[index] === "[") index += 1;
      if (descriptor[index] === "L") {
        const end = descriptor.indexOf(";", index);
        if (end < 0) return null;
        index = end + 1;
      } else {
        index += 1;
      }
      parameters.push(descriptor.slice(start, index));
    }
    return descriptor[index] === ")" ? parameters : null;
  }
}
