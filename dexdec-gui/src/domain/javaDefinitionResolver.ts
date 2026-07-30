import type { EditorState } from "@codemirror/state";
import { javaLanguage } from "@codemirror/lang-java";
import type { SyntaxNode, Tree } from "@lezer/common";

import type {
  Archive,
  ClassSummary,
  SourceDocument,
  SymbolDestination,
} from "./models";
import type {
  ResolvedSymbol,
  SourceDefinitionResolver,
} from "./sourceDefinitionResolver";

export type { ResolvedSymbol } from "./sourceDefinitionResolver";

interface ClassIdentity {
  descriptor: string;
  qualifiedName: string;
  package: string;
  binaryName: string;
  displayName: string;
}

const TYPE_NODES = new Set([
  "PrimitiveType",
  "TypeName",
  "ScopedTypeName",
  "GenericType",
  "ArrayType",
]);

const VALUE_DECLARATIONS = new Set([
  "FormalParameter",
  "SpreadParameter",
  "CatchFormalParameter",
  "VariableDeclarator",
]);

const TYPE_DECLARATIONS = new Set([
  "ClassDeclaration",
  "InterfaceDeclaration",
  "EnumDeclaration",
  "AnnotationTypeDeclaration",
]);

const SYMBOL_NODES = new Set([
  "Definition",
  "Identifier",
  "Label",
  "TypeName",
]);

/**
 * Resolves Java identifiers against lexical declarations and the archive
 * catalog. It deliberately returns candidates rather than selecting overloads;
 * the workspace validates members against DEX outlines before navigating.
 */
export class JavaDefinitionResolver implements SourceDefinitionResolver {
  private readonly classDescriptors: Set<string>;
  private readonly classesByName = new Map<string, ClassSummary[]>();
  private readonly importedClasses = new Map<string, ClassIdentity>();
  private readonly tree: Tree;
  private readonly localsByScope = new Map<
    string,
    Map<string, { definition: SyntaxNode; binding: SyntaxNode; depth: number }[]>
  >();
  private readonly fieldsByClass = new Map<
    string,
    Map<string, { owner: ClassIdentity; type: string }>
  >();
  private resolvedSymbols: ResolvedSymbol[] | null = null;

  constructor(
    private readonly document: SourceDocument,
    private readonly archive: Archive,
  ) {
    this.classDescriptors = new Set(archive.classes.map((candidate) => candidate.descriptor));
    this.tree = javaLanguage.parser.parse(document.source);
    for (const candidate of archive.classes) {
      for (const alias of JavaDefinitionResolver.classAliases(candidate)) {
        const matches = this.classesByName.get(alias) ?? [];
        matches.push(candidate);
        this.classesByName.set(alias, matches);
      }
    }
    for (const imported of this.imports(document.source)) {
      const match =
        this.uniqueClass(imported) ??
        JavaDefinitionResolver.externalClass(imported);
      if (match) {
        this.importedClasses.set(imported.split(".").pop()!, match);
      }
    }
  }

  resolve(state: EditorState, offset: number): ResolvedSymbol | null {
    const indexed = this.indexedSymbolAt(offset);
    if (indexed) {
      return indexed;
    }
    const identifier = this.identifierAt(state, offset);
    if (!identifier) {
      return null;
    }
    const range = { from: identifier.from, to: identifier.to };
    const name = this.text(state, identifier);

    const definition = this.definitionNode(identifier);
    if (definition) {
      const destination = this.declarationDestination(state, definition, range);
      if (destination) {
        return { range, destination };
      }
    }

    if (identifier.name === "Label") {
      const destination = this.labelDestination(state, identifier);
      return destination ? { range, destination } : null;
    }

    const methodName = this.ancestor(identifier, "MethodName");
    if (methodName) {
      const invocation = this.ancestor(methodName, "MethodInvocation");
      if (!invocation) {
        return null;
      }
      const owner = this.receiverClass(state, invocation, methodName);
      const argumentNodes = this.argumentNodes(invocation);
      return owner
        ? {
            range,
            destination: {
              kind: "member",
              classDescriptor: owner.descriptor,
              memberKind: "method",
              name,
              arity: argumentNodes.length,
              parameterDescriptors: argumentNodes.map((argument) =>
                this.argumentDescriptor(state, argument),
              ),
            },
          }
        : null;
    }

    const type = this.typeContaining(identifier);
    if (type) {
      const target = this.resolveClass(this.text(state, type));
      return target
        ? {
            range,
            destination: {
              kind: "class",
              classDescriptor: target.descriptor,
            },
          }
        : null;
    }

    const fieldAccess = this.ancestor(identifier, "FieldAccess");
    if (fieldAccess && this.isAccessMember(fieldAccess, identifier)) {
      const owner = this.receiverClass(state, fieldAccess, identifier);
      return owner
        ? {
            range,
            destination: {
              kind: "member",
              classDescriptor: owner.descriptor,
              memberKind: "field",
              name,
              arity: null,
            },
          }
        : null;
    }

    const local = this.localDefinition(state, identifier, name);
    if (local) {
      return {
        range,
        destination: { kind: "local", from: local.from, to: local.to },
      };
    }

    const currentField = this.fieldBinding(state, identifier, name);
    if (currentField) {
      return {
        range,
        destination: {
          kind: "member",
          classDescriptor: currentField.owner.descriptor,
          memberKind: "field",
          name,
          arity: null,
        },
      };
    }

    const classTarget = this.resolveClass(name);
    return classTarget
      ? {
          range,
          destination: {
            kind: "class",
            classDescriptor: classTarget.descriptor,
          },
        }
      : null;
  }

  /** Resolve a usage target from the exact syntax node under the caret. */
  resolveReferenceTarget(
    state: EditorState,
    offset: number,
  ): ResolvedSymbol | null {
    const symbol = this.resolve(state, offset);
    return symbol && this.isNavigable(symbol.destination) ? symbol : null;
  }

  isDeclaration(state: EditorState, symbol: ResolvedSymbol): boolean {
    if (symbol.destination.kind === "local") {
      return symbol.range.from === symbol.destination.from &&
        symbol.range.to === symbol.destination.to;
    }
    const identifier = this.identifierAt(state, symbol.range.from);
    return identifier != null && this.definitionNode(identifier) != null;
  }

  isNavigable(destination: SymbolDestination): boolean {
    return destination.kind === "local" ||
      this.classDescriptors.has(destination.classDescriptor);
  }

  /** Returns one semantic identity per source token in document order. */
  symbols(state: EditorState): ResolvedSymbol[] {
    if (this.resolvedSymbols) {
      return this.resolvedSymbols;
    }
    const resolved: ResolvedSymbol[] = [];
    const seen = new Set<string>();
    this.tree.iterate({
      enter: (cursor) => {
        if (!SYMBOL_NODES.has(cursor.name)) {
          return;
        }
        const symbol = this.resolve(state, cursor.from);
        if (
          !symbol ||
          symbol.range.from !== cursor.from ||
          symbol.range.to !== cursor.to
        ) {
          return;
        }
        const key = `${symbol.range.from}:${symbol.range.to}`;
        if (!seen.has(key)) {
          seen.add(key);
          resolved.push(symbol);
        }
      },
    });
    this.resolvedSymbols = resolved;
    return resolved;
  }

  /** Stable lexical identity used for local variables, parameters, and labels. */
  localOrdinal(
    state: EditorState,
    destination: Extract<SymbolDestination, { kind: "local" }>,
  ): number | null {
    let ordinal = 0;
    for (const symbol of this.symbols(state)) {
      if (
        symbol.destination.kind !== "local" ||
        symbol.range.from !== symbol.destination.from ||
        symbol.range.to !== symbol.destination.to
      ) {
        continue;
      }
      if (
        symbol.destination.from === destination.from &&
        symbol.destination.to === destination.to
      ) {
        return ordinal;
      }
      ordinal += 1;
    }
    return null;
  }

  localKind(
    state: EditorState,
    destination: Extract<SymbolDestination, { kind: "local" }>,
  ): "local" | "label" {
    return this.nodeAtRange(state, destination.from, destination.to)?.name === "Label"
      ? "label"
      : "local";
  }

  localBindingRange(
    state: EditorState,
    destination: Extract<SymbolDestination, { kind: "local" }>,
  ): { from: number; to: number } | null {
    const declaration = this.nodeAtRange(
      state,
      destination.from,
      destination.to,
    );
    if (!declaration) {
      return null;
    }
    const scope =
      declaration.name === "Label"
        ? declaration.parent
        : this.bindingScope(declaration);
    return scope ? { from: scope.from, to: scope.to } : null;
  }

  private identifierAt(state: EditorState, offset: number): SyntaxNode | null {
    const tree = this.tree;
    const positions = offset > 0 ? [offset, offset - 1] : [offset];
    for (const position of positions) {
      for (const side of [-1, 1] as const) {
        let node: SyntaxNode | null = tree.resolveInner(position, side);
        while (
          node &&
          node.name !== "Identifier" &&
          node.name !== "TypeName" &&
          node.name !== "Definition" &&
          node.name !== "Label"
        ) {
          node = node.parent;
        }
        if (
          node &&
          offset >= node.from &&
          offset <= node.to
        ) {
          return node;
        }
      }
    }
    return null;
  }

  private nodeAtRange(
    state: EditorState,
    from: number,
    to: number,
  ): SyntaxNode | null {
    let node: SyntaxNode | null = this.tree.resolveInner(from, 1);
    while (node) {
      if (
        node.from === from &&
        node.to === to &&
        SYMBOL_NODES.has(node.name)
      ) {
        return node;
      }
      node = node.parent;
    }
    return null;
  }

  private indexedSymbolAt(offset: number): ResolvedSymbol | null {
    const spans = this.document.symbolSpans;
    if (!spans?.length) {
      return null;
    }
    let low = 0;
    let high = spans.length - 1;
    while (low <= high) {
      const middle = (low + high) >>> 1;
      const span = spans[middle];
      if (offset < span.from) {
        high = middle - 1;
      } else if (offset > span.to) {
        low = middle + 1;
      } else {
        return {
          range: { from: span.from, to: span.to },
          destination: span.destination,
        };
      }
    }
    return null;
  }

  private labelDestination(
    state: EditorState,
    reference: SyntaxNode,
  ): Extract<SymbolDestination, { kind: "local" }> | null {
    if (reference.parent?.name === "LabeledStatement") {
      return { kind: "local", from: reference.from, to: reference.to };
    }
    const name = this.text(state, reference);
    const scope =
      this.ancestor(reference, "MethodDeclaration") ??
      this.ancestor(reference, "ConstructorDeclaration") ??
      this.ancestor(reference, "StaticInitializer");
    if (!scope) {
      return null;
    }
    const candidates: SyntaxNode[] = [];
    this.walk(scope, (node) => {
      if (
        node.name === "Label" &&
        node.parent?.name === "LabeledStatement" &&
        node.parent.from <= reference.from &&
        node.parent.to >= reference.to &&
        this.text(state, node) === name
      ) {
        candidates.push(node);
      }
    });
    candidates.sort(
      (left, right) =>
        (left.parent!.to - left.parent!.from) -
          (right.parent!.to - right.parent!.from) ||
        right.from - left.from,
    );
    const declaration = candidates[0];
    return declaration
      ? { kind: "local", from: declaration.from, to: declaration.to }
      : null;
  }

  private receiverClass(
    state: EditorState,
    expression: SyntaxNode,
    member: SyntaxNode,
  ): ClassIdentity | null {
    const receiver = expression.firstChild;
    if (!receiver || receiver.from >= member.from) {
      return this.enclosingClass(state, expression);
    }
    if (receiver.name === "this" || receiver.name === "super") {
      return this.enclosingClass(state, expression);
    }

    const receiverText = this.text(state, receiver);
    if (receiver.name === "Identifier") {
      const definition = this.localDefinition(
        state,
        receiver,
        receiverText,
      );
      const declaredType = definition
        ? this.declaredType(state, definition)
        : this.fieldBinding(state, receiver, receiverText)?.type;
      const boundClass = declaredType ? this.resolveClass(declaredType) : null;
      if (boundClass) {
        return boundClass;
      }
    }
    return this.resolveClass(receiverText);
  }

  private fieldBinding(
    state: EditorState,
    reference: SyntaxNode,
    name: string,
  ): { owner: ClassIdentity; type: string } | null {
    const declaration = this.enclosingTypeDeclaration(reference);
    const owner = declaration
      ? this.classForDeclaration(state, declaration)
      : this.rootClass();
    if (!owner) {
      return null;
    }
    if (declaration) {
      const key = `${declaration.from}:${declaration.to}`;
      let fields = this.fieldsByClass.get(key);
      if (!fields) {
        fields = this.indexFields(state, declaration, owner);
        this.fieldsByClass.set(key, fields);
      }
      return fields.get(name) ?? null;
    }
    if (owner.descriptor !== this.document.descriptor) {
      return null;
    }
    const field = this.document.outline.fields.find(
      (candidate) => candidate.name === name,
    );
    return field ? { owner, type: field.displayType } : null;
  }

  private localDefinition(
    state: EditorState,
    reference: SyntaxNode,
    name: string,
  ): SyntaxNode | null {
    const scope =
      this.ancestor(reference, "MethodDeclaration") ??
      this.ancestor(reference, "ConstructorDeclaration") ??
      this.ancestor(reference, "StaticInitializer");
    if (!scope) {
      return null;
    }
    const scopeKey = `${scope.from}:${scope.to}`;
    let byName = this.localsByScope.get(scopeKey);
    if (!byName) {
      byName = this.indexLocals(state, scope);
      this.localsByScope.set(scopeKey, byName);
    }
    const candidates = (byName.get(name) ?? []).filter(
      (candidate) =>
        candidate.definition.from <= reference.from &&
        candidate.binding.from <= reference.from &&
        candidate.binding.to >= reference.to,
    );
    candidates.sort(
      (left, right) =>
        right.depth - left.depth ||
        right.definition.from - left.definition.from,
    );
    return candidates[0]?.definition ?? null;
  }

  private indexLocals(
    state: EditorState,
    scope: SyntaxNode,
  ): Map<string, { definition: SyntaxNode; binding: SyntaxNode; depth: number }[]> {
    const byName = new Map<
      string,
      { definition: SyntaxNode; binding: SyntaxNode; depth: number }[]
    >();
    this.walk(scope, (node) => {
      if (node.name !== "Definition" || !this.isLocalDefinition(node)) {
        return;
      }
      const binding = this.bindingScope(node);
      if (!binding) {
        return;
      }
      const name = this.text(state, node);
      const declarations = byName.get(name) ?? [];
      declarations.push({
        definition: node,
        binding,
        depth: this.nodeDepth(binding),
      });
      byName.set(name, declarations);
    });
    return byName;
  }

  private indexFields(
    state: EditorState,
    declaration: SyntaxNode,
    owner: ClassIdentity,
  ): Map<string, { owner: ClassIdentity; type: string }> {
    const fields = new Map<string, { owner: ClassIdentity; type: string }>();
    const body =
      declaration.getChild("ClassBody") ??
      declaration.getChild("InterfaceBody") ??
      declaration.getChild("EnumBody") ??
      declaration.getChild("AnnotationTypeBody");
    if (!body) {
      return fields;
    }
    for (let child = body.firstChild; child; child = child.nextSibling) {
      if (child.name !== "FieldDeclaration") {
        continue;
      }
      this.walk(child, (node) => {
        if (node.name !== "Definition") {
          return;
        }
        const type = this.declaredType(state, node);
        if (type) {
          fields.set(this.text(state, node), { owner, type });
        }
      });
    }
    return fields;
  }

  private bindingScope(definition: SyntaxNode): SyntaxNode | null {
    for (
      let declaration: SyntaxNode | null = definition.parent;
      declaration;
      declaration = declaration.parent
    ) {
      if (
        declaration.name === "FormalParameter" ||
        declaration.name === "SpreadParameter"
      ) {
        return (
          this.ancestor(declaration, "LambdaExpression") ??
          this.ancestor(declaration, "MethodDeclaration") ??
          this.ancestor(declaration, "ConstructorDeclaration")
        );
      }
      if (declaration.name === "CatchFormalParameter") {
        return this.ancestor(declaration, "CatchClause");
      }
      if (declaration.name === "LambdaExpression") {
        return declaration;
      }
      if (declaration.name === "VariableDeclarator") {
        for (
          let owner: SyntaxNode | null = declaration.parent;
          owner;
          owner = owner.parent
        ) {
          if (owner.name === "FieldDeclaration") {
            return null;
          }
          if (
            owner.name === "ForStatement" ||
            owner.name === "EnhancedForStatement" ||
            owner.name === "TryStatement" ||
            owner.name === "Block" ||
            owner.name === "ConstructorBody"
          ) {
            return owner;
          }
        }
        return null;
      }
      if (TYPE_DECLARATIONS.has(declaration.name)) {
        return null;
      }
    }
    return null;
  }

  private nodeDepth(node: SyntaxNode): number {
    let depth = 0;
    for (let current = node.parent; current; current = current.parent) {
      depth += 1;
    }
    return depth;
  }

  private declaredType(state: EditorState, definition: SyntaxNode): string | null {
    let declaration = definition.parent;
    while (declaration && !VALUE_DECLARATIONS.has(declaration.name)) {
      declaration = declaration.parent;
    }
    if (!declaration) {
      return null;
    }
    if (declaration.name === "VariableDeclarator") {
      declaration = declaration.parent;
    }
    if (!declaration) {
      return null;
    }
    const types: SyntaxNode[] = [];
    this.walk(declaration, (node) => {
      if (node.to <= definition.from && TYPE_NODES.has(node.name)) {
        types.push(node);
      }
    });
    return types.length ? this.text(state, types[0]) : null;
  }

  private isLocalDefinition(definition: SyntaxNode): boolean {
    if (this.isRecoveredLambdaParameter(definition)) {
      return false;
    }
    for (
      let node: SyntaxNode | null = definition.parent;
      node;
      node = node.parent
    ) {
      if (node.name === "FieldDeclaration") {
        return false;
      }
      if (VALUE_DECLARATIONS.has(node.name)) {
        if (node.name !== "VariableDeclarator") {
          return true;
        }
        for (
          let owner: SyntaxNode | null = node.parent;
          owner;
          owner = owner.parent
        ) {
          if (owner.name === "FieldDeclaration") {
            return false;
          }
          if (
            owner.name === "LocalVariableDeclaration" ||
            owner.name === "ForSpec" ||
            owner.name === "EnhancedForStatement"
          ) {
            return true;
          }
        }
        return false;
      }
      if (
        node.name === "MethodDeclaration" ||
        node.name === "ConstructorDeclaration" ||
        node.name.endsWith("TypeDeclaration") ||
        node.name === "ClassDeclaration"
      ) {
        return false;
      }
      if (node.name === "LambdaExpression") {
        return true;
      }
    }
    return false;
  }

  /**
   * Lezer may recover a malformed parenthesized expression as lambda
   * parameters. Without an arrow it is not a declaration and must remain
   * eligible for normal lexical lookup.
   */
  private isRecoveredLambdaParameter(definition: SyntaxNode): boolean {
    const parameters = this.ancestor(definition, "InferredParameters");
    const lambda = parameters
      ? this.ancestor(parameters, "LambdaExpression")
      : null;
    if (!lambda) {
      return false;
    }
    let hasArrow = false;
    this.walk(lambda, (node) => {
      hasArrow ||= node.name === "->";
    });
    return !hasArrow;
  }

  private definitionNode(identifier: SyntaxNode): SyntaxNode | null {
    return identifier.name === "Definition"
      ? identifier
      : identifier.parent?.name === "Definition"
        ? identifier.parent
        : null;
  }

  private declarationDestination(
    state: EditorState,
    definition: SyntaxNode,
    range: { from: number; to: number },
  ): SymbolDestination | null {
    if (this.isLocalDefinition(definition)) {
      return { kind: "local", ...range };
    }

    const typeDeclaration = this.enclosingTypeDeclaration(definition);
    if (
      typeDeclaration?.getChild("Definition")?.from === definition.from
    ) {
      const owner = this.classForDeclaration(state, typeDeclaration);
      return owner
        ? { kind: "class", classDescriptor: owner.descriptor }
        : null;
    }

    const field = this.ancestor(definition, "FieldDeclaration");
    if (field) {
      const owner = this.enclosingClass(state, field);
      return owner
        ? {
            kind: "member",
            classDescriptor: owner.descriptor,
            memberKind: "field",
            name: this.text(state, definition),
            arity: null,
          }
        : null;
    }

    const method =
      this.ancestor(definition, "MethodDeclaration") ??
      this.ancestor(definition, "ConstructorDeclaration");
    if (!method || method.getChild("Definition")?.from !== definition.from) {
      return null;
    }
    const owner = this.enclosingClass(state, method);
    if (!owner) {
      return null;
    }
    return {
      kind: "member",
      classDescriptor: owner.descriptor,
      memberKind: "method",
      name:
        method.name === "ConstructorDeclaration"
          ? "<init>"
          : this.text(state, definition),
      arity: this.parameterCount(method),
      parameterDescriptors: this.parameterDescriptors(state, method),
    };
  }

  private parameterCount(declaration: SyntaxNode): number {
    let count = 0;
    const parameters = declaration.getChild("FormalParameters");
    if (!parameters) {
      return count;
    }
    this.walk(parameters, (node) => {
      if (
        node.name === "FormalParameter" ||
        node.name === "SpreadParameter"
      ) {
        count += 1;
      }
    });
    return count;
  }

  private parameterDescriptors(
    state: EditorState,
    declaration: SyntaxNode,
  ): (string | null)[] {
    const parameters = declaration.getChild("FormalParameters");
    if (!parameters) {
      return [];
    }
    const descriptors: (string | null)[] = [];
    for (let parameter = parameters.firstChild; parameter; parameter = parameter.nextSibling) {
      if (
        parameter.name !== "FormalParameter" &&
        parameter.name !== "SpreadParameter"
      ) {
        continue;
      }
      const definition = parameter.getChild("Definition");
      const declaredType = definition
        ? this.declaredType(state, definition)
        : null;
      const descriptor = declaredType
        ? this.typeDescriptor(declaredType)
        : null;
      descriptors.push(
        parameter.name === "SpreadParameter" && descriptor
          ? `[${descriptor}`
          : descriptor,
      );
    }
    return descriptors;
  }

  private typeContaining(identifier: SyntaxNode): SyntaxNode | null {
    let node: SyntaxNode | null = TYPE_NODES.has(identifier.name)
      ? identifier
      : identifier.parent;
    let outer: SyntaxNode | null = null;
    while (node && TYPE_NODES.has(node.name)) {
      outer = node;
      node = node.parent;
    }
    return outer;
  }

  private isAccessMember(access: SyntaxNode, identifier: SyntaxNode): boolean {
    const identifiers: SyntaxNode[] = [];
    this.walk(access, (node) => {
      if (node.name === "Identifier" && node.to <= identifier.to) {
        identifiers.push(node);
      }
    });
    return identifiers.at(-1)?.from === identifier.from;
  }

  private argumentNodes(invocation: SyntaxNode): SyntaxNode[] {
    const argumentsNode = invocation.getChild("ArgumentList");
    if (!argumentsNode) {
      return [];
    }
    const nodes: SyntaxNode[] = [];
    for (let child = argumentsNode.firstChild; child; child = child.nextSibling) {
      if (child.name !== "(" && child.name !== ")" && child.name !== ",") {
        nodes.push(child);
      }
    }
    return nodes;
  }

  private argumentDescriptor(
    state: EditorState,
    expression: SyntaxNode,
  ): string | null {
    const text = this.text(state, expression);
    switch (expression.name) {
      case "StringLiteral":
        return "Ljava/lang/String;";
      case "CharacterLiteral":
        return "C";
      case "BooleanLiteral":
        return "Z";
      case "IntegerLiteral":
        return /[lL]$/.test(text) ? "J" : "I";
      case "FloatingPointLiteral":
        return /[fF]$/.test(text) ? "F" : "D";
      case "Null":
      case "NullLiteral":
        return null;
    }

    if (expression.name === "Identifier") {
      const definition = this.localDefinition(state, expression, text);
      const declaredType = definition
        ? this.declaredType(state, definition)
        : this.fieldBinding(state, expression, text)?.type;
      return declaredType ? this.typeDescriptor(declaredType) : null;
    }

    if (
      expression.name === "CastExpression" ||
      expression.name === "NewExpression"
    ) {
      let type: SyntaxNode | null = null;
      this.walk(expression, (node) => {
        if (!type && TYPE_NODES.has(node.name)) {
          type = node;
        }
      });
      return type ? this.typeDescriptor(this.text(state, type)) : null;
    }
    return null;
  }

  private typeDescriptor(rawType: string): string | null {
    const dimensions = [...rawType.matchAll(/\[\]/g)].length;
    const type = JavaDefinitionResolver.eraseType(rawType);
    const primitive = new Map([
      ["boolean", "Z"],
      ["byte", "B"],
      ["char", "C"],
      ["short", "S"],
      ["int", "I"],
      ["long", "J"],
      ["float", "F"],
      ["double", "D"],
    ]).get(type);
    const descriptor = primitive ?? this.resolveClass(type)?.descriptor;
    return descriptor ? `${"[".repeat(dimensions)}${descriptor}` : null;
  }

  private resolveClass(rawName: string): ClassIdentity | null {
    const name = JavaDefinitionResolver.eraseType(rawName);
    if (!name) {
      return null;
    }
    const imported = this.importedClasses.get(name);
    if (imported) {
      return imported;
    }

    const current = this.rootClass();
    if (
      current &&
      (name === current.displayName ||
        name === current.binaryName ||
        name === current.qualifiedName)
    ) {
      return current;
    }

    const packageQualified = this.document.outline.qualifiedName.includes(".")
      ? `${this.document.outline.qualifiedName.slice(
          0,
          this.document.outline.qualifiedName.lastIndexOf("."),
        )}.${name}`
      : name;
    const archiveClass =
      this.uniqueClass(name) ??
      this.uniqueClass(packageQualified) ??
      this.uniqueClass(name.replaceAll(".", "$"));
    if (archiveClass) {
      return archiveClass;
    }

    const [outer, ...nested] = name.split(".");
    const importedOuter = this.importedClasses.get(outer);
    if (importedOuter && nested.length) {
      return {
        descriptor: importedOuter.descriptor.replace(
          /;$/,
          `$${nested.join("$")};`,
        ),
        qualifiedName: `${importedOuter.qualifiedName}.${nested.join(".")}`,
        package: importedOuter.package,
        binaryName: `${importedOuter.binaryName}$${nested.join("$")}`,
        displayName: nested.at(-1)!,
      };
    }
    if (name.includes(".")) {
      return JavaDefinitionResolver.externalClass(name);
    }
    return /^[A-Z_$]/.test(name)
      ? JavaDefinitionResolver.externalClass(`java.lang.${name}`)
      : null;
  }

  private rootClass(): ClassIdentity | null {
    return (
      this.archive.classes.find(
        (candidate) => candidate.descriptor === this.document.descriptor,
      ) ?? null
    );
  }

  private enclosingClass(
    state: EditorState,
    node: SyntaxNode,
  ): ClassIdentity | null {
    const declaration = this.enclosingTypeDeclaration(node);
    return declaration
      ? this.classForDeclaration(state, declaration)
      : this.rootClass();
  }

  private enclosingTypeDeclaration(node: SyntaxNode): SyntaxNode | null {
    for (
      let current: SyntaxNode | null = node;
      current;
      current = current.parent
    ) {
      if (TYPE_DECLARATIONS.has(current.name)) {
        return current;
      }
    }
    return null;
  }

  private classForDeclaration(
    state: EditorState,
    declaration: SyntaxNode,
  ): ClassIdentity | null {
    const names: string[] = [];
    for (
      let current: SyntaxNode | null = declaration;
      current;
      current = current.parent
    ) {
      if (!TYPE_DECLARATIONS.has(current.name)) {
        continue;
      }
      const definition = current.getChild("Definition");
      if (definition) {
        names.unshift(this.text(state, definition));
      }
    }
    if (!names.length) {
      return this.rootClass();
    }
    const sourceName = names.join(".");
    const root = this.rootClass();
    const packageName = root?.package;
    const resolved =
      this.uniqueClass(packageName ? `${packageName}.${sourceName}` : sourceName) ??
      this.uniqueClass(sourceName);
    if (resolved) {
      return resolved;
    }
    return names.length === 1 &&
      root &&
      (names[0] === root.displayName || names[0] === root.binaryName)
      ? root
      : null;
  }

  private uniqueClass(name: string): ClassSummary | null {
    const matches = this.classesByName.get(name);
    return matches?.length === 1 ? matches[0] : null;
  }

  private imports(source: string): string[] {
    return [...source.matchAll(/^import\s+([\w.$]+);$/gm)].map(
      (match) => match[1],
    );
  }

  private static classAliases(candidate: ClassSummary): string[] {
    return [...new Set([
      candidate.qualifiedName,
      candidate.qualifiedName.replaceAll("$", "."),
      candidate.binaryName,
      candidate.binaryName.replaceAll("$", "."),
      candidate.displayName,
    ])];
  }

  private static eraseType(type: string): string {
    return type
      .replace(/<.*>/g, "")
      .replace(/\[\]/g, "")
      .replace(/^\? extends |^\? super /, "")
      .trim();
  }

  private static externalClass(qualifiedName: string): ClassIdentity | null {
    const parts = qualifiedName.split(".").filter(Boolean);
    if (
      !parts.length ||
      parts.some((part) => !/^[$A-Z_a-z][$\w]*$/.test(part))
    ) {
      return null;
    }
    const classIndex = parts.findIndex((part) => /^[A-Z_$]/.test(part));
    const split = classIndex >= 0 ? classIndex : parts.length - 1;
    const packageParts = parts.slice(0, split);
    const classParts = parts.slice(split);
    if (!classParts.length) {
      return null;
    }
    const packageName = packageParts.join(".");
    const binaryName = classParts.join("$");
    const internalName = [...packageParts, binaryName].join("/");
    return {
      descriptor: `L${internalName};`,
      qualifiedName,
      package: packageName,
      binaryName,
      displayName: classParts.at(-1)!,
    };
  }

  private ancestor(node: SyntaxNode, name: string): SyntaxNode | null {
    for (let current: SyntaxNode | null = node; current; current = current.parent) {
      if (current.name === name) {
        return current;
      }
    }
    return null;
  }

  private walk(root: SyntaxNode, visit: (node: SyntaxNode) => void): void {
    const pending = [root];
    while (pending.length) {
      const node = pending.pop()!;
      visit(node);
      for (let child = node.lastChild; child; child = child.prevSibling) {
        pending.push(child);
      }
    }
  }

  private text(state: EditorState, node: SyntaxNode): string {
    return state.doc.sliceString(node.from, node.to);
  }
}
