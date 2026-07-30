import type { EditorState } from "@codemirror/state";

import type {
  Archive,
  ClassSummary,
  MemberNavigation,
  SourceDocument,
  SymbolDestination,
} from "./models";
import { KotlinSourceModel, type KotlinBinding, type KotlinToken } from "./kotlinSourceModel";
import type {
  MemberAtOffset,
  ResolvedSymbol,
  SemanticToken,
  SourceDefinitionResolver,
} from "./sourceDefinitionResolver";

/** Kotlin symbol resolution backed by lexical scopes and the DEX class catalog. */
export class KotlinDefinitionResolver implements SourceDefinitionResolver {
  private readonly model: KotlinSourceModel;
  private resolvedSymbols: ResolvedSymbol[] | null = null;

  constructor(
    private readonly document: SourceDocument,
    archive: Archive,
  ) {
    this.model = new KotlinSourceModel(document, archive);
  }

  resolve(_state: EditorState, offset: number): ResolvedSymbol | null {
    const indexed = this.indexedSymbolAt(offset);
    if (indexed) return indexed;
    const token = this.model.tokenAt(offset);
    if (!token || token.kind !== "identifier") return null;
    const range = { from: token.from, to: token.to };
    const binding = this.model.bindingFor(token);
    if (binding) {
      return { range, destination: this.bindingDestination(binding) };
    }

    const index = this.model.indexOf(token);
    const next = this.model.next(index);
    if (next?.text === "(") {
      const owner = this.receiverClass(index) ?? this.currentClass();
      if (!owner) return null;
      const arity = this.model.argumentCount(index + 1);
      const declared = owner.descriptor === this.document.descriptor
        ? this.model.method(token.text, arity)
        : null;
      return {
        range,
        destination: this.memberDestination(
          owner,
          "method",
          token.text,
          arity,
          declared,
        ),
      };
    }

    if ([".", "?."].includes(this.model.previous(index)?.text ?? "")) {
      const owner = this.receiverClass(index);
      return owner
        ? {
            range,
            destination: this.memberDestination(owner, "field", token.text, null, null),
          }
        : null;
    }

    const field = this.model.field(token.text);
    if (field) {
      const owner = this.currentClass();
      return owner
        ? {
            range,
            destination: this.memberDestination(owner, "field", token.text, null, field),
          }
        : null;
    }

    const target = this.model.resolveClass(token.text);
    return target
      ? { range, destination: { kind: "class", classDescriptor: target.descriptor } }
      : null;
  }

  resolveReferenceTarget(state: EditorState, offset: number): ResolvedSymbol | null {
    const symbol = this.resolve(state, offset);
    return symbol && this.isNavigable(symbol.destination) ? symbol : null;
  }

  isDeclaration(_state: EditorState, symbol: ResolvedSymbol): boolean {
    if (symbol.destination.kind === "local") {
      return symbol.range.from === symbol.destination.from &&
        symbol.range.to === symbol.destination.to;
    }
    const token = this.model.tokenAt(symbol.range.from);
    return token != null && this.model.bindings.some((binding) => binding.token === token);
  }

  isNavigable(destination: SymbolDestination): boolean {
    return destination.kind === "local" ||
      this.model.classDescriptors.has(destination.classDescriptor);
  }

  symbols(state: EditorState): ResolvedSymbol[] {
    if (this.resolvedSymbols) return this.resolvedSymbols;
    const symbols: ResolvedSymbol[] = [];
    for (const token of this.model.tokens) {
      if (token.kind !== "identifier") continue;
      const symbol = this.resolve(state, token.from);
      if (symbol && symbol.range.from === token.from && symbol.range.to === token.to) {
        symbols.push(symbol);
      }
    }
    this.resolvedSymbols = symbols;
    return symbols;
  }

  localOrdinal(
    _state: EditorState,
    destination: Extract<SymbolDestination, { kind: "local" }>,
  ): number | null {
    const declarations = this.localDeclarations();
    const index = declarations.findIndex(
      (binding) =>
        binding.token.from === destination.from && binding.token.to === destination.to,
    );
    return index < 0 ? null : index;
  }

  localKind(
    _state: EditorState,
    destination: Extract<SymbolDestination, { kind: "local" }>,
  ): "local" | "label" {
    return this.localDeclarations().find(
      (binding) =>
        binding.token.from === destination.from && binding.token.to === destination.to,
    )?.kind === "label"
      ? "label"
      : "local";
  }

  localBindingRange(
    _state: EditorState,
    destination: Extract<SymbolDestination, { kind: "local" }>,
  ): { from: number; to: number } | null {
    return this.localDeclarations().find(
      (binding) =>
        binding.token.from === destination.from && binding.token.to === destination.to,
    )?.scope ?? null;
  }

  locateMember(
    state: EditorState,
    target: MemberNavigation,
  ): { from: number; to: number } | null {
    const desiredArity = target.kind === "method"
      ? JvmMethodDescriptor.parameterCount(target.descriptor)
      : null;
    const declarations = this.model.bindings.filter((binding) => {
      if (target.kind === "field") {
        return binding.kind === "field";
      }
      const constructor = target.name === "<init>" && binding.kind === "class";
      return (constructor || binding.kind === "method") &&
        (desiredArity == null || binding.arity === desiredArity);
    });

    const exact = declarations.filter((binding) => {
      const destination = this.resolve(state, binding.token.from)?.destination;
      return destination?.kind === "member" &&
        destination.classDescriptor === target.classDescriptor &&
        destination.memberKind === target.kind &&
        destination.name === target.name &&
        destination.descriptor === target.descriptor;
    });
    if (exact.length === 1) {
      return { from: exact[0].token.from, to: exact[0].token.to };
    }

    const expectedName = this.displayMemberName(target);
    const candidates = declarations.filter((binding) =>
      target.name === "<init>" || binding.token.text === expectedName
    );
    const binding = candidates.length === 1 ? candidates[0] : null;
    return binding ? { from: binding.token.from, to: binding.token.to } : null;
  }

  memberAtOffset(_state: EditorState, offset: number): MemberAtOffset | null {
    return this.model.memberAtOffset(offset);
  }

  semanticTokens(): SemanticToken[] {
    return this.model.semantic;
  }

  private bindingDestination(binding: KotlinBinding): SymbolDestination {
    if (binding.kind === "local" || binding.kind === "label") {
      return {
        kind: "local",
        from: binding.token.from,
        to: binding.token.to,
        localKind: binding.kind,
      };
    }
    if (binding.kind === "class") {
      return {
        kind: "class",
        classDescriptor:
          this.model.resolveClass(binding.token.text)?.descriptor ?? this.document.descriptor,
      };
    }
    const owner = this.currentClass();
    if (!owner) {
      return {
        kind: "local",
        from: binding.token.from,
        to: binding.token.to,
      };
    }
    return this.memberDestination(
      owner,
      binding.kind,
      binding.kind === "method" && binding.token.text === "constructor"
        ? "<init>"
        : binding.token.text,
      binding.arity,
      binding,
    );
  }

  private memberDestination(
    owner: ClassSummary,
    kind: "field" | "method",
    name: string,
    arity: number | null,
    _binding: KotlinBinding | null,
  ): Extract<SymbolDestination, { kind: "member" }> {
    const descriptors = owner.descriptor === this.document.descriptor && kind === "method"
      ? this.document.outline.methods.filter(
          (method) =>
            method.name === name &&
            (arity == null || JvmMethodDescriptor.parameterCount(method.descriptor) === arity),
        )
      : owner.descriptor === this.document.descriptor && kind === "field"
        ? this.document.outline.fields.filter((field) => field.name === name)
        : [];
    const exact = descriptors.length === 1 ? descriptors[0].descriptor : undefined;
    return {
      kind: "member",
      classDescriptor: owner.descriptor,
      memberKind: kind,
      name,
      arity,
      descriptor: exact,
    };
  }

  private receiverClass(memberIndex: number): ClassSummary | null {
    if (![".", "?."].includes(this.model.previous(memberIndex)?.text ?? "")) return null;
    const receiver = this.model.previous(memberIndex, 2);
    if (!receiver) return null;
    if (receiver.text === "this" || receiver.text === "super") return this.currentClass();
    if (receiver.kind !== "identifier") return null;
    const binding = this.model.bindingFor(receiver) ?? this.model.field(receiver.text);
    return binding?.typeName
      ? this.model.resolveClass(binding.typeName)
      : this.model.resolveClass(receiver.text);
  }

  private currentClass(): ClassSummary | null {
    return this.model.archive.classes.find(
      (candidate) => candidate.descriptor === this.document.descriptor,
    ) ?? null;
  }

  private localDeclarations(): KotlinBinding[] {
    return this.model.bindings.filter(
      (binding) => binding.kind === "local" || binding.kind === "label",
    );
  }

  private displayMemberName(target: MemberNavigation): string {
    if (target.name === "<init>") return "constructor";
    const member = target.kind === "field"
      ? this.document.outline.fields.find(
          (field) => field.descriptor === target.descriptor,
        )
      : this.document.outline.methods.find(
          (method) => method.descriptor === target.descriptor,
        );
    return member?.name ?? target.name;
  }

  private indexedSymbolAt(offset: number): ResolvedSymbol | null {
    const spans = this.document.symbolSpans;
    if (!spans?.length) return null;
    let low = 0;
    let high = spans.length - 1;
    while (low <= high) {
      const middle = (low + high) >>> 1;
      const span = spans[middle];
      if (offset < span.from) high = middle - 1;
      else if (offset > span.to) low = middle + 1;
      else return {
        range: { from: span.from, to: span.to },
        destination: span.destination,
      };
    }
    return null;
  }
}

class JvmMethodDescriptor {
  static parameterCount(descriptor: string): number | null {
    if (!descriptor.startsWith("(")) return null;
    let count = 0;
    let index = 1;
    while (index < descriptor.length && descriptor[index] !== ")") {
      while (descriptor[index] === "[") index += 1;
      if (descriptor[index] === "L") {
        const end = descriptor.indexOf(";", index);
        if (end < 0) return null;
        index = end + 1;
      } else index += 1;
      count += 1;
    }
    return descriptor[index] === ")" ? count : null;
  }
}
