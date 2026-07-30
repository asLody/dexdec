import type { Archive, ClassSummary, SourceDocument } from "./models";
import type { MemberAtOffset, SemanticToken } from "./sourceDefinitionResolver";

export interface KotlinToken {
  from: number;
  to: number;
  text: string;
  kind: "identifier" | "keyword" | "number" | "string" | "symbol";
}

export interface KotlinBinding {
  token: KotlinToken;
  kind: "local" | "label" | "field" | "method" | "class";
  scope: { from: number; to: number };
  typeName: string | null;
  arity: number | null;
  body: { from: number; to: number } | null;
}

const KEYWORDS = new Set([
  "as", "break", "class", "continue", "do", "else", "false", "for",
  "fun", "if", "in", "interface", "is", "null", "object", "package",
  "return", "super", "this", "throw", "true", "try", "typealias", "typeof",
  "val", "var", "when", "while", "by", "catch", "constructor", "delegate",
  "dynamic", "field", "file", "finally", "get", "import", "init", "param",
  "property", "receiver", "set", "setparam", "where", "actual", "abstract",
  "annotation", "companion", "const", "crossinline", "data", "enum", "expect",
  "external", "final", "infix", "inline", "inner", "internal", "lateinit",
  "noinline", "open", "operator", "out", "override", "private", "protected",
  "public", "reified", "sealed", "suspend", "tailrec", "vararg",
]);

const TYPE_CONTEXT = new Set([":", "as", "is", "<"]);

export class KotlinSourceModel {
  readonly tokens: KotlinToken[];
  readonly bindings: KotlinBinding[];
  readonly semantic: SemanticToken[];
  readonly classesByName = new Map<string, ClassSummary[]>();
  readonly imports = new Map<string, string>();
  readonly classDescriptors: Set<string>;

  private readonly pairs = new Map<number, number>();
  private readonly tokenIndex = new Map<KotlinToken, number>();
  private readonly classBodyOpens = new Set<number>();
  private readonly rootClass: ClassSummary | null;

  constructor(
    readonly document: SourceDocument,
    readonly archive: Archive,
  ) {
    this.classDescriptors = new Set(
      archive.classes.map((candidate) => candidate.descriptor),
    );
    this.tokens = KotlinLexer.scan(document.source);
    this.tokens.forEach((token, index) => this.tokenIndex.set(token, index));
    this.indexPairs();
    this.rootClass =
      archive.classes.find((candidate) => candidate.descriptor === document.descriptor) ?? null;
    this.indexClasses();
    this.indexImports();
    this.bindings = this.indexBindings();
    this.semantic = this.indexSemanticTokens();
  }

  tokenAt(offset: number): KotlinToken | null {
    let low = 0;
    let high = this.tokens.length - 1;
    while (low <= high) {
      const middle = (low + high) >>> 1;
      const token = this.tokens[middle];
      if (offset < token.from) high = middle - 1;
      else if (offset > token.to) low = middle + 1;
      else return token;
    }
    return null;
  }

  bindingFor(token: KotlinToken): KotlinBinding | null {
    const declaration = this.bindings.find((binding) => binding.token === token);
    if (declaration) return declaration;
    return this.bindings
      .filter(
        (binding) =>
          (binding.kind === "local" || binding.kind === "label") &&
          binding.token.text === token.text &&
          token.from >= binding.scope.from &&
          token.to <= binding.scope.to &&
          (binding.token.from <= token.from || this.isParameter(binding)),
      )
      .sort(
        (left, right) =>
          (left.scope.to - left.scope.from) - (right.scope.to - right.scope.from) ||
          right.token.from - left.token.from,
      )[0] ?? null;
  }

  field(name: string): KotlinBinding | null {
    return this.bindings.find(
      (binding) => binding.kind === "field" && binding.token.text === name,
    ) ?? null;
  }

  method(name: string, arity: number): KotlinBinding | null {
    const candidates = this.bindings.filter(
      (binding) => binding.kind === "method" && binding.token.text === name,
    );
    return candidates.find((binding) => binding.arity === arity) ??
      (candidates.length === 1 ? candidates[0] : null);
  }

  resolveClass(name: string): ClassSummary | null {
    const plain = name.replace(/^`|`$/g, "").replace(/[?!]$/g, "");
    const imported = this.imports.get(plain);
    const packageName = this.rootClass?.package ?? "";
    const known = this.uniqueClass(imported ?? plain) ??
      this.uniqueClass(packageName ? `${packageName}.${plain}` : plain) ??
      this.uniqueClass(plain.replaceAll(".", "$"));
    if (known) return known;
    const builtins = new Map([
      ["Any", "java.lang.Object"],
      ["Boolean", "java.lang.Boolean"],
      ["Byte", "java.lang.Byte"],
      ["Char", "java.lang.Character"],
      ["Double", "java.lang.Double"],
      ["Float", "java.lang.Float"],
      ["Int", "java.lang.Integer"],
      ["Long", "java.lang.Long"],
      ["Short", "java.lang.Short"],
      ["String", "java.lang.String"],
      ["Throwable", "java.lang.Throwable"],
      ["Unit", "kotlin.Unit"],
    ]);
    const qualified = imported ?? builtins.get(plain) ??
      (plain.includes(".") ? plain : null);
    return qualified ? this.externalClass(qualified) : null;
  }

  argumentCount(openIndex: number): number {
    const close = this.pairs.get(openIndex);
    if (close == null || close === openIndex + 1) return 0;
    let count = 1;
    let depth = 0;
    for (let index = openIndex + 1; index < close; index += 1) {
      const text = this.tokens[index].text;
      if (text === "(" || text === "[" || text === "{") depth += 1;
      else if (text === ")" || text === "]" || text === "}") depth -= 1;
      else if (text === "," && depth === 0) count += 1;
    }
    return count;
  }

  memberAtOffset(offset: number): MemberAtOffset | null {
    const containing = this.bindings
      .filter(
        (binding) =>
          (binding.kind === "method" || binding.kind === "field") &&
          binding.body && offset >= binding.body.from && offset <= binding.body.to,
      )
      .sort(
        (left, right) =>
          (left.body!.to - left.body!.from) - (right.body!.to - right.body!.from),
      )[0];
    return containing
      ? {
          kind: containing.kind === "method" ? "method" : "field",
          name: containing.kind === "method" && containing.token.text === this.rootClass?.displayName
            ? "<init>"
            : containing.token.text,
          arity: containing.kind === "method" ? containing.arity : null,
        }
      : null;
  }

  indexOf(token: KotlinToken): number {
    return this.tokenIndex.get(token) ?? -1;
  }

  previous(index: number, distance = 1): KotlinToken | null {
    return this.tokens[index - distance] ?? null;
  }

  next(index: number, distance = 1): KotlinToken | null {
    return this.tokens[index + distance] ?? null;
  }

  matching(index: number): number | null {
    return this.pairs.get(index) ?? null;
  }

  private indexClasses(): void {
    for (const candidate of this.archive.classes) {
      const aliases = [
        candidate.qualifiedName,
        candidate.qualifiedName.replaceAll("$", "."),
        candidate.binaryName,
        candidate.binaryName.replaceAll("$", "."),
        candidate.displayName,
      ];
      for (const alias of new Set(aliases)) {
        const matches = this.classesByName.get(alias) ?? [];
        matches.push(candidate);
        this.classesByName.set(alias, matches);
      }
    }
  }

  private indexImports(): void {
    for (let index = 0; index < this.tokens.length; index += 1) {
      if (this.tokens[index].text !== "import") continue;
      const names: string[] = [];
      let alias: string | null = null;
      for (index += 1; index < this.tokens.length; index += 1) {
        const token = this.tokens[index];
        if (this.lineOf(token.from) !== this.lineOf(this.tokens[index - 1].from)) {
          index -= 1;
          break;
        }
        if (token.text === "as") {
          alias = this.tokens[index + 1]?.text ?? null;
          index += 1;
          continue;
        }
        if (token.kind === "identifier") names.push(token.text);
      }
      const qualified = names.join(".");
      if (qualified) this.imports.set(alias ?? names.at(-1)!, qualified);
    }
  }

  private indexPairs(): void {
    const stacks = new Map<string, number[]>([[")", []], ["]", []], ["}", []]]);
    const closing = new Map([["(", ")"], ["[", "]"], ["{", "}"]]);
    for (let index = 0; index < this.tokens.length; index += 1) {
      const text = this.tokens[index].text;
      const close = closing.get(text);
      if (close) stacks.get(close)!.push(index);
      else if (stacks.has(text)) {
        const open = stacks.get(text)!.pop();
        if (open != null) {
          this.pairs.set(open, index);
          this.pairs.set(index, open);
        }
      }
    }
  }

  private indexBindings(): KotlinBinding[] {
    const bindings: KotlinBinding[] = [];
    for (let index = 0; index < this.tokens.length; index += 1) {
      const token = this.tokens[index];

      if (["class", "interface", "object", "typealias"].includes(token.text)) {
        const name = this.nextIdentifier(index);
        const bodyOpen = this.findAhead(index + 1, "{");
        const bodyClose = bodyOpen == null ? null : this.pairs.get(bodyOpen) ?? null;
        if (bodyOpen != null && bodyClose != null) this.classBodyOpens.add(bodyOpen);
        if (name) {
          const nameIndex = this.indexOf(name);
          const constructorOpen = this.findBetween(nameIndex + 1, bodyOpen, "(");
          const constructorClose = constructorOpen == null
            ? null
            : this.pairs.get(constructorOpen) ?? null;
          const parameters =
            constructorOpen != null && constructorClose != null
              ? this.parameterTokens(constructorOpen, constructorClose)
              : [];
          bindings.push({
            token: name,
            kind: "class",
            scope: this.wholeDocument(),
            typeName: null,
            arity: parameters.length,
            body: bodyOpen != null && bodyClose != null
              ? { from: name.from, to: this.tokens[bodyClose].to }
              : { from: name.from, to: name.to },
          });
          if (bodyOpen != null && bodyClose != null) {
            const scope = {
              from: this.tokens[bodyOpen].from,
              to: this.tokens[bodyClose].to,
            };
            for (const parameter of parameters) {
              const parameterIndex = this.indexOf(parameter);
              const property = ["val", "var"].includes(
                this.previous(parameterIndex)?.text ?? "",
              );
              bindings.push({
                ...this.localBinding(parameter, scope),
                kind: property ? "field" : "local",
                body: property ? { from: parameter.from, to: parameter.to } : null,
              });
            }
          }
        }
        continue;
      }

      if (token.text === "fun") {
        const open = this.findAhead(index + 1, "(");
        if (open == null) continue;
        const name = this.previousIdentifier(open);
        const close = this.pairs.get(open);
        if (!name || close == null) continue;
        const body = this.declarationBody(name.from, close);
        bindings.push({
          token: name,
          kind: "method",
          scope: this.wholeDocument(),
          typeName: null,
          arity: this.parameterTokens(open, close).length,
          body,
        });
        for (const parameter of this.parameterTokens(open, close)) {
          bindings.push(this.localBinding(parameter, body ?? this.blockScope(close)));
        }
        continue;
      }

      if (token.text === "constructor") {
        const open = this.findAhead(index + 1, "(");
        const close = open == null ? null : this.pairs.get(open) ?? null;
        if (open == null || close == null) continue;
        const body = this.declarationBody(token.from, close);
        bindings.push({
          token,
          kind: "method",
          scope: this.wholeDocument(),
          typeName: null,
          arity: this.parameterTokens(open, close).length,
          body,
        });
        for (const parameter of this.parameterTokens(open, close)) {
          bindings.push(this.localBinding(parameter, body ?? this.blockScope(close)));
        }
        continue;
      }

      if (token.text === "val" || token.text === "var") {
        const name = this.nextIdentifier(index);
        if (!name) continue;
        const scope = this.blockScope(index);
        const classLevel = this.isClassLevel(index);
        bindings.push({
          token: name,
          kind: classLevel ? "field" : "local",
          scope,
          typeName: this.declaredType(this.indexOf(name)),
          arity: null,
          body: classLevel ? this.fieldBody(this.indexOf(name)) : null,
        });
        continue;
      }

      if (token.kind === "identifier" && this.tokens[index + 1]?.text === "@") {
        bindings.push({
          token,
          kind: "label",
          scope: this.blockScope(index),
          typeName: null,
          arity: null,
          body: null,
        });
      }
    }
    return bindings;
  }

  private indexSemanticTokens(): SemanticToken[] {
    const semantic = new Map<string, SemanticToken>();
    const mark = (token: KotlinToken, kind: SemanticToken["kind"]) =>
      semantic.set(`${token.from}:${token.to}`, { from: token.from, to: token.to, kind });
    for (const binding of this.bindings) {
      mark(binding.token,
        binding.kind === "class" ? "type" :
        binding.kind === "method" ? "function" :
        binding.kind === "field" ? "property" :
        binding.kind === "local" ? "variable" : binding.kind);
    }
    for (let index = 0; index < this.tokens.length; index += 1) {
      const token = this.tokens[index];
      if (token.kind !== "identifier") continue;
      if (this.previous(index)?.text === "@") {
        mark(token, "annotation");
      } else if (this.next(index)?.text === "(" && this.previous(index)?.text !== "fun") {
        mark(token, "function");
      } else if (this.previous(index)?.text === ".") {
        mark(token, "property");
      } else if (this.isTypeReference(index) || this.resolveClass(token.text)) {
        mark(token, "type");
      } else if (this.bindingFor(token)) {
        mark(token, "variable");
      }
    }
    return [...semantic.values()].sort((left, right) => left.from - right.from);
  }

  private isTypeReference(index: number): boolean {
    const previous = this.previous(index)?.text;
    return Boolean(previous && TYPE_CONTEXT.has(previous)) &&
      !["=", ")", "]", "}"].includes(this.next(index)?.text ?? "");
  }

  private isClassLevel(index: number): boolean {
    for (let cursor = index; cursor >= 0; cursor -= 1) {
      if (this.tokens[cursor].text !== "{") continue;
      const close = this.pairs.get(cursor);
      if (close != null && close >= index) return this.classBodyOpens.has(cursor);
    }
    return false;
  }

  private isParameter(binding: KotlinBinding): boolean {
    const previous = this.tokens[this.indexOf(binding.token) - 1];
    return previous?.text === "(" || previous?.text === "," || previous?.text === "val" || previous?.text === "var";
  }

  private parameterTokens(open: number, close: number): KotlinToken[] {
    const result: KotlinToken[] = [];
    let depth = 0;
    for (let index = open + 1; index < close; index += 1) {
      const token = this.tokens[index];
      if (["(", "[", "<"].includes(token.text)) depth += 1;
      else if ([")", "]", ">"].includes(token.text)) depth -= 1;
      if (depth === 0 && token.kind === "identifier" && this.tokens[index + 1]?.text === ":") {
        result.push(token);
      }
    }
    return result;
  }

  private localBinding(token: KotlinToken, scope: { from: number; to: number }): KotlinBinding {
    return {
      token,
      kind: "local",
      scope,
      typeName: this.declaredType(this.indexOf(token)),
      arity: null,
      body: null,
    };
  }

  private declaredType(nameIndex: number): string | null {
    if (this.tokens[nameIndex + 1]?.text !== ":") return null;
    const parts: string[] = [];
    for (let index = nameIndex + 2; index < this.tokens.length; index += 1) {
      const token = this.tokens[index];
      if (["=", ",", ")", "{"].includes(token.text)) break;
      if (token.kind === "identifier" || token.text === ".") parts.push(token.text);
    }
    return parts.join("") || null;
  }

  private declarationBody(from: number, after: number): { from: number; to: number } | null {
    const open = this.findAhead(after + 1, "{");
    if (open != null) {
      const close = this.pairs.get(open);
      if (close != null) return { from, to: this.tokens[close].to };
    }
    const end = this.lineEnd(this.tokens[after].to);
    return { from, to: end };
  }

  private fieldBody(index: number): { from: number; to: number } {
    return { from: this.tokens[index].from, to: this.lineEnd(this.tokens[index].to) };
  }

  private blockScope(index: number): { from: number; to: number } {
    for (let cursor = index; cursor >= 0; cursor -= 1) {
      if (this.tokens[cursor].text !== "{") continue;
      const close = this.pairs.get(cursor);
      if (close != null && close >= index) {
        return { from: this.tokens[cursor].from, to: this.tokens[close].to };
      }
    }
    return this.wholeDocument();
  }

  private findAhead(start: number, text: string): number | null {
    for (let index = start; index < this.tokens.length; index += 1) {
      const token = this.tokens[index];
      if (token.text === text) return index;
      if (token.text === "=" || token.text === ";") return null;
    }
    return null;
  }

  private findBetween(start: number, end: number | null, text: string): number | null {
    const limit = end ?? this.tokens.length;
    for (let index = start; index < limit; index += 1) {
      if (this.tokens[index].text === text) return index;
    }
    return null;
  }

  private nextIdentifier(index: number): KotlinToken | null {
    for (let cursor = index + 1; cursor < this.tokens.length; cursor += 1) {
      if (this.tokens[cursor].kind === "identifier") return this.tokens[cursor];
      if (["{", "=", ";"].includes(this.tokens[cursor].text)) return null;
    }
    return null;
  }

  private previousIdentifier(index: number): KotlinToken | null {
    for (let cursor = index - 1; cursor >= 0; cursor -= 1) {
      if (this.tokens[cursor].kind === "identifier") return this.tokens[cursor];
      if (["}", ";", "="].includes(this.tokens[cursor].text)) return null;
    }
    return null;
  }

  private uniqueClass(name: string): ClassSummary | null {
    const candidates = this.classesByName.get(name);
    return candidates?.length === 1 ? candidates[0] : null;
  }

  private externalClass(qualifiedName: string): ClassSummary | null {
    const parts = qualifiedName.split(".").filter(Boolean);
    const classIndex = parts.findIndex((part) => /^[A-Z_$]/.test(part));
    if (!parts.length || classIndex < 0) return null;
    const packageParts = parts.slice(0, classIndex);
    const classParts = parts.slice(classIndex);
    const binaryName = classParts.join("$");
    return {
      descriptor: `L${[...packageParts, binaryName].join("/")};`,
      qualifiedName,
      package: packageParts.join("."),
      binaryName,
      displayName: classParts.at(-1)!,
      parentDescriptor: null,
      sourcePath: `${qualifiedName.replaceAll(".", "/")}.kt`,
    };
  }

  private wholeDocument(): { from: number; to: number } {
    return { from: 0, to: this.document.source.length };
  }

  private lineOf(offset: number): number {
    return this.document.source.lastIndexOf("\n", offset) + 1;
  }

  private lineEnd(offset: number): number {
    const end = this.document.source.indexOf("\n", offset);
    return end < 0 ? this.document.source.length : end;
  }

}

class KotlinLexer {
  static scan(source: string): KotlinToken[] {
    const tokens: KotlinToken[] = [];
    let index = 0;
    while (index < source.length) {
      const char = source[index];
      if (/\s/u.test(char)) {
        index += 1;
        continue;
      }
      if (source.startsWith("//", index)) {
        index = KotlinLexer.lineEnd(source, index + 2);
        continue;
      }
      if (source.startsWith("/*", index)) {
        index = KotlinLexer.blockCommentEnd(source, index + 2);
        continue;
      }
      if (source.startsWith('"""', index)) {
        const end = source.indexOf('"""', index + 3);
        const to = end < 0 ? source.length : end + 3;
        tokens.push({ from: index, to, text: source.slice(index, to), kind: "string" });
        index = to;
        continue;
      }
      if (char === '"' || char === "'") {
        const to = KotlinLexer.quotedEnd(source, index, char);
        tokens.push({ from: index, to, text: source.slice(index, to), kind: "string" });
        index = to;
        continue;
      }
      if (char === "`") {
        const end = source.indexOf("`", index + 1);
        const to = end < 0 ? source.length : end + 1;
        tokens.push({
          from: index,
          to,
          text: source.slice(index + 1, Math.max(index + 1, to - 1)),
          kind: "identifier",
        });
        index = to;
        continue;
      }
      const identifier = source.slice(index).match(/^[\p{ID_Start}_$][\p{ID_Continue}_$]*/u)?.[0];
      if (identifier) {
        tokens.push({
          from: index,
          to: index + identifier.length,
          text: identifier,
          kind: KEYWORDS.has(identifier) ? "keyword" : "identifier",
        });
        index += identifier.length;
        continue;
      }
      const number = source.slice(index).match(/^(?:0[xX][\da-fA-F_]+|0[bB][01_]+|\d[\d_]*(?:\.\d[\d_]*)?(?:[eE][+-]?[\d_]+)?)[uUlLfF]*/)?.[0];
      if (number) {
        tokens.push({ from: index, to: index + number.length, text: number, kind: "number" });
        index += number.length;
        continue;
      }
      const operator = ["===", "!==", "::", "?.", "?:", "!!", "->", "..", "<=", ">=", "==", "!=", "&&", "||", "+=", "-=", "*=", "/=", "%="].find((candidate) => source.startsWith(candidate, index)) ?? char;
      tokens.push({ from: index, to: index + operator.length, text: operator, kind: "symbol" });
      index += operator.length;
    }
    return tokens;
  }

  private static lineEnd(source: string, index: number): number {
    const end = source.indexOf("\n", index);
    return end < 0 ? source.length : end;
  }

  private static blockCommentEnd(source: string, index: number): number {
    let depth = 1;
    while (index < source.length && depth > 0) {
      if (source.startsWith("/*", index)) {
        depth += 1;
        index += 2;
      } else if (source.startsWith("*/", index)) {
        depth -= 1;
        index += 2;
      } else index += 1;
    }
    return index;
  }

  private static quotedEnd(source: string, start: number, quote: string): number {
    let escaped = false;
    for (let index = start + 1; index < source.length; index += 1) {
      if (!escaped && source[index] === quote) return index + 1;
      escaped = !escaped && source[index] === "\\";
      if (source[index] !== "\\") escaped = false;
    }
    return source.length;
  }
}
