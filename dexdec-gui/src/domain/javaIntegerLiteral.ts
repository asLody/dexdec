import type { EditorState } from "@codemirror/state";
import { syntaxTree } from "@codemirror/language";
import type { SyntaxNode } from "@lezer/common";

import type { SourceRange } from "./javaSourceIndex";

const ZERO = BigInt(0);
const ONE = BigInt(1);
const MAX_CHARACTER = BigInt(0xffff);

export type IntegerDisplayMode =
  | "original"
  | "hexadecimal"
  | "decimal"
  | "binary"
  | "octal"
  | "character";

/**
 * A parsed Java integer literal. Display conversions operate on its semantic
 * value while the editor continues to retain the original source text.
 */
export class JavaIntegerLiteral {
  private constructor(
    readonly range: SourceRange,
    readonly source: string,
    private readonly value: bigint,
    private readonly bitPattern: bigint,
    private readonly long: boolean,
  ) {}

  static at(state: EditorState, offset: number): JavaIntegerLiteral | null {
    const tree = syntaxTree(state);
    for (const side of [-1, 1] as const) {
      let node: SyntaxNode | null = tree.resolveInner(offset, side);
      while (node) {
        if (
          node.name === "IntegerLiteral" &&
          offset >= node.from &&
          offset <= node.to
        ) {
          return this.parse(
            { from: node.from, to: node.to },
            state.doc.sliceString(node.from, node.to),
          );
        }
        node = node.parent;
      }
    }
    return null;
  }

  format(mode: IntegerDisplayMode): string {
    const suffix = this.long ? "L" : "";
    switch (mode) {
      case "original":
        return this.source;
      case "decimal":
        return `${this.value}${suffix}`;
      case "hexadecimal":
        return `0x${groupDigits(this.bitPattern.toString(16), 4)}${suffix}`;
      case "binary":
        return `0b${groupDigits(this.bitPattern.toString(2), 4)}${suffix}`;
      case "octal":
        return `${this.bitPattern === ZERO ? "0" : `0${groupDigits(
          this.bitPattern.toString(8),
          3,
        )}`}${suffix}`;
      case "character":
        return formatCharacter(this.value);
    }
  }

  supports(mode: IntegerDisplayMode): boolean {
    return (
      mode !== "character" ||
      (!this.long && this.value >= ZERO && this.value <= MAX_CHARACTER)
    );
  }

  private static parse(
    range: SourceRange,
    source: string,
  ): JavaIntegerLiteral | null {
    const compact = source.replaceAll("_", "");
    const long = /[lL]$/.test(compact);
    const digits = long ? compact.slice(0, -1) : compact;
    const radix = literalRadix(digits);

    let unsigned: bigint;
    try {
      unsigned = parseUnsigned(digits, radix);
    } catch {
      return null;
    }

    const bits = BigInt(long ? 64 : 32);
    const modulus = ONE << bits;
    const signBit = ONE << (bits - ONE);
    const isBitPattern = radix !== 10 && unsigned < modulus;
    const value =
      isBitPattern && unsigned >= signBit ? unsigned - modulus : unsigned;
    const bitPattern = value < ZERO ? value + modulus : unsigned;
    return new JavaIntegerLiteral(range, source, value, bitPattern, long);
  }
}

function literalRadix(source: string): 2 | 8 | 10 | 16 {
  if (/^0[xX]/.test(source)) return 16;
  if (/^0[bB]/.test(source)) return 2;
  if (/^0[oO]/.test(source) || /^0[0-7]+$/.test(source)) return 8;
  return 10;
}

function parseUnsigned(source: string, radix: 2 | 8 | 10 | 16): bigint {
  if (radix === 8 && /^0[0-7]+$/.test(source)) {
    return BigInt(`0o${source.slice(1)}`);
  }
  if (radix === 8 && /^0[oO]/.test(source)) {
    return BigInt(`0o${source.slice(2)}`);
  }
  return BigInt(source);
}

function groupDigits(digits: string, width: number): string {
  const groups: string[] = [];
  for (let end = digits.length; end > 0; end -= width) {
    groups.unshift(digits.slice(Math.max(0, end - width), end));
  }
  return groups.join("_");
}

function formatCharacter(value: bigint): string {
  const code = Number(value);
  const escapes: Record<number, string> = {
    0x08: "\\b",
    0x09: "\\t",
    0x0a: "\\n",
    0x0c: "\\f",
    0x0d: "\\r",
    0x27: "\\'",
    0x5c: "\\\\",
  };
  const escaped = escapes[code];
  if (escaped) {
    return `'${escaped}'`;
  }
  if (code >= 0x20 && code <= 0x7e) {
    return `'${String.fromCharCode(code)}'`;
  }
  return `'\\u${code.toString(16).padStart(4, "0")}'`;
}
