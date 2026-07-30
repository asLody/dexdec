const PRIMITIVE_TYPES: Record<string, string> = {
  V: "void",
  Z: "boolean",
  B: "byte",
  S: "short",
  C: "char",
  I: "int",
  J: "long",
  F: "float",
  D: "double",
};

/** Parses one type from a DEX descriptor, returning [shortName, nextIndex]. */
export function parseDescriptorType(source: string, start: number): [string, number] {
  let index = start;
  let arrays = 0;
  while (source[index] === "[") {
    arrays += 1;
    index += 1;
  }
  let base: string;
  if (source[index] === "L") {
    let depth = 0;
    let end = index;
    for (; end < source.length; end += 1) {
      const char = source[end];
      if (char === "<") depth += 1;
      else if (char === ">") depth -= 1;
      else if (char === ";" && depth === 0) break;
    }
    base =
      source
        .slice(index + 1, end)
        .replace(/<.*>/, "")
        .split("/")
        .pop()
        ?.replace(/\$/g, ".") ?? "Object";
    index = end + 1;
  } else {
    base = PRIMITIVE_TYPES[source[index]] ?? source[index];
    index += 1;
  }
  return [base + "[]".repeat(arrays), index];
}

/** Renders a method descriptor's parameter list as short Java type names. */
export function parametersOf(descriptor: string): string {
  const match = descriptor.match(/^\((.*)\)/);
  if (!match || !match[1]) {
    return "()";
  }
  const source = match[1];
  const parts: string[] = [];
  let index = 0;
  while (index < source.length) {
    const [type, next] = parseDescriptorType(source, index);
    if (next <= index) {
      return "(…)";
    }
    parts.push(type);
    index = next;
  }
  return `(${parts.join(", ")})`;
}

/** Renders a field/type descriptor as a short Java type name. */
export function shortTypeOf(descriptor: string): string {
  const [type] = parseDescriptorType(descriptor, 0);
  return type;
}

/** JVM method descriptor parameter count, or null when malformed. */
export function arityOf(descriptor: string): number | null {
  if (!descriptor.startsWith("(")) {
    return null;
  }
  let index = 1;
  let count = 0;
  while (index < descriptor.length && descriptor[index] !== ")") {
    while (descriptor[index] === "[") index += 1;
    if (descriptor[index] === "L") {
      const end = descriptor.indexOf(";", index);
      if (end < 0) {
        return null;
      }
      index = end + 1;
    } else {
      index += 1;
    }
    count += 1;
  }
  return descriptor[index] === ")" ? count : null;
}
