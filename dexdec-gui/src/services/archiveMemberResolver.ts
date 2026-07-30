import type {
  ClassOutline,
  MemberNavigation,
  MethodOutline,
  ReferenceTarget,
  SourceDocument,
  SymbolDestination,
} from "../domain/models";
import type { DecompilerClient } from "./decompilerClient";

/**
 * Validates source-level member candidates against DEX declarations and walks
 * the declared hierarchy. A candidate is navigable only when it identifies one
 * declaration unambiguously.
 */
export class ArchiveMemberResolver {
  private sessionId: number | null = null;
  private readonly outlines = new Map<string, ClassOutline>();

  constructor(private readonly client: DecompilerClient) {}

  closeArchive(): void {
    this.sessionId = null;
    this.outlines.clear();
  }

  async referenceTarget(
    sessionId: number,
    destination: Extract<SymbolDestination, { kind: "member" }>,
    documents: SourceDocument[],
  ): Promise<ReferenceTarget | null> {
    const member = await this.resolve(sessionId, destination, documents);
    if (member?.kind === "field") {
      return {
        kind: "field",
        classDescriptor: member.classDescriptor,
        name: member.name,
        descriptor: member.descriptor,
      };
    }
    if (member?.kind === "method") {
      return {
        kind: "method",
        classDescriptor: member.classDescriptor,
        name: member.name,
        descriptor: member.descriptor,
      };
    }
    return null;
  }

  async resolve(
    sessionId: number,
    destination: Extract<SymbolDestination, { kind: "member" }>,
    documents: SourceDocument[],
  ): Promise<Omit<MemberNavigation, "sequence"> | null> {
    if (destination.descriptor) {
      return {
        classDescriptor: destination.classDescriptor,
        kind: destination.memberKind,
        name: destination.name,
        descriptor: destination.descriptor,
      };
    }
    this.prepareSession(sessionId, documents);
    if (destination.memberKind === "method") {
      return this.resolveMethod(sessionId, destination);
    }

    const pending = [destination.classDescriptor];
    const visited = new Set<string>();

    while (pending.length) {
      const descriptor = pending.shift()!;
      if (visited.has(descriptor)) {
        continue;
      }
      visited.add(descriptor);
      const outline = await this.outline(sessionId, descriptor);
      if (!outline) {
        continue;
      }

      const member = this.field(outline, destination.name);
      if (member) {
        return {
          classDescriptor: outline.descriptor,
          kind: "field",
          name: destination.name,
          descriptor: member.descriptor,
        };
      }
      if (outline.superClass) {
        pending.push(outline.superClass);
      }
      pending.push(...outline.interfaces);
    }
    return null;
  }

  async classOutline(
    sessionId: number,
    descriptor: string,
    documents: SourceDocument[],
  ): Promise<ClassOutline | null> {
    this.prepareSession(sessionId, documents);
    return this.outline(sessionId, descriptor);
  }

  private async resolveMethod(
    sessionId: number,
    destination: Extract<SymbolDestination, { kind: "member" }>,
  ): Promise<Omit<MemberNavigation, "sequence"> | null> {
    const pending = [{ descriptor: destination.classDescriptor, depth: 0 }];
    const visited = new Set<string>();
    const candidates: MethodCandidate[] = [];

    while (pending.length) {
      const current = pending.shift()!;
      if (visited.has(current.descriptor)) {
        continue;
      }
      visited.add(current.descriptor);
      const outline = await this.outline(sessionId, current.descriptor);
      if (!outline) {
        continue;
      }

      for (const method of outline.methods) {
        const parameters = JvmDescriptor.parameters(method.descriptor);
        const originalName = method.originalName ?? method.name;
        if (
          originalName === destination.name &&
          parameters &&
          (destination.arity == null ||
            parameters.length === destination.arity)
        ) {
          candidates.push({
            owner: outline.descriptor,
            method,
            parameters,
            depth: current.depth,
          });
        }
      }
      if (outline.superClass) {
        pending.push({
          descriptor: outline.superClass,
          depth: current.depth + 1,
        });
      }
      pending.push(
        ...outline.interfaces.map((descriptor) => ({
          descriptor,
          depth: current.depth + 1,
        })),
      );
    }

    const visible = this.removeOverriddenMethods(candidates);
    const constrained = this.constrainParameters(
      visible,
      destination.parameterDescriptors,
    );
    const match =
      constrained.length === 1
        ? constrained[0]
        : constrained.length === 0 && visible.length === 1
          ? visible[0]
          : null;
    return match
      ? {
          classDescriptor: match.owner,
          kind: "method",
          name: match.method.originalName ?? match.method.name,
          descriptor: match.method.descriptor,
        }
      : null;
  }

  private prepareSession(sessionId: number, documents: SourceDocument[]): void {
    if (this.sessionId !== sessionId) {
      this.sessionId = sessionId;
      this.outlines.clear();
    }
    for (const document of documents) {
      this.outlines.set(document.descriptor, document.outline);
    }
  }

  private async outline(
    sessionId: number,
    descriptor: string,
  ): Promise<ClassOutline | null> {
    const cached = this.outlines.get(descriptor);
    if (cached) {
      return cached;
    }
    try {
      const outline = await this.client.inspectClass(sessionId, descriptor);
      this.outlines.set(descriptor, outline);
      return outline;
    } catch {
      return null;
    }
  }

  private field(outline: ClassOutline, name: string) {
    const matches = outline.fields.filter(
      (field) => (field.originalName ?? field.name) === name,
    );
    return matches.length === 1 ? matches[0] : null;
  }

  private constrainParameters(
    candidates: MethodCandidate[],
    arguments_: (string | null)[] | undefined,
  ): MethodCandidate[] {
    if (!arguments_) {
      return candidates;
    }
    return candidates.filter(
      (candidate) =>
        candidate.parameters.length === arguments_.length &&
        candidate.parameters.every(
          (parameter, index) =>
            arguments_[index] === null || arguments_[index] === parameter,
        ),
    );
  }

  private removeOverriddenMethods(
    candidates: MethodCandidate[],
  ): MethodCandidate[] {
    const nearest = new Map<string, number>();
    for (const candidate of candidates) {
      const signature = candidate.parameters.join("");
      nearest.set(
        signature,
        Math.min(nearest.get(signature) ?? Number.MAX_SAFE_INTEGER, candidate.depth),
      );
    }
    return candidates.filter(
      (candidate) =>
        candidate.depth === nearest.get(candidate.parameters.join("")),
    );
  }
}

interface MethodCandidate {
  owner: string;
  method: MethodOutline;
  parameters: string[];
  depth: number;
}

class JvmDescriptor {
  static parameters(descriptor: string): string[] | null {
    if (!descriptor.startsWith("(")) {
      return null;
    }
    let index = 1;
    const parameters: string[] = [];
    while (index < descriptor.length && descriptor[index] !== ")") {
      const start = index;
      while (descriptor[index] === "[") {
        index += 1;
      }
      if (descriptor[index] === "L") {
        const end = descriptor.indexOf(";", index);
        if (end < 0) {
          return null;
        }
        index = end + 1;
      } else {
        index += 1;
      }
      parameters.push(descriptor.slice(start, index));
    }
    return descriptor[index] === ")" ? parameters : null;
  }
}
