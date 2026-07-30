import { java } from "@codemirror/lang-java";
import { StreamLanguage } from "@codemirror/language";
import {
  c,
  clike,
  cpp,
  kotlin,
} from "@codemirror/legacy-modes/mode/clike";
import { css } from "@codemirror/legacy-modes/mode/css";
import { gas } from "@codemirror/legacy-modes/mode/gas";
import { groovy } from "@codemirror/legacy-modes/mode/groovy";
import {
  javascript,
  json,
  typescript,
} from "@codemirror/legacy-modes/mode/javascript";
import { properties } from "@codemirror/legacy-modes/mode/properties";
import { protobuf } from "@codemirror/legacy-modes/mode/protobuf";
import { shell } from "@codemirror/legacy-modes/mode/shell";
import { standardSQL } from "@codemirror/legacy-modes/mode/sql";
import { toml } from "@codemirror/legacy-modes/mode/toml";
import { xml } from "@codemirror/legacy-modes/mode/xml";
import { yaml } from "@codemirror/legacy-modes/mode/yaml";
import type { Extension } from "@codemirror/state";

import type { ResourceTextFormat } from "../domain/models";

function words(value: string): Record<string, boolean> {
  return Object.fromEntries(value.split(/\s+/).map((word) => [word, true]));
}

const aidl = clike({
  name: "aidl",
  keywords: words(
    "const enum import in inout interface oneway out package parcelable union",
  ),
  types: words(
    "boolean byte char double float int long String CharSequence List Map IBinder ParcelFileDescriptor",
  ),
  blockKeywords: words("enum interface parcelable union"),
  atoms: words("true false null"),
});

export class ResourceLanguageRegistry {
  private readonly languages: Partial<Record<ResourceTextFormat, Extension>> = {
    xml: StreamLanguage.define(xml),
    html: StreamLanguage.define(xml),
    json: StreamLanguage.define(json),
    css: StreamLanguage.define(css),
    javascript: StreamLanguage.define(javascript),
    typescript: StreamLanguage.define(typescript),
    java: java(),
    kotlin: StreamLanguage.define(kotlin),
    aidl: StreamLanguage.define(aidl),
    smali: StreamLanguage.define(gas),
    properties: StreamLanguage.define(properties),
    yaml: StreamLanguage.define(yaml),
    toml: StreamLanguage.define(toml),
    sql: StreamLanguage.define(standardSQL),
    shell: StreamLanguage.define(shell),
    c: StreamLanguage.define(c),
    cpp: StreamLanguage.define(cpp),
    proto: StreamLanguage.define(protobuf),
    gradle: StreamLanguage.define(groovy),
  };

  extensionFor(format: ResourceTextFormat | null): Extension | null {
    return format ? this.languages[format] ?? null : null;
  }
}

export const resourceLanguages = new ResourceLanguageRegistry();
