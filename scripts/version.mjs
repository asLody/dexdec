#!/usr/bin/env node

import { execFileSync } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const REPOSITORY_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const PRODUCT_MANIFESTS = [
  "dexdec/Cargo.toml",
  "dexdec-workbench/Cargo.toml",
  "dexdec-mcp/Cargo.toml",
  "dexdec-gui/src-tauri/Cargo.toml",
];
const PRODUCT_PACKAGES = ["dexdec", "dexdec-workbench", "dexdec-mcp", "dexdec-app"];
const INTERNAL_MANIFESTS = [
  "dexdec-workbench/Cargo.toml",
  "dexdec-mcp/Cargo.toml",
  "dexdec-gui/src-tauri/Cargo.toml",
];
const PRODUCT_LICENSE = "Apache-2.0";
const PRODUCT_README = "README.md";
const DEXDEC_DOCUMENTATION = "https://docs.rs/dexdec";
const NODE_REQUIREMENT = ">=22";

export class SemanticVersion {
  constructor(major, minor, patch) {
    this.major = major;
    this.minor = minor;
    this.patch = patch;
  }

  static release(value) {
    const normalized = value.startsWith("v") ? value.slice(1) : value;
    const matched = /^(0|[1-9]\d*)\.(0|[1-9]\d*)\.(0|[1-9]\d*)$/.exec(normalized);
    if (!matched) {
      throw new Error(`release version must match vMAJOR.MINOR.PATCH: ${value}`);
    }
    const version = new SemanticVersion(...matched.slice(1).map(Number));
    if (version.compare(FIRST_RELEASE) < 0) {
      throw new Error(`DexDec versions start at ${FIRST_RELEASE}; received ${version}`);
    }
    return version;
  }

  compare(other) {
    return this.major - other.major || this.minor - other.minor || this.patch - other.patch;
  }

  nextPatch() {
    return new SemanticVersion(this.major, this.minor, this.patch + 1);
  }

  toString() {
    return `${this.major}.${this.minor}.${this.patch}`;
  }
}

const FIRST_RELEASE = new SemanticVersion(1, 0, 0);

export class GitRepository {
  constructor(root = REPOSITORY_ROOT) {
    this.root = root;
  }

  exactRelease() {
    if (this.isDirty()) return null;
    return this.releaseTags(["--points-at", "HEAD"])[0] ?? null;
  }

  latestRelease() {
    return this.releaseTags(["--merged", "HEAD", "--sort=-version:refname"])[0] ?? null;
  }

  commitCount(sinceTag = null) {
    return Number(this.git("rev-list", "--count", sinceTag ? `${sinceTag}..HEAD` : "HEAD"));
  }

  shortSha() {
    return this.git("rev-parse", "--short=10", "HEAD");
  }

  isDirty() {
    return this.git("status", "--porcelain").length > 0;
  }

  releaseTags(arguments_) {
    return this.git("tag", ...arguments_)
      .split("\n")
      .map((tag) => tag.trim())
      .filter(Boolean)
      .map((tag) => {
        try {
          return { tag, version: SemanticVersion.release(tag) };
        } catch {
          return null;
        }
      })
      .filter(Boolean)
      .sort((left, right) => right.version.compare(left.version));
  }

  git(...arguments_) {
    return execFileSync("git", ["-C", this.root, ...arguments_], {
      encoding: "utf8",
      stdio: ["ignore", "pipe", "pipe"],
    }).trim();
  }
}

export class VersionPolicy {
  commit(repository) {
    const exact = repository.exactRelease();
    if (exact) return exact.version.toString();

    const latest = repository.latestRelease();
    const base = latest ? latest.version.nextPatch() : FIRST_RELEASE;
    const count = repository.commitCount(latest?.tag ?? null);
    const dirty = repository.isDirty() ? ".dirty" : "";
    return `${base}-dev.${count}+g${repository.shortSha()}${dirty}`;
  }

  release(tag) {
    return SemanticVersion.release(tag).toString();
  }
}

export class TomlDocument {
  constructor(source) {
    this.lines = source.replace(/\r\n/g, "\n").split("\n");
  }

  value(section, key) {
    const bounds = this.section(section);
    if (!bounds) return null;
    for (let index = bounds.start + 1; index < bounds.end; index += 1) {
      const property = parseTomlProperty(this.lines[index]);
      if (property?.key === key) return property.value;
    }
    return null;
  }

  setString(section, key, value) {
    const bounds = this.section(section);
    if (!bounds) throw new Error(`missing TOML section [${section}]`);
    for (let index = bounds.start + 1; index < bounds.end; index += 1) {
      const property = parseTomlProperty(this.lines[index]);
      if (property?.key === key) {
        this.lines[index] = `${key} = ${JSON.stringify(value)}`;
        return;
      }
    }
    this.lines.splice(bounds.start + 1, 0, `${key} = ${JSON.stringify(value)}`);
  }

  section(name) {
    const heading = `[${name}]`;
    const start = this.lines.findIndex((line) => line.trim() === heading);
    if (start < 0) return null;
    let end = this.lines.length;
    for (let index = start + 1; index < this.lines.length; index += 1) {
      if (/^\s*\[.+]\s*$/.test(this.lines[index])) {
        end = index;
        break;
      }
    }
    return { start, end };
  }

  toString() {
    return this.lines.join("\n");
  }
}

export class CargoLockDocument {
  constructor(source) {
    this.lines = source.replace(/\r\n/g, "\n").split("\n");
  }

  packageVersion(name) {
    const package_ = this.package(name);
    return package_ ? unquote(this.property(package_, "version")?.value) : null;
  }

  setPackageVersion(name, version) {
    const package_ = this.package(name);
    if (!package_) throw new Error(`missing Cargo.lock package ${name}`);
    const property = this.property(package_, "version");
    if (!property) throw new Error(`missing Cargo.lock version for ${name}`);
    this.lines[property.index] = `version = ${JSON.stringify(version)}`;
  }

  package(name) {
    const matches = this.packages().filter(
      (package_) => unquote(this.property(package_, "name")?.value) === name,
    );
    if (matches.length > 1) throw new Error(`duplicate Cargo.lock package ${name}`);
    return matches[0] ?? null;
  }

  packages() {
    const packages = [];
    for (let index = 0; index < this.lines.length; index += 1) {
      if (this.lines[index].trim() !== "[[package]]") continue;
      let end = this.lines.length;
      for (let next = index + 1; next < this.lines.length; next += 1) {
        if (/^\s*\[\[.+]]\s*$/.test(this.lines[next])) {
          end = next;
          break;
        }
      }
      packages.push({ start: index, end });
    }
    return packages;
  }

  property(bounds, key) {
    for (let index = bounds.start + 1; index < bounds.end; index += 1) {
      const property = parseTomlProperty(this.lines[index]);
      if (property?.key === key) return { ...property, index };
    }
    return null;
  }

  toString() {
    return this.lines.join("\n");
  }
}

export class VersionSynchronizer {
  constructor(root = REPOSITORY_ROOT) {
    this.root = root;
  }

  sync(version) {
    assertProductVersion(version);
    const cargoPath = this.path("Cargo.toml");
    const cargo = new TomlDocument(readFileSync(cargoPath, "utf8"));
    cargo.setString("workspace.package", "version", version);
    writeFileSync(cargoPath, cargo.toString());

    const cargoLockPath = this.path("Cargo.lock");
    const cargoLock = new CargoLockDocument(readFileSync(cargoLockPath, "utf8"));
    for (const package_ of PRODUCT_PACKAGES) cargoLock.setPackageVersion(package_, version);
    writeFileSync(cargoLockPath, cargoLock.toString());

    const packagePath = this.path("dexdec-gui/package.json");
    const packageDocument = readJson(packagePath);
    packageDocument.version = version;
    writeJson(packagePath, packageDocument);

    const lockPath = this.path("dexdec-gui/package-lock.json");
    const lock = readJson(lockPath);
    lock.version = version;
    if (lock.packages?.[""]) lock.packages[""].version = version;
    writeJson(lockPath, lock);
  }

  check() {
    const errors = [];
    const cargo = new TomlDocument(readFileSync(this.path("Cargo.toml"), "utf8"));
    const cargoVersion = unquote(cargo.value("workspace.package", "version"));
    try {
      assertProductVersion(cargoVersion);
    } catch (error) {
      errors.push(error.message);
    }
    compare(
      errors,
      "Cargo workspace license",
      unquote(cargo.value("workspace.package", "license")),
      PRODUCT_LICENSE,
    );
    compare(
      errors,
      "Cargo workspace readme",
      unquote(cargo.value("workspace.package", "readme")),
      PRODUCT_README,
    );

    const packageDocument = readJson(this.path("dexdec-gui/package.json"));
    const lock = readJson(this.path("dexdec-gui/package-lock.json"));
    const tauri = readJson(this.path("dexdec-gui/src-tauri/tauri.conf.json"));
    compare(errors, "npm package", packageDocument.version, cargoVersion);
    compare(errors, "npm lockfile", lock.version, cargoVersion);
    compare(errors, "npm root lock package", lock.packages?.[""]?.version, cargoVersion);
    compare(errors, "npm package license", packageDocument.license, PRODUCT_LICENSE);
    compare(errors, "npm Node requirement", packageDocument.engines?.node, NODE_REQUIREMENT);
    compare(errors, "npm private package", packageDocument.private, true);
    compare(errors, "Tauri version source", tauri.version, "../package.json");

    const cargoLock = new CargoLockDocument(readFileSync(this.path("Cargo.lock"), "utf8"));
    for (const package_ of PRODUCT_PACKAGES) {
      compare(errors, `Cargo.lock ${package_}`, cargoLock.packageVersion(package_), cargoVersion);
    }

    for (const relative of PRODUCT_MANIFESTS) {
      const manifest = new TomlDocument(readFileSync(this.path(relative), "utf8"));
      compare(errors, `${relative} workspace version`, manifest.value("package", "version.workspace"), "true");
      compare(errors, `${relative} workspace license`, manifest.value("package", "license.workspace"), "true");
      compare(errors, `${relative} workspace readme`, manifest.value("package", "readme.workspace"), "true");
    }
    for (const relative of INTERNAL_MANIFESTS) {
      const manifest = new TomlDocument(readFileSync(this.path(relative), "utf8"));
      compare(errors, `${relative} publish`, manifest.value("package", "publish"), "false");
    }
    const dexdecManifest = new TomlDocument(
      readFileSync(this.path("dexdec/Cargo.toml"), "utf8"),
    );
    compare(
      errors,
      "dexdec documentation",
      unquote(dexdecManifest.value("package", "documentation")),
      DEXDEC_DOCUMENTATION,
    );
    if (errors.length) throw new Error(errors.join("\n"));
    return cargoVersion;
  }

  path(relative) {
    return resolve(this.root, relative);
  }
}

function parseTomlProperty(line) {
  const matched = /^\s*([A-Za-z0-9_.-]+)\s*=\s*(.*?)\s*(?:#.*)?$/.exec(line);
  return matched ? { key: matched[1], value: matched[2] } : null;
}

function unquote(value) {
  if (typeof value !== "string") return value;
  if (value.startsWith('"') && value.endsWith('"')) return JSON.parse(value);
  return value;
}

function readJson(path) {
  return JSON.parse(readFileSync(path, "utf8"));
}

function writeJson(path, document) {
  writeFileSync(path, `${JSON.stringify(document, null, 2)}\n`);
}

function compare(errors, label, actual, expected) {
  if (actual !== expected) errors.push(`${label} is ${actual ?? "missing"}; expected ${expected}`);
}

function assertProductVersion(version) {
  const release = /^(0|[1-9]\d*)\.(0|[1-9]\d*)\.(0|[1-9]\d*)$/;
  const development = /^(0|[1-9]\d*)\.(0|[1-9]\d*)\.(0|[1-9]\d*)-dev\.\d+\+g[0-9a-f]+(?:\.dirty)?$/;
  if (!release.test(version) && !development.test(version)) {
    throw new Error(`invalid DexDec product version: ${version ?? "missing"}`);
  }
  const core = version.split("-")[0];
  if (SemanticVersion.release(core).compare(FIRST_RELEASE) < 0) {
    throw new Error(`DexDec versions start at ${FIRST_RELEASE}`);
  }
}

function option(arguments_, name) {
  const index = arguments_.indexOf(name);
  if (index < 0) return null;
  const value = arguments_[index + 1];
  if (!value || value.startsWith("--")) throw new Error(`${name} requires a value`);
  return value;
}

function resolveVersion(arguments_) {
  const release = option(arguments_, "--release");
  if (release) return new VersionPolicy().release(release);
  const channel = option(arguments_, "--channel") ?? "commit";
  if (channel !== "commit") throw new Error(`unsupported version channel: ${channel}`);
  return new VersionPolicy().commit(new GitRepository());
}

function usage() {
  return [
    "Usage:",
    "  node scripts/version.mjs resolve --channel commit",
    "  node scripts/version.mjs sync --channel commit",
    "  node scripts/version.mjs sync --release v1.0.0",
    "  node scripts/version.mjs check",
  ].join("\n");
}

export function main(arguments_ = process.argv.slice(2)) {
  const [command, ...options] = arguments_;
  const synchronizer = new VersionSynchronizer();
  switch (command) {
    case "resolve": {
      const version = resolveVersion(options);
      process.stdout.write(`${version}\n`);
      return;
    }
    case "sync": {
      const version = resolveVersion(options);
      synchronizer.sync(version);
      process.stdout.write(`${version}\n`);
      return;
    }
    case "check":
      process.stdout.write(`${synchronizer.check()}\n`);
      return;
    default:
      throw new Error(usage());
  }
}

if (process.argv[1] && import.meta.url === pathToFileURL(resolve(process.argv[1])).href) {
  try {
    main();
  } catch (error) {
    process.stderr.write(`version: ${error.message}\n`);
    process.exitCode = 1;
  }
}
