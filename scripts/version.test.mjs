import assert from "node:assert/strict";
import test from "node:test";

import {
  CargoLockDocument,
  SemanticVersion,
  TomlDocument,
  VersionPolicy,
} from "./version.mjs";

class RepositoryFixture {
  constructor({ exact = null, latest = null, commits = 0, sha = "0123456789", dirty = false } = {}) {
    this.exact = exact;
    this.latest = latest;
    this.commits = commits;
    this.sha = sha;
    this.dirty = dirty;
  }

  exactRelease() {
    return this.exact;
  }

  latestRelease() {
    return this.latest;
  }

  commitCount() {
    return this.commits;
  }

  shortSha() {
    return this.sha;
  }

  isDirty() {
    return this.dirty;
  }
}

test("release versions start at 1.0.0", () => {
  assert.equal(SemanticVersion.release("v1.0.0").toString(), "1.0.0");
  assert.throws(() => SemanticVersion.release("v0.9.9"), /start at 1\.0\.0/);
  assert.throws(() => SemanticVersion.release("v1.0.0-beta.1"), /vMAJOR/);
});

test("an unreleased repository starts on the 1.0.0 development line", () => {
  const version = new VersionPolicy().commit(
    new RepositoryFixture({ commits: 42, sha: "abcdef1234" }),
  );
  assert.equal(version, "1.0.0-dev.42+gabcdef1234");
});

test("commits after a release move to the next patch development line", () => {
  const latest = { tag: "v1.4.2", version: SemanticVersion.release("v1.4.2") };
  const version = new VersionPolicy().commit(
    new RepositoryFixture({ latest, commits: 3, sha: "abcdef1234" }),
  );
  assert.equal(version, "1.4.3-dev.3+gabcdef1234");
});

test("a clean release tag resolves to the exact release version", () => {
  const exact = { tag: "v2.0.0", version: SemanticVersion.release("v2.0.0") };
  assert.equal(
    new VersionPolicy().commit(new RepositoryFixture({ exact })),
    "2.0.0",
  );
});

test("TOML workspace version updates without rewriting other sections", () => {
  const document = new TomlDocument(
    '[workspace]\nmembers = []\n\n[workspace.package]\nedition = "2021"\n',
  );
  document.setString("workspace.package", "version", "1.2.3");
  assert.equal(document.value("workspace.package", "version"), '"1.2.3"');
  assert.match(document.toString(), /\[workspace]\nmembers = \[\]/);
});

test("Cargo lock package versions update independently", () => {
  const document = new CargoLockDocument(
    'version = 4\n\n[[package]]\nname = "dexdec"\nversion = "0.1.0"\n' +
      '\n[[package]]\nname = "rusty-dex"\nversion = "0.2.0"\n',
  );
  document.setPackageVersion("dexdec", "1.0.0-dev.4+gabcdef1234");
  assert.equal(document.packageVersion("dexdec"), "1.0.0-dev.4+gabcdef1234");
  assert.equal(document.packageVersion("rusty-dex"), "0.2.0");
});
