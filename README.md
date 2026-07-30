<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="assets/brand/dexdec-wordmark-dark.png">
    <img src="assets/brand/dexdec-wordmark.png" alt="DexDec" width="190">
  </picture>
</p>

<p align="center">
  <strong>Fast, accurate Android decompilation for humans and AI agents.</strong><br />
  Explore APK and DEX bytecode as readable Java or Kotlin, then hand the same live context to your coding agent.
</p>

<p align="center">
  <img src="https://img.shields.io/badge/Rust-2021-CE422B?logo=rust&amp;logoColor=white" alt="Rust 2021" />
  <img src="https://img.shields.io/badge/Desktop-Tauri-24C8DB?logo=tauri&amp;logoColor=white" alt="Tauri desktop application" />
  <img src="https://img.shields.io/badge/Output-Java%20%7C%20Kotlin-7F52FF?logo=kotlin&amp;logoColor=white" alt="Java and Kotlin output" />
  <img src="https://img.shields.io/badge/AI-MCP%20ready-5D8CFF" alt="AI agent integration through MCP" />
  <img src="https://img.shields.io/badge/License-Apache%202.0-4C8BF5" alt="Apache License 2.0" />
</p>

<p align="center">
  <img src="assets/readme/dexdec-workbench.png" alt="DexDec desktop workbench showing an APK project, decompiled Java source, and symbol outline" width="1200" />
</p>

DexDec is a native reverse-engineering workbench for large, complex, and heavily
obfuscated Android applications. It opens projects quickly, produces
higher-fidelity source than previous-generation Java decompilers, and keeps
making progress on APKs that cause older tools to stop.

Use it directly as a focused desktop application, or connect an AI agent through
MCP. The agent can understand what is open in DexDec, inspect only the code it
needs, follow exact references, read packaged resources, and reveal its findings
back in the desktop UI.

## Features

<table>
<tr>
<td width="50%" valign="top">

### Fast on large APKs

Start exploring large multi-DEX applications immediately. DexDec generates
source only when it is needed, keeping project opening, search, and navigation
responsive.

</td>
<td width="50%" valign="top">

### Higher-fidelity source

Recover code that is closer to what a developer would write, with fewer
duplicated conditions, broken exception blocks, artificial temporary variables,
and misleading types than traditional Java decompilers.

</td>
</tr>
<tr>
<td width="50%" valign="top">

### Built to keep going

One difficult class should not make an entire application unusable. DexDec
isolates troublesome code and continues recovering the rest of the project
instead of turning one failure into an all-or-nothing result.

</td>
<td width="50%" valign="top">

### Java and Kotlin

Choose the output that fits the task and switch languages without reopening the
archive. Use familiar Java for compatibility or Kotlin for modern Android work.

</td>
</tr>
<tr>
<td width="50%" valign="top">

### Complete APK exploration

Browse classes, packages, `AndroidManifest.xml`, decoded XML, AIDL, images,
resource tables, native libraries, and other packaged files in one workspace.

</td>
<td width="50%" valign="top">

### Symbol-aware navigation

Quick-open classes and members, jump through declarations and usages, inspect
references, reveal symbols in the Explorer, and move through navigation history.

</td>
</tr>
<tr>
<td width="50%" valign="top">

### Professional workspace

Use preview and pinned tabs, split editor groups, code folding, outlines,
context menus, configurable keymaps, and light or dark editor themes.

</td>
<td width="50%" valign="top">

### Reversible renaming

Rename classes, fields, methods, and local symbols without modifying the input.
Undo or redo edits and persist project state to a DexDB file when ready.

</td>
</tr>
<tr>
<td width="50%" valign="top">

### AI-native analysis

Connect Codex, Claude Code, Cursor, Visual Studio Code, or Grok from Settings.
Agents receive live project and editor context instead of relying on screenshots,
copied snippets, or guessed class names.

</td>
<td width="50%" valign="top">

### Project-wide code search

Search generated source with case-sensitive, whole-word, or regular-expression
matching. Results stream in as classes are analyzed and jump to the exact source
position.

</td>
</tr>
</table>

## MCP

DexDec exposes the current project and editor context through MCP. Compatible
agents can search symbols and resources, decompile code on demand, follow
references, and navigate results in the desktop app.

1. Open **Settings > MCP**.
2. Select an installed client and choose **Configure**.
3. For another MCP client, copy its generated configuration from the same page.

Configured clients can be disconnected from **Settings > MCP** at any time.

## Build the desktop app

Requirements:

- A current stable Rust toolchain
- Node.js and npm
- Platform prerequisites for [Tauri 2](https://v2.tauri.app/start/prerequisites/)

Run the development application:

```sh
cd dexdec-gui
npm ci
npm run desktop
```

Build a production macOS disk image:

```sh
cd dexdec-gui
npm ci
npm run tauri -- build --bundles dmg
```

The DMG is written to `target/release/bundle/dmg/`.

## CLI

Build the command-line tool:

```sh
cargo build --release -p dexdec
```

Common commands:

```sh
dexdec inspect app.apk
dexdec decompile app.apk --class com.example.MainActivity --language java
dexdec decompile app.apk --output-dir decompiled
dexdec resources read app.apk AndroidManifest.xml
```

Run `dexdec --help` or `dexdec <command> --help` for all options.

## Rust library

The high-level API can serve repeated and interactive decompilation requests
without reopening the input each time:

```rust
use dexdec::{DecompileOptions, Decompiler, SourceLanguage};

let options = DecompileOptions::default()
    .with_language(SourceLanguage::Java);
let mut decompiler = Decompiler::open("classes.dex")?
    .with_options(options);

let unit = decompiler.class("Lcom/example/App;")?;
println!("{}", unit.source);
```

Disable default CLI dependencies when embedding only the library:

```toml
[dependencies]
dexdec = { path = "../dexdec", default-features = false }
```

## License

DexDec is available under the [Apache License 2.0](LICENSE).
