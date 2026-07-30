# rusty-dex

[![GitHub Actions Workflow Status](https://img.shields.io/github/actions/workflow/status/rusty-rs/rusty-dex/ci.yml?branch=main&style=for-the-badge)](https://github.com/rusty-rs/rusty-dex/actions/workflows/ci.yml)
[![Crates.io Version](https://img.shields.io/crates/v/rusty-dex?style=for-the-badge)](https://crates.io/crates/rusty-dex)
[![docs.rs](https://img.shields.io/docsrs/rusty-dex?style=for-the-badge)](https://docs.rs/rusty-dex/latest/rusty_dex/)

Rust parser for DEX files

## About

The DEX file contains the bytecode of Android applications. This crate provides
methods to extract and parse them.

## Current status

The parser can handle most of the DEX standard (see [this
issue](https://github.com/rusty-rs/rusty-dex/issues/3) for the up-to-date
details). The API is under active development and might change.
