# `sucds`: Succinct data structures in Rust

![](https://github.com/kampersanda/sucds/actions/workflows/rust.yml/badge.svg)
[![Documentation](https://docs.rs/sucds/badge.svg)](https://docs.rs/sucds)
[![Crates.io](https://img.shields.io/crates/v/sucds.svg)](https://crates.io/crates/sucds)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](https://github.com/kampersanda/sucds/blob/master/LICENSE)

`sucds` contains some [succinct data structures](https://en.wikipedia.org/wiki/Succinct_data_structure) written in Rust.
See [the documentation](https://docs.rs/sucds/latest/sucds/) for the data structures supported.

## Limitation

This library is designed to run on 64-bit machines.

## Build docs

The document can be compiled with the following command:

```
$ RUSTDOCFLAGS="--html-in-header katex.html" cargo doc --no-deps
```

## Licensing

This library is free software provided under MIT.
