# Succinct data structures in Rust

![](https://github.com/kampersanda/sucds/actions/workflows/rust.yml/badge.svg)
[![Documentation](https://docs.rs/sucds/badge.svg)](https://docs.rs/sucds)
[![Crates.io](https://img.shields.io/crates/v/sucds.svg)](https://crates.io/crates/sucds)

Sucds provides some [succinct data structures](https://en.wikipedia.org/wiki/Succinct_data_structure) written in Rust.

## Documentation

See https://docs.rs/sucds/ for supported data structures.

## Limitation

This library is designed to run on 64-bit machines.

## Build docs

The document can be compiled with the following command:

```console
RUSTDOCFLAGS="--html-in-header katex.html" cargo doc --no-deps
```

## Licensing

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.
