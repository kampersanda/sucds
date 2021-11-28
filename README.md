# `sucds`: Succinct data structures in Rust

[![Documentation](https://docs.rs/sucds/badge.svg)](https://docs.rs/sucds)
[![Crates.io](https://img.shields.io/crates/v/sucds.svg)](https://crates.io/crates/sucds)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](https://github.com/kampersanda/sucds/blob/master/LICENSE)

`sucds` contains some succinct data structures written in Rust.

## Data structures

So far, the following data structures are implemented. All of them are yet another Rust ports of implementations of [C++ Succinct library by Ottaviano](https://github.com/ot/succinct).

- `BitVector`
  - Bit vector supporting some utilities such as update, chunking, predecessor, and successor.
- `RsBitVector`
  - Rank/select data structure over bit vector through Vigna's rank9 and hinted selection technique.
- `EliasFano`
  - Compressed monotone sequence through Elias-Fano encoding.
- `DArray`
  - Constant-time select data structure over integer set through dense array technique by Okanohara and Sadakane.

# Usage

To use `sucds`, depend on it in your Cargo manifest:

```toml
# Cargo.toml

[dependencies]
sucds = "0.1"
```

# Licensing

This library is free software provided under MIT.
