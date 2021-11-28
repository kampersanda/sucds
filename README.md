# `sucds`: Succinct data structures in Rust

`sucds` contains some succinct data structures written in Rust.

## Data structures

So far, the following data structures are implemented. All of them are yet another Rust ports of implementations of [C++ Succinct library by Ottaviano](https://github.com/ot/succinct).

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
