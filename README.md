# `sucds`: Succinct data structures in Rust

![](https://github.com/kampersanda/sucds/actions/workflows/rust.yml/badge.svg)
[![Documentation](https://docs.rs/sucds/badge.svg)](https://docs.rs/sucds)
[![Crates.io](https://img.shields.io/crates/v/sucds.svg)](https://crates.io/crates/sucds)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](https://github.com/kampersanda/sucds/blob/master/LICENSE)

`sucds` contains some [succinct data structures](https://en.wikipedia.org/wiki/Succinct_data_structure) written in Rust.

## Data structures

So far, the following data structures are implemented. Most of them are yet another Rust ports of implementations of [C++ Succinct library by Ottaviano](https://github.com/ot/succinct).
For a detailed description of each data structure, please see the [respective documentation](https://docs.rs/sucds/latest/sucds/).

- [`BitVector`](https://docs.rs/sucds/latest/sucds/bit_vector/struct.BitVector.html)
  - Bit vector in a plain format, supporting some utilities such as update, chunking, and predecessor queries.
- [`CompactVector`](https://docs.rs/sucds/latest/sucds/compact_vector/struct.CompactVector.html)
  - Compact vector in which each integer is represented in a fixed number of bits.
- [`RsBitVector`](https://docs.rs/sucds/latest/sucds/rs_bit_vector/struct.RsBitVector.html)
  - Rank/select data structure over bit vectors with Vigna's rank9 and hinted selection techniques.
- [`DArray`](https://docs.rs/sucds/latest/sucds/darray/struct.DArray.html)
  - Constant-time select data structure over integer sets with the dense array technique by Okanohara and Sadakane.
- [`EliasFano`](https://docs.rs/sucds/latest/sucds/elias_fano/struct.EliasFano.html)
  - Compressed monotone sequence with Elias-Fano encoding.
- [`EliasFanoList`](https://docs.rs/sucds/latest/sucds/elias_fano_list/struct.EliasFanoList.html)
  - Compressed integer list with prefix-summed Elias-Fano encoding.
- [`WaveletMatrix`](https://docs.rs/sucds/latest/sucds/wavelet_matrix/struct.WaveletMatrix.html)
  - Space-efficient data structure providing myriad operations over integer sequences.

## Limitation

This library is designed to run on 64-bit machines.

## Build docs

The document can be compiled with the following command:

```
$ RUSTDOCFLAGS="--html-in-header katex.html" cargo doc --no-deps
```

## Licensing

This library is free software provided under MIT.
