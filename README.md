# Succinct data structures in Rust

[![Crates.io](https://img.shields.io/crates/v/sucds.svg)](https://crates.io/crates/sucds)
[![Documentation](https://docs.rs/sucds/badge.svg)](https://docs.rs/sucds)
[![Build Status](https://github.com/kampersanda/sucds/actions/workflows/ci.yml/badge.svg)](https://github.com/kampersanda/sucds/actions)

Sucds provides some [succinct data structures](https://en.wikipedia.org/wiki/Succinct_data_structure) written in Rust.

## Features

- **Curated collection:** Data structures in [four categories](#data-structures) are provided, focusing on those with competitive advantages.
- **Consistent interfaces:** Data structures in the same category share traits such as `Access`, `Rank`, and `Select`, and are easily replaceable.
- **Serialization:** Every data structure can be serialized and deserialized through the `Serializable` trait.
- **Pure Rust:** The implementation is written in safe and pure Rust, with optional `no_std` support.

## Data structures

- [Integer vectors](https://docs.rs/sucds/latest/sucds/int_vectors/): Store a sequence of unsigned integers in compressed space, while allowing for random access.
- [Bit vectors](https://docs.rs/sucds/latest/sucds/bit_vectors/): Store a set of positions in a bit sequence, while allowing for counting and locating the set bits.
- [Monotone-increasing integer sequences](https://docs.rs/sucds/latest/sucds/mii_sequences/): Store a sorted sequence of integers in compressed space, while allowing for searching it.
- [Character sequences](https://docs.rs/sucds/latest/sucds/char_sequences/): Store a string over an alphabet, while allowing for counting and locating each character.

See the module documentation linked above for the available implementations
and their time and space trade-offs.

## Example

```rust
use sucds::bit_vectors::{Rank, Rank9Sel, Select};
use sucds::int_vectors::{Access, DacsOpt};
use sucds::Serializable;

fn main() -> sucds::Result<()> {
    // Bit vector with rank/select indexes.
    let bv = Rank9Sel::from_bits([true, false, false, true]).select1_hints();
    assert_eq!(bv.rank1(3), Some(1)); // Number of ones in bv[0..3]
    assert_eq!(bv.select1(1), Some(3)); // Position of the 1st one (0-origin)

    // Compressed integer vector.
    let iv = DacsOpt::from_slice(&[5u64, 0, 100000, 334], None)?;
    assert_eq!(iv.access(2), Some(100000));

    // Serialization/deserialization.
    let mut bytes = vec![];
    iv.serialize_into(&mut bytes)?;
    assert_eq!(iv, DacsOpt::deserialize_from(&bytes[..])?);

    Ok(())
}
```

## Documentation

https://docs.rs/sucds/

Or, the document can be compiled with the following command:

```console
RUSTDOCFLAGS="--html-in-header katex.html" cargo doc --no-deps
```

## Limitation

This library is designed to run on 64-bit machines.

## Licensing

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.
