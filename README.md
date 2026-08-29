# Succinct data structures in Rust

[![Crates.io](https://img.shields.io/crates/v/sucds.svg)](https://crates.io/crates/sucds)
[![Documentation](https://docs.rs/sucds/badge.svg)](https://docs.rs/sucds)
[![Build Status](https://github.com/kampersanda/sucds/actions/workflows/ci.yml/badge.svg)](https://github.com/kampersanda/sucds/actions)

Sucds provides some [succinct data structures](https://en.wikipedia.org/wiki/Succinct_data_structure) written in Rust.

## Features

- **Rich collection:** Four categories of data structures are provided, as listed [below](#data-structures).
- **Consistent interfaces:** Data structures in the same category share traits such as `Access`, `Rank`, and `Select`, and are easily replaceable.
- **Serialization:** Every data structure can be serialized and deserialized through the `Serializable` trait.
- **Pure Rust:** The implementation is written in safe and pure Rust, with optional `no_std` support.

## Data structures

| Category | Queries | Implementations |
| --- | --- | --- |
| [Integer vectors](https://docs.rs/sucds/latest/sucds/int_vectors/) | Access/Update on a vector of unsigned integers | `CompactVector`, `PrefixSummedEliasFano`, `DacsByte`, `DacsOpt` |
| [Bit vectors](https://docs.rs/sucds/latest/sucds/bit_vectors/) | Access/Rank/Select on a bit vector | `BitVector`, `Rank9Sel`, `DArray`, `SArray` |
| [Monotone-increasing integer sequences](https://docs.rs/sucds/latest/sucds/mii_sequences/) | Rank/Select/Predecessor/Successor on a sorted integer sequence | `EliasFano` |
| [Character sequences](https://docs.rs/sucds/latest/sucds/char_sequences/) | Access/Rank/Select on a sequence over an alphabet | `WaveletMatrix` |

Implementations in the same category differ in time and space trade-offs.
See the module documentation linked above to choose one.

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
