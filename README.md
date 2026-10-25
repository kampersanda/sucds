# Succinct data structures in Rust

[![Crates.io](https://img.shields.io/crates/v/sucds.svg)](https://crates.io/crates/sucds)
[![Documentation](https://docs.rs/sucds/badge.svg)](https://docs.rs/sucds)
[![Build Status](https://github.com/kampersanda/sucds/actions/workflows/ci.yml/badge.svg)](https://github.com/kampersanda/sucds/actions)

Sucds provides some [succinct data structures](https://en.wikipedia.org/wiki/Succinct_data_structure) written in Rust.

## Features

- **Curated collection:** Data structures in four categories are provided, focusing on those with competitive advantages.
- **Consistent interfaces:** Data structures in the same category share traits such as `Access`, `Rank`, and `Select`, and are easily replaceable.
- **Ensured safety:** Unsafe instructions, typically reserved for extremely low-level
  programming, are avoided.
- **Pure Rust:** The implementation is written in safe and pure Rust, with optional `no_std` support.

## Data structures

- [Integer vectors](https://docs.rs/sucds/latest/sucds/int_vectors/): Store a sequence of unsigned integers in compressed space, while allowing for random access.
- [Bit vectors](https://docs.rs/sucds/latest/sucds/bit_vectors/): Store a set of positions in a bit sequence, while allowing for counting and locating the set bits.
- [Monotone-increasing integer sequences](https://docs.rs/sucds/latest/sucds/mii_sequences/): Store a sorted sequence of integers in compressed space, while allowing for searching it.
- [Character sequences](https://docs.rs/sucds/latest/sucds/char_sequences/): Store a string over an alphabet, while allowing for counting and locating each character.

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

## Memory-mapped files

Data structures can be loaded from a memory-mapped file without copying their arrays,
through `Serializable::deserialize_from_bytes_unchecked()` on [`bytes::Bytes`](https://docs.rs/bytes).
The loading takes constant time independent of the data size.

```rust
use std::fs::File;

use memmap2::Mmap;
use sucds::bit_vectors::{Rank, Rank9Sel};
use sucds::serial::Bytes;
use sucds::Serializable;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let path = std::env::temp_dir().join("sucds_readme.bin");
    let bv = Rank9Sel::from_bits([true, false, false, true]);
    bv.serialize_into(File::create(&path)?)?;

    // SAFETY: The file is not modified while mapped.
    let mmap = unsafe { Mmap::map(&File::open(&path)?)? };
    let mut bytes = Bytes::from_owner(mmap);
    let other = Rank9Sel::deserialize_from_bytes_unchecked(&mut bytes)?;
    assert_eq!(other.rank1(4), Some(2));

    Ok(())
}
```

Note that:

- The file must not be modified or truncated while mapped; otherwise, the behavior is undefined.
  This is why `Mmap::map()` is unsafe.
- The arrays are shared only if the bytes start at an 8-byte boundary, which memory maps satisfy,
  and the machine is little-endian. Otherwise, they are copied.
- The unchecked variant skips the consistency checks scanning the whole data,
  so queries may panic for corrupted files.
  Use `deserialize_from_bytes()` for untrusted files.
- Modifying a loaded data structure (e.g., `BitVector::set_bit()`) copies its arrays into the heap.

See [`examples/mmap.rs`](examples/mmap.rs) for a comparison of the loading times.

## Documentation

https://docs.rs/sucds/

Or, the document can be compiled with the following command:

```console
RUSTDOCFLAGS="--html-in-header katex.html" cargo doc --no-deps
```

## Portability

This library is tuned for 64-bit machines but also runs on 32-bit ones, where
the broadword operations are emulated and each data structure holds less than
2^32 bits or integers.

The serialization format is independent of the pointer width, since `usize` and
`isize` are stored as 64-bit little-endian integers. Deserialization fails with
an error if a stored value does not fit in `usize` of the machine.

## Licensing

Licensed under either of

- Apache License, Version 2.0
  ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license
  ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.
