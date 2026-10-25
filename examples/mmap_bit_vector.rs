//! Loads a bit vector from a memory-mapped file without copying the words.
use std::fs::File;

use memmap2::Mmap;
use sucds::bit_vectors::{BitVector, Rank};
use sucds::serial::Bytes;
use sucds::Serializable;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let path = std::env::temp_dir().join("sucds_mmap_bit_vector.bin");

    let bv = BitVector::from_bits((0..1_000_000).map(|i| i % 3 == 0));
    bv.serialize_into(File::create(&path)?)?;

    // SAFETY: The file must not be modified while mapped.
    let mmap = unsafe { Mmap::map(&File::open(&path)?)? };
    let mut bytes = Bytes::from_owner(mmap);
    let other = BitVector::deserialize_from_bytes(&mut bytes)?;

    assert_eq!(bv, other);
    println!("rank1(500000) = {:?}", other.rank1(500_000));
    Ok(())
}
