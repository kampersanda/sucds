//! Compares loading data structures from a file by copying with loading them from a memory-mapped file.
//!
//! Run with `cargo run --release --example mmap`.
use std::fs::File;
use std::io::{BufWriter, Read};
use std::path::Path;
use std::time::Instant;

use memmap2::Mmap;
use sucds::bit_vectors::{Rank, Rank9Sel, Select};
use sucds::char_sequences::WaveletMatrix;
use sucds::int_vectors::CompactVector;
use sucds::serial::Bytes;
use sucds::Serializable;

const NUM_QUERIES: usize = 1_000_000;

/// Simple xorshift for reproducible data without extra dependencies.
fn xorshift(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

fn save<S: Serializable>(x: &S, path: &Path) -> std::io::Result<()> {
    x.serialize_into(BufWriter::new(File::create(path)?))
        .map(|_| ())
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e.to_string()))
}

fn measure<S, F>(name: &str, path: &Path, query: F) -> Result<(), Box<dyn std::error::Error>>
where
    S: Serializable,
    F: Fn(&S, u64) -> usize,
{
    let run = |label: &str, load: &dyn Fn() -> Result<S, Box<dyn std::error::Error>>| {
        let t = Instant::now();
        let x = load()?;
        let load_time = t.elapsed();
        let mut state = 0x1234_5678;
        let t = Instant::now();
        let mut sum = 0;
        for _ in 0..NUM_QUERIES {
            sum += query(&x, xorshift(&mut state));
        }
        let query_time = t.elapsed();
        println!(
            "{name:<16} {label:<28} load {:>10.3} ms, {NUM_QUERIES} queries {:>8.3} ms (checksum {sum})",
            load_time.as_secs_f64() * 1e3,
            query_time.as_secs_f64() * 1e3
        );
        Ok::<_, Box<dyn std::error::Error>>(())
    };
    run("read + deserialize_from", &|| {
        let mut buf = vec![];
        File::open(path)?.read_to_end(&mut buf)?;
        Ok(S::deserialize_from(&buf[..])?)
    })?;
    run("read + .._unchecked", &|| {
        let mut buf = vec![];
        File::open(path)?.read_to_end(&mut buf)?;
        Ok(S::deserialize_from_unchecked(&buf[..])?)
    })?;
    run("mmap + .._bytes", &|| {
        // SAFETY: The file is not modified while mapped.
        let mmap = unsafe { Mmap::map(&File::open(path)?)? };
        Ok(S::deserialize_from_bytes(&mut Bytes::from_owner(mmap))?)
    })?;
    run("mmap + .._bytes_unchecked", &|| {
        // SAFETY: The file is not modified while mapped.
        let mmap = unsafe { Mmap::map(&File::open(path)?)? };
        Ok(S::deserialize_from_bytes_unchecked(&mut Bytes::from_owner(mmap))?)
    })?;
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let dir = std::env::temp_dir();

    let num_bits = 1 << 30;
    let mut state = 42;
    let bits = (0..num_bits).map(|_| xorshift(&mut state) % 4 == 0);
    let r9 = Rank9Sel::from_bits(bits).select1_hints();
    let num_ones = r9.num_ones() as u64;
    let path = dir.join("sucds_mmap_rank9sel.bin");
    save(&r9, &path)?;
    drop(r9);
    println!("Rank9Sel: {num_bits} bits, {} bytes", path.metadata()?.len());
    measure::<Rank9Sel, _>("Rank9Sel", &path, |x, r| {
        x.rank1((r % num_bits) as usize).unwrap() + x.select1((r % num_ones) as usize).unwrap()
    })?;

    let len = 1 << 24;
    let vals: Vec<u64> = (0..len).map(|_| xorshift(&mut state) % 65536).collect();
    let wm = WaveletMatrix::new(CompactVector::from_slice(&vals), |bv| {
        Rank9Sel::new(bv).select1_hints().select0_hints()
    })?;
    let path = dir.join("sucds_mmap_wavelet_matrix.bin");
    save(&wm, &path)?;
    drop(wm);
    println!("WaveletMatrix: {len} values, {} bytes", path.metadata()?.len());
    measure::<WaveletMatrix<Rank9Sel>, _>("WaveletMatrix", &path, |x, r| {
        x.access((r % len) as usize).unwrap() as usize
    })?;
    Ok(())
}
