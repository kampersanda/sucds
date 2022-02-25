use rand::{Rng, SeedableRng};
use rand_chacha::ChaChaRng;

const SEED_BITS: u64 = 113;
const NUM_BITS: usize = 1 << 20;

fn main() {
    show_memories(0.5);
    show_memories(0.1);
    show_memories(0.01);
}

fn gen_random_bits(len: usize, p: f64, seed: u64) -> Vec<bool> {
    let mut rng = ChaChaRng::seed_from_u64(seed);
    (0..len).map(|_| rng.gen_bool(p)).collect()
}

fn show_memories(p: f64) {
    let bits = gen_random_bits(NUM_BITS, p, SEED_BITS);
    println!("[p = {}]", p);

    let bytes = {
        let idx = sucds::RsBitVector::from_bits(bits.iter().cloned());
        idx.size_in_bytes()
    };
    print_memory("RsBitVector", bytes);

    let bytes = {
        let idx = sucds::RsBitVector::from_bits(bits.iter().cloned())
            .select1_hints()
            .select0_hints();
        idx.size_in_bytes()
    };
    print_memory("RsBitVector (with select hints)", bytes);

    let bytes = {
        let idx = sucds::DArray::from_bits(bits.iter().cloned());
        idx.size_in_bytes()
    };
    print_memory("DArray", bytes);

    let bytes = {
        let idx = sucds::EliasFano::from_bits(bits.iter().cloned()).unwrap();
        idx.size_in_bytes()
    };
    print_memory("EliasFano", bytes);

    let bytes = {
        let idx = sucds::EliasFano::from_bits(bits.iter().cloned())
            .unwrap()
            .enable_rank();
        idx.size_in_bytes()
    };
    print_memory("EliasFano (with rank index)", bytes);
}

fn print_memory(name: &str, bytes: usize) {
    println!(
        "{}: {:.3} bits per bit",
        name,
        (bytes * 8) as f64 / NUM_BITS as f64
    );
}
