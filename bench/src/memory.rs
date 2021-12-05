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
        let idx = sucds::RsBitVector::from_bits(&bits, false, false);
        bincode::serialize(&idx).unwrap().len()
    };
    print_memory("RsBitVector(false,false)", bytes);

    let bytes = {
        let idx = sucds::RsBitVector::from_bits(&bits, true, true);
        bincode::serialize(&idx).unwrap().len()
    };
    print_memory("RsBitVector(true,true)", bytes);

    let bytes = {
        let idx = sucds::DArray::from_bits(&bits);
        bincode::serialize(&idx).unwrap().len()
    };
    print_memory("DArray", bytes);

    let bytes = {
        let idx = sucds::EliasFano::from_bits(&bits, false).unwrap();
        bincode::serialize(&idx).unwrap().len()
    };
    print_memory("EliasFano(false)", bytes);

    let bytes = {
        let idx = sucds::EliasFano::from_bits(&bits, true).unwrap();
        bincode::serialize(&idx).unwrap().len()
    };
    print_memory("EliasFano(true)", bytes);
}

fn print_memory(name: &str, bytes: usize) {
    println!(
        "{}: {:.3} bits per bit",
        name,
        (bytes * 8) as f64 / NUM_BITS as f64
    );
}
