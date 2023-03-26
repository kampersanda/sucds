use sucds::bit_vectors::{BitVector, Rank};
use sucds::int_vectors::CompactVector;
use sucds::Serializable;

const DBLP_PSEF_STR: &str = include_str!("../data/texts/dblp.1MiB.txt");
const DNA_PSEF_STR: &str = include_str!("../data/texts/dna.1MiB.txt");
const PROTEINS_PSEF_STR: &str = include_str!("../data/texts/proteins.1MiB.txt");

fn main() {
    show_memories("dblp", &load_text(DBLP_PSEF_STR));
    show_memories("dna", &load_text(DNA_PSEF_STR));
    show_memories("proteins", &load_text(PROTEINS_PSEF_STR));
}

// In effective alphabet
fn load_text(s: &str) -> CompactVector {
    let mut text = s.as_bytes().to_vec();
    let mut alphabet = BitVector::from_bit(false, 256);
    text.iter()
        .for_each(|&c| alphabet.set_bit(usize::from(c), true).unwrap());
    for i in 0..text.len() {
        text[i] = alphabet.rank1(usize::from(text[i])).unwrap() as u8;
    }
    CompactVector::from_slice(&text).unwrap()
}

fn show_memories(title: &str, text: &CompactVector) {
    println!("[{title}]");
    show_data_stats(text);

    let bytes = {
        let idx =
            sucds::char_sequences::WaveletMatrix::<sucds::bit_vectors::Rank9Sel>::new(text.clone())
                .unwrap();
        idx.size_in_bytes()
    };
    print_memory("WaveletMatrix<Rank9Sel>", bytes, text.len());

    let bytes = {
        let idx =
            sucds::char_sequences::WaveletMatrix::<sucds::bit_vectors::DArray>::new(text.clone())
                .unwrap();
        idx.size_in_bytes()
    };
    print_memory("WaveletMatrix<DArray>", bytes, text.len());
}

fn show_data_stats(text: &CompactVector) {
    let nvals = text.len();
    let max = text.iter().max().unwrap();
    println!("Basic: n_vals={nvals}, max_val={max}");
}

fn print_memory(name: &str, bytes: usize, nvals: usize) {
    println!(
        "{}: {:.3} bits per value",
        name,
        (bytes * 8) as f64 / nvals as f64
    );
}
