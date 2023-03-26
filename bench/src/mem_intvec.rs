use sucds::Serializable;

const DBLP_PSEF_STR: &str = include_str!("../data/lcps/dblp.1MiB.txt");
const DNA_PSEF_STR: &str = include_str!("../data/lcps/dna.1MiB.txt");
const PROTEINS_PSEF_STR: &str = include_str!("../data/lcps/proteins.1MiB.txt");

fn parse_ints_from_str(s: &str) -> Vec<u32> {
    let mut ints = vec![];
    for l in s.split('\n') {
        if !l.is_empty() {
            ints.push(l.parse().unwrap());
        }
    }
    ints
}

fn main() {
    show_memories("dblp", &parse_ints_from_str(DBLP_PSEF_STR));
    show_memories("dna", &parse_ints_from_str(DNA_PSEF_STR));
    show_memories("proteins", &parse_ints_from_str(PROTEINS_PSEF_STR));
}

fn show_data_stats(vals: &[u32]) {
    let nvals = vals.len();
    let max = vals.iter().cloned().max().unwrap();
    let mean = vals.iter().cloned().sum::<u32>() as f64 / nvals as f64;

    let mut sorted = vals.to_vec();
    sorted.sort_unstable();
    let median = sorted[nvals / 2];

    println!("Basic: n_vals={nvals}, max_val={max}, mean_val={mean:.3}, median_val={median}");
}

fn show_memories(title: &str, vals: &[u32]) {
    println!("[{title}]");
    show_data_stats(vals);

    let bytes = {
        let idx = sucds::int_vectors::CompactVector::from_slice(vals).unwrap();
        idx.size_in_bytes()
    };
    print_memory("CompactVector", bytes, vals.len());

    let bytes = {
        let idx = sucds::int_vectors::PrefixSummedEliasFano::from_slice(vals).unwrap();
        idx.size_in_bytes()
    };
    print_memory("PrefixSummedEliasFano", bytes, vals.len());

    let bytes = {
        let idx = sucds::int_vectors::DacsByte::from_slice(vals).unwrap();
        idx.size_in_bytes()
    };
    print_memory("DacsByte", bytes, vals.len());

    let bytes = {
        let idx = sucds::int_vectors::DacsOpt::from_slice(vals, None).unwrap();
        idx.size_in_bytes()
    };
    print_memory("DacsOpt", bytes, vals.len());
}

fn print_memory(name: &str, bytes: usize, nvals: usize) {
    println!(
        "{}: {:.3} bits per value",
        name,
        (bytes * 8) as f64 / nvals as f64
    );
}
