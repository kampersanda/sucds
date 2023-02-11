use sucds::Searial;

const DBLP_PSEF_BYTES: &[u8] = include_bytes!("../lcps/dblp.1MiB.psef");
const DNA_PSEF_BYTES: &[u8] = include_bytes!("../lcps/dna.1MiB.psef");
const PROTEINS_PSEF_BYTES: &[u8] = include_bytes!("../lcps/proteins.1MiB.psef");

fn extract_ints_from_psef(bytes: &[u8]) -> Vec<u32> {
    let psef = sucds::PrefixSummedEliasFano::deserialize_from(bytes).unwrap();
    psef.iter().map(|x| x as u32).collect()
}

fn main() {
    show_memories("dblp", &extract_ints_from_psef(DBLP_PSEF_BYTES));
    show_memories("dna", &extract_ints_from_psef(DNA_PSEF_BYTES));
    show_memories("proteins", &extract_ints_from_psef(PROTEINS_PSEF_BYTES));
}

fn show_memories(title: &str, vals: &[u32]) {
    println!("[{title}]");

    let bytes = {
        let idx = sucds::CompactVector::from_slice(vals).unwrap();
        idx.size_in_bytes()
    };
    print_memory("CompactVector", bytes, vals.len());

    let bytes = {
        let idx = sucds::PrefixSummedEliasFano::from_slice(vals).unwrap();
        idx.size_in_bytes()
    };
    print_memory("PrefixSummedEliasFano", bytes, vals.len());

    let bytes = {
        let idx = sucds::DacsByte::from_slice(vals).unwrap();
        idx.size_in_bytes()
    };
    print_memory("DacsByte", bytes, vals.len());

    let bytes = {
        let idx = sucds::DacsOpt::from_slice(vals, None).unwrap();
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
