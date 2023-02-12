use std::time::Duration;

use rand::{Rng, SeedableRng};
use rand_chacha::ChaChaRng;

use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, Criterion, SamplingMode,
};

use sucds::{IntGetter, Searial};

const SAMPLE_SIZE: usize = 30;
const WARM_UP_TIME: Duration = Duration::from_secs(5);
const MEASURE_TIME: Duration = Duration::from_secs(10);

const SEED_QUERIES: u64 = 114514;
const NUM_QUERIES: usize = 1000;

const DBLP_PSEF_BYTES: &[u8] = include_bytes!("../lcps/dblp.1MiB.psef");
const DNA_PSEF_BYTES: &[u8] = include_bytes!("../lcps/dna.1MiB.psef");
const PROTEINS_PSEF_BYTES: &[u8] = include_bytes!("../lcps/proteins.1MiB.psef");

fn extract_ints_from_psef(bytes: &[u8]) -> Vec<u32> {
    let psef = sucds::PrefixSummedEliasFano::deserialize_from(bytes).unwrap();
    psef.iter().map(|x| x as u32).collect()
}

fn gen_random_ints(len: usize, min: usize, max: usize, seed: u64) -> Vec<usize> {
    let mut rng = ChaChaRng::seed_from_u64(seed);
    (0..len).map(|_| rng.gen_range(min..max)).collect()
}

fn criterion_int_get_dblp(c: &mut Criterion) {
    let mut group = c.benchmark_group("timing_int_getter_dblp");
    group.sample_size(SAMPLE_SIZE);
    group.warm_up_time(WARM_UP_TIME);
    group.measurement_time(MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);

    let vals = extract_ints_from_psef(DBLP_PSEF_BYTES);
    perform_int_get(&mut group, &vals);
}

fn criterion_int_get_dna(c: &mut Criterion) {
    let mut group = c.benchmark_group("timing_int_getter_dna");
    group.sample_size(SAMPLE_SIZE);
    group.warm_up_time(WARM_UP_TIME);
    group.measurement_time(MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);

    let vals = extract_ints_from_psef(DNA_PSEF_BYTES);
    perform_int_get(&mut group, &vals);
}

fn criterion_int_get_proteins(c: &mut Criterion) {
    let mut group = c.benchmark_group("timing_int_getter_proteins");
    group.sample_size(SAMPLE_SIZE);
    group.warm_up_time(WARM_UP_TIME);
    group.measurement_time(MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);

    let vals = extract_ints_from_psef(PROTEINS_PSEF_BYTES);
    perform_int_get(&mut group, &vals);
}

fn run_queries<G: IntGetter>(getter: &G, queries: &[usize]) {
    let mut sum = 0;
    for &q in queries {
        sum += getter.get_int(q).unwrap();
    }
    if sum == 0 {
        panic!("Should not come.");
    }
}

fn perform_int_get(group: &mut BenchmarkGroup<WallTime>, vals: &[u32]) {
    let queries = gen_random_ints(NUM_QUERIES, 0, vals.len(), SEED_QUERIES);

    let nvals = vals.len();
    let nvals_str = format!("n_{nvals}");

    group.bench_function(format!("{nvals_str}/sucds/CompactVector"), |b| {
        let getter = sucds::CompactVector::from_slice(vals).unwrap();
        b.iter(|| run_queries(&getter, &queries));
    });

    group.bench_function(format!("{nvals_str}/sucds/PrefixSummedEliasFano"), |b| {
        let getter = sucds::PrefixSummedEliasFano::from_slice(vals).unwrap();
        b.iter(|| run_queries(&getter, &queries));
    });

    group.bench_function(format!("{nvals_str}/sucds/DacsByte"), |b| {
        let getter = sucds::DacsByte::from_slice(vals).unwrap();
        b.iter(|| run_queries(&getter, &queries));
    });

    group.bench_function(format!("{nvals_str}/sucds/DacsOpt"), |b| {
        let getter = sucds::DacsOpt::from_slice(vals, None).unwrap();
        b.iter(|| run_queries(&getter, &queries));
    });
}

criterion_group!(
    benches,
    criterion_int_get_dblp,
    criterion_int_get_dna,
    criterion_int_get_proteins
);

criterion_main!(benches);
