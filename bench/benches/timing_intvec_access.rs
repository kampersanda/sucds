use std::time::Duration;

use rand::{Rng, SeedableRng};
use rand_chacha::ChaChaRng;

use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, Criterion, SamplingMode,
};

use sucds::int_vectors::Access;

const SAMPLE_SIZE: usize = 30;
const WARM_UP_TIME: Duration = Duration::from_secs(5);
const MEASURE_TIME: Duration = Duration::from_secs(10);

const SEED_QUERIES: u64 = 114514;
const NUM_QUERIES: usize = 1000;

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

fn gen_random_ints(len: usize, min: usize, max: usize, seed: u64) -> Vec<usize> {
    let mut rng = ChaChaRng::seed_from_u64(seed);
    (0..len).map(|_| rng.gen_range(min..max)).collect()
}

fn criterion_intvec_access_dblp(c: &mut Criterion) {
    let mut group = c.benchmark_group("timing_intvec_access_dblp_1MiB");
    group.sample_size(SAMPLE_SIZE);
    group.warm_up_time(WARM_UP_TIME);
    group.measurement_time(MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);

    let vals = parse_ints_from_str(DBLP_PSEF_STR);
    perform_intvec_access(&mut group, &vals);
}

fn criterion_intvec_access_dna(c: &mut Criterion) {
    let mut group = c.benchmark_group("timing_intvec_access_dna_1MiB");
    group.sample_size(SAMPLE_SIZE);
    group.warm_up_time(WARM_UP_TIME);
    group.measurement_time(MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);

    let vals = parse_ints_from_str(DNA_PSEF_STR);
    perform_intvec_access(&mut group, &vals);
}

fn criterion_intvec_access_proteins(c: &mut Criterion) {
    let mut group = c.benchmark_group("timing_intvec_access_proteins_1MiB");
    group.sample_size(SAMPLE_SIZE);
    group.warm_up_time(WARM_UP_TIME);
    group.measurement_time(MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);

    let vals = parse_ints_from_str(PROTEINS_PSEF_STR);
    perform_intvec_access(&mut group, &vals);
}

fn run_queries<G: Access>(idx: &G, queries: &[usize]) {
    let mut sum = 0;
    for &q in queries {
        sum += idx.access(q).unwrap();
    }
    if sum == 0 {
        panic!("Should not come.");
    }
}

fn perform_intvec_access(group: &mut BenchmarkGroup<WallTime>, vals: &[u32]) {
    let queries = gen_random_ints(NUM_QUERIES, 0, vals.len(), SEED_QUERIES);

    group.bench_function("sucds/CompactVector", |b| {
        let idx = sucds::int_vectors::CompactVector::from_slice(vals).unwrap();
        b.iter(|| run_queries(&idx, &queries));
    });

    group.bench_function("sucds/PrefixSummedEliasFano", |b| {
        let idx = sucds::int_vectors::PrefixSummedEliasFano::from_slice(vals).unwrap();
        b.iter(|| run_queries(&idx, &queries));
    });

    group.bench_function("sucds/DacsByte", |b| {
        let idx = sucds::int_vectors::DacsByte::from_slice(vals).unwrap();
        b.iter(|| run_queries(&idx, &queries));
    });

    group.bench_function("sucds/DacsOpt", |b| {
        let idx = sucds::int_vectors::DacsOpt::from_slice(vals, None).unwrap();
        b.iter(|| run_queries(&idx, &queries));
    });
}

criterion_group!(
    benches,
    criterion_intvec_access_dblp,
    criterion_intvec_access_dna,
    criterion_intvec_access_proteins
);

criterion_main!(benches);
