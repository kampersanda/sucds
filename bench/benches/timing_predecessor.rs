use std::time::Duration;

use rand::{Rng, SeedableRng};
use rand_chacha::ChaChaRng;

use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, Criterion, SamplingMode,
};

use sucds::Predecessor;

const SAMPLE_SIZE: usize = 30;
const WARM_UP_TIME: Duration = Duration::from_secs(5);
const MEASURE_TIME: Duration = Duration::from_secs(10);

const SEED_BITS: u64 = 334;
const SEED_QUERIES: u64 = 114514;

const NUM_BITS: &[usize] = &[1 << 10, 1 << 15, 1 << 20];
const NUM_QUERIES: usize = 1000;

fn gen_random_bits(len: usize, p: f64, seed: u64) -> Vec<bool> {
    let mut rng = ChaChaRng::seed_from_u64(seed);
    let mut bits: Vec<_> = (0..len).map(|_| rng.gen_bool(p)).collect();
    bits[0] = true; // Set to 1 so that Predecessor always succeeds.
    bits
}

fn gen_random_ints(len: usize, min: usize, max: usize, seed: u64) -> Vec<usize> {
    let mut rng = ChaChaRng::seed_from_u64(seed);
    (0..len).map(|_| rng.gen_range(min..max)).collect()
}

fn criterion_predecessor_50(c: &mut Criterion) {
    let mut group = c.benchmark_group("timing_predecessor_50");
    group.sample_size(SAMPLE_SIZE);
    group.warm_up_time(WARM_UP_TIME);
    group.measurement_time(MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);

    let max_nbits = *NUM_BITS.last().unwrap();
    let bits = gen_random_bits(max_nbits, 0.5, SEED_BITS);

    perform_predecessor(&mut group, &bits);
}

fn criterion_predecessor_10(c: &mut Criterion) {
    let mut group = c.benchmark_group("timing_predecessor_10");
    group.sample_size(SAMPLE_SIZE);
    group.warm_up_time(WARM_UP_TIME);
    group.measurement_time(MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);

    let max_nbits = *NUM_BITS.last().unwrap();
    let bits = gen_random_bits(max_nbits, 0.1, SEED_BITS);

    perform_predecessor(&mut group, &bits);
}

fn criterion_predecessor_1(c: &mut Criterion) {
    let mut group = c.benchmark_group("timing_predecessor_1");
    group.sample_size(SAMPLE_SIZE);
    group.warm_up_time(WARM_UP_TIME);
    group.measurement_time(MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);

    let max_nbits = *NUM_BITS.last().unwrap();
    let bits = gen_random_bits(max_nbits, 0.01, SEED_BITS);

    perform_predecessor(&mut group, &bits);
}

fn run_queries<P: Predecessor>(pred: &P, queries: &[usize]) {
    let mut sum = 0;
    for &q in queries {
        sum += pred.predecessor1(q).unwrap();
    }
    if sum == 0 {
        panic!("Should not come.");
    }
}

fn perform_predecessor(group: &mut BenchmarkGroup<WallTime>, bits: &[bool]) {
    for &nbits in NUM_BITS {
        let bits = &bits[..nbits];
        let queries = gen_random_ints(NUM_QUERIES, 0, bits.len(), SEED_QUERIES);

        let nbits_str = format!("n_{nbits}");

        group.bench_function(format!("{nbits_str}/sucds/BitVector"), |b| {
            let pred = sucds::BitVector::from_bits(bits.iter().cloned());
            b.iter(|| run_queries(&pred, &queries));
        });

        group.bench_function(format!("{nbits_str}/sucds/RsBitVector"), |b| {
            let pred = sucds::RsBitVector::from_bits(bits.iter().cloned());
            b.iter(|| run_queries(&pred, &queries));
        });

        group.bench_function(format!("{nbits_str}/sucds/EliasFano"), |b| {
            let pred = sucds::EliasFano::from_bits(bits.iter().cloned())
                .unwrap()
                .enable_rank();
            b.iter(|| run_queries(&pred, &queries));
        });
    }
}

criterion_group!(
    benches,
    criterion_predecessor_50,
    criterion_predecessor_10,
    criterion_predecessor_1
);

criterion_main!(benches);
