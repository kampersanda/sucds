use std::time::Duration;

use rand::{Rng, SeedableRng};
use rand_chacha::ChaChaRng;

use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, Criterion, SamplingMode,
};

const SAMPLE_SIZE: usize = 30;
const WARM_UP_TIME: Duration = Duration::from_secs(5);
const MEASURE_TIME: Duration = Duration::from_secs(10);

const SEED_BITS: u64 = 113;
const SEED_QUERIES: u64 = 114514;

const NUM_BITS: usize = 1 << 20;
const NUM_QUERIES: usize = 1000;

fn gen_random_bits(len: usize, p: f64, seed: u64) -> Vec<bool> {
    let mut rng = ChaChaRng::seed_from_u64(seed);
    (0..len).map(|_| rng.gen_bool(p)).collect()
}

fn gen_random_ints(len: usize, min: usize, max: usize, seed: u64) -> Vec<usize> {
    let mut rng = ChaChaRng::seed_from_u64(seed);
    (0..len).map(|_| rng.gen_range(min..=max)).collect()
}

fn count_ones(bits: &[bool]) -> usize {
    bits.iter().filter(|&&b| b).count()
}

fn criterion_select_50(c: &mut Criterion) {
    let mut group = c.benchmark_group("timing_select_50");
    group.sample_size(SAMPLE_SIZE);
    group.warm_up_time(WARM_UP_TIME);
    group.measurement_time(MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);

    let bits = gen_random_bits(NUM_BITS, 0.5, SEED_BITS);
    let queries = gen_random_ints(NUM_QUERIES, 0, count_ones(&bits) - 1, SEED_QUERIES);

    perform_select(&mut group, &bits, &queries);
}

fn criterion_select_10(c: &mut Criterion) {
    let mut group = c.benchmark_group("timing_select_10");
    group.sample_size(SAMPLE_SIZE);
    group.warm_up_time(WARM_UP_TIME);
    group.measurement_time(MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);

    let bits = gen_random_bits(NUM_BITS, 0.1, SEED_BITS);
    let queries = gen_random_ints(NUM_QUERIES, 0, count_ones(&bits) - 1, SEED_QUERIES);

    perform_select(&mut group, &bits, &queries);
}

fn criterion_select_1(c: &mut Criterion) {
    let mut group = c.benchmark_group("timing_select_1");
    group.sample_size(SAMPLE_SIZE);
    group.warm_up_time(WARM_UP_TIME);
    group.measurement_time(MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);

    let bits = gen_random_bits(NUM_BITS, 0.01, SEED_BITS);
    let queries = gen_random_ints(NUM_QUERIES, 0, count_ones(&bits) - 1, SEED_QUERIES);

    perform_select(&mut group, &bits, &queries);
}

fn perform_select(group: &mut BenchmarkGroup<WallTime>, bits: &[bool], queries: &[usize]) {
    group.bench_function("sucds/RsBitVector", |b| {
        let idx = sucds::RsBitVector::from_bits(bits, true, false);
        b.iter(|| {
            let mut sum = 0;
            for &q in queries {
                sum += idx.select1(q);
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("sucds/DArray", |b| {
        let idx = sucds::DArray::from_bits(bits);
        b.iter(|| {
            let mut sum = 0;
            for &q in queries {
                sum += idx.select(q);
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("sucds/EliasFano", |b| {
        let idx = sucds::EliasFano::from_bits(bits, false).unwrap();
        b.iter(|| {
            let mut sum = 0;
            for &q in queries {
                sum += idx.select(q);
            }
            if sum == 0 {
                panic!();
            }
        });
    });
}

criterion_group!(
    benches,
    criterion_select_50,
    criterion_select_10,
    criterion_select_1
);

criterion_main!(benches);
