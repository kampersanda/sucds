use rand::{Rng, SeedableRng};
use rand_chacha::ChaChaRng;

use sucds::WaveletMatrixBuilder;

const SIGMA: u64 = 256;
const NUM_INTS: usize = 1 << 26;

fn main() {
    let mut rng = ChaChaRng::seed_from_u64(13);
    // let mut wmb = WaveletMatrixBuilder::new();
    let mut wmb = WaveletMatrixBuilder::with_width(8);
    for _ in 0..NUM_INTS {
        wmb.push(rng.gen_range(0..SIGMA) as usize);
    }
    let wm = wmb.build().unwrap();
    dbg!(wm.len());
}
