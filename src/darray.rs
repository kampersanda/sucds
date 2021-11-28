#![cfg(target_pointer_width = "64")]

use crate::{broadword, BitVector};
use serde::{Deserialize, Serialize};

const BLOCK_LEN: usize = 1024;
const SUBBLOCK_LEN: usize = 32;
const MAX_IN_BLOCK_DISTANCE: usize = 1 << 16;

#[derive(Serialize, Deserialize)]
pub struct DArray {
    block_inventory: Vec<isize>,
    subblock_inventory: Vec<u16>,
    overflow_positions: Vec<usize>,
    num_positions: usize,
    over_one: bool, // TODO: Solve with generics
}

impl DArray {
    pub fn new(bv: &BitVector, over_one: bool) -> Self {
        Self::build(bv, over_one)
    }

    pub fn select(&self, bv: &BitVector, n: usize) -> usize {
        debug_assert!(n < self.num_positions);

        let block = n / BLOCK_LEN;
        let block_pos = self.block_inventory[block];

        if block_pos < 0 {
            let overflow_pos = (-block_pos - 1) as usize;
            return self.overflow_positions[overflow_pos + (n % BLOCK_LEN)];
        }

        let subblock = n / SUBBLOCK_LEN;
        let mut reminder = n % SUBBLOCK_LEN;
        let start_pos = block_pos as usize + self.subblock_inventory[subblock] as usize;

        if reminder == 0 {
            start_pos
        } else {
            let w = {
                if self.over_one {
                    Self::get_word_over_one
                } else {
                    Self::get_word_over_zero
                }
            };

            let mut word_idx = start_pos / 64;
            let word_shift = start_pos % 64;
            let mut word = w(bv, word_idx) & (std::usize::MAX << word_shift);

            loop {
                let popcnt = broadword::popcount(word);
                if reminder < popcnt {
                    break;
                }
                reminder -= popcnt;
                word_idx += 1;
                word = w(bv, word_idx);
            }

            64 * word_idx + broadword::select_in_word(word, reminder)
        }
    }

    pub const fn len(&self) -> usize {
        self.num_positions
    }

    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn build(bv: &BitVector, over_one: bool) -> Self {
        let mut cur_block_positions = vec![];
        let mut block_inventory = vec![];
        let mut subblock_inventory = vec![];
        let mut overflow_positions = vec![];
        let mut num_positions = 0;

        let w = {
            if over_one {
                Self::get_word_over_one
            } else {
                Self::get_word_over_zero
            }
        };

        for word_idx in 0..bv.num_words() {
            let mut cur_pos = word_idx * 64;
            let mut cur_word = w(bv, word_idx);

            while let Some(l) = broadword::lsb(cur_word) {
                cur_pos += l;
                cur_word >>= l;
                if cur_pos >= bv.len() {
                    break;
                }

                cur_block_positions.push(cur_pos);
                if cur_block_positions.len() == BLOCK_LEN {
                    Self::flush_cur_block(
                        &mut cur_block_positions,
                        &mut block_inventory,
                        &mut subblock_inventory,
                        &mut overflow_positions,
                    );
                }

                cur_word >>= 1;
                cur_pos += 1;
                num_positions += 1;
            }
        }

        if !cur_block_positions.is_empty() {
            Self::flush_cur_block(
                &mut cur_block_positions,
                &mut block_inventory,
                &mut subblock_inventory,
                &mut overflow_positions,
            );
        }

        block_inventory.shrink_to_fit();
        subblock_inventory.shrink_to_fit();
        overflow_positions.shrink_to_fit();

        Self {
            block_inventory,
            subblock_inventory,
            overflow_positions,
            num_positions,
            over_one,
        }
    }

    fn flush_cur_block(
        cur_block_positions: &mut Vec<usize>,
        block_inventory: &mut Vec<isize>,
        subblock_inventory: &mut Vec<u16>,
        overflow_positions: &mut Vec<usize>,
    ) {
        let &first = cur_block_positions.first().unwrap();
        let &last = cur_block_positions.last().unwrap();
        if last - first < MAX_IN_BLOCK_DISTANCE {
            block_inventory.push(first as isize);
            for i in (0..cur_block_positions.len()).step_by(SUBBLOCK_LEN) {
                subblock_inventory.push((cur_block_positions[i] - first) as u16);
            }
        } else {
            block_inventory.push(-((overflow_positions.len() + 1) as isize));
            for &x in cur_block_positions.iter() {
                overflow_positions.push(x);
            }
            for _ in (0..cur_block_positions.len()).step_by(SUBBLOCK_LEN) {
                subblock_inventory.push(std::u16::MAX);
            }
        }
        cur_block_positions.clear();
    }

    fn get_word_over_one(bv: &BitVector, word_idx: usize) -> usize {
        bv.get_word(word_idx)
    }

    fn get_word_over_zero(bv: &BitVector, word_idx: usize) -> usize {
        !bv.get_word(word_idx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    fn gen_random_bits(len: usize, seed: u64) -> Vec<bool> {
        let mut rng = ChaChaRng::seed_from_u64(seed);
        (0..len).map(|_| rng.gen::<bool>()).collect()
    }

    fn test_select(bv: &BitVector, da: &DArray) {
        let mut cur_rank = 0;
        for i in 0..bv.len() {
            if bv.get_bit(i) {
                assert_eq!(i, da.select(bv, cur_rank));
                cur_rank += 1;
            }
        }
        assert_eq!(cur_rank, da.len());
    }

    fn test_select0(bv: &BitVector, da: &DArray) {
        let mut cur_rank = 0;
        for i in 0..bv.len() {
            if !bv.get_bit(i) {
                assert_eq!(i, da.select(bv, cur_rank));
                cur_rank += 1;
            }
        }
    }

    #[test]
    fn test_tiny_bits() {
        let bv = BitVector::from_bits(&[true, false, false, true, false, true, true]);
        let da = DArray::new(&bv, true);
        assert_eq!(da.select(&bv, 0), 0);
        assert_eq!(da.select(&bv, 1), 3);
        assert_eq!(da.select(&bv, 2), 5);
        assert_eq!(da.select(&bv, 3), 6);
        let da = DArray::new(&bv, false);
        assert_eq!(da.select(&bv, 0), 1);
        assert_eq!(da.select(&bv, 1), 2);
        assert_eq!(da.select(&bv, 2), 4);
    }

    #[test]
    fn test_random_bits() {
        for seed in 0..100 {
            let bv = BitVector::from_bits(&gen_random_bits(10000, seed));
            let da = DArray::new(&bv, true);
            test_select(&bv, &da);
            let da = DArray::new(&bv, false);
            test_select0(&bv, &da);
        }
    }

    #[test]
    fn test_serialize() {
        let bv = BitVector::from_bits(&gen_random_bits(10000, 42));
        let da = DArray::new(&bv, true);
        let bytes = bincode::serialize(&da).unwrap();
        let other: DArray = bincode::deserialize(&bytes).unwrap();
        assert_eq!(da.len(), other.len());
        test_select(&bv, &other);
    }
}
