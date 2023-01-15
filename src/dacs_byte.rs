//! Bytewise Dacs
#![cfg(target_pointer_width = "64")]

use std::convert::TryInto;

use anyhow::Result;

use crate::util;
use crate::{BitVector, RsBitVector};

const LEVEL_WIDTH: usize = 8;
const LEVEL_MASK: usize = (1 << LEVEL_WIDTH) - 1;

///
pub struct DacsByte {
    bytes: Vec<Vec<u8>>,
    flags: Vec<RsBitVector>,
}

impl DacsByte {
    ///
    pub fn from_slice(ints: &[usize]) -> Result<Self> {
        let maxv = ints.iter().cloned().max().unwrap();
        let bits = util::needed_bits(maxv);

        // .max(1) is required for the case of all zeros.
        let num_levels = util::ceiled_divide(bits, LEVEL_WIDTH).max(1);

        if num_levels == 1 {
            let bytes: Vec<_> = ints.iter().map(|&x| x.try_into().unwrap()).collect();
            return Ok(Self {
                bytes: vec![bytes],
                flags: vec![],
            });
        }

        let mut bytes = vec![];
        let mut flags = vec![];
        bytes.resize(num_levels, vec![]);
        flags.resize(num_levels - 1, BitVector::default());

        for mut x in ints.iter().cloned() {
            for j in 0..num_levels {
                bytes[j].push((x & LEVEL_MASK) as u8);
                x >>= LEVEL_WIDTH;
                if j == num_levels - 1 {
                    assert_eq!(x, 0);
                    break;
                } else if x == 0 {
                    flags[j].push_bit(false);
                    break;
                }
                flags[j].push_bit(true);
            }
        }

        let flags = flags.into_iter().map(|f| RsBitVector::new(f)).collect();
        Ok(Self { bytes, flags })
    }

    ///
    pub fn get(&self, mut pos: usize) -> usize {
        let mut x = 0;
        for j in 0..self.num_levels() {
            x |= usize::from(self.bytes[j][pos]) << (j * LEVEL_WIDTH);
            if j == self.num_levels() - 1 || !self.flags[j].get_bit(pos) {
                break;
            }
            pos = self.flags[j].rank1(pos);
        }
        x
    }

    /// Gets the number of bits.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.bytes[0].len()
    }

    /// Checks if the vector is empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets the number of levels.
    #[inline(always)]
    pub fn num_levels(&self) -> usize {
        self.bytes.len()
    }
}
