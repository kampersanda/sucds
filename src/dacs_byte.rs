//! Bytewise Dacs
#![cfg(target_pointer_width = "64")]

use anyhow::Result;

use crate::util;
use crate::RsBitVector;

///
pub struct DacsByte {
    bytes: Vec<Vec<u8>>,
    flags: Vec<RsBitVector>,
}

impl DacsByte {
    ///
    pub fn from_slice(ints: &[usize]) -> Result<Self> {
        let mut bytes = vec![];
        let mut flags = vec![];

        let maxv = ints.iter().cloned().max().unwrap();
        let bits = util::needed_bits(maxv);

        Ok(Self { bytes, flags })
    }
}
