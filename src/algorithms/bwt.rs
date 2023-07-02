//!
//!

///
pub fn compute_bwt(text: &[u8], chunk_size: usize) -> Vec<u8> {
    assert_ne!(chunk_size, 0);
    let cuts = CutGenerator::generate(text, chunk_size);
    bwt_from_cuts(text, &cuts)
}

/// # Arguments
///
/// * `text` - The text to be transformed.
/// * `cuts` - Minimal set of prefixes that each prefix starts no more than b suffixes of `text`.
fn bwt_from_cuts(text: &[u8], cuts: &[Vec<u8>]) -> Vec<u8> {
    assert!(cuts[0].is_empty(), "cuts[0] must be empty.");

    let text = text.as_ref();
    let mut bwt = Vec::with_capacity(text.len());
    let mut chunks = vec![];

    for q in 1..=cuts.len() {
        if q < cuts.len() {
            for j in 0..text.len() {
                let cut_p = cuts[q - 1].as_slice();
                let cut_q = cuts[q].as_slice();
                if cut_p < &text[j..] && &text[j..] <= cut_q {
                    chunks.push(j);
                }
            }
        } else {
            for j in 0..text.len() {
                let cut_p = cuts[q - 1].as_slice();
                if cut_p < &text[j..] {
                    chunks.push(j);
                }
            }
        }
        chunks.sort_by(|&a, &b| text[a..].cmp(&text[b..]));
        for &j in &chunks {
            eprintln!("{}:\t{}", j, String::from_utf8_lossy(&text[j..]));
            bwt.push(if j == 0 {
                *text.last().unwrap()
            } else {
                text[j - 1]
            });
        }
        chunks.clear();
    }
    bwt
}

///
struct CutGenerator<'a> {
    text: &'a [u8],
    chunk_size: usize,
    cuts: Vec<Vec<u8>>,
    lens: Vec<usize>,
}

impl<'a> CutGenerator<'a> {
    fn generate(text: &'a [u8], chunk_size: usize) -> Vec<Vec<u8>> {
        let mut builder = Self {
            text,
            chunk_size,
            cuts: vec![vec![]],
            lens: vec![],
        };
        builder.expand(vec![]);
        builder.cuts
    }

    fn expand(&mut self, mut cut: Vec<u8>) {
        let freqs = Self::symbol_freqs(self.text, &cut);
        cut.push(0); // dummy last symbol
        for (symbol, &freq) in freqs.iter().enumerate() {
            if freq == 0 {
                continue;
            }
            *cut.last_mut().unwrap() = symbol as u8;
            if freq <= self.chunk_size {
                if self.lens.is_empty() || *self.lens.last().unwrap() + freq > self.chunk_size {
                    self.cuts.push(vec![]);
                    self.lens.push(0);
                }
                *self.cuts.last_mut().unwrap() = cut.clone();
                *self.lens.last_mut().unwrap() += freq;
            } else {
                self.expand(cut.clone());
            }
        }
    }

    /// Computes the frequencies of symbols following cut in text.
    fn symbol_freqs(text: &[u8], cut: &[u8]) -> Vec<usize> {
        let cut = cut.as_ref();
        let mut freqs = vec![0; 256];
        for j in cut.len()..text.len() {
            let i = j - cut.len();
            if cut == &text[i..j] {
                freqs[text[j] as usize] += 1;
            }
        }
        freqs
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bwt_builder_3() {
        let text = "abracadabra$";
        let bwt = compute_bwt(text.as_bytes(), 3);
        let bwt_str = String::from_utf8_lossy(&bwt);
        assert_eq!(bwt_str, "ard$rcaaaabb");
    }

    #[test]
    fn test_bwt_builder_4() {
        let text = "abracadabra$";
        let bwt = compute_bwt(text.as_bytes(), 4);
        let bwt_str = String::from_utf8_lossy(&bwt);
        assert_eq!(bwt_str, "ard$rcaaaabb");
    }

    #[test]
    fn test_bwt_from_cuts_3() {
        let text = b"abracadabra$";
        let cuts = &[
            b"".to_vec(),
            b"a$".to_vec(),
            b"ac".to_vec(),
            b"b".to_vec(),
            b"d".to_vec(),
            b"r".to_vec(),
        ];
        let bwt = bwt_from_cuts(text, cuts);
        let bwt_str = String::from_utf8_lossy(&bwt);
        assert_eq!(bwt_str, "ard$rcaaaabb");
    }

    #[test]
    fn test_bwt_from_cuts_4() {
        let text = b"abracadabra$";
        let cuts = &[b"".to_vec(), b"ab".to_vec(), b"b".to_vec(), b"r".to_vec()];
        let bwt = bwt_from_cuts(text, cuts);
        let bwt_str = String::from_utf8_lossy(&bwt);
        assert_eq!(bwt_str, "ard$rcaaaabb");
    }

    #[test]
    fn test_symbol_freqs() {
        let text = b"abracadabra$";
        let cut = b"ra";
        let freqs = CutGenerator::symbol_freqs(text, cut);
        let mut expected = vec![0; 256];
        expected[b'$' as usize] = 1;
        expected[b'c' as usize] = 1;
        assert_eq!(freqs, expected);
    }

    #[test]
    fn test_symbol_freqs_empty() {
        let text = b"abracadabra$";
        let cut = b"";
        let freqs = CutGenerator::symbol_freqs(text, cut);
        let mut expected = vec![0; 256];
        expected[b'$' as usize] = 1;
        expected[b'a' as usize] = 5;
        expected[b'b' as usize] = 2;
        expected[b'c' as usize] = 1;
        expected[b'd' as usize] = 1;
        expected[b'r' as usize] = 2;
        assert_eq!(freqs, expected);
    }
}
