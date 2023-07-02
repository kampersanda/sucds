//!
//!

struct CutGenerator<'a> {
    text: &'a [u8],
    chunk_size: usize,
    cuts: Vec<Vec<u8>>,
    lens: Vec<usize>,
}

impl<'a> CutGenerator<'a> {
    fn generate(text: &'a [u8], chunk_size: usize) -> Vec<Vec<u8>> {
        let mut gen = Self {
            text: text.as_ref(),
            chunk_size,
            cuts: vec![vec![]],
            lens: vec![],
        };
        gen.expand(vec![]);
        gen.cuts
    }

    fn expand(&mut self, mut cut: Vec<u8>) {
        let freqs = self.symbol_freqs(&cut);
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
    fn symbol_freqs(&self, cut: &[u8]) -> Vec<usize> {
        let cut = cut.as_ref();
        let mut freqs = vec![0; 256];
        for j in cut.len()..self.text.len() {
            let i = j - cut.len();
            if cut == &self.text[i..j] {
                freqs[self.text[j] as usize] += 1;
            }
        }
        freqs
    }
}

/// # Arguments
///
/// * `text` - The text to be transformed.
/// * `cuts` - Minimal set of prefixes that each prefix starts no more than b suffixes of `text`.
fn bwt_from_cuts<S: AsRef<[u8]>>(text: S, cuts: &[S]) -> Vec<u8> {
    assert!(cuts[0].as_ref().is_empty(), "cuts[0] must be empty.");

    let text = text.as_ref();
    let mut bwt = Vec::with_capacity(text.len());
    let mut chunks = vec![];

    for q in 1..=cuts.len() {
        if q < cuts.len() {
            for j in 0..text.len() {
                let cut_p = cuts[q - 1].as_ref();
                let cut_q = cuts[q].as_ref();
                if cut_p < &text[j..] && &text[j..] <= cut_q {
                    chunks.push(j);
                }
            }
        } else {
            for j in 0..text.len() {
                let cut_p = cuts[q - 1].as_ref();
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_cuts() {
        let text = "abracadabra$";
        let cuts = CutGenerator::generate(text.as_bytes(), 3);
        println!("{:?}", cuts);
    }

    // #[test]
    // fn test_symbol_freqs() {
    //     let text = "abracadabra$";
    //     let cut = "ra";
    //     let freqs = symbol_freqs(text, cut);
    //     let mut expected = vec![0; 256];
    //     expected[b'$' as usize] = 1;
    //     expected[b'c' as usize] = 1;
    //     assert_eq!(freqs, expected);
    // }

    // #[test]
    // fn test_symbol_freqs_2() {
    //     let text = "abracadabra$";
    //     let cut = "";
    //     let freqs = symbol_freqs(text, cut);
    //     let mut expected = vec![0; 256];
    //     expected[b'$' as usize] = 1;
    //     expected[b'a' as usize] = 5;
    //     expected[b'b' as usize] = 2;
    //     expected[b'c' as usize] = 1;
    //     expected[b'd' as usize] = 1;
    //     expected[b'r' as usize] = 2;
    //     assert_eq!(freqs, expected);
    // }

    #[test]
    fn test_bwt_from_cuts() {
        let text = "abracadabra$";
        let cuts = vec!["", "ab", "b", "r"];
        let bwt = bwt_from_cuts(text, &cuts);
        let bwt_str = String::from_utf8_lossy(&bwt);
        assert_eq!(bwt_str, "ard$rcaaaabb");
    }

    #[test]
    fn test_bwt_from_cuts_2() {
        let text = "abracadabra$";
        let cuts = vec!["", "a$", "ac", "b", "d", "r"];
        let bwt = bwt_from_cuts(text, &cuts);
        let bwt_str = String::from_utf8_lossy(&bwt);
        assert_eq!(bwt_str, "ard$rcaaaabb");
    }
}
