use std::error::Error;
use std::io::Read;

use suffix::SuffixTable;

fn main() -> Result<(), Box<dyn Error>> {
    let mut text = String::new();
    std::io::stdin().read_to_string(&mut text)?;
    for l in SuffixTable::new(&text).lcp_lens() {
        println!("{l}");
    }
    Ok(())
}
