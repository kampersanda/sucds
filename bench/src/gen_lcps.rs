use std::error::Error;
use std::fs::File;
use std::io::{BufReader, BufWriter, Read};
use std::path::PathBuf;

use clap::Parser;
use suffix::SuffixTable;

use sucds::{PrefixSummedEliasFano, Serializable};

#[derive(Parser, Debug)]
#[clap(name = "gen_lcps", about = "Generate LCP lens.")]
struct Args {
    #[clap(short = 'i', long)]
    text_path: PathBuf,

    #[clap(short = 'o', long)]
    lcp_path: PathBuf,
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();

    let text = {
        let mut text = String::new();
        let mut reader = BufReader::new(File::open(args.text_path)?);
        reader.read_to_string(&mut text)?;
        text
    };

    let lcp_lens = SuffixTable::new(&text).lcp_lens();
    let psef = PrefixSummedEliasFano::from_slice(&lcp_lens)?;
    {
        let mut writer = BufWriter::new(File::create(args.lcp_path)?);
        psef.serialize_into(&mut writer)?;
    }
    Ok(())
}
