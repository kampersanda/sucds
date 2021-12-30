use sucds::{BitVector, CompactVector};

fn main() {
    let bv = BitVector::from_bits(&[true, false, false, true]);
    println!("{:?}", bv);

    let cv = CompactVector::from_slice(&[5, 256, 0, 10]);
    println!("{:?}", cv);
}
