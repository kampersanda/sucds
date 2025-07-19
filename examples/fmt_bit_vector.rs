//! Example to demonstrate the usage of `fmt::Debug` for `BitVector`.

use sucds::bit_vectors::BitVector;

fn main() {
    let bv = BitVector::from_bits([
        false, true, false, false, true, false, true, false, false, true, // 10
        true, false, true, false, false, true, false, true, false, true, // 20
        false, true, false, true, false, false, true, true, false, true, // 30
        true, false, true, false, false, true, false, true, false, false, // 40
    ]);

    // Print the BitVector using the default debug format.
    // The output will be "BitVector { bits: [... 40 items ...], len: 40 }".
    println!("{:?}", bv);

    // For a more detailed view, use the debug format.
    // The output will be:
    //
    // BitVector {
    //     bits: [
    //         0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
    //         0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0,
    //         1, 0, 0, 1, 0, 1, 0, 0,
    //     ],
    //     len: 40,
    // }
    println!("{:#?}", bv);
}
