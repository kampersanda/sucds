# sucds/bench

## Benchmark for bit vectors

This crate provides benchmarks for bit vectors using random bits
with different scales (n = 1K and 1M)
and different densities (p = 50\%, 10\%, and 1\%).

You can measure time performances with the following commands.

```console
cargo bench timing_bitvec_rank
cargo bench timing_bitvec_select
```

You can also measure memory efficiency with the following command.

```console
cargo run --release --bin mem_bitvec
```

## Benchmark for integer arrays

This crate provides benchmarks for integer arrays
using LCP arrays computed from three texts
in [Pizza&Chili Corpus](http://pizzachili.dcc.uchile.cl/texts.html),
referencing to the experiments
in [DACs' paper](https://www.sciencedirect.com/science/article/abs/pii/S0306457312001094).

We use the head 1 MiB of each text.
The basic statistics of the LCP values are as follows.

| Data     | Number |   Max |    Mean | Meadian |
| -------- | -----: | ----: | ------: | ------: |
| dblp     |  1 MiB |   192 |  36.198 |      23 |
| dna      |  1 MiB |   747 |  10.807 |      10 |
| proteins |  1 MiB | 8,085 | 284.555 |       5 |

You can measure time performances with the following command.

```console
cargo bench timing_intvec_access
```

You can also measure memory efficiency with the following command.

```console
cargo run --release --bin mem_intvec
```

## Native optimizations

We recommend setting the `native` option to maximize the performance of CPU intrinsics.

```console
RUSTFLAGS="-C target-cpu=native" cargo bench
```

## License

The softwere under `data` are generated from [Pizza&Chili Corpus](http://pizzachili.dcc.uchile.cl/texts.html) and follow [LGPL License](https://www.gnu.org/licenses/lgpl-3.0.html).
