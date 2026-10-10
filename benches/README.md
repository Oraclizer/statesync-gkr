# Development measurements

The measurement harness is [`src/bin/measure.rs`](../src/bin/measure.rs). It
reports single-path latency, component timing, pre-wrap proof size, sparse
oracle memory, and independent-job batch throughput over selected tree depths.

```sh
RUSTFLAGS="-Ctarget-cpu=native" cargo run --release --locked --bin measure
```

Historical development observations are in [`REPORT.md`](REPORT.md).

These results are not a controlled-hardware release benchmark. They were not
produced for comparative leadership claims and do not establish production
latency, capacity, resource ceilings, deadline compliance, or behavior under
network, queue, lock, retry, and overload conditions.

Reproducing the harness on another machine may be useful for development, but
hardware, firmware, operating system, compiler flags, thread placement,
frequency control, background load, and repetition policy must be fixed before
absolute values can be compared.
