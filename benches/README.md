# Development measurements

The measurement harness is [`src/bin/measure.rs`](../src/bin/measure.rs). It
reports single-path latency, component timing, pre-wrap proof size, sparse
oracle memory, and independent-job batch throughput over selected tree depths.

```sh
RUSTFLAGS="-Ctarget-cpu=native" cargo run --release --locked --bin measure
```

Historical development observations are in [`REPORT.md`](REPORT.md).

Serving components for proof services, a reference proof server with four
serving modes and a load frontend are in [`serving/`](serving/README.md). Their
controlled v1.2.0 measurements are reported in
[Serving capacity on one server](../docs/performance.md#serving-capacity-on-one-server).

`REPORT.md` records development observations from one machine. Latency,
capacity, deadline and overload results come from the controlled studies in
[Performance and operating profiles](../docs/performance.md), which state their
hosts, timers and conditions.

The controlled studies in this directory are summarized online in
[Benchmark results](https://oraclizer.io/ss-gkr/docs/benchmarks/results/), with
their controls and timer boundaries in
[Benchmark methodology](https://oraclizer.io/ss-gkr/docs/benchmarks/methodology/).

Reproducing the harness on another machine may be useful for development, but
hardware, firmware, operating system, compiler flags, thread placement,
frequency control, background load, and repetition policy must be fixed before
absolute values can be compared.
