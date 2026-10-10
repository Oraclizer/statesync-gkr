# Controlled capacity and arrival benchmarks

The caller in `Load` reproduces prepared independent proof jobs, local batching, actual TCP transport, and final encoded-proof acceptance against the original request. It uses the production implementation and the same deterministic corpus constructor as the measured driver. The portable caller uses a repository-relative dependency path and the current BUSL-1.1 license. Its Cargo declaration and bundled LICENSE agree with the repository root. `PORTABLE_SOURCE.json` distinguishes the historical driver identity from the portable file hashes. A new binary records its own source/binary/environment identity.

The separate dataset holds the exact condition/process tables, full memory curves, actual arrival envelopes and raw observations described by `DATASET_LOCATOR.json`. This repository distributes the replay code and methodological guide. The controlled memory comparison uses production Sparse and a test-only Dense reference in one driver; requested allocation, Vec capacity and whole-process RSS remain separate. Counter/stage overhead stays in both memory timers, and CPU0 single-job measurements do not measure 48-core throughput. The companion package and engineering manuscript are prepared for review; no new dataset DOI, public download URL or engineering-paper arXiv identifier is asserted. Data and figure publication rights await the final review described in `DATA_RIGHTS.md`.

The existing 243-process and 175-process studies remain at `../controlled-cpu-2026-10-06` and `../controlled-cpu-2026-10-06-supplement`. The new memory study contains 264 independent processes; the additional limit/load studies contain 17 + 38 + 12 + 57 + 47 executions. These denominators are different experimental units and are not added into one throughput sample population.

Run a small caller check from the repository root on Linux using Rust 1.96.1:

```sh
cargo build --release --locked --manifest-path benches/controlled-capacity-2026-10-07/Load/Cargo.toml
python3 benches/controlled-capacity-2026-10-07/smoke.py --binary benches/controlled-capacity-2026-10-07/Load/target/release/ssgkr-load-driver --out /tmp/ssgkr-caller-small-check
```

This runs only six small control proofs (three operation kinds, two fixtures each), checks sequential/parallel equality, honest encoded acceptance, mutated typed proof/root/value digest rejection and trailing-byte rejection. A new empty output directory is required. It does not rerun the archived campaigns. `smoke.py` records the actual built binary hash and source commit. Linux `/proc` telemetry is part of the full load profile; unsupported telemetry stays unavailable.

Once the dataset attachments are available, obtain the exact contract hash from its publication metadata and verify the extracted payload:

```sh
python3 benches/controlled-capacity-2026-10-07/verify-dataset.py --contract PACKAGE_CONTRACT.json --contract-sha256 THE_PUBLISHED_CONTRACT_SHA256 --manifest PUBLIC_MANIFEST.json --public Public
```

The verifier rejects empty/subset manifests, null or incorrect types, duplicate/unsafe members, schema mismatch, missing files, wrong rows, changed bytes/hashes and unmanifested files. Its result is file-contract verification; it does not assign licensing, reproduce a benchmark result or approve publication.

`DATASET_LOCATOR.json` records that the package is prepared for review and
publication is pending. Its dataset DOI, archive digest and public download URL
remain null. Data/figure licensing is a separate
rights-holder decision. The current caller and package metadata use the root
[LICENSE](../../LICENSE). Historical source hashes in the portable manifest
preserve the measured driver identity and do not change that current grant.
As recorded in [NOTICE](../../NOTICE), non-production use is free under BSL 1.1,
production verification-only use is granted, and other production use needs a
commercial license. Versions through v1.1.0 retain their original terms.

Cite the existing [v1.1.0 software record](https://doi.org/10.5281/zenodo.23136385)
for that software identity. [arXiv:2610.05335](https://arxiv.org/abs/2610.05335)
is the formal study. Neither is a new dataset or engineering-paper record.

For a complete small Linux check including a build, CLI rejection, nine localhost requests and the smallest mixed Memory cells, use Python 3.12+ and a clean checkout of the current BSL distribution:

```sh
python3 benches/controlled-capacity-2026-10-07/linux-small-smoke.py --out /tmp/ssgkr-public-small-smoke
```

This builds the separate caller with its supplied lock, runs six encoded control fixtures, rejects unknown/duplicate flags, then checks six timed plus three warmup requests over loopback with exact original-input/proof hash and length binding and cryptographic acceptance. It first checks the clean current BSL source against the strict distribution policy. Its Memory branch extracts that current commit into the fresh temporary output, appends the cfg(test) observer and dev dependencies there, installs the captured observer lock, runs the four tiny normal/tamper families plus allocator control, then checks Dense/Sparse mixed width4/depth2 with one timed sample each. It preserves each raw/log/receipt in the temporary output. The checkout's production files, root Cargo/lock and formal sources are not edited. This is a functional smoke, with no archived-performance rerun or performance claim. The Memory canonical proof JSON identity is distinct from the caller's official encoded codec bytes.

`Results` CSV and `Figures` PNG rights are pending the final dataset/figure rights-holder decision. Neither the historical software notices nor the maintained-source BSL terms assign a publication license to those data/figure files. See `DATA_RIGHTS.md`.
