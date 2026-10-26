# Troubleshooting

The online
[troubleshooting guide](https://oraclizer.io/ss-gkr/docs/guides/troubleshooting/)
covers more symptoms in detail, including preparation and proving errors,
encoding failures and performance problems.

## The pinned Rust toolchain is missing

Run `rustup show`. Rustup should install the exact version from
`rust-toolchain.toml`. If policy prevents installation, record the installed
version and stop rather than silently using an unpinned compiler.

## Cargo reports a lock-file change

Use `--locked`. A requested lock update means the checked-in dependency graph
and the local resolution differ. Do not regenerate `Cargo.lock` as a quick
fix; identify the manifest or toolchain cause first.

## The honest proof is rejected

Confirm that the `SyncRequest`, public inputs, witness, configuration, and
`SyncResult` all come from the same operation and source revision. Reusing a
proof with a changed path, root, asset identifier, or operation must fail.

## A tampered proof is accepted

Stop immediately and open a private security report through
[SECURITY.md](../SECURITY.md). Include the exact revision and minimal local
reproduction, but do not disclose a suspected vulnerability in a public issue.

## The public-surface verifier reports manifest drift

The release manifests bind exact path, mode, size, and SHA-256 tuples. First
decide whether the file is an intended release change. Regenerate the release
manifests only after that decision and rerun the verifier. Never update the
protected-source manifest or frozen allowlist to absorb a protected byte
change.

## The external proof file is missing

Source verification can run without the external proof. A release-asset check
requires the exact `statesync-gkr-v1.2-proof.cbor` attachment. Download it from
the matching immutable GitHub Release and verify its SHA-256 before use.

## The exact identity build cannot be reproduced

The controlled identity recipe requires private, checksum-pinned build
materials that are not needed for ordinary source use. Do not claim exact
identity reproduction from a normal source build. Follow
`spikes/zkvm-wrap/reproducible/risc0-route-b/README.md` and report the observed
artifact hashes as a deviation.

## Proving is slower than the published measurements

Check the build first. The published CPU and serving measurements use
`RUSTFLAGS="-Ctarget-cpu=native"`; in the v1.2.0 one-thread measurements the
default release build took 1.66–1.71 times as long per prepared proof. Build
on the host that runs the prover, or name its CPU with `-Ctarget-cpu`, and
compare the same tree depth, operation mix, worker count and request path.
See [Build for proving speed](usage.md#build-for-proving-speed).

## The reference server rejects requests

A reply with an empty proof and a reason in its `error` field is an explicit
rejection. `server_total_queue_full` means the admission cap (`--max-queue`)
was reached: that many admitted jobs were waiting to start computing. Lower
the offered rate, add servers, or raise the cap only when the extra waiting
work still fits the latency budget and the memory limit.
`server_run_limit_before_compute` means admission closed at `--run-ms` or the
stop file before the job started. The
[serving guide](../benches/serving/README.md) lists every reason.

## One connection stops near 3,300 requests per second

Each reply carries a complete encoded proof, about 182.6 kB on average for the
balanced depth-24 mix. In the controlled 192-core runs one connection carried
at most about 4.96 Gbit/s of replies, and every request met one second up to
3,300 requests/s in three 60-second runs; in 15-second screens, two
connections to the same server met it up to 5,000 requests/s, where the
frontend became the limit. When the server's CPU has headroom while its return budget
stays full, spread the load over more connections, for example by naming the
server more than once in the frontend's `--targets`.
