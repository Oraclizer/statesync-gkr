# Troubleshooting

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
requires the exact `statesync-gkr-v1.1-proof.cbor` attachment. Download it from
the matching immutable GitHub Release and verify its SHA-256 before use.

## The exact identity build cannot be reproduced

The controlled identity recipe requires private, checksum-pinned build
materials that are not needed for ordinary source use. Do not claim exact
identity reproduction from a normal source build. Follow
`spikes/zkvm-wrap/reproducible/risc0-route-b/README.md` and report the observed
artifact hashes as a deviation.
