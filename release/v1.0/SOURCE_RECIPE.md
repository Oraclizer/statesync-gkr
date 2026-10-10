# Source and identity reproduction

## Two distinct claims

StateSync-GKR separates anonymous source reproduction from the recorded exact
identity build.

**Anonymous source reproduction** uses the public source, pinned Rust
toolchain, lock file, and public dependencies to build and test the workspace.
It is expected to reproduce behavior and the documented deterministic proof
digest.

**Recorded exact identity reproduction** compares a locked, offline,
network-disabled build against the published program binary, image ID, guest
ELF, generated methods source, host binary, and diagnostic hashes. The original
build used a content-addressed dependency cache and OCI payload held in private
durable custody. A user who does not possess those exact materials must not
interpret an ordinary networked build as the recorded identity build.

## Public source checks

```sh
rustup show
cargo fmt --all --check
cargo clippy --workspace --all-targets --locked -- -D warnings
cargo test --workspace --release --locked
cargo run --release --locked --bin proof_digest
python3 release/v1.0/verify.py --mode clean-history --require-proof \
  --proof /path/to/statesync-gkr-v1.0-proof.cbor
```

The receipt-gated example is local and host-only:

```sh
cargo run --release --locked --example receipt_gated_transition_v1 -- \
  tests/vectors/risc0-route-b-volta-2.0.0-runtime-rebind-v1.json \
  tests/vectors/risc0-route-b-destination-policy-v1.json
```

It creates a local candidate, submits no transaction, and leaves
`secondary_finalized` false.

The proof file is a release attachment, not a source-tree member. The published
release workflow downloads the exact named attachment and runs the same
required-proof command. Pull-request checks validate the frozen protected
source, the sensitive-content rules, and the path-membership diff without
generating or replacing a proof; the full-tree content manifests are enforced
when a change lands on the release line.

## Deterministic source archive

The release-owned archive uses `SOURCE_MANIFEST.json` as its member authority.
After that final manifest exists, run:

```sh
python3 release/v1.0/build-source-archive.py \
  --root . \
  --manifest release/v1.0/SOURCE_MANIFEST.json \
  --output statesync-gkr-v1.0-source.tar.gz
```

Generate it independently twice and require identical size and SHA-256. The
archive builder sorts paths, fixes timestamps, normalizes ownership and modes,
and rejects symlinks, devices, missing files, extra manifest members, and hash
mismatches. GitHub-generated archives are not the immutable source artifact.

## Failure interpretation

- A protected source, key-order, annotation, or proof hash mismatch is a hard
  failure. Do not update expected values.
- A normal networked build that differs from the recorded identity is not a
  replacement identity and does not authorize proof regeneration.
- Missing private custody material means the exact recorded build was not
  attempted.
- Passing the local example does not establish a chain transition or
  deployment.
