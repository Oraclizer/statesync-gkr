# Source and identity reproduction

## Two distinct claims

StateSync-GKR separates anonymous source reproduction from the recorded exact
identity build.

**Anonymous source reproduction** uses the public source, pinned Rust
toolchain, lock file, and public dependencies to build and test the workspace.
It is expected to reproduce behavior and the documented deterministic proof
digest.

**Historical exact identity reproduction** compares a locked, offline,
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
python3 release/v1.1/verify.py --mode clean-history --require-proof \
  --proof /path/to/statesync-gkr-v1.1-proof.cbor
```

The receipt-gated example is local and host-only:

```sh
cargo run --release --locked --example receipt_gated_transition_v1 -- \
  tests/vectors/risc0-route-b-volta-2.0.0-runtime-rebind-v1.json \
  tests/vectors/risc0-route-b-destination-policy-v1.json
```

It creates a local candidate, submits no transaction, and leaves
`secondary_finalized` false. Its vectors record the earlier submission and are
kept exactly as that submission happened; they are history, not a claim about
the current identity.

The proof file is a release attachment, not a source-tree member. The published
release workflow downloads the exact named attachment and runs the same
required-proof command for the historical program. Pull-request checks validate
78 unchanged protected files and the exact root Cargo license-field delta,
the sensitive-content rules, and the path-membership diff without
generating or replacing a proof; the full-tree content manifests are enforced
when a change lands on the release line.

## The superseded baseline

`release/v1.0` is the baseline of the previous identity cycle. It stays byte
frozen and is never regenerated. `release/v1.1/verify.py` compares every file
under it against one recorded digest, so an edit or a removal fails the live
gate instead of silently rewriting what the earlier release claimed. To check
the earlier claim on its own terms requires the original historical copy and the commit named in
[RELEASE_NOTES.md](RELEASE_NOTES.md); that commit is not part of this current
public repository. Existing recipients retain their original rights.

## Identity source selection

The current BSL distribution changes the root Cargo license field. Its exact
source digest differs from the historical identity selection. The frozen
expected record is preserved, and the current licensing metadata has not
completed an exact compiled identity reproduction. The source-policy checker
must report this distinction; it must not rename a historical proof as a new
current-source proof. See [LICENSING_DISTRIBUTION.json](LICENSING_DISTRIBUTION.json).

The historical accepted program identity depends on an exact subset of the tree, not on
the whole repository. That subset is `Cargo.toml`, `Cargo.lock`,
`rust-toolchain.toml`, `src`, `crates`, `spikes/zkvm-wrap/common`,
`spikes/zkvm-wrap/risc0-host`, `spikes/zkvm-wrap/risc0-methods` and
`tests/vectors/inner-proof-v1/membership-d24.bin`. Its digest is recorded as
`identity_source_manifest_sha256` in
[PROTECTED_SOURCE_MANIFEST.json](PROTECTED_SOURCE_MANIFEST.json) and is
recomputed by
`spikes/zkvm-wrap/reproducible/risc0-route-b/test_validate_toolchain_payload_packaging.py`,
which runs in the ordinary test lane. The test independently checks the raw
current digest and the historical digest after reversing only the approved
Cargo license field in memory. Other changes fail; neither check assigns a
compiled program identity to the current source.

## Historical controlled identity build

The following recipe documents the historical source selection. Running it
against changed current package metadata fails its exact source guard. It is
not a command that converts a current BSL copy to the historical license.

```sh
spikes/zkvm-wrap/reproducible/risc0-route-b/verify-two-clean-builds.sh \
  --source-repo /absolute/path/to/clone \
  --expected-source-commit <40-hex> \
  --cargo-cache-archive /absolute/path/to/cache.tar \
  --cargo-cache-manifest /absolute/path/to/cache.sha256 \
  --evidence-root /absolute/empty/evidence/dir \
  --identity-guard /absolute/path/to/clone/spikes/zkvm-wrap/identity/risc0-route-b-guest-expected-v1.1.json
```

The packaging identifier of the intermediate build image is builder metadata,
not part of the program identity. Two clean builds of the same commit produce
different packaging identifiers and the same eight identity outputs. Compare
the outputs, never the packaging identifier.

## Deterministic source archive

The release-owned archive uses `SOURCE_MANIFEST.json` as its member authority.
After that final manifest exists, run:

```sh
python3 release/v1.1/build-source-archive.py \
  --root . \
  --manifest release/v1.1/SOURCE_MANIFEST.json \
  --output release/v1.1/artifacts/statesync-gkr-v1.1-source.tar.gz
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
