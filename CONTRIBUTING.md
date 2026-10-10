# Contributing

Thank you for looking at StateSync-GKR. This is a small research project with
one maintainer, and careful outside review is one of the most valuable things
it can receive.

The contributions that help most right now:

- **Reproduction reports** on hardware or operating systems we have not
  tested. See [REPRODUCING.md](REPRODUCING.md). A FAIL result is as useful as
  a PASS.
- **Defects** in the sparse-Merkle semantics, circuit compilation, or GKR
  verification path, especially with a failing test.
- **Independent review of the claim boundaries.** If
  [FORMAL_VERIFICATION.md](FORMAL_VERIFICATION.md) claims more than the
  theorems actually establish, that is a bug worth reporting.
- **Documentation that was wrong or unclear on first read.** If you had to
  work something out yourself, the docs should have told you.

Because one person reviews everything, please open an issue before starting a
large change so we can agree on the approach before you spend the time. Small
fixes can go straight to a pull request.

## Where to start

Issues are labelled to show what kind of work they need:

- [`good first issue`](https://github.com/Oraclizer/statesync-gkr/labels/good%20first%20issue)
  is scoped, has a clear finish line, and does not require knowing the GKR
  protocol.
- [`help wanted`](https://github.com/Oraclizer/statesync-gkr/labels/help%20wanted)
  is work the maintainer wants but is not currently doing.
- [`reproduction`](https://github.com/Oraclizer/statesync-gkr/labels/reproduction)
  needs someone with hardware or an operating system we have not tested, and
  needs no Rust at all.

If you want to work on something, comment on the issue first so two people do
not build the same thing.

## Before opening a change

- Use a public issue for ordinary bugs, documentation, or design discussion.
- Follow [SECURITY.md](SECURITY.md) for suspected vulnerabilities. Do not open
  a public security issue.
- Open an issue before a large API, proof-system, encoding, dependency, or
  architecture change.
- Do not include private code, credentials, personal data, private repository
  coordinates, generated work attribution, or material you do not have the
  right to submit.

## Development checks

These are exactly what CI runs, in the same order. If all of them pass
locally, the hosted checks should pass too.

```sh
rustup show
cargo fmt --all --check
cargo clippy --workspace --all-targets --locked -- -D warnings
cargo test --workspace --release --locked

# Rust and Python must agree byte-for-byte on the canonical encodings.
cargo run --release --locked -p ssgkr-wrap --example risc0-route-b-manifest-v1 -- \
  tests/vectors/risc0-route-b-manifest-v1.json > /tmp/route-rust.txt
python3 tests/reference/risc0_route_b_manifest_v1.py \
  tests/vectors/risc0-route-b-manifest-v1.json > /tmp/route-python.txt
diff -u tests/vectors/risc0-route-b-manifest-v1.transcript.txt /tmp/route-rust.txt
diff -u tests/vectors/risc0-route-b-manifest-v1.transcript.txt /tmp/route-python.txt

cargo run --release --locked --example receipt_gated_transition_v1 -- \
  tests/vectors/risc0-route-b-volta-2.0.0-runtime-rebind-v1.json \
  tests/vectors/risc0-route-b-destination-policy-v1.json > /tmp/receipt-rust.txt
python3 tests/reference/receipt_gated_local_transition_v1.py \
  tests/vectors/receipt-gated-local-transition-v1.json > /tmp/receipt-python.txt
diff -u /tmp/receipt-rust.txt /tmp/receipt-python.txt

# The proof digest must not depend on CPU features. CI compares a baseline
# x86-64 build against a -Ctarget-cpu=native build of the same binary.
cargo run --release --locked --bin proof_digest

# Policy and public-surface checks.
python3 release/v1.1/verify_dependency_update_policy.py
python3 release/v1.1/test_verify_mode_policy.py
python3 release/v1.1/test_documentation_consistency.py
python3 release/v1.1/verify.py --mode pull-request
python3 spikes/zkvm-wrap/reproducible/risc0-route-b/test_validate_toolchain_payload_packaging.py
```

`verify.py --mode pull-request` is the check CI runs on a pull request: it
validates the frozen protected surface and the sensitive-content rules without
requiring you to regenerate any release manifest. The command after it checks
the controlled-build payload profiles against the identity record of their own
release line. `test_documentation_consistency.py` holds the prose to the files
that decide it, so a count or an asset name that drifts from its authority
fails here rather than in a reader's hands. The full-tree manifests are
maintained on the release line, not by contributors.

If a change affects Isabelle theories or mapped verification claims, build the
registered sessions (see
[FORMAL_VERIFICATION.md](FORMAL_VERIFICATION.md) for the exact command and
prerequisites) and update that document in the same pull request.

### How long this takes

Measured on the maintainer's development machine (16 logical cores, 32 GB
RAM), release mode:

| Command | Wall time | Notes |
|---|---|---|
| `cargo run --release --locked --example state_sync_prove_verify` | about 21 s from a cold clone | Measured on the previous line; see `release/v1.0/RELEASE_NOTES.md` |
| `cargo test --workspace --release --locked` | about 30 s warm, dominated by compilation when cold | A first cold build takes substantially longer |
| Hosted CI, all jobs | about 3 minutes with a warm dependency cache | Fork pull requests start with a cold cache and take longer |
| Isabelle sessions | a long-running job; each session declares a 7200 s timeout | Advanced profile; the hosted Proofs workflow rebuilds all registered sessions on the maintained branch, weekly, and on proof-touching pull requests |

The Proofs lane is a required check, but it does not tax ordinary changes: a
gate job compares your pull request against its base, and the long Isabelle
build runs only when something under `formal/` or the workflow itself
changed. Every other pull request gets a fast positive "no proof input
changed" result in about a minute.

Release mode is not optional. The proving paths are impractically slow under a
debug build, so `--release` is part of every documented command.

## Commit and branch conventions

Write commit subjects in the imperative mood, under 72 characters, in English:

```text
Reject out-of-domain sparse-Merkle operations in the compiler

The compiler accepted an operation code outside the documented domain and
produced a circuit that verified. Add a domain check and a negative test.
```

- English only, including comments and test names.
- One logical change per pull request. Do not mix a fix with unrelated
  formatting.
- Branch names describe the change (`fix/compiler-domain-check`), not the
  tool or person that produced it.
- Do not add trailers or generated-by attribution for authoring tools.
- In tracked files (comments and documents alike), refer to a pull request
  as `pull request 42`, not with the number-sign shorthand. The
  public-surface scanner rejects the shorthand form together with other
  internal-coordinate patterns, and reports the exact file, line, and token
  when something matches. If a legitimate technical term collides with a
  pattern, say so in the pull request so the allowlist can learn it
  explicitly.

## Frozen proof-bound source

The published proof is bound to the 79 paths in
`release/v1.1/PROTECTED_SOURCE_MANIFEST.json`. Do not edit those files,
including comments, package descriptions, diagnostics, field names, key order,
test names, or vectors, as an incidental cleanup.

A protected change is not an ordinary contribution. It requires a new identity
and a separately authorized proof lifecycle. Expected hashes must never be
updated simply to make a changed build pass.

`release/v1.0` holds the frozen record of the previous identity cycle. It is
never regenerated, and the live verifier holds its whole directory to one
recorded digest, so an edit there fails the required check.

Historical labels that remain in protected source are governed only by
[docs/frozen-source-identifiers.md](docs/frozen-source-identifiers.md) and the
exact allowlist. Do not reuse them in new source.

## Dependency updates

The root `Cargo.lock` and the zkVM manifests under `spikes/` are part of the
frozen proof-bound source, so cargo version updates cannot merge during the
current identity cycle. Dependabot's cargo version-update pull requests are
paused until the next identity cycle; security alerts and security updates
stay enabled, and
[release/v1.1/DEPENDENCY_UPDATE_POLICY.json](release/v1.1/DEPENDENCY_UPDATE_POLICY.json)
records the policy.

GitHub Actions dependency updates do merge. Before merging one, run
`python3 release/v1.1/update-release-manifests.py` on the pull-request branch
and commit the refreshed release manifests. Skipping that step makes the
post-merge check on the maintained branch fail with a manifest hash mismatch,
because the release manifests cover every tracked file.

## Pull request requirements

A pull request should:

- explain the problem and user-visible effect;
- identify affected claims, trust boundaries, and compatibility surfaces;
- include positive and negative tests where applicable;
- update public documentation and release evidence when a claim changes;
- preserve deterministic encodings and source-archive behavior;
- contain no unrelated changes; and
- pass the required hosted checks.

Security-sensitive changes may need additional independent review before they
land, which is about risk, not about the quality of the work.

## Contribution license and rights

By submitting a contribution, you represent that you have the right to submit
it and that it does not include third-party confidential or restricted
material.

You license your contribution under the Business Source License 1.1 that
governs this repository. In addition, you grant Oraclizer Labs, Inc. a
perpetual, worldwide, non-exclusive, royalty-free, irrevocable license to
reproduce, modify, distribute and sublicense your contribution under the
Change License named in LICENSE, under commercial license terms offered by
Oraclizer Labs, Inc., and under any later license of this repository. This
grant is what lets each version convert to the Change License on its Change
Date and lets commercial licenses cover the whole repository. If you cannot
make this grant, for example because your employer holds the rights, say so
in the pull request before the change is reviewed.

Contributions accepted before 2026-10-09 were submitted under the former
MIT OR Apache-2.0 terms; see [NOTICE](NOTICE).

Meaningful contributions are credited through Git history, release notes, or
an advisory as appropriate.

## Signed release identity

Signed release tags begin with `v1.1.0`. Earlier commits keep their original
signing status. Maintainer commits made after that release are signed, and
merges preserve their signatures; rebase merging is disabled on the published
repository. The maintainer's SSH signing key is listed on the GitHub account.