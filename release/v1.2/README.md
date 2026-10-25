# StateSync-GKR v1.2 release evidence

This index connects the v1.2 release line to its verification material. The
v1.2 source has its own program identity: two controlled clean builds of the
identity source selection produced the same eight identity outputs, recorded
in [the expected identity record](../../spikes/zkvm-wrap/identity/risc0-route-b-guest-expected-v1.2.json)
and summarized in [IDENTITY_DISTRIBUTION.json](IDENTITY_DISTRIBUTION.json).
The newest external proof belongs to the historical v1.1 program and is not a
proof of the v1.2 program identity.

- [Release verifier](verify.py)
- [Identity and distribution record](IDENTITY_DISTRIBUTION.json)
- [Attachment inventory](ATTACHMENTS.json)
- [Checksums](SHA256SUMS)
- [Software bill of materials](SBOM.spdx.json)
- [Local provenance statement](PROVENANCE.intoto.jsonl)
- [Protected-source manifest](PROTECTED_SOURCE_MANIFEST.json)
- [Frozen-source allowlist](FROZEN_SOURCE_ALLOWLIST.json)
- [Dependency update policy](DEPENDENCY_UPDATE_POLICY.json)
- [Reproduction report template](REPRODUCTION_REPORT_TEMPLATE.json)
- [Source reproduction recipe](SOURCE_RECIPE.md)
- [Reproduce the release](../../REPRODUCING.md)

The line is prepared on the main branch and has not been published as a
release. Until it is, the citation metadata names the latest published
release, v1.1.1, archived at
[DOI 10.5281/zenodo.23280552](https://doi.org/10.5281/zenodo.23280552).
Manifests on the main branch describe the current branch source tree.

## What changed in the protected source

The protected path set is the same 79 paths as the previous line; five of
them changed:

- the sparse layer prover computes the same proof with less arithmetic
  (`crates/protocol/src/reduce.rs`); the reference vectors, the dense test
  oracle and the proof digest across CPU backends match the previous prover
  byte for byte;
- the prepared prover entry points refuse a request of another operation kind
  with `SyncError::KindMismatch`, and the leaf hash refuses a pre-image of the
  wrong width, in every build profile (`src/lib.rs`,
  `crates/verification/src/lib.rs`, `crates/primitives/src/hash.rs`); and
- one encoding note now states the statement section's real size
  (`crates/wrap/src/encoding.rs`).

The verifier-side functions are unchanged. Because the compiled guest
includes the changed source, the program identity changed, and this line
records it.

The allowlist also enrolls two annotation forms that the previous allowlist's
scan patterns did not cover, as the frozen-source glossary announced: the
model-boundary note and the review wording. With the forms the previous line
already classified, the allowlist classifies 131 occurrences.

## Relation to the previous baselines

`release/v1.1` and `release/v1.0` are the baselines of the previous identity
cycles. They are kept byte frozen and are not regenerated: each records what
its release claimed. The live gate is this directory. The verifier here
compares each superseded directory against one recorded digest, so an earlier
record cannot be edited without failing a check.

When a later identity line opens, its own directory under `release/` becomes
the live gate and this directory becomes a frozen baseline in turn. The pull
request that opens the line is judged by the new line's verifier only if it
leaves every existing release directory byte-identical to its base, and a
direct call of this verifier hands its arguments to the newest line's
verifier.

Point-in-time receipts of the v1.0 cycle, such as the dependency and advisory
scans, belong to that cycle and are published with it in `release/v1.0`. The
dependency lock files are unchanged since then, but those scans are not
reissued for this line and this line makes no claim from them.
