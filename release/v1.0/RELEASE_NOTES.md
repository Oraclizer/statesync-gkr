# StateSync-GKR v1.0 component release notes

## Status

This package describes an unaudited research component. It is not production
software, does not authorize deployment, and does not claim secondary
finality. The repository is dual-licensed under Apache-2.0 or MIT.

Release artifacts were uploaded to AWS durable object storage with a
version-bound retention lock and restored bit-for-bit in a separate
project-operated check. The redacted public receipt of that custody check is
`AWS_CUSTODY_RECEIPT.json` in this directory; raw operational logs are
retained privately. AWS did not audit, certify, or endorse this project.

Two further point-in-time receipts ship in this directory and are bound to
the identifiers recorded inside them: `DEPENDENCY_RECEIPT.json` fixes the
exact locked dependency inventory and resolved metadata graph for the
release lockfile, and `ADVISORY_RECEIPT.json` records the advisory scan
against the vulnerability-database commit named in the receipt, including
the reviewed disposition of each finding. Later database states are tracked
by the repository's live dependency alerts, not by these receipts. Publication remains
conditional on the final clean-history audit, exact release attachments,
required checks, and an explicit publication decision. This file is not a tag
or release.

## Included component

- sparse-Merkle semantics and circuit compilation;
- sumcheck and layered GKR proving and verification;
- deterministic transcript and proof-digest checks;
- registered Isabelle sessions for GKR assembly and compiler correctness;
- bounded Rust-to-model refinement evidence with documented trusted seams;
- an exact RISC Zero program identity and public-verifiable proof profile;
- receipt, route, destination-policy, and local candidate-transition codecs;
- an EVM-compatible reference seam tested on a stock compatible execution
  environment.

## Exact proof identity

| Layer | SHA-256 or identifier |
|---|---|
| Program binary | `7dcb6d1ddd47618f65a250361a4b9e3fdb77be1104f51c66225b78e114c7a9ba` |
| Image ID | `dd947fec1fe270c41bc0457912e1e77427c16797ac47dc6a1c825a9323648643` |
| Raw guest ELF | `ab6fcf8796d12bddec6eb3fb3a6115272eaada997a40014e3a984384b1897f81` |
| Generated methods source | `a749506bb1c68a13b718f4678af3884fc43cc1fb7e2fa16cae177a191186b5db` |
| Host binary | `5e6e8969b3dc12a49972ef79f577af10fa642e2b0e394e802174abfaa415fdf8` |
| Diagnostic program binary | `99bc2a68e6ca656cbd69e949c1489ff4b6b8f227c6fdc37d0dc18c211d18a7cf` |
| Diagnostic raw guest ELF | `cadb6596855987ef6a7a2b19ab7c5e7f2330cc841ffe4da9c9cccb23ce99ca8b` |
| External proof CBOR | `2ed107368d0e3cc2f23b4c8366ac7f5992115fa37a2abbd33953fbb78330582a` (279,130 bytes) |

Expected values are immutable comparison targets. A mismatch is a failure;
the release process never updates them to fit a new build.

## Scan results at packaging time

At packaging time the dependency tree carried no unresolved security
advisory, the license inventory contained only the declared permissive
licenses, and the shortest quick start completed from a cold single-branch
shallow clone in 21.157 seconds on Windows 11 x86-64 with the pinned Rust
toolchain (16 logical cores, 32 GB class memory; the build target added about
177 MB and the sampled peak working set of the cargo process tree was about
1.2 GB). The output reported an honest-proof pass, tamper rejection, and
`secondary-finalized=false`. These were project-operated measurements, not an
independent reproduction, audit, or endorsement; the underlying process
records are retained privately.

## Verification boundary

The protected source and its historical annotations are documented in
[`docs/frozen-source-identifiers.md`](../../docs/frozen-source-identifiers.md).
The exact source manifest and occurrence allowlist live next to this file.

The final surface verifier checks bytes and release hygiene. It does not by
itself rerun the Rust tests, Isabelle sessions, zkVM proof, external receipt,
artifact-restore check, or destination integration.

The public workflow never rebuilds or changes the zkVM identity. A pull
request verifies the exact frozen source, the sensitive-content rules, and
the path-membership diff; a push to `main` additionally verifies the
full-tree content manifests. A published release additionally downloads the
named proof attachment and requires its 279,130-byte size and SHA-256 to
match the protected manifest.

The verifier source necessarily contains the private-coordinate signatures it
rejects. Its exact path, `release/v1.0/verify.py`, is excluded only from that
single signature check. Credential, private-path, AI-attribution, email,
protected-byte, and all other checks still apply to the verifier itself.

## Non-claims

This release does not claim a security audit, absence of vulnerabilities,
production fitness, zero knowledge beyond the documented proof profile,
aggregate-proof batching, controlled-hardware performance, deployed contracts,
native rollup proving, parent-chain confirmation, legal compliance, or
operational support commitments.
