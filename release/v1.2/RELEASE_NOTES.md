# StateSync-GKR v1.2 release notes

## Status

StateSync-GKR v1.1.1 and later versions are distributed under BUSL-1.1;
production proving requires a commercial license (see the root LICENSE).

Version 1.2.0 computes the same proofs with less prover arithmetic, adds
reusable serving components, and refuses two misuses in every build profile.
For every input it produces the same proof bytes as v1.1: the reference
vectors, the dense test oracle and the proof digest across CPU backends match.
The verifier, the proof format, the transcript order and the formal sources
are unchanged. Because the compiled guest includes the changed source, the
program identity is new, and this release records it.

## What changed

### Prover arithmetic

The sparse layer prover builds each scaled output-line weight table in one
pass, evaluates the round nodes of both sumcheck phases from a single table
read with fewer field multiplications, and interpolates every round from a
fixed inverse Vandermonde matrix instead of a per-round Lagrange step. The
Creusot replay records of the changed functions and of the four new helpers
are regenerated; no existing contract regressed.

### Serving components

`benches/serving` is a separate crate of reusable serving parts: bounded
admission with explicit rejection reasons, request and frame size limits, a
bounded return queue with job and byte budgets and deadline writes, parallel
witness and output helpers, and per-job stage timing. A reference proof
server composes them in four scheduling modes, one of which reproduces the
loop used for the earlier capacity measurements, and the crate ships a load
frontend and real-TCP checks. See [the serving guide](../../benches/serving/README.md).

### Misuse checks

`prove_sync_op_prepared` and `make_job_prepared` return
`SyncError::KindMismatch` when a request's operation kind differs from the
prepared circuit, and `hash_leaf_pre` panics on a pre-image of the wrong
width. Both checks previously held only in debug builds.

### Release baseline

`release/v1.2` is the live gate: a protected-source manifest over the same 79
paths as before, an allowlist of 131 occurrences that also enrolls the
model-boundary and review annotation forms the frozen-source glossary
announced, the [identity and distribution record](IDENTITY_DISTRIBUTION.json),
and the verifier, helper and wrapper set. The verifier scans every UTF-8 file
of the protected surface for legacy and stable identifier occurrences, and it
holds `release/v1.1` and `release/v1.0` byte frozen.

## Program identity

| Layer | SHA-256 or identifier |
|---|---|
| Program binary | `e552917c28f7030a46171d33fb90661edb0d1be149efabb1b70bde5b63cc4a28` (699,944 bytes) |
| Image ID | `1a8b55f4e1a5f703386dcfc07e5e8b2e42b5adade6be3d0057f2d565f75eb131` |
| Raw guest ELF | `d8dbb98fcde9cd56089db24af8a7f9a7a28220c526a1a3405b60ec6d751995ee` |
| Generated methods source | `04c2d2af369acc302e22252fe6a2018a73343276a97ae48b844169ebd5620edb` |
| Host binary | `3344d9335fcdddfdd4b491ae9d8a8f5139191a136dec57a3d9a154c0288ff90d` |
| Diagnostic program binary | `b5d431e56d338140869e4de717c834cc599d4770de5d8f28ac2a2fdee0f502cb` |
| Diagnostic raw guest ELF | `de2b3a3bd6fb38c00ad2f58f40b32925b454461359a6f0504a0afdcc744bf420` |

Two clean, locked, offline, network-disabled builds of the recorded source
selection agreed on all eight outputs. The expected record is
[`risc0-route-b-guest-expected-v1.2.json`](../../spikes/zkvm-wrap/identity/risc0-route-b-guest-expected-v1.2.json).
Expected values are immutable comparison targets; the release process never
updates them to fit a new build.

## Proof scope

The attached external proof, `statesync-gkr-v1.1-proof.cbor`, was produced for
the historical v1.1 program (image ID
`dc9a5f0da608178bbe56e98604cb895060c555c18329846b453f71d562d16530`) and is
distributed as evidence for that program. It is not a proof of the v1.2.0
program identity. Its public-verifier observation is recorded in
[`release/v1.1/PROOF_MANIFEST.json`](../v1.1/PROOF_MANIFEST.json).

## Verification boundary

The final surface verifier checks bytes and release hygiene. It does not by
itself rerun the Rust tests, Isabelle sessions, zkVM proof, external receipt,
or destination integration.

A pull request verifies the 79 protected files byte for byte, the
sensitive-content rules, and the path-membership diff. A push to `main`
additionally verifies the full-tree content manifests and the superseded
baseline digests. A published release additionally downloads the named proof
attachment and requires its exact size and SHA-256 to match the identity and
distribution record.

`release/v1.1` last held as the live gate at commit
`1b47601e34b2bfc0d4566973a0f3d00f8be7f861`, and `release/v1.0` at commit
`a456846f98df6e0b60c9e6d33d67592a82ef9500`. Point-in-time receipts of the
v1.0 cycle, such as the dependency and advisory scans, are not reissued for
this release and make no claim about it.

The verifier sources necessarily contain the private-coordinate signatures
they reject. The three verifier paths under `release/` are excluded only from
that single signature check. Credential, private-path, AI-attribution, email,
protected-byte, and all other checks still apply to them.

## Non-claims

This release does not claim zero knowledge beyond the documented proof
profile, aggregate-proof batching, deployed contracts, native rollup proving or
parent-chain confirmation. It does not claim compiled-Rust semantics,
Fiat-Shamir soundness, whole-program refinement, or the converse of the
verifier acceptance refinement. Warranty and liability terms are those of the
[license](../../LICENSE) and the [disclaimer](../../DISCLAIMER.md).

Published performance measurements refer to v1.1.0. The separate
[controlled studies](../../docs/performance.md) contain limited self-measured
results for their stated hardware, workloads and timing boundaries.
