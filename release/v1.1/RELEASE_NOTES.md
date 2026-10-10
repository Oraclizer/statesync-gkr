# StateSync-GKR v1.1.1 licensing distribution notes

## Status

This package describes an unaudited research component. It is not production
software, does not authorize deployment, and does not claim secondary
finality. The current distribution is licensed under BUSL-1.1.

Version 1.1.1 changes licensing and distribution metadata. The Rust kernel,
formal sources, locks and toolchain pins retain their recorded bytes. The
historical v1.1 identity cycle and its proof are preserved as historical
evidence. The exact current metadata source has not completed a compiled
identity comparison and is not assigned a new verified program identity.
[LICENSING_DISTRIBUTION.json](LICENSING_DISTRIBUTION.json) records that boundary.

## Relation to v1.0

`release/v1.0` is kept byte frozen. It records what the previous cycle
claimed, and it last held over the whole tree at commit
`a456846f98df6e0b60c9e6d33d67592a82ef9500`. To check that earlier claim on its
own terms requires the original historical copy at that commit. Its history
is preserved separately from this current public repository. The verifier in this directory holds the whole
superseded directory to one recorded digest, so the earlier record cannot be
edited without failing a required check.

Three point-in-time receipts belong to the previous cycle and are not reissued
here: the AWS durable-storage custody check, dependency scan, and advisory
scan recorded in `release/v1.0`. They remain true statements about the v1.0
artifacts and make no claim about v1.1.

## Historical v1.1 implementation changes

- The sumcheck, per-layer GKR, and facade verifier bodies no longer opt out of
  Creusot translation as a whole. Each opt-out was narrowed to the single
  foreign extension-field equality it needs.
- The protocol verifier rejects an empty circuit, a layer-proof count
  mismatch, and an output width at or above the machine word width before it
  can evaluate a shift, each with a direct rejection test.
- `Verifier_Acceptance_Refinement` relates a successful acceptance trace of
  the shipped Rust verifier to the reduction-chain event of the GKR assembly
  result, and states the reverse direction as a non-claim. The relation
  between the Rust trace values and the model is an explicit premise and is
  not discharged, so the result is a conditional refinement.

## Included component

- sparse-Merkle semantics and circuit compilation;
- sumcheck and layered GKR proving and verification;
- deterministic transcript and proof-digest checks;
- six registered Isabelle sessions covering GKR assembly, compiler
  correctness, the degree-four extension-field transfer, and the conditional
  verifier acceptance refinement;
- bounded Rust-to-model refinement evidence with documented trusted seams;
- the historical v1.1 RISC Zero program identity and its public-verifiable proof profile;
- receipt, route, destination-policy, and local candidate-transition codecs;
- an EVM-compatible reference seam tested on a stock compatible execution
  environment.

## Historical v1.1 proof identity

| Layer | SHA-256 or identifier |
|---|---|
| Program binary | `9bb3740d9c0e35f55a42adafa5bfd5cc89fe2520e1c391632807c4e33931cb04` |
| Image ID | `dc9a5f0da608178bbe56e98604cb895060c555c18329846b453f71d562d16530` |
| Raw guest ELF | `38b337c16334226f9dcd2ea319b5e6924aa583ba637126c9d7a8cfacb5cb9a5d` |
| Generated methods source | `3b8c0c23d5f0ceb84e1224b472428772c1f53bcd5c97b5ff1502acc1a6878e03` |
| Host binary | `cad5e07c07465c9f8baddbf6364ad52ae8f35529954d742f5a1449c0ee77aab9` |
| Diagnostic program binary | `0ea12e7bb8a02b0003aa3b190b0707c6e2ef22df00648ca96896909fb01a4610` |
| Diagnostic raw guest ELF | `ca7cdb1de37397232ae5cd799e0ca09217a08fe90a2556292db8f227cfee4b89` |
| External proof CBOR | `b1a9c3dc86802da706af32eb8ea17eb1ae0ed9c52954a4829cc5e3e9fdee1822` (279,128 bytes) |

Expected values are immutable comparison targets. A mismatch is a failure;
the release process never updates them to fit a new build.

The historical identity was produced by two clean, locked, offline,
network-disabled builds of the then-recorded source selection, which agreed on all eight outputs. The
two builds produced different intermediate build-image identifiers, which is
builder packaging metadata and not part of the program identity.

## Public verifier observation

The proof for this identity was submitted to the zkVerify Volta test chain and
accepted. The chain reported the proof verified and queued it for aggregation
in domain 2 under aggregation identifier 56583, and the aggregation was
published 23 blocks later. The receipt covers a single leaf whose value is the
statement of this identity, and its authenticated root was recomputed from
that leaf with a local Keccak-256 implementation rather than taken from the
node.

| Item | Value |
|---|---|
| Submission block | 7,267,596 |
| Aggregation block | 7,267,619 |
| Statement leaf | `ea414507f2843a858178ece4775ebc99f7502dc5b6554c82c38d77092475ce66` |
| Authenticated root | `43820b7d3a614a3df41ce846d149c5955501a208108e8c90e9d9a3dac60fb4b9` |

This is a public test network. Acceptance there is evidence that the proof
verifies under the named verifier and runtime. It is not a production
deployment, a destination settlement, or secondary finality.

## Verification boundary

The protected source and its historical annotations are documented in
[`docs/frozen-source-identifiers.md`](../../docs/frozen-source-identifiers.md).
The exact source manifest and occurrence allowlist live next to this file.

The final surface verifier checks bytes and release hygiene. It does not by
itself rerun the Rust tests, Isabelle sessions, zkVM proof, external receipt,
artifact-restore check, or destination integration.

The public workflow never rebuilds or changes the zkVM identity. A pull
request verifies 78 unchanged protected files, the exact root Cargo
license-field delta, the sensitive-content rules, and the path-membership diff. A push to `main` additionally verifies the
full-tree content manifests and the superseded baseline digest. A published
release additionally downloads the named proof attachment and requires its
exact size and SHA-256 to match the protected manifest.

The verifier source necessarily contains the private-coordinate signatures it
rejects. The two verifier paths, `release/v1.0/verify.py` and
`release/v1.1/verify.py`, are excluded only from that single signature check.
Credential, private-path, AI-attribution, email, protected-byte, and all other
checks still apply to both.

## Non-claims

This release does not claim a security audit, absence of vulnerabilities,
production fitness, zero knowledge beyond the documented proof profile,
aggregate-proof batching, controlled-hardware performance, deployed contracts,
native rollup proving, parent-chain confirmation, legal compliance, or
operational support commitments. It does not claim compiled-Rust semantics,
Fiat-Shamir soundness, whole-program refinement, or the converse of the
verifier acceptance refinement.
