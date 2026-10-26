# Changelog

This changelog records user-visible component changes.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).
[Versioning](https://oraclizer.io/ss-gkr/docs/project/versioning/) explains how
component releases, Cargo packages, documentation and proof encodings are
versioned.

## [Unreleased]

## [1.2.1] - 2026-10-26

Archived as [DOI 10.5281/zenodo.23655511](https://doi.org/10.5281/zenodo.23655511).

The library crates, the proof format and the program identity are unchanged
from 1.2.0.

### Added

- An external zkVM proof of the v1.2 program identity,
  `statesync-gkr-v1.2-proof.cbor`: a secure succinct RISC Zero proof bound to
  image ID `1a8b55f4e1a5f703386dcfc07e5e8b2e42b5adade6be3d0057f2d565f75eb131`.
  The zkVerify RISC0 verifier on the Volta test network accepted it and
  aggregated it into an authenticated receipt. `release/v1.2/PROOF_MANIFEST.json`
  and `release/v1.2/PUBLIC_INPUTS.json` record the proof, its public statement
  and the receipt, and `spikes/zkvm-wrap/logs/` records the run that produced
  it.

### Changed

- The identity and distribution record, the attachment inventory, the release
  check and the documentation name the v1.2 proof as the current proof. The
  v1.1 proof stays a record of the v1.1 program and is no longer attached to
  this line's release.
- The saved-proof verifier in `spikes/zkvm-wrap/risc0-proof-verify` checks the
  v1.2 proof against the v1.2 image ID and public journal.
- Documentation: the README, the performance profiles, the benchmark and
  serving guides, the usage and architecture guides and the troubleshooting
  notes report the v1.2.0 measurements, with v1.1.0 measured on the same days
  and instance types as the reference. They describe how to choose a serving
  mode and its settings and how to build for proving speed. The README adds a
  figure of the serving results, and CONTRIBUTING lists the serving-crate
  checks that CI runs.

## [1.2.0] - 2026-10-25

Archived as [DOI 10.5281/zenodo.23643505](https://doi.org/10.5281/zenodo.23643505).

### Added

- Serving components and a reference proof server in `benches/serving`:
  bounded admission with explicit rejection reasons, request and frame size
  limits, a bounded return queue with job and byte budgets and deadline
  writes, parallel witness and output helpers, per-job stage timing, four
  scheduling modes, a load frontend and real-TCP checks.
- `SyncError::KindMismatch`: the prepared prover entry points refuse a request
  of another operation kind in every build profile.
- A `release/v1.2` baseline for the new program identity, with its own
  protected-source manifest, frozen-source allowlist, identity and
  distribution record and verifier. The verifier holds `release/v1.1` and
  `release/v1.0` byte frozen and scans every UTF-8 file of the protected
  surface for legacy and stable identifier occurrences.
- The expected v1.2 guest identity and its payload profile, recorded from two
  controlled clean builds that agreed on all eight identity outputs.
- A refinement evidence guide, `docs/refinement.md`, that maps the forward
  acceptance theorem, the selected Rust contract proofs and selected open
  obligations to their source.

### Changed

- The sparse layer prover computes the same proofs with less arithmetic: one
  pass per scaled output-line weight table, round nodes of both sumcheck
  phases from a single table read, and a fixed inverse Vandermonde matrix
  for round interpolation. Proof bytes are unchanged.
- `hash_leaf_pre` panics on a pre-image of the wrong width in every build
  profile; the check previously held only in debug builds.
- The program identity is new (image ID
  `1a8b55f4e1a5f703386dcfc07e5e8b2e42b5adade6be3d0057f2d565f75eb131`). The
  attached external proof stays scoped to the historical v1.1 program.
- The frozen-source allowlist enrolls the model-boundary and review
  annotation forms that the glossary announced, for 131 classified
  occurrences.
- The public-API transcript and codec regressions run from the root tests;
  the serving crate keeps the ones that need the raw duplex challenger or its
  wire profile.
- The controlled capacity replay job checks out the source it measured.
- Documentation: the README summarizes the verification results and links to
  their exact scope, and licensing notes, citation coordinates and stale
  references were corrected.

## [1.1.1] - 2026-10-10

Archived as [DOI 10.5281/zenodo.23280552](https://doi.org/10.5281/zenodo.23280552).

### Changed

- License: StateSync-GKR v1.1.1 and later versions are licensed under the
  Business Source License 1.1, with a production grant limited to proof
  verification and conversion of each version to Apache-2.0 three years after
  it is first publicly distributed under BSL. Versions up to and including
  v1.1.0 were released under MIT OR Apache-2.0. The workspace and caller
  package metadata, CITATION.cff and the package inventory declare BUSL-1.1;
  the historical program and proof expectations are unchanged. See LICENSE,
  NOTICE and release/v1.1/LICENSING_DISTRIBUTION.json.
- CONTRIBUTING records the contribution license grant that the Business
  Source License and commercial licensing require.

## [1.1.0] - 2026-10-04

Archived as [DOI 10.5281/zenodo.23136385](https://doi.org/10.5281/zenodo.23136385).

### Added

- Four Isabelle sessions that transfer the GKR soundness chain from the
  KoalaBear base field to the exact degree-four extension field used for
  verifier challenges: nonsquare certificates, the quartic field instance
  with cardinality `p^4` and the base-field embedding, polynomial,
  multilinear-extension, and circuit lifting, and the exact-field GKR
  soundness instance with a conditional uniform-coefficient pushforward.
- `Verifier_Acceptance_Refinement`, which relates a successful acceptance
  trace of the shipped Rust verifier to the reduction-chain event of the GKR
  assembly result, and states the reverse direction as a non-claim.
- An acceptance trace populated from the actual public-input, request-guard,
  zero-output, protocol-result, and final input-MLE observations, with a
  proved classifier contract, compiled on the test and translation
  configurations only.
- Fail-closed shape guards in the protocol verifier for an empty circuit, a
  layer-proof count mismatch, and an output width at or above the machine word
  width, each with a direct rejection test.
- Honest, tampered-public-input, tampered-sumcheck, false-carry, and final
  input-MLE executable witnesses, and a direct last-layer protocol-boundary
  witness.
- A `release/v1.1` baseline for the new program identity, with its own
  protected-source manifest, frozen-source allowlist and verifier. The
  verifier additionally holds the superseded `release/v1.0` baseline to one
  recorded digest so the earlier record cannot be edited.
- Pure packaging-root tests for the controlled-identity payload validator,
  including one that pins the identity-bound source selection so a silent
  drift fails in the ordinary test lane rather than at a rebuild.

### Changed

- The hosted Proofs lane builds all six registered sessions.
- The sumcheck, per-layer GKR, and facade verifier bodies no longer opt out of
  translation as a whole. Each opt-out was narrowed to the single foreign
  extension-field equality it needs, leaving the surrounding rejection and
  acceptance control flow translated as ordinary code.
- The controlled-identity payload validator accepts both an OCI index and a
  single manifest as the packaging root and separates packaging drift from
  payload drift.
- The two-clean-builds recipe anchors its ancestry check on the repository's
  own root commit, so it runs on the published repository, and its optional
  identity guard accepts either release line's expected-identity file.
- The release line moved to v1.1 with a new program identity. `release/v1.0`
  stays byte frozen as the record of the previous cycle.

### Limits

- The exact Rust-value and off-cube polynomial representation relation is not
  discharged. This work adds no axiom, trusted claim, Fiat-Shamir theorem,
  compiled-Rust semantics, whole-program refinement, deployment, or
  production-readiness claim.
- Two source-bound and task-bound type-invariant leaves remain open and carry
  no claim: the `mle_eval_base` result type invariant and the shared verifier
  body's opaque derived-wiring entry type invariant. No third open leaf is
  accepted and the trusted count is unchanged.
- The ordinary build keeps the original short-circuit rejection form; the
  accumulating acceptance-trace form exists only on the test and translation
  configurations, and the equivalence of the two forms is part of the relation
  that is not discharged.

## [1.0.0 candidate] - 2026-08-27

Completed component baseline, retained as historical evidence. No GitHub tag
or Release was published for this candidate.

### Added

- Layered GKR proving and verification over compiled sparse-Merkle
  membership, non-membership, and single-leaf update operations.
- Registered Isabelle sessions for GKR assembly and SMT compiler correctness,
  building with no admitted proof, with concrete non-vacuity instances over
  the production field.
- Bounded Rust-to-model refinement evidence with explicit trusted and tool
  boundaries.
- Independent-job batching with pointwise single-job agreement checks and
  worker-count-invariant proof bytes.
- Canonical prepared-material encoding with local reconstruction of derived
  wiring.
- A fixed RISC Zero program identity, a public proof content address, and a
  saved-proof verification path.
- Canonical route, receipt, destination-policy, and local
  candidate-transition encodings with Rust and Python equality checks.
- An exact frozen-source manifest and a finite historical-annotation
  allowlist, enforced by the release verifier.
- A public-surface verifier with worktree, clean-history, source-archive, and
  pull-request modes.
- A deterministic release-owned source archive recipe.
- Dual-license dispatcher, security policy, governance, support,
  contribution, citation, and disclaimer documents.

### Changed

- Public documentation separates the component evidence from external receipt
  operation, deployed destination behavior, native rollup proving, parent
  settlement, and secondary finality.
- Public release evidence uses semantic names and content addresses.
- Internal process receipts moved out of the public tree; the facts they
  establish are summarized in the release notes, and the records are retained
  privately.

### Security

At release, this candidate had not received a security audit and was not
intended for production use.
Passing tests and mechanized model results do not guarantee cryptographic
security, absence of implementation defects, side-channel resistance,
availability, deployment correctness, or operational safety.

The published proof is bound to the exact protected source. A protected-byte
change is a new candidate identity and is never accepted by updating expected
hashes.
