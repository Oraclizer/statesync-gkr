# Frozen source identifiers

StateSync-GKR preserves a finite source surface byte-for-byte. The
published zkVM proof is bound to the resulting program identity, so changing a
comment, diagnostic string, package description, field name, or test label in
that surface can change the identity even when the algorithm appears
unchanged.

The source is byte-preserved because the published zkVM proof is bound to this
exact program identity. The current line is v1.1. Its identity supersedes the
v1.0 identity, and the v1.0 record stays frozen under `release/v1.0`. Some
non-sensitive historical source annotations are retained to preserve the
identity they are part of. They are documented here and do not
represent current release gates, runtime roles, or external endorsements.

The machine-readable owners are
[`PROTECTED_SOURCE_MANIFEST.json`](../release/v1.1/PROTECTED_SOURCE_MANIFEST.json)
and
[`FROZEN_SOURCE_ALLOWLIST.json`](../release/v1.1/FROZEN_SOURCE_ALLOWLIST.json).
The first fixes the protected path set, modes, byte lengths, Git blob objects,
SHA-256 values, and canonical JSON key order. The second fixes every retained
legacy occurrence by path, containing-blob hash, byte offset, line hash,
occurrence ordinal, and count.

## Compatibility seals

### S-1: Dependency-direction seal

- **Technical meaning and canonical source:** The workspace crate graph and dependency direction fixed in `Cargo.toml`. Generic sumcheck and protocol crates do not depend on workload-specific compiler crates.
- **Related evidence:** Workspace metadata and dependency checks.
- **Guarantees:** The published source keeps the reviewed ownership direction.
- **Does not guarantee:** Correctness of every dependency or absence of supply-chain risk.

### S-2: Sumcheck-interface seal

- **Technical meaning and canonical source:** `SumcheckInstance`, `SumcheckOracle`, `Subclaim`, and round-message order in `crates/sumcheck/src/lib.rs`.
- **Related evidence:** Sumcheck tests and the `GKR_Protocol` Isabelle session.
- **Guarantees:** The public prover and verifier use the reviewed interface and message order.
- **Does not guarantee:** Standalone cryptographic security or a proof for an altered interface.

### S-3: Circuit-shape seal

- **Technical meaning and canonical source:** Layer list, gate family, coefficients, additive constants, and native gate semantics in `crates/protocol/src/circuit.rs`, paired with the Isabelle circuit model.
- **Related evidence:** `Layered_Circuit.thy`, wiring tests, and circuit-evaluation tests.
- **Guarantees:** The published Rust and model retain the reviewed circuit vocabulary.
- **Does not guarantee:** That an arbitrary new gate or circuit is covered.

### S-4: Compiler-boundary seal

- **Technical meaning and canonical source:** The pair of native sparse-Merkle validity semantics and circuit acceptance in `crates/compiler/src/lib.rs`.
- **Related evidence:** Compiler differential tests and the compiler-correctness Isabelle session.
- **Guarantees:** The published compiler is compared with an independent meaning standard.
- **Does not guarantee:** Whole-program refinement or correctness for unsupported operations.

### S-5: Transcript-order seal

- **Technical meaning and canonical source:** Domain tag, circuit digest, public-input order, layer claims, and sumcheck messages in `crates/primitives/src/transcript.rs`.
- **Related evidence:** Proof-digest determinism and transcript tests.
- **Guarantees:** The published proof path retains the reviewed observation order and domain tag.
- **Does not guarantee:** Random-oracle security, side-channel resistance, or security after reordering.

### S-6: Public-input-layout seal

- **Technical meaning and canonical source:** Field set and declaration order of `PublicInputs` in `crates/compiler/src/witness.rs`.
- **Related evidence:** Compiler, witness, transcript, and vector tests.
- **Guarantees:** Externally trusted inputs are fixed in one reviewed order.
- **Does not guarantee:** Correctness of data supplied by an untrusted external system.

## Refinement scopes and theorem families

### R1: Compiler refinement scope

- **Technical meaning and canonical source:** Sparse-Merkle semantics, witness layout, compiler acceptance, and local hash/layout anchors centered in `crates/compiler` and `crates/primitives`.
- **Related theorem, test, or artifact:** Theorem A, compiler differential tests, and compiler-correctness theories.
- **Guarantees:** The recorded bounded obligations connect selected Rust operations to the model under stated assumptions.
- **Does not guarantee:** Verification of every compiler function or external library.

### R2: Protocol refinement scope

- **Technical meaning and canonical source:** Sumcheck, multilinear-extension, wiring, and layer-reduction anchors in `crates/sumcheck` and `crates/protocol`.
- **Related theorem, test, or artifact:** Theorem B, protocol tests, and the `GKR_Protocol` session.
- **Guarantees:** The recorded bounded obligations cover the named protocol seams.
- **Does not guarantee:** A proof of every generic trait implementation or cryptographic primitive.

### R3: Composed verification scope

- **Technical meaning and canonical source:** Configuration, public request/result ownership, composed prove/verify entry points, and facade wiring in `crates/verification` and `src/lib.rs`.
- **Related theorem, test, or artifact:** Theorem C, end-to-end tests, and recorded replay metadata.
- **Guarantees:** The named public path is connected to the reviewed compiler and protocol owners.
- **Does not guarantee:** Whole-repository refinement, deployment correctness, or external-chain finality.

### R4: Opaque primitive boundary

- **Technical meaning and canonical source:** Hash, field, foreign-constant, and external-interface seams that are modeled through explicit assumptions.
- **Related theorem, test, or artifact:** Interface-conformance checks and assumption inventories.
- **Guarantees:** The boundary and its assumptions are visible and finite.
- **Does not guarantee:** A proof of Poseidon2 security, compiler correctness, or third-party implementation behavior.

### R2-1: Leaf-tag domain-separation obligation

- **Technical meaning and canonical source:** The leaf preimage reserves its first field element for the encoding tag, enforced in compiler and primitive hash paths.
- **Related theorem, test, or artifact:** Leaf-fold vectors and adversarial compiler tests.
- **Guarantees:** Membership, non-membership, and update leaf encodings retain the reviewed tag lane.
- **Does not guarantee:** Collision resistance of the underlying hash or validity of arbitrary encodings.

### Theorem A: Compiler semantic equivalence

- **Technical meaning and canonical source:** The compiled circuit accepts exactly when the modeled sparse-Merkle operation semantics hold, within the theorem's domain.
- **Related theorem, test, or artifact:** `SMT_Circuit_Compiler_Correctness` and compiler tests.
- **Guarantees:** Model-level compiler correctness for the stated operations and assumptions.
- **Does not guarantee:** Intrinsic validity of unconstrained raw vectors, production security, or external deployment correctness.

### Theorem B: GKR layer-reduction soundness

- **Technical meaning and canonical source:** Layer claims reduce through sumcheck and the wiring identity to the input-layer claim.
- **Related theorem, test, or artifact:** `GKR_Protocol`, materialized/regular wiring comparisons, and verifier tests.
- **Guarantees:** Model-level soundness of the stated assembly under its assumptions.
- **Does not guarantee:** Cryptographic security of every external primitive or implementation-wide refinement.

### Theorem C: Composed state-to-proof result

- **Technical meaning and canonical source:** The compiler-correctness and GKR-assembly results compose for the named verification path.
- **Related theorem, test, or artifact:** `Composition.thy`, concrete instances, and end-to-end tests.
- **Guarantees:** The named model composition holds under the combined assumptions.
- **Does not guarantee:** A claim about wrappers, chains, custody, or production deployment.

### Theorem D: Independent-job batching agreement

- **Technical meaning and canonical source:** Each proof produced by the independent-job batch path agrees pointwise with the corresponding single-proof path.
- **Related theorem, test, or artifact:** `GKR_Batching.thy` and sequential/parallel equality tests.
- **Guarantees:** Batching does not change the per-job proof meaning in the stated model.
- **Does not guarantee:** A single aggregate proof, scheduler liveness, or performance leadership.

## Prepared material profile

### A0: Prepared Material Profile

- **Technical meaning and canonical source:** The exact depth-24, strategy-A membership circuit-and-hints profile encoded by `PreparedMaterialV1` in `crates/wrap/src/prepared.rs`. Derived wiring is reconstructed locally rather than accepted as serialized authority.
- **Related evidence:** Canonical codec tests, mutation tests, and prepared-material binding tests.
- **Guarantees:** The named profile has a finite canonical encoding and reviewed validation path.
- **Does not guarantee:** Route activation, production authorization, universal profile support, or a new proof identity.

## Public proof-bound legacy annotations

The protected source contains 123 occurrences classified as **PUBLIC
PROOF-BOUND LEGACY ANNOTATION**. The finite families include historical phase,
gate, decision, design-priority, finding, mapping, approval, and broad
development-coordinate labels, including exact uppercase and lowercase field
name forms recorded by the allowlist.

For every such occurrence:

- it is a historical development annotation;
- it is not a current public workflow or approval procedure;
- it is not an external endorsement;
- it is not runtime authorization or a security role;
- it remains only because the exact proof-bound source bytes are frozen;
- this document owns its current public meaning; and
- reuse in new source is forbidden.

The labels include historical forms such as `1a`, `2a`, `2b`, `2c`, `2d`,
`3a`, `3b`, `G1`, `G2`, `PG-3`, `N1`, `N2`, `N3`, `D-*`, `mapping #*`,
`Finding-*`, approval wording, and exact `A*`/`W*` coordinate or schema-key
forms. Their presence does not approve a release, identify an actor, grant a
role, or state that an audit is current. Only the exact occurrences in the
allowlist are permitted. A moved, added, removed, or altered occurrence fails
verification.

Two further annotation forms in the frozen source predate the allowlist's
scan patterns: the `SD-*` model-boundary note and the bare
`supervisor`/`decision-*` review wording. This document catalogues them ahead
of their allowlist enrollment in the next identity cycle. They are historical
development annotations with the same meaning and the same restrictions as
every other legacy label above, and reuse in new source is forbidden.

Credentials, private keys, personal information, private machine paths,
artificial-intelligence work attribution, and operational secrets have no
exception. The only declared public professional contact is the exact author
and vulnerability-reporting tuple recorded in the protected manifest.

## Verification boundary

Run `python3 release/v1.1/verify.py --mode clean-history --require-proof` on a
final clean checkout. The verifier checks the protected path set and bytes,
canonical JSON key order, all 123 legacy occurrences, the exact public contact
tuple, the external proof hash, sensitive-data scans, and the absence of new
legacy identifiers outside these definitions.

Passing the verifier establishes release-surface integrity only. It does not
rerun Rust, Isabelle, a zkVM proof, an external verifier, a chain transition,
or a deployment.
