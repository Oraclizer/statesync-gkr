# Disclaimer

## What this repository establishes

The pinned Rust workspace builds and passes its release-mode unit,
integration, differential, adversarial, codec, and deterministic proof-digest
tests. The toolchain and every dependency are locked, the workspace contains
no `unsafe` code, proof bytes are independent of worker count and CPU
features, and the published source matches a byte-exact manifest that anyone
can re-check with one command. The published external proof verifies against
one fixed program identity with recorded public inputs, and a tampered proof
is rejected.

Beyond testing, the core algorithms are mechanized in Isabelle/HOL: six
registered sessions with no admitted proof establish that the compiled circuit
agrees with the modeled sparse-Merkle semantics, that a false claim survives
the reduction only with a proved probability bound, that these results compose,
that batching preserves each single-job proof, and that the soundness statement
transfers to the exact degree-four extension field the implementation uses. A
further forward theorem connects related acceptance traces to the GKR
reduction-chain event and derives the former local-bridge premise from the
concrete round checks and the finish-evaluation part of the value relation. Recorded Creusot proofs cover selected public-input
equality and acceptance-classifier contracts. Narrowed foreign-field equality
seams expose the surrounding verifier control flow to contract translation.
These artifacts give developers a review map for the checks that determine
acceptance and a reusable basis for integration and maintenance.

The Rust/model value and off-cube representation relation remains an explicit
premise that is not discharged against the compiled program. Translation
coverage does not give proof credit to the recorded open contract obligations.
[Refinement evidence and reuse](docs/refinement.md) identifies both the
completed and open records. The exact statements, assumptions, and their limits are
in [FORMAL_VERIFICATION.md](FORMAL_VERIFICATION.md).

The source-level test and model commands are in [README.md](README.md) and
[REPRODUCING.md](REPRODUCING.md). The external proof applies to its recorded
historical program, whose exact identity reproduction also requires its
original controlled-build materials. The current source checks do not
establish an independently reproduced compiled identity for this working tree.

## What this repository does not establish

This software is provided as is, without warranties or conditions of any
kind, under the [Business Source License 1.1](LICENSE). The implementation
has not undergone a comprehensive independent security audit, and the verified
models do not substitute for one. A production deployment should
review the documented implementation and cryptographic assumptions and the
intended application's operational risks.

A model result is not a statement about the whole implementation. The
mechanized theorems do not establish whole-repository refinement,
cryptographic security of the underlying primitives, resistance to side
channels, availability under load, deployment correctness, or operational
safety. Passing tests bound the untested area; they do not remove it.

The published proof applies only to the fixed protected program identity.
Modified source, a fork, a different build environment, or a different
deployment falls outside that evidence until it is independently verified. A
local candidate transition is not a transaction and does not create secondary
finality. Deployed contracts, key handling, operational recovery, native
rollup proving, and parent-chain settlement are outside this repository.

Nothing here is legal, regulatory, financial, investment, or operational
advice. Users are responsible for their own review, testing, security
assessment, deployment decisions, and compliance obligations.

The LICENSE file is the controlling legal text. This summary does not
replace or modify it.
