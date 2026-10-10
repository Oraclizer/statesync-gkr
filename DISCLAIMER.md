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
further result relates a successful acceptance trace of the shipped verifier to
the model, and it carries an explicit premise that is not discharged against
the compiled program. The exact statements, assumptions, and their limits are
in [FORMAL_VERIFICATION.md](FORMAL_VERIFICATION.md).

Each of these claims is reproducible from this repository. The commands are
in [README.md](README.md) and [REPRODUCING.md](REPRODUCING.md).

## What this repository does not establish

This software is provided as is, without warranties or conditions of any
kind, under the [Business Source License 1.1](LICENSE). In addition, StateSync-GKR is research software: it has received no external
security audit and is not ready for production use.

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
