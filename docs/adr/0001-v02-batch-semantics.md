# ADR-0001: v0.2 batch semantics, independent-job throughput batching

## Status

Accepted, 2026-07-12, at the v0.2 stage entry. Decided by project direction;
this record holds the binding rationale.

## Scope

`ssgkr-batching` and the facade batch surface.

## Context

v0.1 `StateSyncProver::prove_batch` shares one compiled circuit across a
batch and then runs the UNMODIFIED single-proof `gkr::prove` per job:
compilation is amortized, proving is not. The v0.2 stage brief is
"throughput": make batching amortize everything that can be shared, add
simple parallelism, and measure.

Three different features could be called "batching". They need different
guarantees and must not be conflated under one name:

| Candidate | Meaning | What it would require |
|---|---|---|
| **Independent-job batch** | N independent sync operations proved together; one proof per operation, each byte-identical to the single-proof path | Theorem D (pointwise agreement + length), ordering, failure isolation |
| Aggregate batch proof | N statements verified through one cryptographic aggregate | NEW aggregate soundness model, membership/index binding, new proof shape, new audits |
| Atomic multi-leaf transition | One transaction atomically updating several leaves under one root transition | NEW multi-update circuit + NEW semantic model (Theorem A rework), atomicity |

## Decision

**v0.2 implements independent-job throughput batching only.**

1. A batch item stays one sync operation with its own `GkrProof`. The
   batch pipe must deliver, at every position, a proof **bit-identical**
   to what the single-proof pipeline produces for that job (same
   transcript convention, same proof bytes). Amortization may only share
   work that cannot influence proof bytes: circuit compilation, the
   verifier's wiring derivation (`v_setup`), and (if measurement ever
   justifies it) allocation reuse, never transcript state across jobs,
   never proof-shape changes.
2. Parallelism is job-level: each job's transcript is seeded from its own
   public inputs only, so worker count and scheduling order cannot change
   any proof byte. Results are returned in queue order.
3. Mixed-kind batches stay out: a batch shares one compiled circuit, so
   jobs batch per `SmtOpKind` (the existing per-kind queue lanes).

## Rationale

- **Theorem D is an independent-job theorem.** The mechanized locale
  `batch_pipeline` (`formal/isabelle/GKR_Protocol/GKR_Batching.thy`) grants all of
  Theorem D to any pipe discharging exactly two obligations: length
  preservation and `batch_pipe ops ! i = prove (ops ! i)` (pointwise
  agreement). An aggregate proof or a multi-leaf circuit produces
  DIFFERENT proofs/statements, so neither obligation is dischargeable;
  reusing Theorem D as their justification would be a category error.
  They are separate circuits/models with their own audits, explicitly
  out of v0.2 scope.
- **Soundness first:** independent jobs preserve the established
  adversarial tests and the existing model/refinement boundary;
  the verifier is untouched.
- **Deterministic primary-record floor:** per-job proofs isolate failures
  (one bad witness rejects one item, not the batch) and keep tail latency
  a per-item property the deadline scheduler can reason about.
- **Product mapping:** "100+ state changes in one call" (Oraclizer spec
  language) is not this feature. If it arrives as independent sync units,
  it is exactly this batch; if it must be one atomic root transition, it
  is the multi-leaf feature (new circuit + model, v0.3+ decision at the
  earliest, and Theorem D must NOT be cited for it.

## Consequences

- The v0.2 amortized pipe re-instantiates the mechanized `batch_pipeline`
  locale (a new interpretation discharging the two obligations); the
  generic theorem is NOT re-proved (no-rework principle).
- The bit-identity gate becomes executable: tests pin `batch(1) ==
  single`, amortized == v0.1 path across kinds/batch sizes, and
  worker-count invariance of proof bytes.
- Aggregate/multi-leaf remain recorded as separate future features with
  their own soundness work; nothing in v0.2 may silently drift toward
  them.
