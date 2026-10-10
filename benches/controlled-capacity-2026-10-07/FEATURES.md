# Product benefits and evidence coordinates

The nine mechanisms use different kinds of evidence. The map below identifies
those kinds; the notes preserve the measurement boundary and reuse condition.
It does not describe nine independently isolated causal experiments.

| Mechanism | Product benefit | Evidence type |
|---|---|---|
| Sparse layer reduction | More circuit/job capacity within RAM | Measurement and source |
| Structural wiring | Less prepared verification work | Measurement and model |
| Cube-gate/affine fusion | Fewer intermediate wires and layers | Source structure |
| Parallel Merkle constraints | Compact schedule as path depth grows | Shape and proof bytes |
| Prepare reuse | Avoid repeated circuit, wiring and commitment setup | Direct timing |
| Independent proof parallelism | Use workers while preserving request/result mapping | Measurement and controls |
| State lifecycle | Distinguish empty, tombstone and occupied states | Semantics and input controls |
| Strict codec and binding | Reject malformed or wrong-request proofs | Rejection controls |
| Reusable protocol core | Support other arithmetic frontends | Generic fixtures and model |

## Measurement and application conditions

- **Sparse reduction:** at two-layer mixed width 4,096, the same-driver
  Dense/Sparse comparison has 89.46-fold lower whole-process RSS and a separate
  3,242.41-fold lower additional requested-allocation peak. Capacity and RSS
  remain separate. Dense is StateSync-GKR's test-only reference, not Plonky3 or
  an external GKR implementation.
- **Structural wiring:** the supplement's Table/Derived ratio is 10.80–23.68
  for the whole prepared typed verifier call on the same proof and request.
  It includes native input/path hashing and excludes preparation. Table wiring
  is already sparse and is not the Dense prover memory reference. Model wiring
  equivalence and the partial Rust connection are distinct evidence.
- **Cube/affine fusion:** compiler design and source establish the compact
  representation; no separate unfused-compiler speed multiplier is claimed.
- **Merkle constraints:** existing depth-24/28/32 shape and proof-byte curves
  show the same layer schedule, with about 2.93% membership proof-byte growth
  from depth 24 to 32. Width and total work still grow.
- **Prepare reuse:** direct depth-24 fresh/prepared proving-path timings give
  3.46–4.45-fold lower per-request time. Reuse requires the same operation kind,
  configuration and circuit; each request has its own witness and proof.
- **Independent jobs:** caller controls and the deployment/load studies keep
  request correspondence and individual results. The output-policy comparison
  gives 9.71–10.71-fold lower complete prepared local-batch time at depth 24,
  batch 768 and 192 workers. Both policies parallelize witness/proving; only
  encoding and encoded verification change. Preparation, transport and
  post-timer hashing/logging are excluded. Persistent state and consensus are
  outside this profile.
- **State lifecycle:** compiler semantics and existing input controls cover
  supported operations and leaf states, without a persistent-database claim.
- **Codec and binding:** `smoke.py` and encoded-acceptance controls exercise
  wrong original statements and malformed trailing bytes. A proof-byte hash
  alone is not acceptance.
- **Reusable core:** generic Add/Mul/cubic-affine fixtures and the existing
  formal model support reuse. A frontend must consume both residual input MLE
  claims. The maintained source follows the root [LICENSE](../../LICENSE),
  including its non-production and verification-only production permissions.

Detailed raw records and scientific result selection have different roles.
Retaining every observation does not require putting every diagnostic failure
in the paper. Each public claim uses its actual measurement conditions and
source/model evidence. [Performance](../../docs/performance.md) gives the
statistical units, matched references and full-proof serving observations.
