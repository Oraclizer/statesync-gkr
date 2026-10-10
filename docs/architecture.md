# Implementation architecture and application benefits

Version 1.1.1 is a BSL distribution and package-metadata revision. The Rust
kernel and formal sources retain their recorded contents. The root Cargo
license field is the sole change in the identity-source selection. The
[licensing distribution record](../release/v1.1/LICENSING_DISTRIBUTION.json)
separates that source comparison from the historical v1.1 executable and
proof. The current metadata revision has not completed an exact compiled
identity reproduction; the historical proof is evidence of its recorded
program only.

StateSync-GKR separates a reusable sumcheck/GKR engine from its sparse-Merkle
frontend. The engine reduces a layered arithmetic circuit; the frontend defines
the statement, compiles its constraints, supplies witnesses and checks the
residual input claims. This separation lets an application reuse the engine
without adopting the SMT operation language.

The measurements refer to the historical v1.1.0 kernel,
commit `1b8d2f829792172b347dedbfde969016c2c05789`, archived as
[software DOI 10.5281/zenodo.23136385](https://doi.org/10.5281/zenodo.23136385).
The benchmark callers and observations are separate from that software identity.
The [performance guide](performance.md) defines every reported interval.

## Sparse layer reduction

The production oracle in [reduce.rs](../crates/protocol/src/reduce.rs) uses
Libra-style two-phase sparse booking. Linear and cube terms depend on the first
input block, while multiplication contributes a sparse list of weighted input
pairs. Summing the second block first folds multiplication into a booking table.
The first phase binds the first block; the second phase builds the remaining
second-block coefficients at the fixed first point. The production path never
materializes the complete quadratic input-pair hypercube.

For one layer with `n_in` input wires, `n_out` output wires and `m` multiplication
gates, auxiliary ownership is `O(n_out + n_in + m)`. The output-weight vector,
embedded values, retained capacities and second-phase buffers belong in that
boundary. The test-only Dense reference constructs six `n_in²` factor tables and
constructor temporaries. Both paths use one prover driver and transcript order.

The application benefit is more circuit or concurrent-job capacity per RAM
budget. In a two-layer width-4,096 mixed circuit, the additional requested
allocation peak was 1,879,247,872 B for Dense and 579,584 B for Sparse
(3,242.41 times lower). Whole-process RSS was 1,855,016 versus 20,736 KiB
(89.46 times lower), a separate measurement. Owned Vec capacity is also
reported separately. Under an active
3-GiB cgroup with swap disabled, Sparse returned proofs through tested width
65,536; Dense at width 8,192 was killed by the native OOM mechanism. These are
bounded internal comparisons. For shared cases where both modes complete,
canonical field-basis proof observations match and verification accepts.
These benchmark observations use their own JSON representation, separate from
the official `inner-proof-v1` encoding. Sparse-only scale points have no
completed Dense proof counterpart. The largest tested point is not a global
supported maximum or a ranking of all GKR implementations.

## Wiring structure at verification

[wiring.rs](../crates/protocol/src/wiring.rs) supplies a general sparse gate-list
oracle, `TableWiring`, and a derived regular-family oracle. The latter evaluates
arithmetic-progression families in closed form and retains an exact sparse
residue. Derivation checks every member's progression, kind and coefficient,
retaining unsupported gates on the sparse path. Audit tests re-expand the
representation and compare the weighted gate multiset.

The application gains less work in the full prepared verifier call. In nine
depth/operation profiles, paired verification was 10.80–23.68 times faster with
the derived oracle. The timer encloses all of `verify_sync_op_with`, including
request validation and native leaf/path hashing. It holds the circuit, request,
proof and verification body fixed and changes only the wiring oracle. Circuit,
wiring and commitment preparation, proof generation, encoding and transport
are excluded. The Table oracle already iterates sparse gates: it is
not the quadratic Dense prover oracle above. The model proves wiring-extension
equality under its repartition premise; the actual Rust check/fallback belongs
to the declared partial implementation connection.

## Cube gates, fused rounds and shallow path constraints

The IR has weighted linear, product and cube gates. `Pow3` is a built-in cube
gate, not a specialized processor instruction. The builder's `combine` and the
compiler's `fused_round` in [builder.rs](../crates/compiler/src/builder.rs) and
[compile.rs](../crates/compiler/src/compile.rs) accumulate cube/linear taps and
constants into one round layer. This represents the Poseidon2 cube and matrix
step without a separate layer for every arithmetic subexpression.

The witness still computes the authentication path's accumulators in order.
Compilation checks each compression transition against those supplied
intermediate values as parallel residual constraints. The round schedule then
depends on the hash template, while a deeper path increases width and work.
All nine measured membership/absence/update profiles at depths 24, 28 and 32
have 118 layers. Membership encoded proof size grows from 176,948 B to 182,132 B
between depths 24 and 32, about 2.93%. This is a compact schedule and modest
proof-size growth; witness work, total computation and verification are not
constant with depth. There is no new unfused-compiler speedup measurement.

## Prepared material and independent jobs

`PreparedSync` in [the facade](../src/lib.rs) owns the operation-kind circuit,
full circuit commitment and derived wiring. It is immutable and shareable.
Reuse it for the same kind, SMT parameters, strategy and configuration. Each
request retains its own public inputs, witness, transcript and proof.

Commitment reuse is especially valuable: the depth-24 membership measurements
recorded 105.027310 ms for commitment versus 7.902078 ms for compilation.
Direct fresh/prepared depth-24 measurements show approximately 3.69/3.46/4.45
times lower per-request proving-path latency for membership/absence/update.
Each operation and mode has three processes of 1,000 timed requests; ratios
compare run-matched process summaries. Encoding, transport and acceptance are
outside that timer. Reuse removes setup while each job keeps its own
challenge-dependent proof state.

`prove_batch_parallel` follows the caller's explicitly sized Rayon pool and
collects one proof per input job in input order. It preserves the existing proof
format; independent batching is not aggregation. The measured caller also
parallelizes witness generation and output encoding/verification. At depth 24,
batch 768 and 192 workers, the output-mode comparison improved the complete
prepared local batch interval by 9.71–10.71 times across three operations.
That interval includes witness generation, proving, encoding and encoded
verification. Both policies parallelize witness generation and proving; only
encoding and encoded verification change mode. Preparation, transport and
post-timer hashing/logging are excluded. This range
spans the three operation-specific medians across five processes, each process
summarized by the median of ten paired serial/parallel interval ratios.
Smaller-batch effects are separately reported.

Remote dispatch is another caller policy. Asynchronous replies may complete out
of order; request IDs, fixture IDs and operation kinds bind them to the original
requests. The actual one-worker/two-worker study transferred complete proof
payloads and ended at frontend cryptographic acceptance. It compares resource
equivalent deployment configurations whose batch caps scale with worker count,
not topology in isolation. [Usage](usage.md#choosing-worker-and-batch-settings)
lists the confirmed settings and their periods.

## State lifetime and acceptance

[SMT semantics](../crates/compiler/src/smt.rs) distinguish `Empty`,
`Occupied(payload)` and `Tombstone`. A never-used and a deleted slot remain
different, while either can satisfy non-membership. Updates cover insertion,
replacement, deletion and restoration with their old/new path and root
conditions. The input-variant study exercises eight concrete lifecycle and
payload/key cases. It measures cryptographic operation semantics, not a live
database commit or consensus system.

`verify_encoded_sync_op` consumes the entire received inner-proof encoding,
checks shape and circuit/configuration identity, then verifies the statement
against the original request. Roots, value digest and input claims remain
load-bearing checks; trailing bytes and mismatched inputs are rejected. See
[the strict format](encoding/inner-proof-v1.md). The current SMT verifier also
recomputes native leaf and path hashes from the private witness. The measured
full-call gain from derived wiring retains that hashing work.

## Reuse and formal foundation

The protocol and sumcheck crates have no dependency on the SMT compiler.
The shipped entry points use KoalaBear circuit values, degree-four extension
challenges and the pinned Poseidon2 primitives. Another frontend supplies its
own circuit, witness, output claim, transcript conventions and the consumption
of both residual input MLE claims. Arbitrary Rust-program compilation and a
runtime field/hash-selection service are not bundled interfaces.

The measured v1.1.0 source was released under MIT or Apache-2.0. The maintained
branch and later versions use [BSL 1.1](../LICENSE), with free non-production
use and the verification-only production grant; [NOTICE](../NOTICE) preserves
the version history. Reuse of the maintained engine follows those terms. Six
Isabelle sessions with twenty theories provide the compiler equivalence, GKR
assembly model, composition, batching and supporting results described in
[formal verification](../FORMAL_VERIFICATION.md) and
[the paper](https://arxiv.org/abs/2610.05335). Performance and differential proof
observations strengthen the engineering account without adding a new theorem,
whole-program verification, Fiat–Shamir reduction or security-audit grade.
