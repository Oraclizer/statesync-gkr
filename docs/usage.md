# Usage and API boundary

Version 1.1.1 is a BSL distribution and package-metadata revision. The Rust
kernel and formal sources retain their recorded contents. The root Cargo
license field is the sole change in the identity-source selection. The
[licensing distribution record](../release/v1.1/LICENSING_DISTRIBUTION.json)
separates that source comparison from the historical v1.1 executable and
proof. The current metadata revision has not completed an exact compiled
identity reproduction; the historical proof is evidence of its recorded
program only.

StateSync-GKR is a Rust source release. Start with its SMT facade for
membership, non-membership and single-leaf updates. The lower `sumcheck` and
`gkr` modules are reusable by other circuit frontends.

> **WARNING:** This is a research implementation, unaudited and not ready for
> production use. Model verification and the remaining implementation
> assumptions are described in [FORMAL_VERIFICATION.md](../FORMAL_VERIFICATION.md).

## Choosing a path

For a direct check of a supplied Merkle path and SMT operation, the public
`compiler::smt_valid_native` function is the native semantics checker. It
does not compile a GKR circuit or generate proof messages.

The GKR facade adds a circuit, proof generation, transcript replay, residual
input-claim checks and its own public-input guards. It is useful for the
layered-circuit engine, the compiler-to-protocol model and the documented
external-proof route. It is not a substitute for authenticating the root's
source or providing database consensus.

The current SMT verifier rebuilds its circuit input vector from the supplied
private witness. That reconstruction computes the leaf hash and all sibling
hashes along the old path; an update also computes the new path. It then checks
the GKR proof and the input multilinear-extension claims. This frontend
therefore retains the native Merkle hashing work and requires the full witness;
it is not a public-input-only verifier that eliminates those hash computations.

The direct semantics check and GKR proof verification have different work
and output contracts. Their measured timings must not be read as two
implementations of the same verifier. The CPU note reports those boundaries
separately.

## Run the existing example

The commands below use the maintained source distribution under
[BSL 1.1](../LICENSE): research, development and other non-production use are
free; production use solely to verify proofs is granted. Other production use,
including proof generation, embedding or redistributing proving functionality
and third-party proof services, requires a commercial license. Each version
converts to Apache 2.0 three years after first publication under BSL. See
[NOTICE](../NOTICE) for the version boundary and preserved metadata.

```sh
git clone --depth 1 https://github.com/Oraclizer/statesync-gkr.git
cd statesync-gkr
rustup show
cargo run --release --locked --example state_sync_prove_verify
```

The example must print:

```text
honest-proof=PASS
tampered-proof=REJECTED
secondary-finalized=false
```

Its complete source is
[`examples/state_sync_prove_verify.rs`](../examples/state_sync_prove_verify.rs).
This local path requires neither the zkVM build environment nor a network
submission. The reference transition and external proof routes have separate
requirements under [Reproducing the release](../REPRODUCING.md).

## Pin the source in an application

The packages are unpublished. The following standalone application's
`Cargo.toml` selects the current maintained source. Pin a current commit when recording a fixed reproduction subject.
Choose a maintained source revision separately if that is the version you
intend to integrate; its root LICENSE controls, even while frozen package
metadata still carries the old declaration:


```toml
[package]
name = "statesync-gkr-integration"
version = "0.1.0"
edition = "2024"
publish = false

[dependencies.statesync-gkr]
git = "https://github.com/Oraclizer/statesync-gkr.git"
branch = "main"
```

Use Rust `1.96.1`, the release's pinned toolchain:

```sh
rustup toolchain install 1.96.1 --profile minimal
cargo +1.96.1 run --release
```

The first application build creates its own `Cargo.lock`. Preserve that lock
and use `cargo +1.96.1 run --release --locked` on subsequent runs. A Git commit
pin fixes source; the application's lock records its resolved dependency
graph. Release reproduction uses the repository's own lock and commands.

The tested host paths are x86-64 Linux in CI and the controlled CPU study,
and Windows 11 with the x86-64 GNU Rust target. A normal Rust linker/build
environment is required. Release-surface and codec tools use Python 3.11 or
later. The selected zkVM identity build has its own documented environment.

## Complete application

Save the following as `src/main.rs`. It builds a small synthetic membership
request, reuses a prepared circuit, verifies the inner and encoded proof, and
requires rejection after tampering. The supplied identity bytes and sibling
digests are deterministic fixture data, not records from an external registry.

```rust
use std::process::ExitCode;

use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs,
    SmtOperation, SmtParams, SmtWitness,
};
use statesync_gkr::primitives::field::{
    BaseField, ChallengeField, PrimeCharacteristicRing,
};
use statesync_gkr::primitives::hash::{Digest, HashGadget, Poseidon2Gadget};
use statesync_gkr::{StateSyncGkrConfig, StateSyncProver, SyncRequest};

fn field(value: u32) -> BaseField {
    BaseField::from_u32(value)
}

fn membership_request(params: &SmtParams) -> Result<SyncRequest, String> {
    if !(1..=64).contains(&params.depth) || params.leaf_max_fields < 10 {
        return Err("this example requires depth 1..=64 and leaf_max_fields >= 10".to_owned());
    }
    let hasher = Poseidon2Gadget::new(params.leaf_max_fields as usize);
    let key = AssetId(5);
    let payload = LeafPayload {
        sync_state: vec![field(42), field(7)],
        identity_digest: [9_u8; 32],
    };
    let leaf = LeafState::Occupied(payload.clone());
    let path = MerklePath {
        siblings: (0..params.depth)
            .map(|index| Digest([field(index * 13 + 1); 8]))
            .collect(),
    };
    let root = path
        .compute_root(&hasher, params, key, &leaf)
        .map_err(|error| format!("root construction failed: {error:?}"))?;
    let value_digest = hasher
        .hash_leaf(&leaf.encode())
        .map_err(|error| format!("leaf hashing failed: {error:?}"))?;
    let operation = SmtOperation::Membership { key, payload };
    let op_kind_tag = PublicInputs::kind_tag(operation.kind());
    Ok(SyncRequest {
        operation,
        witness: SmtWitness { leaf, path },
        public_inputs: PublicInputs {
            old_root: root,
            new_root: root,
            op_kind_tag,
            asset_id: key,
            value_digest,
        },
    })
}

fn run() -> Result<(), String> {
    let params = SmtParams { depth: 4, ..Default::default() };
    let prover = StateSyncProver::new(StateSyncGkrConfig {
        smt: params,
        layer_strategy: LayerStrategy::A,
        ..Default::default()
    });
    let request = membership_request(&params)?;
    let prepared = prover
        .prepare(request.operation.kind())
        .map_err(|error| format!("preparation failed: {error:?}"))?;
    let mut result = prover
        .prove_sync_op_prepared(&prepared, &request)
        .map_err(|error| format!("proving failed: {error:?}"))?;
    if !prover.verify_sync_op_prepared(&prepared, &request, &result) {
        return Err("the honest proof was rejected".to_owned());
    }
    println!("honest-proof=PASS");

    let bytes = prover
        .encode_sync_result(&prepared, &result)
        .map_err(|error| format!("encoding failed: {error:?}"))?;
    if !prover.verify_encoded_sync_op(&prepared, &request, &bytes) {
        return Err("the encoded proof was rejected".to_owned());
    }
    println!("encoded-proof=PASS");

    let first_layer = result.proof.layer_proofs.first_mut()
        .ok_or_else(|| "the proof contains no layer proof".to_owned())?;
    first_layer.eval_x += ChallengeField::ONE;
    if prover.verify_sync_op_prepared(&prepared, &request, &result) {
        return Err("the tampered proof was accepted".to_owned());
    }
    println!("tampered-proof=REJECTED");
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("integration=FAIL: {error}");
            ExitCode::FAILURE
        }
    }
}
```

For a real state store, supply its authenticated roots, operation and witness.
Recomputing a root from arbitrary caller-supplied siblings does not establish
that the root belongs to a trusted database, chain or registry.

## Supported SMT inputs

| Operation | Witness leaf | Value digest |
|---|---|---|
| Membership | Asserted occupied payload | Hash of the occupied leaf encoding |
| NonMembership | Empty or tombstone | Hash of the asserted leaf encoding |
| Update | The operation's old leaf | Hash of the new leaf encoding |

For membership and non-membership, `new_root` equals `old_root`. An update
binds the previous and resulting roots under the same sibling path and uses
`new_leaf.encode()` for its value digest. The witness states are `Empty`,
`Tombstone` and `Occupied`; the update witness is the operation's `old_leaf`.

Every `SyncRequest` supplies the operation, `SmtWitness` and `PublicInputs`.
The public-input fields are `old_root`, `new_root`, `op_kind_tag`, `asset_id`
and `value_digest`; use `PublicInputs::kind_tag` to obtain the operation tag.
The path contains one sibling digest per tree level, ordered from the leaf
toward the root. `AssetId` is a `u64`; for a depth below 64 it must be less
than `2^depth`. The integration example restricts depth to 1..=64 before calling
the API. The existing quickstart uses depth 4; the controlled study covers
depth 24, 28 and 32 rather than every possible configuration.

The compiler currently implements `LayerStrategy::A`. Other enum variants
return `CompileError::UnsupportedConfig`. A zero depth and a leaf encoding
bound below 10 also return that error. Choose practical bounds before accepting
untrusted requests; configuration values are not a resource-limiting service.

## Field, hash and encoding profile

| Item | Shipped profile |
|---|---|
| Circuit field | KoalaBear, `p = 2^31 - 2^24 + 1 = 2130706433` |
| Challenge field | Degree-four binomial extension of KoalaBear |
| Hash / transcript | Poseidon2 over KoalaBear; fixed transcript conventions |
| State-tree digest | Eight base-field elements, `Digest<BaseField>` |
| Occupied leaf | State tag, sync-state fields, nine identity limbs |
| Identity input | Caller-supplied 32-byte off-circuit identity digest |
| Default leaf encoding bound | 31 field elements, including tag and identity limbs; at most 21 sync-state fields |

Identity limbs use little-endian base `2^30`; sync-state fields are encoded by
the caller. `LeafState::encode()` assigns distinct tags to `Empty`, `Occupied` and
`Tombstone`. `hash_leaf` applies the length-bound, lossless leaf layout before
hashing; it rejects an empty or oversized encoding. State-field conversion and
the meaning of the supplied identity digest are the application's responsibility.
This compiler does not prove the off-circuit Keccak computation.

The generic traits and circuit representation are useful extension points,
but the shipped GKR proving functions use the field aliases above. Replacing
the field, hash, transcript or compiler is a new implementation and verification
task. The existing proof and model claims do not transfer automatically.

## Prepared execution and independent jobs

Prepare one `(operation kind, configuration)` at startup with `prepare`.
Reuse it through `prove_sync_op_prepared` and `verify_sync_op_prepared`.
Recreate it after changing tree depth, leaf bound or another circuit parameter;
do not mutate a prover's configuration while reusing old prepared state.

`make_job_prepared` generates one job's witness. `prove_batch_prepared` proves
a homogeneous slice sequentially. `prove_batch_parallel` uses the current
Rayon pool and preserves input order. Callers choose a fixed worker count by
constructing a Rayon pool and invoking the method inside `pool.install`.
Check that every job has the prepared operation kind and expected configuration.
One job produces one proof; batching is independent execution, not a single
aggregate proof.

The controlled benchmark also measures a separate caller that parallelizes
`make_job_prepared` before invoking `prove_batch_parallel`. That orchestration
lives in the benchmark driver and is not a built-in witness-parallel method
of the released facade. The two stages complete in sequence.

## Choosing worker and batch settings

Reuse `PreparedSync` only for the same operation kind, SMT depth and leaf
capacity, strategy and configuration. It owns the circuit, full circuit
commitment and derived wiring; each request still needs its own witness,
transcript and proof. Create the reusable material once per supported profile
and use an explicitly sized Rayon pool around independent proving jobs.

The measured balanced depth-24 workload supports the following starting points:

All settings use a 5-ms maximum batch wait. Workers and batch cap are equal
per worker; the two-worker configuration splits the offered load equally.

| Worker resources | Offered requests/s | Workers / cap | Confirmation |
|---|---:|---:|---|
| 48 cores, 96 GiB | 500 | 48 / 48 | One 15-minute run |
| Two 48-core, 96-GiB workers | 1,000 total | 48 / 48 each | Three 20-second runs |
| 192 cores, 384 GiB | 1,000 | 192 / 192 | Three 60-second runs |

Every timed request in both 48-core configurations was accepted within 500 ms.
Every timed request in the three 192-core confirmations was accepted within
one second. These periods describe the observations, not an unlimited-duration
service guarantee. A separate 1,150/s, 60-second run accepted all 69,000 requests
within two seconds, but only 70.3667% within one second while its queue grew;
it does not replace the one-second starting point above.

These settings belong to the benchmark's thin serving caller, not a new
built-in network service or latency guarantee. It maintains one FIFO per
operation kind, flushes the oldest ready kind, and processes one compute batch
at a time. A maximum wait makes a batch ready; waiting for an earlier batch can
take longer. The facade's parallel method follows the caller's Rayon pool and
returns one proof per job in input order. An asynchronous remote caller instead
matches completed replies by request ID.

Small batches can leave the pool underused: caps 16/24 could not meet the
balanced 500/s deadline objective on the measured 48-core VM. Caps 40/48 and
worker counts 36–48 were short-run candidates; reducing thread count on a
48-core host does not establish a smaller VM's performance or price.
Membership-only, absence-only and update-only loads differ from the balanced
mix. The update-only 500/s case did not meet the one-second objective in every
short run. Choose by final accepted fraction, queue trend, latency budget and
memory observations, rather than eventual acceptances divided by offered time.

Keep offered, submitted, accepted, late, rejected and pre-send overload outcomes
separate. A bounded generator/worker queue must record overflow. Count the
complete received proof through `verify_encoded_sync_op`; a proof hash alone
is not verification. Preserve the original request's configuration, roots and
value digest, and stop on a semantic or identity mismatch. See
[measured profiles](performance.md) for the complete measurement boundaries.

## Errors and rejected proofs

**Preparation and fresh proving**

`prepare` and `prove_sync_op` return `SyncError::Compile` for unsupported
compilation. Fresh proving can also return `SyncError::Witness`.

**Prepared witness construction**

`prove_sync_op_prepared` and `make_job_prepared` return `SyncError::Witness`,
including for a malformed path or an oversized leaf encoding.

**Typed verification**

`verify_sync_op` and `verify_sync_op_prepared` return `false` for a rejected
proof, invalid request, wrong kind or failed binding.

**Encoding and received-proof verification**

`encode_sync_result` returns `EncodeError` for unsupported shape, counts or
metadata widths. `verify_encoded_sync_op` returns `false` on decoding, identity,
request or proof verification failure.

Proving success is not an acceptance verdict. Always check the matching
verification result, as the example does. Do not retry malformed input
indefinitely, discard a `false` result, weaken the verifier or replace an
expected identity after a mismatch. Record the source revision, configuration
and error class when diagnosing failures.

## Inner proof transport and generic core

Use `encode_sync_result` for the existing `inner-proof-v1` format and
`verify_encoded_sync_op` to decode and check it. The bytes include circuit
identity, public inputs and proof messages. They do not include the private
Merkle witness, which the current facade still requires when verifying.
Field limbs, byte order and strict shape rules are specified in
[Inner proof encoding](encoding/inner-proof-v1.md). This format is distinct
from the wrapper's external statement and proof.

The recorded vendor guest is a fixed depth-24 membership example that checks
one preserved inner proof with its fixed request. The general `wrap_relation`
API does not make that vendor program an arbitrary-request proof service.
A different vendor workload needs its own program, identity and verification
work; the current recording does not authorize or establish that change.

The sumcheck verifier returns a residual `Subclaim`, and the GKR verifier
returns residual input claims. A custom frontend must discharge them against
its bound input data and supply its circuit, witness, output claim and transcript
conventions. The SMT facade performs those checks for its supported request
format. Arbitrary program compilation, alternative field/hash profiles and
other application adapters are not bundled with this release.

## Contributor checks

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets --locked -- -D warnings
cargo test --workspace --release --locked
python3 release/v1.1/verify.py --mode pull-request
```

The quickstart is separate from contributor and proof reproduction. Changes to
the proof-bound source follow [CONTRIBUTING.md](../CONTRIBUTING.md) and
[FORMAL_VERIFICATION.md](../FORMAL_VERIFICATION.md).
