# Receipt-gated local transition profile v1

This document specifies a host-only, non-deployment reference transition that
consumes the selected StateSync-GKR proof and receipt profile. It is not a
production API, chain wire format, deployed transition, parent confirmation, or
secondary-finality result.

## Ownership

| Owner | Meaning consumed by this profile |
|---|---|
| StateSync-GKR | Application correctness and the primary record |
| Selected zkVM profile | Fixed external proof identity |
| External verifier | Proof-verification and receipt evidence |
| Destination policy | Route, domain, receipt root, authorization, lifecycle, replay, and conflict checks |
| Local adapter | An in-memory candidate after every prior check passes |

Service semantics, inner-proof encoding, and local-transition encoding have
separate version fields. A value in one namespace never selects or upgrades
another.

## Content authority

The protected vector
`tests/vectors/receipt-gated-local-transition-v1.json` owns every exact input,
field name, field order, canonical byte, and expected result. Its raw bytes and
JSON object-key order are fixed by
`release/v1.1/PROTECTED_SOURCE_MANIFEST.json`.

The adapter recomputes route identity, raw statement hash, native statement,
primary-record identity, authenticated one-leaf receipt root, claim identity,
settlement identity, signatures, and all checked negative cases. It does not
redefine those formulas.

Historical commit and assurance fields remain in the protected vector because
they are part of the canonical v1 encoding. Their names are proof-bound legacy
annotations, not current release gates or external endorsements. Their exact
public classification is in
[`docs/frozen-source-identifiers.md`](../frozen-source-identifiers.md).

## Validation and atomicity

A request is accepted only after these checks pass:

1. exact version namespaces and protected content anchors;
2. route manifest identity and fixed program identity;
3. canonical raw statement parsing, full SHA-256, and statement recomputation;
4. committed primary-record identity and fixture signature recovery;
5. source network, destination, aggregation domain, and aggregation identity;
6. leaf count, index, path, and authenticated receipt root;
7. lifecycle status, revision, registration, and cutoff;
8. settlement and delivery replay state;
9. expected predecessor and next application state.

All fallible checks occur before replay or application state is mutated. Every
rejection preserves the complete reference-state digest and event count.

An accepted result is a `LocalTransitionCandidate`. It updates only in-memory
reference state, emits one in-memory event, and always carries
`secondary_finalized = false`.

## Lifecycle

- `Active`: the registered revision equals the current nonzero revision.
- `Draining`: the registered revision and half-open cutoff checks pass.
- `Revoked` and `Replaced`: reject.
- Abandoned lineage: reject before route-local state changes.

Vector block values are test inputs, not operating policy. The fixture does not
show that a historical route is currently active or consumable.

## Canonical bytes

Integers are unsigned fixed-width big-endian. Hashes and Git object IDs are raw
bytes. Booleans are exactly `0` or `1`. Lifecycle status is one of
`1..=4`. Trailing bytes are forbidden.

The version-one field order is:

```text
domain
service-major || service-minor || service-patch || inner-proof-version || codec-version
product-commit || product-tree || readiness-index || closure-report || closure-manifest
evm-commit || evm-tree || lifecycle-evidence || lifecycle-vector
route-vector || destination-vector
route-id || ProgramBinary-size || ProgramBinary-hash || Image-ID || raw-guest-hash
raw192-hash || statement-leaf || primary-record-ID || primary-record-committed
source-network || destination-chain || destination-consumer
domain-id || aggregation-id || leaf-count || leaf-index || path-length || path
authenticated-receipt-root
lifecycle-status || current-revision || registered-revision || draining-from-revision
registered-at || drain-started-at || consume-until || destination-block
lineage-abandoned || replacement-route-id
claim-id || settlement-key || expected-predecessor || next-application-state
```

The candidate ID is `sha256(canonical_bytes)`. The protected vector fixes 930
bytes and candidate ID
`7350decf282c65b3f8770a89dbebb296910579cba3c91655ea072747e5444db5`.
Rust and the independent Python standard-library implementation emit the same
ASCII transcript with literal LF line endings.

## Reproduction

```sh
cargo test --locked --test receipt_gated_transition_v1
cargo run --locked --example receipt_gated_transition_v1 -- \
  tests/vectors/risc0-route-b-volta-2.0.0-runtime-rebind-v1.json \
  tests/vectors/risc0-route-b-destination-policy-v1.json
python3 tests/reference/receipt_gated_local_transition_v1.py \
  tests/vectors/receipt-gated-local-transition-v1.json
```

No command in this profile creates a key, signs new data, connects to an RPC,
funds an account, deploys a contract, submits a transaction, or selects a
rollup backend.

## External boundary

This local candidate and an EVM-compatible integration check do not establish
an actual rollup transition, native execution proof, parent settlement,
secondary finality, human security review, custody, or operational readiness.
