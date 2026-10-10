# RISC Zero Route B destination receipt policy v1

## Status and boundary

This document defines a deterministic reference policy and cross-language test
vector. It is not a deployed contract, deployment authorization, proof of live
source consensus, or production-readiness claim. Version 1 selects an approved
receipt-root quorum policy. A direct source-consensus adapter would be a
replaceable, separately reviewed policy version; it is not an unimplemented
promise made by this profile.

The Rust oracle is `crates/wrap/src/risc0_destination_policy.rs`. The checked
vector is `tests/vectors/risc0-route-b-destination-policy-v1.json`, and
`tests/risc0_destination_policy_v1.rs` recomputes every derived identifier from
the input half without trusting the expected half and executes every state
transition. All signer addresses and signatures in that
vector come from public test-only secp256k1 scalars. They are never deployment
principals and must never receive assets or authority.

## Source identities

All concatenations are exact byte concatenations. Strings are UTF-8, integers
are unsigned fixed-width big endian, and hashes are raw 32-byte values.

```text
source_network_id = keccak256(
  "SSGKR_SOURCE_NETWORK_V1" ||
  utf8(network_name) ||
  source_genesis_hash
)

source_runtime_id = keccak256(
  "SSGKR_SOURCE_RUNTIME_V1" ||
  u16be(len(utf8(runtime_spec_name))) ||
  utf8(runtime_spec_name) ||
  u32be(runtime_spec_version) ||
  u32be(runtime_transaction_version) ||
  u8(runtime_state_version) ||
  runtime_code_hash
)
```

The vector uses `zkVerify Volta`, its exact genesis hash, `tzkv-runtime` spec
version `2000000`, transaction version `1`, state version `1`, and the pinned
runtime code hash. The derived values are data, not arbitrary labels.

## Receipt-root authorization

The signing preimage is:

```text
"SSGKR_RECEIPT_ROOT_QUORUM_V1" ||
u64be(signer_set_epoch) ||
source_network_id ||
source_genesis_hash ||
source_runtime_id ||
verification_context_hash ||
u32be(domain_id) ||
u64be(source_block_number) ||
source_block_hash ||
u64be(aggregation_id) ||
root ||
u32be(leaf_count) ||
u64be(authorization_nonce)
```

`signing_digest = keccak256(signing_preimage)`. The preimage is exactly 260
bytes. Signers sign that digest directly: no EIP-191 `personal_sign` prefix
and no EIP-712 wrapper. The Rust reference and an EVM implementation both
reject zero or invalid `r/s`, high-`s`, a recovery value other than 27 or 28,
failed recovery, and the zero address. Recovered identities are supplied in
strict ascending byte order to the semantic policy.

The receipt authority has an epoch independent of the primary-finality signer
epoch. Version 1 starts the receipt authority at epoch `1`. Configured signers
and recovered signers must each be strictly sorted; duplicates, nonmembers,
stale epochs, zero addresses, and counts below threshold fail before state
changes. Configured zero addresses are also forbidden. A valid
primary-finality-role signature is not a receipt-root authorization unless its
identity is independently configured in this receipt authority.

The cross-role fixture signs the existing settlement module's canonical
`PrimaryFinalityRecordV1::record_id()`. Its preimage begins with the distinct
`ssgkr/primary-finality-record/v1` domain and binds the full frozen route,
raw-statement commitment/preclaim, source, destination, action, checkpoint,
session, BVC, accepted root, primary state, PFR signer epoch, issuance height,
and supersession marker. It is not derived from the receipt digest.

The fixture recovers its expected test-only signer under that digest. Applying
the same signature to the receipt signing digest does not recover that signer
and fails receipt-authority membership.

## Registry and nonce rules

The logical coordinate is exactly
`(source_network_id, domain_id, aggregation_id)`. Its portable identifier is:

```text
keccak256(
  "SSGKR_RECEIPT_ROOT_COORDINATE_V1" ||
  source_network_id || u32be(domain_id) || u64be(aggregation_id)
)
```

Runtime, context, block number/hash, root, leaf count, epoch, genesis, and
authorization nonce remain signed metadata stored with the coordinate. A
fresh registry requires nonce `1`; each successful new coordinate requires the
exact next nonce. Reuse and skips fail. An exact authorization retry is
`AuthorizationReplay`; any changed signed metadata at an occupied coordinate
is `RootConflict`. Both leave the root, nonce, and accepted-transition count
unchanged. There is no successful overwrite or idempotent write path.

## Receipt and settlement rules

This safe profile supports only the observed native one-leaf receipt:
`leaf_count=1`, `leaf_index=0`, `merkle_path=[]`, and
`root=keccak256(statement)`. The vector carries the exact sealed statement
`0xb4b058ae...eb8492` and recomputes its published root. Wrong statement,
authenticated root, index, nonempty path, and leaf count all reject without a
registry or event-equivalent change. Multi-leaf semantics are not inferred
from the generic historical reference model. In particular, `leaf_count=2`,
index `0`, empty path fails. A future native multi-leaf profile requires a new
version and independently imported source semantics.

The delivery claim ID reuses the existing
`WrapSettlementClaimV1::claim_id()` semantics byte-for-byte and remains
distinct from the route-independent settlement key:

```text
claim_id = sha256(
  "ssgkr/wrap-settlement-claim/v1" ||
  route_id || primary_finality_record_id || canonical_raw192
)
```

The frozen raw192 has byte `11 = 0`, so
`CanonicalRawStatement::action_kind()` yields `Membership`. The JSON action
label must match that parser result; no parallel action decoder exists. The PFR
record ID, its separate test signature, claim ID, and settlement key are all
derived from this membership value.

After root authentication, claim ID and the route-independent settlement key
are checked together before either is inserted. Reuse of either key rejects
the whole transition; claim count, settlement count, and the event-equivalent
accepted-transition count remain unchanged.

The native N=1 publication commits `root=keccak256(statement_leaf)`, while the
earlier `ReferenceSettlementConsumer` defines its N=1 reference Merkle root as
the leaf itself. Those seams remain distinct. The host-only transition uses a
versioned adapter for the native receipt-policy result; it does not redefine
either formula or make the historical destination experiment activatable.

## Frozen vector

The vector includes canonical payload bytes, signing digest, source identities,
coordinate ID, signer order, two compact `r||s||v` receipt-digest signatures,
one separate PFR-record-digest signature, the complete existing settlement
claim fixture, replay keys, and expected errors. Its 33 negative rows use a
typed operation/field/value schema and are all executed by the Rust
interpreter. Each row freezes a canonical whole-state digest before and after;
that state commits the full registry records and sorted signers, exact consumed
claim/settlement identities, counters, and complete emitted-event transcript.
Case `id` values are labels only. Scalar authorization mutations use exact
subfield tags, and a test renames an ID while preserving identical execution.
Signatures were made from fixed public test scalars and verified both by Rust
`k256` recovery and Foundry `cast wallet verify --no-hash`; no keystore,
environment secret, wallet session, or real signer was used.

The vector derives `raw_accepted_root` from the canonical raw192 parser, checks
the JSON fixture label for exact equality, and uses only the derived value in
the PFR. A typed label-mutation row rejects with `AcceptedRootMismatch` without
changing registry, replay, or event state.

The Rust oracle performs direct-digest secp256k1 recovery for parity. A deployed
EVM still owns its `ecrecover` implementation and must match the frozen digest,
address, unique-signer/quorum, immutable registry, one-leaf attachment, claim,
and atomic replay results.
