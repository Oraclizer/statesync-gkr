# RISC Zero Route B manifest version 1

This document fixes the canonical static identity for the native RISC Zero
v3.0.4 path through the zkVerify RISC0 pallet. It is a separate codec from the
stock Groth16 two-public-input `RouteManifestV1`. Neither that type nor its
`ssgkr/route-manifest/v1` domain is reinterpreted.

## Identity

The route identifier is:

```text
SHA-256(
  UTF8("ssgkr/risc0-route-b-manifest/v1") ||
  canonical_manifest_bytes
)
```

JSON is only an input representation. Key order and insignificant whitespace
do not affect identity. The parser rejects missing, duplicate, and unknown
properties at every level. Fixed-width bytes and addresses use an exact
lowercase `0x` representation. Integers must be in-range JSON integers;
numeric strings, floats, booleans in numeric fields, and negative values are
invalid.

The machine-readable input contract is
[`risc0-route-b-manifest-v1.schema.json`](risc0-route-b-manifest-v1.schema.json).
The vector includes dynamic raw192 and settlement-key samples only to produce
the statement and key transcripts. Those samples are not manifest fields.

## Scalar encodings

| Value | Canonical binary |
|---|---|
| `u8`, enum, boolean | one byte; enum tag `1`; boolean `0` or `1` |
| `u16`, `u32`, `u64` | unsigned little-endian |
| string | `u16_le(UTF-8 byte length) || UTF-8 bytes` |
| address / source commit | raw 20 bytes decoded from exact lowercase hex |
| hash / image ID | raw 32 bytes decoded from exact lowercase hex |

Only the enum spellings present in the schema are version-one tags. Adding an
enum value or changing field order requires a new codec version.

## Canonical field order

The encoder appends every leaf in the following order:

1. `manifest_version`, `route_family`, `proof_system`.
2. `source_network`: network name, genesis hash, runtime spec name, spec
   version, transaction version, state version, source tag, source commit.
3. `verifier`: RISC Zero release, source commit, guest toolchain, guest ELF
   SHA-256, verification context, verifier-version preimage and SHA-256,
   image ID, image-ID encoding, zkVerify VK semantics.
4. `statement`: application-statement version, raw statement encoding and
   byte length, public-values semantics, circuit-commitment binding, native
   statement formula.
5. aggregation domain ID.
6. `destination`: network name, chain ID, gateway proxy and code hash,
   gateway implementation and code hash.
7. `trust`: role model, observed publisher, its capability, upgrader and
   default-admin capabilities, the two principal-pinned booleans, upgradeable
   proxy flag, proxy/implementation TCB flag.
8. `transport`: authentication, destination GRANDPA-verification flag, source
   finality policy.
9. `conflict`: same-coordinate overwrite flag, conflict-rejection policy,
   enforcement owner.
10. `settlement_key`: domain, hash, preimage order, transition-ID width,
    destination-chain encoding, consumer width, action encoding, route-ID
    inclusion flag.
11. `receipt_tuple`: domain, aggregation, leaf-count and leaf-index encodings,
    Merkle-node width, canonical-relation requirement, live-enforcement state,
    enforcement owner.

The checked-in input is
`tests/vectors/risc0-route-b-manifest-v1.json`. The Rust example and the
standard-library Python reference must emit identical complete transcripts.

## Native statement

For exact 192-byte public values:

```text
context_hash = Keccak-256(UTF8("risc0"))
version_hash = SHA-256(UTF8("risc0:v3.0"))
pubs_hash    = Keccak-256(raw192)

statement = Keccak-256(
  context_hash || image_id_bytes32 || version_hash || pubs_hash
)
```

The image ID is the zkVerify `Vk` bytes32 formed by the RISC Zero digest's
eight little-endian `u32` words in word order. No aggregation ID, receipt root,
transaction, block coordinate, proof bytes, or raw192 value is part of static
route identity.

## Settlement key and enforcement boundary

The manifest pins the existing route-independent contract:

```text
SHA-256(
  UTF8("ssgkr/settlement-key/v1") ||
  primary_transition_id_bytes32 ||
  intended_destination_chain_id_le64 ||
  intended_destination_consumer_bytes32 ||
  action_kind_u8
)
```

`route_id` is deliberately absent. Route rotation changes delivery claim
identity but not economic exactly-once identity.

The manifest records an operator-authenticated transport, no destination-side
Volta GRANDPA verification, upgradeable proxy and implementation TCB, observed
publisher capability, unpinned upgrader/admin principals, possible
same-coordinate overwrite, and absent conflict/tuple enforcement. These are
content-addressed policy and trust-ceiling facts, not enforcement claims.
Live finality authentication, current code and role checks, conflict
rejection, replay protection, and canonical receipt-tuple validation belong
to the destination receiver.
