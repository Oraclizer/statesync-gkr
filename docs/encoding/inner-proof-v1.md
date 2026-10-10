# inner-proof-v1: canonical encoding (FROZEN)

- Status: **FROZEN** at the component external-proof boundary.
  Normative twin: `crates/wrap/src/encoding.rs` (layout + decoder),
  `crates/commitment/src/lib.rs` (circuit identity),
  `crates/wrap/src/statement.rs` (wrap statement + field bridge).
  Executable pins: `tests/encoding_v03.rs` + committed golden vectors
  (`tests/vectors/inner-proof-v1/`). Any byte-level change to this
  layout bumps `proof_encoding_version`; any semantic change bumps the
  matching axis below. This file supersedes `inner-proof-v1-draft.md`
  (v0.2); pre-freeze dev-era bytes were never wire-stable and are not a
  compatibility target.
- Scope: the CRYPTOGRAPHIC inner-proof layer only. Service APIs, OIP
  protobuf, OSS/CDK gRPC are separate layers with their own versioning;
  wrapped (outer SNARK) proofs carry `wrap-statement-v1` (section 8).
- Witness bytes are NEVER part of this encoding. The internal verifier
  consumes the witness through a separate typed request.

## 1. Version axes (never merged into one product version)

| Axis | Bumps when | Frozen value |
|---|---|---|
| `proof_encoding_version` | inner proof byte encoding changes | 1 |
| `protocol_version` | transcript/proof semantics change (observation order, degree bounds, claim carry, circuit-digest content) | 1 |
| `circuit_version` | compiler/circuit semantics change | 1 |
| `leaf_encoding_version` | `LeafState::encode` layout changes | 1 |

`protocol_version` 1 binds the transcript and public-input conventions plus
the full circuit commitment absorbed into the transcript (the v0.3
hardening). The version inside the
domain tag (`statesync-gkr/v0.1`) tracks this axis.

`config_id` (draft axis 4) is RESOLVED as a governance-layer concept,
not an envelope field: the envelope carries the explicit instance values
(depth, `leaf_max_fields`, strategy) and the full circuit commitment
binds them cryptographically; WHICH configs a verifier accepts is
verifier-side policy (a registry of allowed tuples), not proof bytes.

Later axes (out of inner-proof scope, listed to prevent collapse):
`wrapper_version` (= `wrap_statement_version`, section 8),
`context_version`, `asset_mapping_version`, `leaf_schema_version`,
`root_encoding_version`, `service_api_version`, `oip_schema_version`.

## 2. Byte layout (normative; all integers little-endian)

```text
Header (17 bytes)
   0..8    magic  b"SSGKRPRF"
   8..10   proof_encoding_version  u16 = 1
  10..12   protocol_version        u16 = 1
  12..13   proof_kind              u8  = 0 (inner GKR)
  13..17   total message length    u32 (must equal the buffer length)
Circuit identity (44 bytes)
  17..18   op_kind_tag             u8  (0 Membership / 1 NonMembership / 2 Update)
  18..22   tree depth              u32
  22..24   circuit_version         u16 = 1
  24..26   leaf_encoding_version   u16 = 1
  26..28   leaf_max_fields         u16
  28..29   layer_strategy_id       u8  = 0 (strategy A)
  29..61   full_circuit_commitment 8 x fe
Statement (frozen public-input field order, 77 bytes)
  61..93   old_root                8 x fe
  93..125  new_root                8 x fe
 125..126  op_kind_tag             u8 (MUST equal the identity tag)
 126..130  asset_id low limb       u32
 130..134  asset_id high limb      u32
 134..166  value_digest            8 x fe
Proof payload
 166..170  layer count             u32
 per layer, output layer first:
   round-poly count               u32
   per round poly, round order:
     coefficient count            u8 (MUST be 5 = degree bound 4 + 1)
     5 x ef                       ascending coefficient order
   eval_x                         ef
   eval_y                         ef
```

- `fe` = one base-field element (KoalaBear, p = 2^31 - 2^24 + 1):
  canonical residue as u32 LE; values >= p are REJECTED (one value, one
  encoding).
- `ef` = one degree-4 extension element: 4 x fe in basis order.
- Round polynomials carry EXACTLY 5 coefficients under protocol_version
  1, trailing zeros preserved (the prover pipeline always emits
  degree-bound-plus-one coefficients, pinned by tests); encoders MUST
  NOT strip them, decoders MUST NOT pad.
- A batch proof kind is deliberately ABSENT (ADR-0001: a v0.2+ batch is
  a sequence of ordinary inner proofs, bit-identical to the single
  path). An aggregate kind may only be added by a future batch-protocol
  ADR with its own soundness model.
- Proof kinds for wrapped proofs live in the wrap layer, not here.

## 3. Cryptographic suite identity (recorded)

- base field: KoalaBear, p = 2^31 - 2^24 + 1
- challenge field: degree-4 binomial extension over KoalaBear
- hash/permutation: Poseidon2-KoalaBear, width 16, external 4+4 /
  internal 20 rounds, plonky3 `KOALABEAR_RC16_*` constants
- transcript: duplex sponge (rate 8) over the same permutation; domain
  separator = `statesync-gkr/v0.1`

The suite is bound by `protocol_version` (fail-closed version check),
not by per-message suite bytes.

## 4. Circuit identity + full circuit commitment

The identity section carries the instance values explicitly AND the
**full circuit commitment**: a Poseidon2-duplex digest (domain
`ssgkr/circuit-commitment/v1`) over op kind, depth, `leaf_max_fields`,
strategy identity, input width, layer count, and EVERY layer's widths,
gates `(kind, out, in1, in2, coeff)` and constants `(wire, value)` in
canonical (compiler emission) order. Definition + rationale:
`crates/commitment/src/lib.rs`.

This closes the v0.1 gap where the shape-level digest could not
distinguish two circuits of identical shape but different wiring - a
non-issue for same-binary canonical recompilation, unacceptable at the
external boundary where circuit identity is part of soundness. The same
commitment is absorbed into the versioned transcript by prover and verifier
(after the shape values, which are kept as a hash-independent direct
binding), so every proof is cryptographically bound to the exact gate
list.

**Verifiers never trust the commitment (or any identity field) from the
wire**: the verifying side recomputes the commitment from its own
canonical recompilation for the (version, config) it accepts and
rejects any mismatch - see `StateSyncProver::verify_encoded_sync_op`.

## 5. Statement / public inputs

Field order = the frozen public-input observation order: `old_root`, `new_root`,
`op_kind_tag`, `asset_id`, `value_digest`.

- digests: 8 base-field elements, 4 bytes each
- `asset_id`: u64 as two u32 limbs (low, high) - the injective split
  the transcript already uses
- the statement's `op_kind_tag` MUST equal the identity section's
  (the order is frozen and self-contained; the identity section stands
  alone; the decoder rejects disagreement)

## 6. Decoder discipline + error taxonomy (frozen)

Decoding is strict and fail-closed:

- unknown version / proof kind / strategy / op tag: REJECTED, never
  inferred or defaulted
- every count validated against the remaining byte budget BEFORE any
  allocation
- non-canonical field elements rejected with the exact byte offset
- declared total length must equal the buffer length; trailing bytes
  rejected
- decode-then-re-encode is byte-identical (canonical fixed point)

Error codes (`ssgkr_wrap::encoding::DecodeError`, each pinned reachable
by `tests/encoding_v03.rs::decode_reject_taxonomy_is_complete`):
`HeaderTooShort`, `BadMagic`, `UnsupportedProofEncodingVersion`,
`UnsupportedProtocolVersion`, `UnsupportedProofKind`,
`DeclaredLengthMismatch`, `UnsupportedCircuitVersion`,
`UnsupportedLeafEncodingVersion`, `UnsupportedLayerStrategy`,
`UnknownOpKindTag`, `OpKindMismatch`, `NonCanonicalFieldElement`,
`BadRoundPolyArity`, `OversizedCount`, `Truncated`, `TrailingBytes`.

What the decoder does NOT check, and who does: proof shape against the
actual circuit (layer/round counts vs the compiled circuit) and
commitment truth belong to the VERIFYING side against its own canonical
recompilation. A decoder alone cannot know the circuit; trusting counts
from the wire would invert the boundary.

## 7. Responsibility split at the component boundary

1. **Decoder** (`ssgkr-wrap::encoding`): byte shape, versions,
   canonicality. Stateless; no circuit knowledge.
2. **Verifying side** (facade `verify_encoded_sync_op`): decoded
   identity == the local config's identity, INCLUDING the locally
   recomputed full circuit commitment; then the inner verifier.
3. **Inner verifier** (native acceptance semantics unchanged): the cryptography, with
   witness access via the typed request.
4. **Wrap backend** (`ssgkr-wrap::WrapBackend`): proves exactly the
   facade's `wrap_relation` (decode + identity + inner-verifier
   acceptance -> wrap statement). It may reject; it may never widen
   what the inner verifier accepts. The facade checks the relation
   natively BEFORE invoking a backend and cross-checks the backend's
   echoed statement.

## 8. wrap-statement-v1 + field bridge (outer public inputs)

Normative source: `crates/wrap/src/statement.rs`. Six BN254 scalars:

```text
fr[0] header word: wrap_statement_version(=1) | protocol_version |
      circuit_version | leaf_encoding_version | leaf_max_fields |
      layer_strategy_id | op_kind_tag | depth   (LE byte layout, < 2^128)
fr[1] full_circuit_commitment  (packed digest)
fr[2] old_root                 (packed digest)
fr[3] new_root                 (packed digest)
fr[4] asset_id                 (u64, direct)
fr[5] value_digest             (packed digest)
```

Digest packing (the KoalaBear -> BN254 bridge, design §B.6's separate
verification item): **31-bit stride**, `packed = sum limb_i * 2^(31 i)`
over the 8 canonical residues. Injective; always `< 2^248 < r_BN254`.
A 32-bit stride would reach 2^255 > r and alias residues - rejected.
Unpacking is exact and total-checked (each digit `< p`, no bits above
position 247). An outer circuit binding inner digests MUST enforce the
same digit ranges and recomposition in-circuit as part of that backend's
soundness review.

Scalar wire form: 32 bytes little-endian (matches zkVerify's BN254
Groth16 public-input convention); `to_be_bytes()` for EVM/snarkjs-style
consumers. The consumer never trusts fr[1]: it compares against the
commitment it registered/recomputed for the versions in fr[0].

## 9. Canonical proof bytes - determinism scope

Byte-identity applies to the deterministic inner GKR path: same input +
same `protocol_version` => same transcript observations and same
canonical bytes across scalar/AVX2/AVX-512 builds and any worker count
(ADR-0001 determinism gate; cross-build digest CI leg; AVX-512 leg on
the controlled server). The canonical proof DIGEST
(`cargo run --release --bin proof_digest`) remains the cheap equality
anchor; the encoder is the wire format; golden vectors tie the two.

## 10. Golden vectors (committed)

`tests/vectors/inner-proof-v1/{membership,nonmembership,update}-d24.bin`
- one honest proof per op kind at the default config (d = 24,
`leaf_max_fields` = 31, strategy A), canonical bytes as committed
artifacts. Guarded by `golden_vectors_are_stable_and_verify` (byte
equality against a fresh prove+encode, then full verification) and the
tamper/reject batteries (per-byte identity/statement flips, payload
tamper, cross-kind, full decoder taxonomy). Regeneration is manual and
version-bump-only (`generate_golden_vectors`, `#[ignore]`).

Batch-size vectors are deliberately absent (ADR-0001: batched proofs
ARE these bytes). Scalar-vs-AVX identity is carried by the CI digest
job; compatibility vectors start accumulating at the first version
bump (there is no prior wire-stable version to be compatible with).

## 11. Resolution of the draft's open items

1. magic + envelope framing: frozen as section 2 (`b"SSGKRPRF"`,
   total-length header, strict framing).
2. full circuit commitment algorithm + domain tag: frozen
   (`ssgkr/circuit-commitment/v1`, section 4); registry-or-recompile
   discipline stated in sections 4/7.
3. base-field canonical byte form vs BN254 packing: fe = canonical u32
   LE on the wire; the BN254 packing is the 31-bit stride of section 8
   (the two coexist; the bridge is bijective on canonical digests).
4. `config_id` registry shape: resolved as verifier-side governance
   (section 1), not an envelope field.
5. error-code taxonomy: frozen (section 6).
6. golden-vector corpus + CI wiring: committed vectors + test battery
   (section 10); CI runs them as part of the release-mode suite.
