//! inner-proof-v1: the canonical byte encoding of one inner GKR proof
//! with its statement and circuit identity - the FROZEN external proof
//! boundary (docs/encoding/inner-proof-v1.md is the prose twin of this
//! module; the byte layout below is normative and pinned by golden
//! vectors).
//!
//! Scope: the cryptographic inner-proof layer only. Service APIs, OIP
//! schemas and wrapped (outer SNARK) statements are separate layers;
//! witness bytes are NEVER part of this encoding (the internal verifier
//! consumes the witness through a separate typed request, seal S-4).
//!
//! # Byte layout (all integers little-endian; offsets from message start)
//!
//! ```text
//! Header (17 bytes)
//!    0..8    magic  b"SSGKRPRF"
//!    8..10   proof_encoding_version  u16 = 1
//!   10..12   protocol_version        u16 = 1
//!   12..13   proof_kind              u8  = 0 (inner GKR)
//!   13..17   total message length    u32 (must equal the buffer length)
//! Circuit identity (44 bytes)
//!   17..18   op_kind_tag             u8  (0/1/2, = PublicInputs::kind_tag)
//!   18..22   tree depth              u32
//!   22..24   circuit_version         u16 = 1
//!   24..26   leaf_encoding_version   u16 = 1
//!   26..28   leaf_max_fields         u16
//!   28..29   layer_strategy_id       u8  = 0 (strategy A)
//!   29..61   full_circuit_commitment 8 x fe
//! Statement (frozen S-6 field order, 77 bytes)
//!   61..93   old_root                8 x fe
//!   93..125  new_root                8 x fe
//!  125..126  op_kind_tag             u8 (MUST equal the identity tag)
//!  126..130  asset_id low limb       u32
//!  130..134  asset_id high limb      u32
//!  134..166  value_digest            8 x fe
//! Proof payload
//!  166..170  layer count             u32
//!  per layer, output layer first:
//!    round-poly count               u32
//!    per round poly, round order:
//!      coefficient count            u8 (MUST be 5 = degree bound 4 + 1)
//!      5 x ef                       ascending coefficient order
//!    eval_x                         ef
//!    eval_y                         ef
//! ```
//!
//! - `fe` = one base-field element: canonical residue as u32 LE; values
//!   >= p are rejected (one value, one encoding).
//! - `ef` = one degree-4 extension element: 4 x fe in basis order.
//! - Round polynomials carry EXACTLY `LAYER_ROUND_DEGREE + 1 = 5`
//!   coefficients, trailing zeros preserved (the prover pipeline always
//!   emits them; encoders must not strip, decoders must not pad - a
//!   stripped encoding of the same polynomial would be a second byte
//!   form of one value).
//! - The op kind appears in BOTH the circuit identity and the statement
//!   (S-6's field order is frozen and self-contained; the identity
//!   section must also stand alone). The decoder rejects any mismatch.
//! - Decoders validate every count against the remaining byte budget
//!   BEFORE allocating, reject unknown versions/kinds/strategies (fail
//!   closed - never inferred, never defaulted), reject non-canonical
//!   field elements, and reject trailing bytes. Decode-then-re-encode
//!   is byte-identical (round-trip pinned by tests and golden vectors).
//!
//! What the decoder does NOT check (and who does): proof shape against
//! the actual circuit (layer/round counts vs the compiled circuit) and
//! commitment truth are checked by the verifying side against its OWN
//! canonical recompilation - see the facade's encoded-proof entries.
//! A decoder alone cannot know the circuit; trusting counts from the
//! wire would invert the boundary.

use ssgkr_compiler::{AssetId, PublicInputs};
use ssgkr_primitives::field::{
    BaseField, CHALLENGE_EXT_DEGREE, ChallengeField, ExtensionField, PrimeCharacteristicRing,
    PrimeField32,
};
use ssgkr_primitives::hash::{DIGEST_WIDTH, Digest};
use ssgkr_protocol::reduce::LAYER_ROUND_DEGREE;
use ssgkr_protocol::{GkrProof, LayerProof};
use ssgkr_sumcheck::{RoundPoly, SumcheckProof};

/// Envelope magic bytes (frozen).
pub const MAGIC: [u8; 8] = *b"SSGKRPRF";
/// Inner proof byte-encoding version (bumps when THIS layout changes).
pub const PROOF_ENCODING_VERSION: u16 = 1;
/// Transcript/proof semantics version (S-5 order, degree bounds, claim
/// carry, circuit-digest content). Tracks the version inside the S-5
/// domain tag.
pub const PROTOCOL_VERSION: u16 = 1;
/// Compiler/circuit semantics version.
pub const CIRCUIT_VERSION: u16 = 1;
/// Leaf-state encoding version (`LeafState::encode` layout).
pub const LEAF_ENCODING_VERSION: u16 = 1;
/// Proof kind: inner GKR proof. Wrapped kinds live in the wrap-statement
/// layer; an aggregate kind is deliberately ABSENT (ADR-0001: a batch is
/// a sequence of ordinary inner proofs).
pub const PROOF_KIND_INNER_GKR: u8 = 0;
/// Layer strategy identity for strategy A (the only compilable strategy;
/// the R1 domain iff rejects B/C).
pub const LAYER_STRATEGY_ID_A: u8 = 0;
/// Coefficients per round polynomial (degree bound 4 + 1; frozen with
/// protocol_version 1).
pub const ROUND_POLY_COEFFS: usize = LAYER_ROUND_DEGREE + 1;

/// Bytes of one base-field element on the wire.
const FE_BYTES: usize = 4;
/// Bytes of one extension element on the wire.
const EF_BYTES: usize = FE_BYTES * CHALLENGE_EXT_DEGREE;
/// Fixed byte size of one encoded round polynomial.
const ROUND_POLY_BYTES: usize = 1 + ROUND_POLY_COEFFS * EF_BYTES;
/// Fixed per-layer overhead (round-poly count + eval_x + eval_y).
const LAYER_FIXED_BYTES: usize = 4 + 2 * EF_BYTES;
/// Header size.
const HEADER_BYTES: usize = 17;

/// The circuit identity carried by (and validated against) the envelope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircuitIdentity {
    /// Operation kind tag (0 = Membership, 1 = NonMembership, 2 = Update).
    pub op_kind_tag: u8,
    /// Tree depth (instance genesis parameter).
    pub depth: u32,
    /// Compiler/circuit semantics version.
    pub circuit_version: u16,
    /// Leaf-state encoding version.
    pub leaf_encoding_version: u16,
    /// Maximum leaf encoding length (instance genesis parameter).
    pub leaf_max_fields: u16,
    /// Layer strategy identity.
    pub layer_strategy_id: u8,
    /// Full circuit commitment (crate::commitment). The verifying side
    /// never trusts this value - it recomputes and compares.
    pub full_circuit_commitment: Digest<BaseField>,
}

/// One decoded inner-proof envelope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InnerProofEnvelope {
    /// Circuit identity section.
    pub identity: CircuitIdentity,
    /// Statement section (frozen S-6 field order).
    pub public_inputs: PublicInputs,
    /// Proof payload.
    pub proof: GkrProof,
}

/// Encoder rejections (structural errors in OUR data - e.g. a foreign
/// proof shape the frozen layout cannot carry canonically).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EncodeError {
    /// A round polynomial does not carry exactly
    /// [`ROUND_POLY_COEFFS`] coefficients.
    BadRoundPolyArity {
        /// Layer index (0 = output layer).
        layer: usize,
        /// Round index within the layer.
        round: usize,
        /// Coefficients found.
        got: usize,
    },
    /// A count does not fit its wire width.
    CountOverflow,
    /// The total message would exceed `u32::MAX` bytes.
    MessageTooLong,
}

/// Decoder rejections - the frozen error taxonomy of inner-proof-v1
/// (every reject path is a distinct, testable code; fail closed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecodeError {
    /// Buffer ends before the fixed header completes.
    HeaderTooShort {
        /// Bytes present.
        have: usize,
    },
    /// Magic bytes mismatch.
    BadMagic,
    /// Unknown `proof_encoding_version` (never inferred).
    UnsupportedProofEncodingVersion(u16),
    /// Unknown `protocol_version`.
    UnsupportedProtocolVersion(u16),
    /// Unknown proof kind.
    UnsupportedProofKind(u8),
    /// Declared total length differs from the actual buffer length.
    DeclaredLengthMismatch {
        /// Length declared in the header.
        declared: u32,
        /// Actual buffer length.
        actual: usize,
    },
    /// Unknown `circuit_version`.
    UnsupportedCircuitVersion(u16),
    /// Unknown `leaf_encoding_version`.
    UnsupportedLeafEncodingVersion(u16),
    /// Unknown layer strategy id.
    UnsupportedLayerStrategy(u8),
    /// Op kind tag outside the frozen 0/1/2 range.
    UnknownOpKindTag(u8),
    /// Identity and statement op kind tags disagree.
    OpKindMismatch {
        /// Tag in the circuit identity section.
        identity: u8,
        /// Tag in the statement section.
        statement: u8,
    },
    /// A field element is not a canonical residue (value >= p).
    NonCanonicalFieldElement {
        /// Byte offset of the offending element.
        offset: usize,
    },
    /// A round polynomial does not declare exactly
    /// [`ROUND_POLY_COEFFS`] coefficients.
    BadRoundPolyArity {
        /// Layer index.
        layer: u32,
        /// Round index.
        round: u32,
        /// Declared coefficient count.
        got: u8,
    },
    /// A declared count exceeds the remaining byte budget (checked
    /// BEFORE any allocation).
    OversizedCount {
        /// Byte offset of the count field.
        offset: usize,
    },
    /// Buffer ends inside a field the layout requires.
    Truncated {
        /// Byte offset where more bytes were required.
        offset: usize,
    },
    /// Bytes remain after the last field of the layout.
    TrailingBytes {
        /// Number of extra bytes.
        extra: usize,
    },
}

// ---------------------------------------------------------------------
// Encoding
// ---------------------------------------------------------------------

fn put_fe(out: &mut Vec<u8>, x: BaseField) {
    out.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
}

fn put_ef<EF: ExtensionField<BaseField>>(out: &mut Vec<u8>, x: &EF) {
    for &limb in x.as_basis_coefficients_slice() {
        put_fe(out, limb);
    }
}

fn put_digest(out: &mut Vec<u8>, d: &Digest<BaseField>) {
    for &x in &d.0 {
        put_fe(out, x);
    }
}

/// Encode one envelope into its canonical bytes.
pub fn encode_inner_proof(env: &InnerProofEnvelope) -> Result<Vec<u8>, EncodeError> {
    // Validate the proof shape against the frozen layout FIRST (canonical
    // arity; also guards the u32 count fields).
    for (li, lp) in env.proof.layer_proofs.iter().enumerate() {
        if u32::try_from(lp.sumcheck.round_polys.len()).is_err() {
            return Err(EncodeError::CountOverflow);
        }
        for (ri, rp) in lp.sumcheck.round_polys.iter().enumerate() {
            if rp.coeffs().len() != ROUND_POLY_COEFFS {
                return Err(EncodeError::BadRoundPolyArity {
                    layer: li,
                    round: ri,
                    got: rp.coeffs().len(),
                });
            }
        }
    }
    let layer_count =
        u32::try_from(env.proof.layer_proofs.len()).map_err(|_| EncodeError::CountOverflow)?;

    let mut out = Vec::new();
    // Header (total length back-patched below).
    out.extend_from_slice(&MAGIC);
    out.extend_from_slice(&PROOF_ENCODING_VERSION.to_le_bytes());
    out.extend_from_slice(&PROTOCOL_VERSION.to_le_bytes());
    out.push(PROOF_KIND_INNER_GKR);
    out.extend_from_slice(&0u32.to_le_bytes());

    // Circuit identity.
    let id = &env.identity;
    out.push(id.op_kind_tag);
    out.extend_from_slice(&id.depth.to_le_bytes());
    out.extend_from_slice(&id.circuit_version.to_le_bytes());
    out.extend_from_slice(&id.leaf_encoding_version.to_le_bytes());
    out.extend_from_slice(&id.leaf_max_fields.to_le_bytes());
    out.push(id.layer_strategy_id);
    put_digest(&mut out, &id.full_circuit_commitment);

    // Statement (frozen S-6 field order).
    let pi = &env.public_inputs;
    put_digest(&mut out, &pi.old_root);
    put_digest(&mut out, &pi.new_root);
    out.push(pi.op_kind_tag);
    out.extend_from_slice(&((pi.asset_id.0 & 0xFFFF_FFFF) as u32).to_le_bytes());
    out.extend_from_slice(&((pi.asset_id.0 >> 32) as u32).to_le_bytes());
    put_digest(&mut out, &pi.value_digest);

    // Proof payload.
    out.extend_from_slice(&layer_count.to_le_bytes());
    for lp in &env.proof.layer_proofs {
        let rp_count = lp.sumcheck.round_polys.len() as u32;
        out.extend_from_slice(&rp_count.to_le_bytes());
        for rp in &lp.sumcheck.round_polys {
            out.push(ROUND_POLY_COEFFS as u8);
            for c in rp.coeffs() {
                put_ef(&mut out, c);
            }
        }
        put_ef(&mut out, &lp.eval_x);
        put_ef(&mut out, &lp.eval_y);
    }

    // Back-patch the total length.
    let total = u32::try_from(out.len()).map_err(|_| EncodeError::MessageTooLong)?;
    out[13..17].copy_from_slice(&total.to_le_bytes());
    Ok(out)
}

// ---------------------------------------------------------------------
// Decoding
// ---------------------------------------------------------------------

/// Strict cursor over the message: every read is bounds-checked and
/// reports the exact offset on failure.
struct Rd<'a> {
    b: &'a [u8],
    off: usize,
}

impl<'a> Rd<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], DecodeError> {
        if self.b.len() - self.off < n {
            return Err(DecodeError::Truncated { offset: self.off });
        }
        let s = &self.b[self.off..self.off + n];
        self.off += n;
        Ok(s)
    }

    fn u8(&mut self) -> Result<u8, DecodeError> {
        Ok(self.take(1)?[0])
    }

    fn u16(&mut self) -> Result<u16, DecodeError> {
        let s = self.take(2)?;
        Ok(u16::from_le_bytes([s[0], s[1]]))
    }

    fn u32(&mut self) -> Result<u32, DecodeError> {
        let s = self.take(4)?;
        Ok(u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
    }

    fn fe(&mut self) -> Result<BaseField, DecodeError> {
        let at = self.off;
        let v = self.u32()?;
        if v >= BaseField::ORDER_U32 {
            return Err(DecodeError::NonCanonicalFieldElement { offset: at });
        }
        Ok(BaseField::from_u32(v))
    }

    fn ef(&mut self) -> Result<ChallengeField, DecodeError> {
        let mut limbs = [BaseField::ZERO; CHALLENGE_EXT_DEGREE];
        for l in &mut limbs {
            *l = self.fe()?;
        }
        Ok(ext_from_limbs(limbs))
    }

    fn digest(&mut self) -> Result<Digest<BaseField>, DecodeError> {
        let mut d = [BaseField::ZERO; DIGEST_WIDTH];
        for x in &mut d {
            *x = self.fe()?;
        }
        Ok(Digest(d))
    }

    fn remaining(&self) -> usize {
        self.b.len() - self.off
    }
}

/// Rebuild an extension element from its basis limbs (the inverse of the
/// sanctioned trait accessor used by `put_ef`; the fixed-size array makes
/// the arity total, with no fallible path).
fn ext_from_limbs<EF: ExtensionField<BaseField>>(limbs: [BaseField; CHALLENGE_EXT_DEGREE]) -> EF {
    EF::from_basis_coefficients_fn(|i| limbs[i])
}

/// Decode canonical bytes into an envelope (strict; fail closed).
pub fn decode_inner_proof(bytes: &[u8]) -> Result<InnerProofEnvelope, DecodeError> {
    if bytes.len() < HEADER_BYTES {
        return Err(DecodeError::HeaderTooShort { have: bytes.len() });
    }
    let mut rd = Rd { b: bytes, off: 0 };

    // Header.
    if rd.take(8)? != MAGIC {
        return Err(DecodeError::BadMagic);
    }
    let enc_v = rd.u16()?;
    if enc_v != PROOF_ENCODING_VERSION {
        return Err(DecodeError::UnsupportedProofEncodingVersion(enc_v));
    }
    let proto_v = rd.u16()?;
    if proto_v != PROTOCOL_VERSION {
        return Err(DecodeError::UnsupportedProtocolVersion(proto_v));
    }
    let kind = rd.u8()?;
    if kind != PROOF_KIND_INNER_GKR {
        return Err(DecodeError::UnsupportedProofKind(kind));
    }
    let declared = rd.u32()?;
    if declared as usize != bytes.len() {
        return Err(DecodeError::DeclaredLengthMismatch {
            declared,
            actual: bytes.len(),
        });
    }

    // Circuit identity.
    let id_kind_tag = rd.u8()?;
    if id_kind_tag > 2 {
        return Err(DecodeError::UnknownOpKindTag(id_kind_tag));
    }
    let depth = rd.u32()?;
    let circuit_v = rd.u16()?;
    if circuit_v != CIRCUIT_VERSION {
        return Err(DecodeError::UnsupportedCircuitVersion(circuit_v));
    }
    let leaf_v = rd.u16()?;
    if leaf_v != LEAF_ENCODING_VERSION {
        return Err(DecodeError::UnsupportedLeafEncodingVersion(leaf_v));
    }
    let leaf_max_fields = rd.u16()?;
    let strategy_id = rd.u8()?;
    if strategy_id != LAYER_STRATEGY_ID_A {
        return Err(DecodeError::UnsupportedLayerStrategy(strategy_id));
    }
    let commitment = rd.digest()?;

    // Statement (frozen S-6 field order).
    let old_root = rd.digest()?;
    let new_root = rd.digest()?;
    let st_kind_tag = rd.u8()?;
    if st_kind_tag > 2 {
        return Err(DecodeError::UnknownOpKindTag(st_kind_tag));
    }
    if st_kind_tag != id_kind_tag {
        return Err(DecodeError::OpKindMismatch {
            identity: id_kind_tag,
            statement: st_kind_tag,
        });
    }
    let asset_lo = rd.u32()?;
    let asset_hi = rd.u32()?;
    let value_digest = rd.digest()?;

    // Proof payload. Counts are budget-checked BEFORE allocation.
    let layer_count_at = rd.off;
    let layer_count = rd.u32()? as usize;
    if layer_count.saturating_mul(LAYER_FIXED_BYTES) > rd.remaining() {
        return Err(DecodeError::OversizedCount {
            offset: layer_count_at,
        });
    }
    let mut layer_proofs = Vec::with_capacity(layer_count);
    for li in 0..layer_count {
        let rp_count_at = rd.off;
        let rp_count = rd.u32()? as usize;
        if rp_count.saturating_mul(ROUND_POLY_BYTES) + 2 * EF_BYTES > rd.remaining() {
            return Err(DecodeError::OversizedCount {
                offset: rp_count_at,
            });
        }
        let mut round_polys = Vec::with_capacity(rp_count);
        for ri in 0..rp_count {
            let arity = rd.u8()?;
            if usize::from(arity) != ROUND_POLY_COEFFS {
                return Err(DecodeError::BadRoundPolyArity {
                    layer: li as u32,
                    round: ri as u32,
                    got: arity,
                });
            }
            let mut coeffs = Vec::with_capacity(ROUND_POLY_COEFFS);
            for _ in 0..ROUND_POLY_COEFFS {
                coeffs.push(rd.ef()?);
            }
            round_polys.push(RoundPoly::from_coeffs(coeffs));
        }
        let eval_x = rd.ef()?;
        let eval_y = rd.ef()?;
        layer_proofs.push(LayerProof {
            sumcheck: SumcheckProof { round_polys },
            eval_x,
            eval_y,
        });
    }

    if rd.remaining() != 0 {
        return Err(DecodeError::TrailingBytes {
            extra: rd.remaining(),
        });
    }

    Ok(InnerProofEnvelope {
        identity: CircuitIdentity {
            op_kind_tag: id_kind_tag,
            depth,
            circuit_version: circuit_v,
            leaf_encoding_version: leaf_v,
            leaf_max_fields,
            layer_strategy_id: strategy_id,
            full_circuit_commitment: commitment,
        },
        public_inputs: PublicInputs {
            old_root,
            new_root,
            op_kind_tag: st_kind_tag,
            asset_id: AssetId((u64::from(asset_hi) << 32) | u64::from(asset_lo)),
            value_digest,
        },
        proof: GkrProof { layer_proofs },
    })
}
