//! wrap-statement-v1: the six-scalar application-statement layout and the
//! KoalaBear -> BN254 field bridge it is built on.
//!
//! This layer is deliberately independent of any concrete SNARK backend:
//! it defines WHAT the application statement asserts and serializes as the
//! zkVM public-values byte stream, not HOW it is proved. A stock Groth16 wrapper
//! may expose only its guest/program VK and public-values digest as proof public
//! inputs. Backends implement [`crate::WrapBackend`] against
//! this statement; the field bridge is the "base field conversion"
//! obligation the Refinement Scope Statement (design B.6) earmarks as a
//! separate verification item at v0.3.
//!
//! # Field bridge (frozen): 31-bit-stride digest packing
//!
//! A digest is 8 canonical KoalaBear residues (each `< p < 2^31`). One
//! digest packs into ONE BN254 scalar as
//!
//! ```text
//! packed = sum_{i<8} limb_i * 2^(31*i)      (limb_0 = digest word 0)
//! ```
//!
//! - Injective: base-2^31 positional encoding with every digit `< 2^31`.
//! - Always canonical: `packed < 2^248 < r_BN254 (~2^253.6)`. A 32-bit
//!   stride would reach `2^255 > r` and alias residues - REJECTED; the
//!   31-bit stride is the frozen choice.
//! - Unpacking is exact and total-checked: 31-bit digits are extracted,
//!   each must be a canonical residue (`< p`) and the remaining high
//!   bits must be zero, else the value is rejected (one value, one
//!   encoding - same rule as inner-proof-v1).
//!
//! An outer circuit binding inner digests MUST constrain each digit to
//! `< p` and recompose with the same strides; that in-circuit obligation
//! is part of the backend's soundness review (R4-adjacent item).
//!
//! # Statement layout (6 BN254 scalars, frozen order)
//!
//! ```text
//! fr[0] header word (little-endian byte layout, value < 2^128):
//!       bytes 0..2   wrap_statement_version u16 = 1
//!       bytes 2..4   protocol_version       u16
//!       bytes 4..6   circuit_version        u16
//!       bytes 6..8   leaf_encoding_version  u16
//!       bytes 8..10  leaf_max_fields        u16
//!       byte  10     layer_strategy_id      u8
//!       byte  11     op_kind_tag            u8
//!       bytes 12..16 depth                  u32
//! fr[1] full_circuit_commitment (packed digest)
//! fr[2] old_root                (packed digest)
//! fr[3] new_root                (packed digest)
//! fr[4] asset_id                (u64, direct)
//! fr[5] value_digest            (packed digest)
//! ```
//!
//! The verifying consumer never trusts fr[1]: it compares against the
//! registered/recomputed circuit commitment for the (version, config)
//! it accepts - the same registry-or-recompile discipline as the inner
//! boundary.

use ssgkr_compiler::PublicInputs;
use ssgkr_primitives::field::{BaseField, PrimeCharacteristicRing, PrimeField32};
use ssgkr_primitives::hash::{DIGEST_WIDTH, Digest};

use crate::encoding::CircuitIdentity;

/// wrap-statement layout version.
pub const WRAP_STATEMENT_VERSION: u16 = 1;

/// Number of BN254 scalars in one wrap statement.
pub const WRAP_STATEMENT_FRS: usize = 6;

/// The BN254 scalar-field modulus `r`, big-endian (the Groth16/PLONK
/// public-input field of the external verifier targets). Recorded here
/// for range documentation and tests; the packing never reaches it.
pub const BN254_R_BE: [u8; 32] = [
    0x30, 0x64, 0x4E, 0x72, 0xE1, 0x31, 0xA0, 0x29, 0xB8, 0x50, 0x45, 0xB6, 0x81, 0x81, 0x58, 0x5D,
    0x28, 0x33, 0xE8, 0x48, 0x79, 0xB9, 0x70, 0x91, 0x43, 0xE1, 0xF5, 0x93, 0xF0, 0x00, 0x00, 0x01,
];

/// One BN254 scalar as WIRE BYTES (little-endian, value `< r`). This is
/// a transport type, not arithmetic: backends convert it into their own
/// field representation; external submission formats serialize from it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bn254Fr(pub [u8; 32]);

impl Bn254Fr {
    /// Big-endian form (EVM/snarkjs-style hex ordering).
    pub fn to_be_bytes(self) -> [u8; 32] {
        let mut b = self.0;
        b.reverse();
        b
    }

    fn from_u128(x: u128) -> Self {
        let mut b = [0u8; 32];
        b[..16].copy_from_slice(&x.to_le_bytes());
        Bn254Fr(b)
    }

    fn from_u64(x: u64) -> Self {
        Self::from_u128(u128::from(x))
    }
}

/// Pack one digest into one BN254 scalar (31-bit stride; header comment).
pub fn pack_digest(d: &Digest<BaseField>) -> Bn254Fr {
    // 8 digits x 31 bits = 248 bits < 256: accumulate over the 32-byte
    // little-endian buffer with plain shifts (no bignum needed - each
    // digit spans at most 5 bytes).
    let mut out = [0u8; 32];
    for (i, x) in d.0.iter().enumerate() {
        let v = u64::from(x.as_canonical_u32());
        let bit = 31 * i;
        let (byte, shift) = (bit / 8, bit % 8);
        // v < 2^31, shift < 8 -> shifted < 2^39: five bytes cover it.
        let shifted = v << shift;
        for k in 0..5 {
            out[byte + k] |= (shifted >> (8 * k)) as u8;
        }
    }
    Bn254Fr(out)
}

/// Exact inverse of [`pack_digest`]. Rejects (returns `None`) any value
/// that is not the packing of 8 canonical residues: a non-canonical
/// digit (`>= p`) or any set bit above position 247.
pub fn unpack_digest(fr: &Bn254Fr) -> Option<Digest<BaseField>> {
    // Bits 248..256 must be zero.
    if fr.0[31] != 0 {
        return None;
    }
    let mut limbs = [BaseField::ZERO; DIGEST_WIDTH];
    for (i, l) in limbs.iter_mut().enumerate() {
        let bit = 31 * i;
        let (byte, shift) = (bit / 8, bit % 8);
        let mut window = 0u64;
        for k in 0..5 {
            window |= u64::from(fr.0[byte + k]) << (8 * k);
        }
        // The mask bounds the digit below 2^31, so the narrowing is exact.
        let digit = ((window >> shift) & 0x7FFF_FFFF) as u32;
        if digit >= BaseField::ORDER_U32 {
            return None;
        }
        *l = BaseField::from_u32(digit);
    }
    // Re-pack and compare: any stray bit between digit windows (there are
    // none by construction, but the check keeps the map exactly
    // bijective onto its image) rejects.
    let repacked = pack_digest(&Digest(limbs));
    if repacked != *fr {
        return None;
    }
    Some(Digest(limbs))
}

/// One six-scalar application statement, in frozen order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WrapStatementV1 {
    /// The six scalars, layout as in the module header.
    pub frs: [Bn254Fr; WRAP_STATEMENT_FRS],
}

/// Build the wrap statement for one inner statement + circuit identity.
pub fn wrap_statement_v1(identity: &CircuitIdentity, pi: &PublicInputs) -> WrapStatementV1 {
    let mut header = [0u8; 16];
    header[0..2].copy_from_slice(&WRAP_STATEMENT_VERSION.to_le_bytes());
    header[2..4].copy_from_slice(&crate::encoding::PROTOCOL_VERSION.to_le_bytes());
    header[4..6].copy_from_slice(&identity.circuit_version.to_le_bytes());
    header[6..8].copy_from_slice(&identity.leaf_encoding_version.to_le_bytes());
    header[8..10].copy_from_slice(&identity.leaf_max_fields.to_le_bytes());
    header[10] = identity.layer_strategy_id;
    header[11] = identity.op_kind_tag;
    header[12..16].copy_from_slice(&identity.depth.to_le_bytes());
    let header_word = u128::from_le_bytes(header);

    WrapStatementV1 {
        frs: [
            Bn254Fr::from_u128(header_word),
            pack_digest(&identity.full_circuit_commitment),
            pack_digest(&pi.old_root),
            pack_digest(&pi.new_root),
            Bn254Fr::from_u64(pi.asset_id.0),
            pack_digest(&pi.value_digest),
        ],
    }
}
