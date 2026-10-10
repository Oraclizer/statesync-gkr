//! Full circuit commitment - the frozen circuit-identity binding of
//! inner-proof-v1 (v0.3 hardening; design S-5 deadline note).
//!
//! v0.1 committed the circuit SHAPE only (op kind, depth, widths,
//! per-layer gate/const counts): sufficient for same-binary canonical
//! recompilation, but two circuits with identical shape and different
//! gate wiring/coefficients would collide - unacceptable once proofs
//! cross the external boundary, where circuit identity is part of
//! soundness. This module commits to EVERY gate and constant.
//!
//! Definition (frozen with inner-proof-v1):
//!
//! ```text
//! commitment = squeeze_digest( duplex_sponge(
//!     domain = "ssgkr/circuit-commitment/v1",
//!     op_kind_tag, depth, leaf_max_fields,
//!     strategy_id, strategy_arg,
//!     input_width_bits, layer_count,
//!     for each layer (output layer first):
//!         width_bits, gate_count,
//!         for each gate (compile order):  kind_tag, out, in1, in2, coeff,
//!         const_count,
//!         for each const (compile order): wire, value,
//! ))
//! ```
//!
//! - The sponge is the same Poseidon2-KoalaBear duplex the Fiat-Shamir
//!   transcript uses (capacity 8 -> ~124-bit collision resistance,
//!   matching [`Digest`]'s width); the digest is the base-field limbs of
//!   two squeezed extension challenges.
//! - Every scalar is absorbed as ONE canonical field element. All counts
//!   and indices are structurally far below the field order; this is
//!   asserted, never wrapped (a wrap would silently alias two preimages).
//! - Gate/const order is the compiler's deterministic emission order
//!   (pinned deterministic by the v0.2 adversarial audit), so equal
//!   circuits give equal commitments and any reordering is a different
//!   commitment on purpose: the commitment identifies the circuit AS
//!   COMPILED, which is what the transcript must bind.
//! - Compiler/tooling versions are deliberately NOT part of the
//!   preimage: identical circuits must commit identically across
//!   compiler versions. Version axes are validated (fail-closed) at the
//!   envelope layer instead.
//!
//! Verifiers never trust a commitment from a request: they recompute it
//! from the canonically recompiled circuit (or a registry pin) and
//! compare - see the facade's encoded-proof entry points.

use ssgkr_compiler::{LayerStrategy, PublicInputs, SmtOpKind, SmtParams};
use ssgkr_primitives::Transcript;
use ssgkr_primitives::field::{
    BaseField, ChallengeField, ExtensionField, PrimeCharacteristicRing, PrimeField32,
};
use ssgkr_primitives::hash::{DIGEST_WIDTH, Digest};
use ssgkr_protocol::{GateKind, LayeredCircuit};

/// Domain separation tag of commitment algorithm v1. The `v1` tracks the
/// COMMITMENT ALGORITHM (preimage schema + sponge), not the product
/// version; any change to the schema above bumps it.
pub const CIRCUIT_COMMITMENT_DOMAIN_V1: &[u8] = b"ssgkr/circuit-commitment/v1";

/// Frozen gate-kind tags of the commitment preimage (S-3 declaration
/// order; also reused by the encoder's error taxonomy).
pub fn gate_kind_tag(kind: GateKind) -> u8 {
    match kind {
        GateKind::Lin => 0,
        GateKind::Mul => 1,
        GateKind::Pow3 => 2,
    }
}

/// Frozen layer-strategy identity `(id, arg)`. Only strategy A (0, 0) is
/// compilable today (the R1 domain iff rejects B/C), but the commitment
/// is total so the identity encoding never has an undefined case.
pub fn strategy_identity(strategy: LayerStrategy) -> (u8, u32) {
    match strategy {
        LayerStrategy::A => (0, 0),
        LayerStrategy::B { merge_k } => (1, merge_k),
        LayerStrategy::C => (2, 0),
    }
}

/// Absorb a u32 scalar as one canonical field element. Every scalar in
/// the preimage is structurally far below the KoalaBear order (counts,
/// wire indices, widths); wrapping would alias distinct preimages, so it
/// is a hard error, never a reduction.
fn absorb_u32(t: &mut Transcript, x: u32) {
    assert!(
        x < BaseField::ORDER_U32,
        "circuit-commitment scalar {x} exceeds the field order - schema violation"
    );
    t.observe_base(BaseField::from_u32(x));
}

/// [`absorb_u32`] for usize-typed structure values (lengths, widths).
/// The bound check runs BEFORE the narrowing cast, so the cast is exact.
fn absorb_len(t: &mut Transcript, x: usize) {
    assert!(
        x < BaseField::ORDER_U32 as usize,
        "circuit-commitment length {x} exceeds the field order - schema violation"
    );
    t.observe_base(BaseField::from_u32(x as u32));
}

/// Base-field limbs of an extension element, reached through the
/// sanctioned re-exported trait vocabulary (`ExtensionField`'s
/// vector-space supertrait; the workspace rule keeps `p3_field::*` paths
/// inside `ssgkr-primitives` only).
pub(crate) fn ext_limbs<EF: ExtensionField<BaseField>>(x: &EF) -> &[BaseField] {
    x.as_basis_coefficients_slice()
}

/// Compute the full circuit commitment for a compiled circuit under its
/// instance parameters. One-shot per `(kind, config)`: callers on hot
/// paths cache it (the facade caches it in `PreparedSync`).
pub fn full_circuit_commitment(
    circuit: &LayeredCircuit<BaseField>,
    kind: SmtOpKind,
    params: &SmtParams,
    strategy: LayerStrategy,
) -> Digest<BaseField> {
    let mut t = Transcript::new(CIRCUIT_COMMITMENT_DOMAIN_V1);
    let (sid, sarg) = strategy_identity(strategy);
    absorb_u32(&mut t, u32::from(PublicInputs::kind_tag(kind)));
    absorb_u32(&mut t, params.depth);
    absorb_u32(&mut t, params.leaf_max_fields);
    absorb_u32(&mut t, u32::from(sid));
    absorb_u32(&mut t, sarg);
    absorb_len(&mut t, circuit.input_width_bits);
    absorb_len(&mut t, circuit.layers.len());
    for layer in &circuit.layers {
        absorb_len(&mut t, layer.width_bits);
        absorb_len(&mut t, layer.gates.len());
        for g in &layer.gates {
            absorb_u32(&mut t, u32::from(gate_kind_tag(g.kind)));
            absorb_u32(&mut t, g.out);
            absorb_u32(&mut t, g.in1);
            absorb_u32(&mut t, g.in2);
            t.observe_base(g.coeff);
        }
        absorb_len(&mut t, layer.consts.len());
        for &(wire, value) in &layer.consts {
            absorb_u32(&mut t, wire);
            t.observe_base(value);
        }
    }
    squeeze_digest(&mut t)
}

/// Squeeze a full digest (8 base elements) as the limbs of two extension
/// challenges - the duplex sponge's native output path, at the digest
/// width the workspace already standardizes on (~124-bit collision
/// resistance, equal to the sponge capacity bound).
fn squeeze_digest(t: &mut Transcript) -> Digest<BaseField> {
    let mut out = [BaseField::ZERO; DIGEST_WIDTH];
    let a: ChallengeField = t.sample_challenge();
    let b: ChallengeField = t.sample_challenge();
    let (la, lb) = (ext_limbs(&a), ext_limbs(&b));
    let half = DIGEST_WIDTH / 2;
    out[..half].copy_from_slice(&la[..half]);
    out[half..].copy_from_slice(&lb[..half]);
    Digest(out)
}
