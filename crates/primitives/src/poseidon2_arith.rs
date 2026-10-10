//! Poseidon2 (KoalaBear, width 16) in-circuit ARITHMETIZATION spec.
//!
//! This module exposes the exact data the circuit compiler (Module 1) needs
//! to reproduce the production Poseidon2 permutation GATE-BY-GATE: the two
//! linear-layer matrices (`M_E` external, `M_I` internal), the round
//! constants, the round schedule, and a native reference permutation used as
//! the cross-check oracle.
//!
//! S-1 boundary: only `ssgkr-primitives` may name `p3_*` paths, so the entire
//! Poseidon2 surface (constants, linear layers, permutation) is re-expressed
//! here as plain [`BaseField`] data; the compiler consumes it without ever
//! touching plonky3.
//!
//! # Why basis-probing for the matrices
//!
//! `M_E` and `M_I` are FIXED linear maps over the 16-wide state. Rather than
//! transcribe their entries by hand (a soundness-critical transcription risk,
//! N2), we EXTRACT them from plonky3's own generic linear-layer functions by
//! applying each to the 16 unit vectors: for a linear map `L`, `L(e_x)` is
//! exactly column `x` of the matrix (`L(e_x)[z] = M[z][x]`). This makes the
//! circuit's matrix definitionally equal to plonky3's, with zero transcription
//! surface. It is a deterministic build-time computation (16 evaluations per
//! matrix).
//!
//! The generic linear layers probed here are the same maps the optimized
//! `default_koalabear_poseidon2_16()` instance uses:
//! - external: both go through `mds_light_permutation(_, &MDSMat4)` (identical
//!   code path in `p3-monty-31`);
//! - internal: plonky3's own test (`test_generic_internal_linear_layer_16`)
//!   asserts the generic and optimized internal layers compute the same map.
//!
//! Independently of that, the [`permute`] reference below wraps the REAL
//! `default_koalabear_poseidon2_16()` instance, so the compiler's
//! permutation-level cross-check compares the emitted circuit against the
//! actual production permutation - the ultimate arbiter of correctness.

use p3_field::PrimeCharacteristicRing;
use p3_koala_bear::{
    GenericPoseidon2LinearLayersKoalaBear, KOALABEAR_RC16_EXTERNAL_FINAL,
    KOALABEAR_RC16_EXTERNAL_INITIAL, KOALABEAR_RC16_INTERNAL, default_koalabear_poseidon2_16,
};
use p3_poseidon2::GenericPoseidon2LinearLayers;
use p3_symmetric::Permutation;

use crate::field::BaseField;

/// Permutation width (state size in field elements).
pub const P2_WIDTH: usize = 16;

/// Number of initial external rounds (equals the number of terminal ones).
pub const P2_EXTERNAL_HALF_ROUNDS: usize = 4;

/// Number of internal (partial) rounds.
pub const P2_INTERNAL_ROUNDS: usize = 20;

/// S-box degree (`x^3`); matches the circuit IR's `Pow3` gate.
pub const P2_SBOX_DEGREE: usize = 3;

/// Extract a `16 x 16` matrix by applying a linear map to each unit vector.
///
/// For a linear map `L`, `L(e_x)[z] = M[z][x]`, so the image of `e_x` is the
/// `x`-th COLUMN of `M`. Both plonky3 linear layers are purely linear
/// (no additive offset), so this recovers the exact matrix.
fn probe_matrix(apply: impl Fn(&mut [BaseField; P2_WIDTH])) -> [[BaseField; P2_WIDTH]; P2_WIDTH] {
    let mut m = [[BaseField::ZERO; P2_WIDTH]; P2_WIDTH];
    for x in 0..P2_WIDTH {
        let mut e = [BaseField::ZERO; P2_WIDTH];
        e[x] = BaseField::ONE;
        apply(&mut e);
        for (z, row) in m.iter_mut().enumerate() {
            row[x] = e[z];
        }
    }
    m
}

/// The external linear layer `M_E` as a dense `16 x 16` matrix
/// (`out[z] = sum_x M_E[z][x] * in[x]`), extracted from plonky3's
/// `mds_light_permutation(_, &MDSMat4)`.
pub fn external_matrix() -> [[BaseField; P2_WIDTH]; P2_WIDTH] {
    probe_matrix(|s| {
        <GenericPoseidon2LinearLayersKoalaBear as GenericPoseidon2LinearLayers<P2_WIDTH>>::external_linear_layer::<BaseField>(s)
    })
}

/// The internal linear layer `M_I` as a dense `16 x 16` matrix
/// (`out[z] = sum_x M_I[z][x] * in[x]`), extracted from plonky3's
/// `generic_internal_linear_layer` (`M_I = 1 + Diag(V)`, closed form
/// `out[z] = V[z]*in[z] + sum_x in[x]`).
pub fn internal_matrix() -> [[BaseField; P2_WIDTH]; P2_WIDTH] {
    probe_matrix(|s| {
        <GenericPoseidon2LinearLayersKoalaBear as GenericPoseidon2LinearLayers<P2_WIDTH>>::internal_linear_layer::<BaseField>(s)
    })
}

/// Round constants of the 4 initial external rounds (`[round][lane]`).
pub fn external_initial_rc() -> [[BaseField; P2_WIDTH]; P2_EXTERNAL_HALF_ROUNDS] {
    KOALABEAR_RC16_EXTERNAL_INITIAL
}

/// Round constants of the 4 terminal external rounds (`[round][lane]`).
pub fn external_final_rc() -> [[BaseField; P2_WIDTH]; P2_EXTERNAL_HALF_ROUNDS] {
    KOALABEAR_RC16_EXTERNAL_FINAL
}

/// Round constants of the 20 internal rounds (added to lane 0 only).
pub fn internal_rc() -> [BaseField; P2_INTERNAL_ROUNDS] {
    KOALABEAR_RC16_INTERNAL
}

/// Native reference permutation: the REAL `default_koalabear_poseidon2_16()`
/// instance. This is the cross-check oracle the compiler's emitted circuit is
/// verified against (any divergence, including a generic-vs-optimized
/// linear-layer mismatch, would surface here).
pub fn permute(mut state: [BaseField; P2_WIDTH]) -> [BaseField; P2_WIDTH] {
    default_koalabear_poseidon2_16().permute_mut(&mut state);
    state
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;

    /// The probed linear layers are genuinely LINEAR (map 0 -> 0), so the
    /// unit-vector probe recovers the matrix with no hidden constant offset.
    #[test]
    fn linear_layers_are_offset_free() {
        let mut z = [BaseField::ZERO; P2_WIDTH];
        <GenericPoseidon2LinearLayersKoalaBear as GenericPoseidon2LinearLayers<P2_WIDTH>>::external_linear_layer::<BaseField>(&mut z);
        assert_eq!(z, [BaseField::ZERO; P2_WIDTH]);
        let mut z = [BaseField::ZERO; P2_WIDTH];
        <GenericPoseidon2LinearLayersKoalaBear as GenericPoseidon2LinearLayers<P2_WIDTH>>::internal_linear_layer::<BaseField>(&mut z);
        assert_eq!(z, [BaseField::ZERO; P2_WIDTH]);
    }

    /// The probed matrices reproduce the plonky3 linear layers on random
    /// inputs: `M * v == linear_layer(v)` (matrix form matches the map).
    #[test]
    fn probed_matrices_match_plonky3_linear_layers() {
        let me = external_matrix();
        let mi = internal_matrix();
        for seed in 0u32..8 {
            let v: [BaseField; P2_WIDTH] = core::array::from_fn(|i| {
                BaseField::from_u32(
                    seed.wrapping_mul(2_654_435_761)
                        .wrapping_add(i as u32 * 40_503 + 7)
                        % 65_521,
                )
            });

            let mut ext = v;
            <GenericPoseidon2LinearLayersKoalaBear as GenericPoseidon2LinearLayers<P2_WIDTH>>::external_linear_layer::<BaseField>(&mut ext);
            let mut int = v;
            <GenericPoseidon2LinearLayersKoalaBear as GenericPoseidon2LinearLayers<P2_WIDTH>>::internal_linear_layer::<BaseField>(&mut int);

            for z in 0..P2_WIDTH {
                let me_row: BaseField = (0..P2_WIDTH).map(|x| me[z][x] * v[x]).sum();
                let mi_row: BaseField = (0..P2_WIDTH).map(|x| mi[z][x] * v[x]).sum();
                assert_eq!(me_row, ext[z], "external row {z} seed {seed}");
                assert_eq!(mi_row, int[z], "internal row {z} seed {seed}");
            }
        }
    }
}
