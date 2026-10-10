//! Multilinear-extension helpers used by the GKR layer reduction.
//!
//! Variable-order convention (frozen with S-2, shared with
//! `ssgkr_sumcheck::poly`): variable 0 is the MOST significant index bit.
//! For an `n`-bit index `idx`, the bit assigned to variable `j` is
//! `(idx >> (n - 1 - j)) & 1`.
//!
//! All evaluations happen in the challenge (extension) field: the circuit
//! carries base-field values, but the verifier samples random points from
//! the extension so that per-round soundness error stays `deg / |EF|`
//! (design N2). Base values are embedded via [`embed`].

use ssgkr_primitives::field::{BaseField, ChallengeField, PrimeCharacteristicRing};

#[cfg(creusot)]
use creusot_std::prelude::requires;

/// Embed a base-field element into the challenge field.
#[inline]
pub fn embed(x: BaseField) -> ChallengeField {
    ChallengeField::from(x)
}

/// A small non-negative integer as a challenge-field element (interpolation
/// nodes, coefficients). Goes through the base field so it is unambiguous.
#[inline]
pub fn cf_u64(k: u64) -> ChallengeField {
    ChallengeField::from(BaseField::from_u64(k))
}

/// `eq(point, idx)` = the multilinear Lagrange basis weight of the boolean
/// point `idx` at `point`: product over variables of `point_j` when the
/// `j`-th bit of `idx` is 1, and `1 - point_j` when it is 0.
///
/// `point.len()` is the number of variables; `idx` must be `< 2^len`.
///
/// FV-CONTRACT (Creusot, R2 - design contract, NOT tool-checked):
///   #[ensures(result == Multilinear_Extension.eq_pi point idx)]
/// (variable 0 = MSB: bit (n-1-j) of idx feeds variable j, literally
/// `Multilinear_Extension.bit_at`). EXPRESSION-WALLED: the product is
/// black-box field arithmetic (design B.6) and the bit extraction is
/// axiom-free in the int-mode prelude (R1 wall 3); the value fact is
/// held by the model (`eq_pi`) and the Kronecker pin
/// (`eq_is_kronecker_on_boolean_points`).
pub fn eq_point_index(point: &[ChallengeField], idx: usize) -> ChallengeField {
    let n = point.len();
    let mut acc = ChallengeField::ONE;
    for (j, &p) in point.iter().enumerate() {
        // Variable j is the (n-1-j)-th bit (variable 0 = MSB).
        let bit = (idx >> (n - 1 - j)) & 1;
        acc *= if bit == 1 { p } else { ChallengeField::ONE - p };
    }
    acc
}

/// `eq(a, b)` for two challenge-field points of equal length: the "same
/// point" indicator MLE, `prod_j (a_j b_j + (1 - a_j)(1 - b_j))`. On boolean
/// points it is 1 iff `a == b`, and `sum_b eq(a, b) = 1` over the hypercube.
#[cfg_attr(creusot, requires(a@.len() == b@.len()))]
pub fn eq_points(a: &[ChallengeField], b: &[ChallengeField]) -> ChallengeField {
    debug_assert_eq!(a.len(), b.len(), "eq_points arity mismatch");
    a.iter()
        .zip(b)
        .fold(ChallengeField::ONE, |acc, (&ai, &bi)| {
            acc * (ai * bi + (ChallengeField::ONE - ai) * (ChallengeField::ONE - bi))
        })
}

/// Three-way "same point" indicator MLE:
/// `prod_j (a_j b_j c_j + (1 - a_j)(1 - b_j)(1 - c_j))`, which equals
/// `sum_p eq(a, p) eq(b, p) eq(c, p)` over the hypercube (NOT
/// `eq_points(a, b) * eq_points(a, c)`). Used when a binary gate's output
/// and both inputs must lie in the same data-parallel block.
#[cfg_attr(creusot, requires(a@.len() == b@.len() && a@.len() == c@.len()))]
pub fn eq3_points(
    a: &[ChallengeField],
    b: &[ChallengeField],
    c: &[ChallengeField],
) -> ChallengeField {
    debug_assert_eq!(a.len(), b.len());
    debug_assert_eq!(a.len(), c.len());
    let one = ChallengeField::ONE;
    a.iter().zip(b).zip(c).fold(one, |acc, ((&ai, &bi), &ci)| {
        acc * (ai * bi * ci + (one - ai) * (one - bi) * (one - ci))
    })
}

/// Evaluate the multilinear extension of a base-field value table at an
/// arbitrary challenge-field point. `values.len()` must equal `2^point.len()`.
///
/// This is the same spec-literal Lagrange fold as
/// `MultilinearPoly::evaluate` but embeds base values into the extension;
/// variable 0 (the first fold) is the MSB.
///
/// FV-CONTRACT (Creusot, R2 - design contract, NOT tool-checked):
///   #[requires(values.len() == 1 << point.len())]
///   #[ensures(result == Multilinear_Extension.mle n (embedded values) point)]
/// EXPRESSION-WALLED (black-box field ops + the `2^n` length arithmetic
/// sits behind the axiom-free bitwise prelude, R1 wall 3); value fact
/// held by the model (`mle`) and the executable pins
/// (`mle_eval_matches_table_on_hypercube`, `mle_eval_as_eq_combination`).
pub fn mle_eval_base(values: &[BaseField], point: &[ChallengeField]) -> ChallengeField {
    debug_assert_eq!(values.len(), 1usize << point.len(), "arity mismatch");
    let mut table: Vec<ChallengeField> = values.iter().copied().map(embed).collect();
    fold_point(&mut table, point);
    table.first().copied().unwrap_or(ChallengeField::ZERO)
}

/// Evaluate the multilinear extension of a challenge-field value table at a
/// challenge-field point. `values.len()` must equal `2^point.len()`.
pub fn mle_eval_ext(values: &[ChallengeField], point: &[ChallengeField]) -> ChallengeField {
    debug_assert_eq!(values.len(), 1usize << point.len(), "arity mismatch");
    let mut table = values.to_vec();
    fold_point(&mut table, point);
    table.first().copied().unwrap_or(ChallengeField::ZERO)
}

/// Fold a challenge-field table down to a scalar over `point` (MSB first).
fn fold_point(table: &mut Vec<ChallengeField>, point: &[ChallengeField]) {
    for &r in point {
        let half = table.len() / 2;
        for i in 0..half {
            table[i] = table[i] + r * (table[i + half] - table[i]);
        }
        table.truncate(half);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cf(x: u32) -> ChallengeField {
        ChallengeField::from(BaseField::from_u32(x))
    }

    #[test]
    fn eq_is_kronecker_on_boolean_points() {
        // 2 variables: eq(boolean a, idx) = [a == idx].
        for a in 0..4usize {
            let point: Vec<ChallengeField> = (0..2)
                .map(|j| {
                    let bit = (a >> (2 - 1 - j)) & 1;
                    cf(bit as u32)
                })
                .collect();
            for idx in 0..4usize {
                let v = eq_point_index(&point, idx);
                assert_eq!(v, cf((a == idx) as u32), "a={a} idx={idx}");
            }
        }
    }

    #[test]
    fn mle_eval_matches_table_on_hypercube() {
        let values = [3u32, 5, 7, 11].map(BaseField::from_u32);
        // On boolean points, the MLE equals the table entry.
        assert_eq!(mle_eval_base(&values, &[cf(0), cf(0)]), cf(3));
        assert_eq!(mle_eval_base(&values, &[cf(0), cf(1)]), cf(5));
        assert_eq!(mle_eval_base(&values, &[cf(1), cf(0)]), cf(7));
        assert_eq!(mle_eval_base(&values, &[cf(1), cf(1)]), cf(11));
    }

    #[test]
    fn mle_eval_as_eq_combination() {
        // MLE(v)(r) = sum_idx v[idx] * eq(r, idx).
        let values = [3u32, 5, 7, 11].map(BaseField::from_u32);
        let point = [cf(9), cf(4)];
        let direct = mle_eval_base(&values, &point);
        let combo: ChallengeField = (0..4)
            .map(|idx| embed(values[idx]) * eq_point_index(&point, idx))
            .sum();
        assert_eq!(direct, combo);
    }
}
