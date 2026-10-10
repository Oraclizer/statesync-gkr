//! Skeleton smoke tests: exercise every semantic anchor that is already
//! real (not `todo!`). These anchors are the spec-literal functions the
//! FV track will verify against, so they must behave from day one.

// Test code may unwrap freely; the workspace-level lint targets library
// code paths.
#![allow(clippy::unwrap_used, clippy::expect_used)]

use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, SmtOperation, SmtParams,
    SmtWitness, smt_valid_native,
};
use statesync_gkr::gkr::{Gate, GateKind, Layer, LayeredCircuit, evaluate_circuit, gate_semantics};
use statesync_gkr::primitives::field::{BaseField, PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{Digest, HashGadget, Poseidon2Gadget};
use statesync_gkr::sumcheck::{
    ChallengeSource, MultilinearPoly, RoundPoly, SumcheckInstance, SumcheckOracle, verify,
};

fn f(x: u32) -> BaseField {
    BaseField::from_u32(x)
}

// ---------------------------------------------------------------- fields

#[test]
fn multilinear_evaluate_agrees_with_table_on_hypercube() {
    // p(x0, x1) table with x0 as MSB: [p(0,0), p(0,1), p(1,0), p(1,1)]
    let p = MultilinearPoly::from_evals(vec![f(3), f(5), f(7), f(11)]).unwrap();
    assert_eq!(p.num_vars(), 2);
    assert_eq!(p.evaluate(&[f(0), f(0)]), f(3));
    assert_eq!(p.evaluate(&[f(0), f(1)]), f(5));
    assert_eq!(p.evaluate(&[f(1), f(0)]), f(7));
    assert_eq!(p.evaluate(&[f(1), f(1)]), f(11));
}

#[test]
fn fix_first_var_matches_partial_evaluation() {
    let p = MultilinearPoly::from_evals(vec![f(3), f(5), f(7), f(11)]).unwrap();
    let r = f(13);
    let mut q = p.clone();
    q.fix_first_var(r);
    assert_eq!(q.num_vars(), 1);
    for b in [f(0), f(1)] {
        assert_eq!(q.evaluate(&[b]), p.evaluate(&[r, b]));
    }
}

#[test]
fn round_poly_horner() {
    // g(x) = 2 + 3x + x^2
    let g = RoundPoly::from_coeffs(vec![f(2), f(3), f(1)]);
    assert_eq!(g.degree(), 2);
    assert_eq!(g.eval_at(f(0)), f(2));
    assert_eq!(g.eval_at(f(2)), f(12));
}

// -------------------------------------------------------------- sumcheck

/// Honest oracle over an explicit multilinear polynomial (spec-literal
/// reference implementation used only in tests).
struct TableOracle {
    poly: MultilinearPoly<BaseField>,
}

impl SumcheckOracle<BaseField> for TableOracle {
    fn num_vars(&self) -> usize {
        self.poly.num_vars()
    }

    fn degree_bound(&self) -> usize {
        1 // multilinear
    }

    fn round_poly(&self) -> RoundPoly<BaseField> {
        // g(X) = sum over remaining boolean vars with first var free.
        // For a multilinear table split in halves: g(0) = sum(lo),
        // g(1) = sum(hi); represent as g(X) = g0 + (g1 - g0) X.
        let evals = self.poly.evals();
        let half = evals.len() / 2;
        let g0: BaseField = evals[..half].iter().copied().sum();
        let g1: BaseField = evals[half..].iter().copied().sum();
        RoundPoly::from_coeffs(vec![g0, g1 - g0])
    }

    fn bind(&mut self, r: BaseField) {
        self.poly.fix_first_var(r);
    }
}

/// Deterministic challenge source for tests (fixed sequence).
struct FixedChallenges {
    seq: Vec<BaseField>,
    next: usize,
}

impl ChallengeSource<BaseField> for FixedChallenges {
    fn observe_round_poly(&mut self, _poly: &RoundPoly<BaseField>) {}

    fn draw_challenge(&mut self) -> BaseField {
        let r = self.seq[self.next % self.seq.len()];
        self.next += 1;
        r
    }
}

#[test]
fn sumcheck_prove_verify_roundtrip_and_subclaim() {
    let table = vec![f(3), f(5), f(7), f(11), f(13), f(17), f(19), f(23)];
    let claimed: BaseField = table.iter().copied().sum();
    let poly = MultilinearPoly::from_evals(table).unwrap();

    let instance = SumcheckInstance {
        num_vars: 3,
        degree_bound: 1,
        claimed_sum: claimed,
    };

    let mut oracle = TableOracle { poly: poly.clone() };
    let mut prover_ch = FixedChallenges {
        seq: vec![f(29), f(31), f(37)],
        next: 0,
    };
    let (proof, prover_claim) = statesync_gkr::sumcheck::prove(&mut oracle, &mut prover_ch);

    let mut verifier_ch = FixedChallenges {
        seq: vec![f(29), f(31), f(37)],
        next: 0,
    };
    let subclaim = verify(&instance, &proof, &mut verifier_ch).expect("honest proof verifies");

    // Prover and verifier agree on the residual claim, and the oracle
    // polynomial indeed evaluates to it (AFP sc_ver0 discharge).
    assert_eq!(subclaim, prover_claim);
    assert_eq!(poly.evaluate(&subclaim.point), subclaim.expected_eval);
}

#[test]
fn sumcheck_rejects_wrong_claim() {
    let table = vec![f(1), f(2), f(3), f(4)];
    let wrong: BaseField = f(999);
    let poly = MultilinearPoly::from_evals(table).unwrap();

    let instance = SumcheckInstance {
        num_vars: 2,
        degree_bound: 1,
        claimed_sum: wrong,
    };
    let mut oracle = TableOracle { poly };
    let mut ch = FixedChallenges {
        seq: vec![f(5), f(7)],
        next: 0,
    };
    let (proof, _) = statesync_gkr::sumcheck::prove(&mut oracle, &mut ch);

    let mut vch = FixedChallenges {
        seq: vec![f(5), f(7)],
        next: 0,
    };
    assert!(verify(&instance, &proof, &mut vch).is_err());
}

// ---------------------------------------------------------------- gates

fn gate(kind: GateKind, out: u32, in1: u32, in2: u32, coeff: BaseField) -> Gate<BaseField> {
    Gate {
        kind,
        out,
        in1,
        in2,
        coeff,
    }
}

#[test]
fn gate_semantics_match_spec() {
    // Unary kinds ignore b; coefficients are applied by layer evaluation.
    assert_eq!(gate_semantics(GateKind::Lin, f(3), f(99)), f(3));
    assert_eq!(gate_semantics(GateKind::Mul, f(3), f(4)), f(12));
    assert_eq!(gate_semantics(GateKind::Pow3, f(3), f(99)), f(27));
}

#[test]
fn evaluate_circuit_two_layers() {
    // inputs (width 2): [a, b]
    // layer 1 (width 2): [a + b (two Lin gates into one output), a * b]
    // layer 0 (width 1): [(a+b)^3]
    let one = BaseField::ONE;
    let circuit = LayeredCircuit {
        layers: vec![
            Layer {
                width_bits: 0,
                gates: vec![gate(GateKind::Pow3, 0, 0, 0, one)],
                consts: vec![],
            },
            Layer {
                width_bits: 1,
                gates: vec![
                    gate(GateKind::Lin, 0, 0, 0, one),
                    gate(GateKind::Lin, 0, 1, 1, one),
                    gate(GateKind::Mul, 1, 0, 1, one),
                ],
                consts: vec![],
            },
        ],
        input_width_bits: 1,
    };
    let witness = evaluate_circuit(&circuit, &[f(2), f(3)]).unwrap();
    assert_eq!(witness.layer_values.len(), 3);
    assert_eq!(witness.layer_values[2], vec![f(2), f(3)]); // inputs last
    assert_eq!(witness.layer_values[1], vec![f(5), f(6)]);
    assert_eq!(witness.layer_values[0], vec![f(125)]);
}

#[test]
fn affine_then_sbox_round_is_expressible() {
    // The freeze-gate counterexample, kept as a regression test: one
    // Poseidon2-shaped round = affine layer (constant multiplications +
    // round constant) followed by an x^3 S-box.
    //   layer 1 (affine): t = 2 * a + 3 * b + 5
    //   layer 0 (S-box):  t^3
    // inputs (2, 3) => t = 4 + 9 + 5 = 18, output = 18^3 = 5832.
    let circuit = LayeredCircuit {
        layers: vec![
            Layer {
                width_bits: 0,
                gates: vec![gate(GateKind::Pow3, 0, 0, 0, BaseField::ONE)],
                consts: vec![],
            },
            Layer {
                width_bits: 0,
                gates: vec![
                    gate(GateKind::Lin, 0, 0, 0, f(2)),
                    gate(GateKind::Lin, 0, 1, 1, f(3)),
                ],
                consts: vec![(0, f(5))],
            },
        ],
        input_width_bits: 1,
    };
    let witness = evaluate_circuit(&circuit, &[f(2), f(3)]).unwrap();
    assert_eq!(witness.layer_values[1], vec![f(18)]);
    assert_eq!(witness.layer_values[0], vec![f(5832)]);
}

// ------------------------------------------------------------------ smt

#[test]
fn smt_membership_and_update_native_semantics() {
    let hasher = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: 4,
        ..Default::default()
    }; // small tree for the test
    let key = AssetId(5);

    let payload = LeafPayload {
        sync_state: vec![f(42)],
        identity_digest: [7u8; 32],
    };
    let old_leaf = LeafState::Occupied(payload.clone());
    let new_leaf = LeafState::Tombstone;

    let path = MerklePath {
        siblings: vec![Digest::zero(); 4],
    };
    let old_root = path.compute_root(&hasher, &params, key, &old_leaf).unwrap();
    let new_root = path.compute_root(&hasher, &params, key, &new_leaf).unwrap();

    // Membership of the occupied leaf under old_root.
    let witness = SmtWitness {
        leaf: old_leaf.clone(),
        path: path.clone(),
    };
    let op = SmtOperation::Membership { key, payload };
    assert!(smt_valid_native(&hasher, &params, &op, &old_root, &old_root, &witness).unwrap());

    // Membership must FAIL against the wrong root.
    assert!(!smt_valid_native(&hasher, &params, &op, &new_root, &new_root, &witness).unwrap());

    // Update old_leaf -> Tombstone moves old_root to new_root.
    let op = SmtOperation::Update {
        key,
        old_leaf,
        new_leaf: new_leaf.clone(),
    };
    assert!(smt_valid_native(&hasher, &params, &op, &old_root, &new_root, &witness).unwrap());

    // After the update, NonMembership holds under new_root (tombstone).
    let witness2 = SmtWitness {
        leaf: new_leaf,
        path,
    };
    let op = SmtOperation::NonMembership { key };
    assert!(smt_valid_native(&hasher, &params, &op, &new_root, &new_root, &witness2).unwrap());
}

#[test]
fn leaf_encoding_is_domain_separated() {
    let payload = LeafPayload {
        sync_state: vec![f(42)],
        identity_digest: [7u8; 32],
    };
    let e = LeafState::Empty.encode();
    let t = LeafState::Tombstone.encode();
    let o = LeafState::Occupied(payload).encode();
    assert_ne!(e, t);
    assert_ne!(e[0], o[0]);
    assert_ne!(t[0], o[0]);
}

#[test]
fn hash_gadget_is_deterministic_and_leaf_prehash_differs_from_compress() {
    let hasher = Poseidon2Gadget::default();
    let a = hasher.hash_leaf(&[f(1), f(2), f(3)]).unwrap();
    let b = hasher.hash_leaf(&[f(1), f(2), f(3)]).unwrap();
    assert_eq!(a, b);
    let c = hasher.compress(&a, &b);
    let d = hasher.compress(&a, &b);
    assert_eq!(c, d);
    assert_ne!(c, a);
}

// --------------------------------------------------------------- config

#[test]
fn default_config_carries_design_defaults() {
    let cfg = statesync_gkr::StateSyncGkrConfig::default();
    assert_eq!(cfg.smt.depth, 24);
    assert_eq!(cfg.layer_strategy, LayerStrategy::A);
    assert!(cfg.batching.max_batch_size >= cfg.batching.min_batch_size);
}
