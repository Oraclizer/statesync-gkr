//! Succinct-verifier soundness battery for the alternate verifier path.
//!
//! Four pins:
//! 1. The derived closed-form oracle is BIT-IDENTICAL to the materialized
//!    table oracle on the real compiled SMT circuits - every op kind,
//!    boundary depths (including the non-multiple-of-8 depth 28), random
//!    extension-field points, predicates and constants.
//! 2. The derivation is an EXACT REPARTITION of each circuit layer: the
//!    re-expanded groups plus the sparse remainder are a permutation of the
//!    layer's gate/const lists (nothing dropped, added, or altered).
//! 3. Closed-form coverage stays near-total on the production circuits - a
//!    silent fit regression would keep the verifier correct but degrade it
//!    back to O(#gates), which this test turns into a loud failure.
//! 4. The succinct facade verifier and the O(#gates) reference verifier
//!    agree verdict-for-verdict on honest AND tampered proofs (the audit
//!    suites' rejection behavior transfers to the succinct path).

#![allow(clippy::unwrap_used, clippy::expect_used)]

use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOpKind,
    SmtOperation, SmtParams, SmtWitness, compile_with_hints,
};
use statesync_gkr::gkr::wiring::{DerivedRegularWiring, TableWiring, WiringOracle};
use statesync_gkr::gkr::{Gate, GateKind};
use statesync_gkr::primitives::field::{
    BaseField, ChallengeField, PrimeCharacteristicRing, PrimeField32,
};
use statesync_gkr::primitives::hash::{Digest, HashGadget, Poseidon2Gadget};
use statesync_gkr::sumcheck::RoundPoly;
use statesync_gkr::{StateSyncGkrConfig, StateSyncProver, SyncRequest};

fn f(x: u32) -> BaseField {
    BaseField::from_u32(x)
}

fn config(depth: u32) -> StateSyncGkrConfig {
    StateSyncGkrConfig {
        smt: SmtParams {
            depth,
            ..Default::default()
        },
        layer_strategy: LayerStrategy::A,
        batching: Default::default(),
    }
}

fn siblings(depth: usize) -> Vec<Digest<BaseField>> {
    (0..depth)
        .map(|i| Digest([f(i as u32 * 13 + 1); 8]))
        .collect()
}

fn rand_point(len: usize, seed: u32) -> Vec<ChallengeField> {
    (0..len)
        .map(|i| {
            ChallengeField::from(f(seed
                .wrapping_mul(2_654_435_761)
                .wrapping_add(i as u32 * 40_503 + 7)
                % 1_000_003))
        })
        .collect()
}

fn membership_request(depth: usize, key: u64) -> SyncRequest {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: depth as u32,
        ..Default::default()
    };
    let key = AssetId(key);
    let payload = LeafPayload {
        sync_state: vec![f(42), f(7)],
        identity_digest: [9u8; 32],
    };
    let leaf = LeafState::Occupied(payload.clone());
    let path = MerklePath {
        siblings: siblings(depth),
    };
    let old_root = path.compute_root(&h, &params, key, &leaf).unwrap();
    let value_digest = h.hash_leaf(&leaf.encode()).unwrap();
    SyncRequest {
        operation: SmtOperation::Membership { key, payload },
        witness: SmtWitness { leaf, path },
        public_inputs: PublicInputs {
            old_root,
            new_root: old_root,
            op_kind_tag: 0,
            asset_id: key,
            value_digest,
        },
    }
}

fn non_membership_request(depth: usize, key: u64) -> SyncRequest {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: depth as u32,
        ..Default::default()
    };
    let key = AssetId(key);
    let leaf = LeafState::Tombstone;
    let path = MerklePath {
        siblings: siblings(depth),
    };
    let old_root = path.compute_root(&h, &params, key, &leaf).unwrap();
    let value_digest = h.hash_leaf(&leaf.encode()).unwrap();
    SyncRequest {
        operation: SmtOperation::NonMembership { key },
        witness: SmtWitness { leaf, path },
        public_inputs: PublicInputs {
            old_root,
            new_root: old_root,
            op_kind_tag: 1,
            asset_id: key,
            value_digest,
        },
    }
}

fn update_request(depth: usize, key: u64) -> SyncRequest {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: depth as u32,
        ..Default::default()
    };
    let key = AssetId(key);
    let old_leaf = LeafState::Occupied(LeafPayload {
        sync_state: vec![f(100)],
        identity_digest: [3u8; 32],
    });
    let new_leaf = LeafState::Tombstone;
    let path = MerklePath {
        siblings: siblings(depth),
    };
    let old_root = path.compute_root(&h, &params, key, &old_leaf).unwrap();
    let new_root = path.compute_root(&h, &params, key, &new_leaf).unwrap();
    let value_digest = h.hash_leaf(&new_leaf.encode()).unwrap();
    SyncRequest {
        operation: SmtOperation::Update {
            key,
            old_leaf: old_leaf.clone(),
            new_leaf,
        },
        witness: SmtWitness {
            leaf: old_leaf,
            path,
        },
        public_inputs: PublicInputs {
            old_root,
            new_root,
            op_kind_tag: 2,
            asset_id: key,
            value_digest,
        },
    }
}

const KINDS: [SmtOpKind; 3] = [
    SmtOpKind::Membership,
    SmtOpKind::NonMembership,
    SmtOpKind::Update,
];

fn compiled(
    depth: u32,
    kind: SmtOpKind,
) -> (
    statesync_gkr::gkr::LayeredCircuit<BaseField>,
    DerivedRegularWiring,
) {
    let params = SmtParams {
        depth,
        ..Default::default()
    };
    let template = Poseidon2Gadget::default().round_template();
    let (circuit, hints) =
        compile_with_hints(&params, kind, LayerStrategy::A, &template).expect("compile");
    let derived = DerivedRegularWiring::derive(&circuit, &hints);
    (circuit, derived)
}

/// Layer sample for big circuits: ends, middle, and the residual-formation
/// region; full sweep for small ones.
fn layer_sample(depth_layers: usize, full: bool) -> Vec<usize> {
    if full || depth_layers <= 12 {
        return (0..depth_layers).collect();
    }
    let mut v = vec![
        0,
        1,
        2,
        depth_layers / 3,
        depth_layers / 2,
        2 * depth_layers / 3,
        depth_layers - 3,
        depth_layers - 2,
        depth_layers - 1,
    ];
    v.dedup();
    v
}

/// Pin 1: derived == table on the real compiled circuits, random points,
/// every gate kind plus the constant MLE. Depth 28 exercises the
/// non-multiple-of-8 key-bit section offsets; depths 1 and 3 the degenerate
/// and small trees; 24 the production default.
#[test]
fn derived_oracle_matches_table_on_compiled_circuits() {
    for &(depth, full) in &[(1u32, true), (3, true), (24, false), (28, false)] {
        for kind in KINDS {
            let (circuit, derived) = compiled(depth, kind);
            let table = TableWiring::new(&circuit);
            for layer in layer_sample(circuit.layers.len(), full) {
                let ob = table.out_width_bits(layer);
                let ib = table.in_width_bits(layer);
                assert_eq!(derived.out_width_bits(layer), ob);
                assert_eq!(derived.in_width_bits(layer), ib);
                for seed in 0..2u32 {
                    let z = rand_point(ob, seed * 31 + layer as u32 + depth);
                    let x = rand_point(ib, seed * 37 + layer as u32 + 11);
                    let y = rand_point(ib, seed * 41 + layer as u32 + 23);
                    for gk in [GateKind::Lin, GateKind::Mul, GateKind::Pow3] {
                        assert_eq!(
                            derived.eval_predicate_mle(layer, gk, &z, &x, &y),
                            table.eval_predicate_mle(layer, gk, &z, &x, &y),
                            "{kind:?} d={depth} layer {layer} {gk:?} seed {seed}"
                        );
                    }
                    assert_eq!(
                        derived.eval_const_mle(layer, &z),
                        table.eval_const_mle(layer, &z),
                        "{kind:?} d={depth} layer {layer} const seed {seed}"
                    );
                }
            }
        }
    }
}

fn gate_key(g: &Gate<BaseField>) -> (u8, u32, u32, u32, u32) {
    let k = match g.kind {
        GateKind::Lin => 0u8,
        GateKind::Mul => 1,
        GateKind::Pow3 => 2,
    };
    (k, g.out, g.in1, g.in2, g.coeff.as_canonical_u32())
}

/// Pin 2: the derivation is an exact repartition - re-expanding the groups
/// plus the sparse remainder reproduces each layer's gate/const list as a
/// multiset. No gate is dropped, added, or altered by
/// the closed form.
#[test]
fn derivation_is_exact_repartition_of_the_circuit() {
    for &depth in &[3u32, 24] {
        for kind in KINDS {
            let (circuit, derived) = compiled(depth, kind);
            for (li, layer) in circuit.layers.iter().enumerate() {
                let mut expanded: Vec<_> = derived.expand_gates(li).iter().map(gate_key).collect();
                let mut source: Vec<_> = layer.gates.iter().map(gate_key).collect();
                expanded.sort_unstable();
                source.sort_unstable();
                assert_eq!(expanded, source, "{kind:?} d={depth} layer {li} gates");

                let mut ec: Vec<_> = derived
                    .expand_consts(li)
                    .iter()
                    .map(|&(w, v)| (w, v.as_canonical_u32()))
                    .collect();
                let mut sc: Vec<_> = layer
                    .consts
                    .iter()
                    .map(|&(w, v)| (w, v.as_canonical_u32()))
                    .collect();
                ec.sort_unstable();
                sc.sort_unstable();
                assert_eq!(ec, sc, "{kind:?} d={depth} layer {li} consts");
            }
        }
    }
}

/// Pin 3: closed-form coverage stays near-total on the production circuits.
/// Sparse leftovers are correct but cost O(1) per gate per evaluation; if a
/// layout or scoping change silently un-fits a big family, this fails loudly
/// instead of quietly re-linearizing the verifier.
#[test]
fn closed_form_coverage_is_near_total() {
    for kind in KINDS {
        let (circuit, derived) = compiled(24, kind);
        let total_gates: usize = circuit.layers.iter().map(|l| l.gates.len()).sum();
        let total_consts: usize = circuit.layers.iter().map(|l| l.consts.len()).sum();
        let stats = derived.stats();
        assert_eq!(
            stats.grouped_gates + stats.sparse_gates,
            total_gates,
            "{kind:?}: partition accounts for every gate"
        );
        assert_eq!(stats.grouped_consts + stats.sparse_consts, total_consts);
        let sparse_frac = stats.sparse_gates as f64 / total_gates as f64;
        assert!(
            sparse_frac < 0.02,
            "{kind:?}: sparse gate fraction {sparse_frac:.4} (stats {stats:?})"
        );
    }
}

/// Pin 4: the succinct and reference facade verifiers agree verdict-for-
/// verdict - honest proofs accept on both, and every tamper class rejects
/// on both. "Rejects differently" anywhere is a CONFIRMED bug (the task's
/// acceptance bar for the verify swap).
#[test]
fn succinct_and_reference_verifiers_agree_on_honest_and_tampered() {
    let depth = 4usize;
    let prover = StateSyncProver::new(config(depth as u32));

    let requests = [
        membership_request(depth, 5),
        non_membership_request(depth, 11),
        update_request(depth, 9),
    ];
    for request in &requests {
        let result = prover.prove_sync_op(request).expect("prove");

        // Honest: both accept.
        assert!(prover.verify_sync_op(request, &result));
        assert!(prover.verify_sync_op_reference(request, &result));

        // Tamper batteries: each mutation must reject on BOTH verifiers.
        // (a) corrupt a sumcheck round-polynomial coefficient
        let mut t = result.clone();
        let rp = &t.proof.layer_proofs[0].sumcheck.round_polys[0];
        let mut coeffs = rp.coeffs().to_vec();
        coeffs[0] += ChallengeField::from(f(1));
        t.proof.layer_proofs[0].sumcheck.round_polys[0] = RoundPoly::from_coeffs(coeffs);
        let (s, r) = (
            prover.verify_sync_op(request, &t),
            prover.verify_sync_op_reference(request, &t),
        );
        assert_eq!(s, r, "round-poly tamper verdicts must match");
        assert!(!s, "round-poly tamper must reject");

        // (b) corrupt a claimed layer evaluation
        let mut t = result.clone();
        t.proof.layer_proofs[0].eval_x += ChallengeField::from(f(1));
        let (s, r) = (
            prover.verify_sync_op(request, &t),
            prover.verify_sync_op_reference(request, &t),
        );
        assert_eq!(s, r, "eval_x tamper verdicts must match");
        assert!(!s);

        // (c) tampered public value_digest
        let mut tr = request.clone();
        tr.public_inputs.value_digest = Digest([f(77); 8]);
        let mut tres = result.clone();
        tres.public_inputs.value_digest = Digest([f(77); 8]);
        let (s, r) = (
            prover.verify_sync_op(&tr, &tres),
            prover.verify_sync_op_reference(&tr, &tres),
        );
        assert_eq!(s, r, "value_digest tamper verdicts must match");
        assert!(!s);

        // (d) perturbed witness sibling against the original proof
        let mut tr = request.clone();
        tr.witness.path.siblings[1] = Digest([f(999); 8]);
        let (s, r) = (
            prover.verify_sync_op(&tr, &result),
            prover.verify_sync_op_reference(&tr, &result),
        );
        assert_eq!(s, r, "witness tamper verdicts must match");
        assert!(!s);
    }

    // (e) critical shape: NonMembership claimed for an occupied key -
    // both verifiers must reject it identically.
    let mut forged = non_membership_request(depth, 11);
    forged.witness.leaf = LeafState::Occupied(LeafPayload {
        sync_state: vec![f(1), f(2)],
        identity_digest: [1u8; 32],
    });
    let honest = non_membership_request(depth, 11);
    let result = prover.prove_sync_op(&honest).expect("prove");
    let (s, r) = (
        prover.verify_sync_op(&forged, &result),
        prover.verify_sync_op_reference(&forged, &result),
    );
    assert_eq!(s, r, "occupied-nonmembership verdicts must match");
    assert!(!s);
}
