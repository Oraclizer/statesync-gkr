//! Adversarial hash-binding audit of the materialized core.
//! (in-circuit Poseidon2 arithmetization + Libra-style sparse booking oracle).
//!
//! Method: every suspicion is exercised with a real
//! forgery/mismatch ATTEMPT, not a read-only argument. Extraction axis =
//! Soundness and security take precedence.
//!
//! Findings anchored here.
//!
//! Confirmed then fixed by the collision-resistance repair: the original
//! `leaf_fold` was NOT injective for Occupied leaves whose encoding exceeded
//! 16 field elements (sync_state length >= 7) - it WRAPPED the encoding onto
//! 16 lanes, so distinct valid leaves collided onto one pre-image, `h_leaf`
//! collided WITHOUT breaking Poseidon2, and a forged Membership of a
//! never-committed payload was accepted by BOTH the composed verifier and the
//! native semantics. FIXED by the lossless, length-bound fold (`[tag, len,
//! verbatim, 0-pad]` up to the `leaf_max_fields` bound, every lane absorbed by
//! the sponge): the collision class is gone and the forgery is rejected
//! end-to-end. The `leaf_fold_collision_*` / `forged_membership_*` tests below
//! keep their finding names but now assert the FIXED (rejecting) behavior -
//! regression pins, per the audit_2b convention.
//!
//! CLEAN (verified here): the Poseidon2 arithmetization data (probed matrices,
//! exposed round constants, round schedule) reproduces the native permutation;
//! the R2-1 tag domain separation still holds on the Poseidon2 circuit for
//! long Occupied leaves; and non-colliding wrong payloads are still rejected
//! (the pre-fix forgery was specifically a collision, not trivially-forgeable
//! membership).

#![allow(clippy::unwrap_used, clippy::expect_used)]

use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOpKind,
    SmtOperation, SmtParams, SmtWitness, compile, generate_witness, is_accepting, smt_valid_native,
};
use statesync_gkr::primitives::field::{BaseField, PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{
    DEFAULT_LEAF_MAX_FIELDS, Digest, HashGadget, Poseidon2Gadget, leaf_fold,
};
use statesync_gkr::primitives::poseidon2_arith as p2;
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

/// Tiny deterministic PRNG (SplitMix64-style); no external rand crate.
struct Lcg(u64);
impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed ^ 0x9E37_79B9_7F4A_7C15)
    }
    fn next_u32(&mut self) -> u32 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 32) as u32
    }
    fn below(&mut self, n: u32) -> u32 {
        self.next_u32() % n
    }
}

/// Build an Occupied leaf whose sync_state has length 16, differing from a
/// sibling only at positions 0 and 15. Under the PRE-FIX wrapping fold those
/// two rest indices both landed in pre-image slot 1 (`slot1 = s0 + s15`), so
/// any pair with equal sums collided. Post-fix the fold copies the encoding
/// VERBATIM (lossless), so these leaves fold apart - the pair is kept as the
/// regression anchor.
///
/// encode() = [tag=1, sync_state[0..16], keccak_limbs[0..9]] => length 26
/// (in-bound: <= leaf_max_fields = 31).
fn colliding_occupied(s0: u32, s15: u32) -> LeafState {
    let mut ss = vec![f(0); 16];
    ss[0] = f(s0);
    ss[15] = f(s15);
    // Fixed, identical "real" middle state so the leaves are non-trivial and
    // differ ONLY where we intend (positions 0 and 15).
    ss[3] = f(77);
    ss[8] = f(123);
    LeafState::Occupied(LeafPayload {
        sync_state: ss,
        identity_digest: [11u8; 32],
    })
}

// ---------------------------------------------------------------------------
// Item 2: leaf_fold injectivity / leaf-hash collision resistance.
// ---------------------------------------------------------------------------

/// Confirmed then fixed: under the pre-fix wrapping fold, two
/// DISTINCT valid Occupied leaves folded onto the SAME pre-image, hence
/// collided under the production Poseidon2 `h_leaf` -- a collision found with
/// ZERO cryptanalysis, purely from the lossy fold sum. The lossless
/// length-bound fold removes the class: this exact pair (and, per the
/// injectivity property test in `primitives::hash`, every in-bound pair) now
/// folds apart. Regression pin.
#[test]
fn leaf_fold_collision_breaks_leaf_hash_cr() {
    let a = colliding_occupied(5, 0); // pre-fix: slot1 = 5 + 0 = 5
    let b = colliding_occupied(3, 2); // pre-fix: slot1 = 3 + 2 = 5 (collided)

    // Distinct leaves (different asset sync state at positions 0 and 15).
    assert_ne!(a, b, "the two leaves must be genuinely different");
    let enc_a = a.encode();
    let enc_b = b.encode();
    assert_ne!(enc_a, enc_b, "encodings differ (a genuine distinct pair)");

    // FIXED: the lossless fold keeps distinct encodings apart ...
    assert_ne!(
        leaf_fold(&enc_a, DEFAULT_LEAF_MAX_FIELDS).unwrap(),
        leaf_fold(&enc_b, DEFAULT_LEAF_MAX_FIELDS).unwrap(),
        "regression: the lossless leaf_fold must separate this pair \
         (pre-fix it collapsed them onto one pre-image)"
    );

    // ... hence distinct Poseidon2 leaf hashes: h_leaf collisions again
    // require breaking Poseidon2 itself.
    let h = Poseidon2Gadget::default();
    assert_ne!(
        h.hash_leaf(&enc_a).unwrap(),
        h.hash_leaf(&enc_b).unwrap(),
        "regression: h_leaf must separate the former collision pair"
    );
}

/// Confirmed then fixed: the collision was exploitable
/// end-to-end. A tree commits leaf A at key k (fixing old_root); an attacker
/// forged a Membership proof for a DIFFERENT payload B (never committed) under
/// the SAME old_root, and both the facade verifier and the native semantics
/// accepted it - the state commitment did not bind a unique leaf (Theorem A
/// held, but `smt_valid` itself was unsound because `h_leaf` was not CR).
/// FIXED: with the lossless fold, `h_leaf(B) != h_leaf(A)`, so B's chain no
/// longer reaches A's root - the forgery is REJECTED by the composed verifier
/// AND by the native semantics. Regression pin.
#[test]
fn forged_membership_of_uncommitted_payload_is_accepted() {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: 4,
        ..Default::default()
    };
    let key = AssetId(5);
    let path = MerklePath {
        siblings: siblings(4),
    };

    let a = colliding_occupied(5, 0);
    let b = colliding_occupied(3, 2);
    let payload_a = match &a {
        LeafState::Occupied(p) => p.clone(),
        _ => unreachable!(),
    };
    let payload_b = match &b {
        LeafState::Occupied(p) => p.clone(),
        _ => unreachable!(),
    };

    // The tree commits ONLY A. old_root is a function of h_leaf(A) + siblings.
    let old_root = path.compute_root(&h, &params, key, &a).unwrap();

    let prover = StateSyncProver::new(config(4));

    // Sanity: honest Membership of A verifies.
    let req_a = SyncRequest {
        operation: SmtOperation::Membership {
            key,
            payload: payload_a,
        },
        witness: SmtWitness {
            leaf: a.clone(),
            path: path.clone(),
        },
        public_inputs: PublicInputs {
            old_root,
            new_root: old_root,
            op_kind_tag: 0,
            asset_id: key,
            value_digest: h.hash_leaf(&a.encode()).unwrap(),
        },
    };
    let res_a = prover.prove_sync_op(&req_a).unwrap();
    assert!(
        prover.verify_sync_op(&req_a, &res_a),
        "honest membership of the committed leaf A verifies"
    );

    // FORGERY ATTEMPT: Membership of B (never committed) under the SAME
    // old_root, using A's authentication path. Pre-fix this succeeded because
    // h_leaf(B) == h_leaf(A) (the fold collision); post-fix the hashes differ.
    let req_b = SyncRequest {
        operation: SmtOperation::Membership {
            key,
            payload: payload_b,
        },
        witness: SmtWitness {
            leaf: b.clone(),
            path: path.clone(),
        },
        public_inputs: PublicInputs {
            old_root, // the SAME root that commits A
            new_root: old_root,
            op_kind_tag: 0,
            asset_id: key,
            value_digest: h.hash_leaf(&b.encode()).unwrap(),
        },
    };
    let res_b = prover.prove_sync_op(&req_b).unwrap();

    // FIXED: the forged membership of B is REJECTED (h_leaf(B) != h_leaf(A),
    // so B's accumulator chain does not reach A's root). Regression pin.
    assert!(
        !prover.verify_sync_op(&req_b, &res_b),
        "regression: membership of never-committed payload B must be REJECTED \
         under A's root (the lossless fold removed the h_leaf collision)"
    );

    // And the native meaning standard rejects it too (the spec-level hole is
    // closed at its root: `h_leaf` is genuinely collision resistant now).
    assert!(
        !smt_valid_native(
            &h,
            &params,
            &req_b.operation,
            &old_root,
            &old_root,
            &req_b.witness
        )
        .unwrap(),
        "regression: native smt_valid must also reject the forged membership"
    );
}

/// Contrast: a wrong payload that does NOT collide under `leaf_fold` is
/// correctly rejected. This proves the forgery above is due specifically to
/// the collision, not to trivially-forgeable membership.
#[test]
fn non_colliding_wrong_payload_is_rejected() {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: 4,
        ..Default::default()
    };
    let key = AssetId(5);
    let path = MerklePath {
        siblings: siblings(4),
    };

    let a = colliding_occupied(5, 0);
    let old_root = path.compute_root(&h, &params, key, &a).unwrap();

    // C: a genuinely different, non-colliding Occupied payload (short leaf).
    let c_payload = LeafPayload {
        sync_state: vec![f(999)],
        identity_digest: [200u8; 32],
    };
    let c = LeafState::Occupied(c_payload.clone());
    assert_ne!(
        h.hash_leaf(&a.encode()).unwrap(),
        h.hash_leaf(&c.encode()).unwrap(),
        "C must NOT collide with A (otherwise this test is vacuous)"
    );

    let prover = StateSyncProver::new(config(4));
    let req_c = SyncRequest {
        operation: SmtOperation::Membership {
            key,
            payload: c_payload,
        },
        witness: SmtWitness { leaf: c, path },
        public_inputs: PublicInputs {
            old_root,
            new_root: old_root,
            op_kind_tag: 0,
            asset_id: key,
            value_digest: h
                .hash_leaf(
                    &LeafState::Occupied(LeafPayload {
                        sync_state: vec![f(999)],
                        identity_digest: [200u8; 32],
                    })
                    .encode(),
                )
                .unwrap(),
        },
    };
    let res_c = prover.prove_sync_op(&req_c).unwrap();
    assert!(
        !prover.verify_sync_op(&req_c, &res_c),
        "non-colliding wrong payload C must be rejected"
    );
}

// ---------------------------------------------------------------------------
// Item 1: Poseidon2 arithmetization data correctness (independent re-check).
// ---------------------------------------------------------------------------

/// CLEAN: independently recompute the width-16 KoalaBear Poseidon2 permutation
/// from ONLY the public arithmetization data (basis-probed M_E/M_I, the
/// exposed round-constant arrays, and the round counts) via the standard
/// Poseidon2 schedule, and compare to the native p3 permutation on strong
/// near-full-field random inputs. This validates the DATA the circuit consumes
/// (matrices + round constants + round schedule), independently of the
/// compiler crate's own cross-check tests. A wrong matrix, wrong/misordered
/// round constant, or wrong round count would diverge here.
#[test]
fn poseidon2_exposed_schedule_reconstruction_matches_native() {
    let me = p2::external_matrix();
    let mi = p2::internal_matrix();
    let ext_init = p2::external_initial_rc();
    let ext_final = p2::external_final_rc();
    let int_rc = p2::internal_rc();

    let matmul = |m: &[[BaseField; 16]; 16], s: &[BaseField; 16]| -> [BaseField; 16] {
        core::array::from_fn(|z| (0..16).fold(BaseField::ZERO, |acc, x| acc + m[z][x] * s[x]))
    };
    let cube = |x: BaseField| x * x * x;

    let mut rng = Lcg::new(0x0A2D_5EED);
    for _ in 0..64 {
        // Near-full-field random state (< KoalaBear modulus, canonical).
        let input: [BaseField; 16] = core::array::from_fn(|_| f(rng.below(2_000_000_000)));

        // Standard Poseidon2 schedule using the EXPOSED data.
        let mut s = matmul(&me, &input); // initial external linear layer
        // Full external round: AddRC (all lanes), x^3 (all lanes), M_E.
        let external_round = |s: &mut [BaseField; 16], rc_row: &[BaseField; 16]| {
            for (v, rc) in s.iter_mut().zip(rc_row.iter()) {
                *v += *rc;
            }
            for v in s.iter_mut() {
                *v = cube(*v);
            }
            *s = matmul(&me, s);
        };
        for rc_row in &ext_init {
            external_round(&mut s, rc_row);
        }
        for &rc in &int_rc {
            s[0] += rc; // AddRC, lane 0
            s[0] = cube(s[0]); // x^3, lane 0
            s = matmul(&mi, &s); // M_I
        }
        for rc_row in &ext_final {
            external_round(&mut s, rc_row);
        }

        assert_eq!(
            s,
            p2::permute(input),
            "reconstructed Poseidon2 schedule diverges from native"
        );
    }
}

// ---------------------------------------------------------------------------
// R2-1 circuit-intrinsic regression on the Poseidon2 circuit.
// ---------------------------------------------------------------------------

/// CLEAN: R2-1 holds on the Poseidon2 circuit even for a LONG Occupied leaf
/// (encoding beyond the old 16-lane fold). The fold reserves lane 0 for the
/// tag at any encoding length, so the circuit-intrinsic `tag*(tag-2)` residual
/// (tag = leaf_pre[0]) rejects the Occupied tag (1) and the occupied-key
/// non-membership forgery is rejected both circuit-intrinsically and at the
/// facade.
#[test]
fn r2_1_long_occupied_nonmembership_is_rejected() {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: 4,
        ..Default::default()
    };
    let key = AssetId(6);
    // sync_state length 12 => encoding length 22 (beyond the old 16 lanes).
    let long_occ = LeafState::Occupied(LeafPayload {
        sync_state: (0..12).map(|i| f(i as u32 + 1)).collect(),
        identity_digest: [4u8; 32],
    });
    let path = MerklePath {
        siblings: siblings(4),
    };
    let old_root = path.compute_root(&h, &params, key, &long_occ).unwrap();
    let op = SmtOperation::NonMembership { key };
    let pi = PublicInputs {
        old_root,
        new_root: old_root,
        op_kind_tag: 1,
        asset_id: key,
        value_digest: h.hash_leaf(&long_occ.encode()).unwrap(),
    };
    let witness = SmtWitness {
        leaf: long_occ.clone(),
        path,
    };

    // Circuit-intrinsic rejection (tag residual), not just the facade belt.
    let template = Poseidon2Gadget::default().round_template();
    let circuit = compile(
        &params,
        SmtOpKind::NonMembership,
        LayerStrategy::A,
        &template,
    )
    .unwrap();
    let cw = generate_witness(&params, LayerStrategy::A, &circuit, &op, &pi, &witness).unwrap();
    assert!(
        !is_accepting(&cw),
        "circuit must reject occupied-key non-membership for a long leaf (R2-1)"
    );

    // Facade rejects too.
    let prover = StateSyncProver::new(config(4));
    let req = SyncRequest {
        operation: op,
        witness,
        public_inputs: pi,
    };
    let res = prover.prove_sync_op(&req).unwrap();
    assert!(
        !prover.verify_sync_op(&req, &res),
        "facade must reject occupied-key non-membership for a long leaf"
    );
}
