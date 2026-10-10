//! Extended adversarial verification of the leaf collision-resistance fix.
//!
//! The prior audit confirmed a critical soundness break (the wrapping
//! `leaf_fold` made `h_leaf` non-collision-resistant). The repair
//! claims to have closed it with a lossless, length-bound `[tag, len, verbatim,
//! 0-pad]` fold plus a structural encoding bound. This file does NOT trust that
//! claim: it independently RE-CONSTRUCTS collision/forgery attempts and the
//! bound-bypass paths and checks they are actually rejected. The method uses
//! convention (every suspicion is a real attempt, run to a verdict).
//!
//! soundness- and security-first review.
//!
//! Verdicts recorded here (all CLEAN - the fix holds):
//!   1. the former wrap-collision pair now folds apart and its forged
//!      Membership is rejected end-to-end (facade + native);
//!   2. length-shift / zero-suffix / limb-tail encodings do not collide
//!      (the length lane closes that class);
//!   3. an over-bound encoding is rejected UNIFORMLY (hash_leaf, native
//!      compute_root, witness generation, facade) with no lossy hash and no
//!      panic (no DoS);
//!   4. the circuit's multi-block leaf sponge mirrors native `h_leaf` for
//!      2-, 3-, and 4-block pre-images (honest membership verifies);
//!   5. R2-1 (occupied-key non-membership) is still rejected on the new fold.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOpKind,
    SmtOperation, SmtParams, SmtWitness, compile, generate_witness, is_accepting, smt_valid_native,
};
use statesync_gkr::primitives::field::{BaseField, PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{
    DEFAULT_LEAF_MAX_FIELDS, Digest, HashError, HashGadget, Poseidon2Gadget, leaf_fold,
    leaf_pre_width,
};
use statesync_gkr::{StateSyncGkrConfig, StateSyncProver, SyncRequest};

fn f(x: u32) -> BaseField {
    BaseField::from_u32(x)
}

fn config_lmf(depth: u32, leaf_max_fields: u32) -> StateSyncGkrConfig {
    StateSyncGkrConfig {
        smt: SmtParams {
            depth,
            leaf_max_fields,
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

/// An Occupied leaf with a length-16 sync_state (encoding 26, in-bound) whose
/// only varying lanes are positions 0 and 15 - the two rest indices the PRE-FIX
/// wrapping fold summed into pre-image slot 1. Any (s0, s15) with equal sum
/// collided pre-fix; the lossless fold copies them to distinct pre-image lanes.
fn occ16(s0: u32, s15: u32) -> LeafState {
    let mut ss = vec![f(0); 16];
    ss[0] = f(s0);
    ss[15] = f(s15);
    ss[4] = f(55); // fixed, identical "real" middle state
    ss[9] = f(66);
    LeafState::Occupied(LeafPayload {
        sync_state: ss,
        identity_digest: [22u8; 32],
    })
}

fn occ_payload(leaf: &LeafState) -> LeafPayload {
    match leaf {
        LeafState::Occupied(p) => p.clone(),
        _ => unreachable!("occupied leaf"),
    }
}

// ---------------------------------------------------------------------------
// 1. The former wrap-collision pair: folds apart + forgery rejected.
// ---------------------------------------------------------------------------

#[test]
fn former_wrap_collision_pair_folds_apart_and_forgery_rejected() {
    let h = Poseidon2Gadget::default();
    let max = DEFAULT_LEAF_MAX_FIELDS;
    // Independently chosen equal-sum pair (9+0 == 4+5): pre-fix these collided
    // onto one pre-image; post-fix they must fold apart.
    let a = occ16(9, 0);
    let b = occ16(4, 5);
    assert_ne!(a, b);

    let enc_a = a.encode();
    let enc_b = b.encode();
    assert_ne!(
        leaf_fold(&enc_a, max).unwrap(),
        leaf_fold(&enc_b, max).unwrap(),
        "former collision pair must now fold to distinct pre-images"
    );
    assert_ne!(
        h.hash_leaf(&enc_a).unwrap(),
        h.hash_leaf(&enc_b).unwrap(),
        "former collision pair must now hash apart (h_leaf CR restored)"
    );

    // End-to-end: tree commits A; forged Membership of B under A's root fails.
    let params = SmtParams {
        depth: 4,
        ..Default::default()
    };
    let key = AssetId(5);
    let path = MerklePath {
        siblings: siblings(4),
    };
    let old_root = path.compute_root(&h, &params, key, &a).unwrap();
    let prover = StateSyncProver::new(config_lmf(4, max as u32));

    // Sanity: honest membership of A verifies.
    let req_a = SyncRequest {
        operation: SmtOperation::Membership {
            key,
            payload: occ_payload(&a),
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
            value_digest: h.hash_leaf(&enc_a).unwrap(),
        },
    };
    let res_a = prover.prove_sync_op(&req_a).unwrap();
    assert!(prover.verify_sync_op(&req_a, &res_a), "honest A verifies");

    // Forgery: Membership of B under A's old_root.
    let req_b = SyncRequest {
        operation: SmtOperation::Membership {
            key,
            payload: occ_payload(&b),
        },
        witness: SmtWitness {
            leaf: b.clone(),
            path,
        },
        public_inputs: PublicInputs {
            old_root,
            new_root: old_root,
            op_kind_tag: 0,
            asset_id: key,
            value_digest: h.hash_leaf(&enc_b).unwrap(),
        },
    };
    let res_b = prover.prove_sync_op(&req_b).unwrap();
    assert!(
        !prover.verify_sync_op(&req_b, &res_b),
        "forged membership of B must be rejected (no h_leaf collision)"
    );
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
        "native must also reject the forged membership"
    );
}

// ---------------------------------------------------------------------------
// 2. Length-shift / zero-suffix / limb-tail collisions (the length-lane class).
// ---------------------------------------------------------------------------

#[test]
fn length_shift_and_limb_tail_do_not_collide() {
    let h = Poseidon2Gadget::default();
    let max = DEFAULT_LEAF_MAX_FIELDS;

    // (a) Raw zero-suffix: [t, a] vs [t, a, 0] (the classic pad collision).
    let e1 = vec![f(1), f(7)];
    let mut e2 = e1.clone();
    e2.push(f(0));
    assert_ne!(
        leaf_fold(&e1, max).unwrap(),
        leaf_fold(&e2, max).unwrap(),
        "length lane must separate [t,a] from [t,a,0]"
    );

    // (b) Two VALID Occupied leaves whose encodings differ only by a trailing
    // sync field (length shift) collide pre-fix under a shift-fold; post-fix
    // the length lane (11 vs 12) separates them.
    let la = LeafState::Occupied(LeafPayload {
        sync_state: vec![f(7)],
        identity_digest: [3u8; 32],
    });
    let lb = LeafState::Occupied(LeafPayload {
        sync_state: vec![f(7), f(0)],
        identity_digest: [3u8; 32],
    });
    assert_ne!(la.encode().len(), lb.encode().len());
    assert_ne!(
        h.hash_leaf(&la.encode()).unwrap(),
        h.hash_leaf(&lb.encode()).unwrap(),
        "length-shifted valid leaves must hash apart"
    );

    // (c) Limb-tail control: same sync_state, different keccak identity digest
    // (attacker-chosen bytes) -> different verbatim limbs -> distinct hash.
    let lc = LeafState::Occupied(LeafPayload {
        sync_state: vec![f(7)],
        identity_digest: [3u8; 32],
    });
    let ld = LeafState::Occupied(LeafPayload {
        sync_state: vec![f(7)],
        identity_digest: {
            let mut d = [3u8; 32];
            d[31] ^= 0x80; // flip a top bit of the identity digest
            d
        },
    });
    assert_ne!(
        h.hash_leaf(&lc.encode()).unwrap(),
        h.hash_leaf(&ld.encode()).unwrap(),
        "distinct identity digests must hash apart (verbatim limbs)"
    );
}

// ---------------------------------------------------------------------------
// 3. The structural bound: uniform rejection, no lossy hash, no panic.
// ---------------------------------------------------------------------------

#[test]
fn oversized_leaf_rejected_uniformly() {
    let h = Poseidon2Gadget::default();
    let max = DEFAULT_LEAF_MAX_FIELDS;
    // sync_state 22 -> encoding 1 + 22 + 9 = 32 > 31 (the default bound).
    let over = LeafState::Occupied(LeafPayload {
        sync_state: (0..22).map(|i| f(i + 1)).collect(),
        identity_digest: [1u8; 32],
    });
    let enc = over.encode();
    assert!(enc.len() > max, "the leaf is genuinely over the bound");

    // (1) hash_leaf: structural error, never a lossy hash.
    assert!(matches!(
        h.hash_leaf(&enc),
        Err(HashError::EncodingTooLong { .. })
    ));
    // (2) leaf_fold: same structural error.
    assert!(matches!(
        leaf_fold(&enc, max),
        Err(HashError::EncodingTooLong { .. })
    ));

    let params = SmtParams {
        depth: 4,
        ..Default::default()
    };
    let path = MerklePath {
        siblings: siblings(4),
    };
    // (3) native compute_root surfaces the error (no lossy root).
    assert!(
        path.compute_root(&h, &params, AssetId(3), &over).is_err(),
        "native path refuses an over-bound leaf"
    );
    // (4) smt_valid_native surfaces it too.
    let op = SmtOperation::Membership {
        key: AssetId(3),
        payload: occ_payload(&over),
    };
    let wit = SmtWitness {
        leaf: over.clone(),
        path: path.clone(),
    };
    assert!(
        smt_valid_native(&h, &params, &op, &Digest::zero(), &Digest::zero(), &wit).is_err(),
        "native semantics refuse an over-bound leaf"
    );

    // (5) the prover cannot build a witness for it.
    let prover = StateSyncProver::new(config_lmf(4, max as u32));
    let req = SyncRequest {
        operation: op,
        witness: wit,
        public_inputs: PublicInputs {
            old_root: Digest::zero(),
            new_root: Digest::zero(),
            op_kind_tag: 0,
            asset_id: AssetId(3),
            value_digest: Digest::zero(),
        },
    };
    assert!(
        prover.prove_sync_op(&req).is_err(),
        "an over-bound leaf cannot be proven (witness generation refuses it)"
    );

    // (6) a bound too small to admit any Occupied leaf is a config error, not a
    // silent truncation.
    let bad = SmtParams {
        depth: 4,
        leaf_max_fields: 9,
    };
    let template = Poseidon2Gadget::default().round_template();
    assert!(
        compile(&bad, SmtOpKind::Membership, LayerStrategy::A, &template).is_err(),
        "a bound too small to admit any Occupied leaf must be a config error"
    );
}

/// The verifier must reject an over-bound request GRACEFULLY (return false),
/// never panic - an over-bound leaf in a request is an adversary-controlled DoS
/// vector otherwise (resource bound).
#[test]
fn verify_does_not_panic_on_oversized_request() {
    let prover = StateSyncProver::new(config_lmf(4, DEFAULT_LEAF_MAX_FIELDS as u32));
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: 4,
        ..Default::default()
    };
    let key = AssetId(7);
    let path = MerklePath {
        siblings: siblings(4),
    };

    // A genuine in-bound proof, reused only to supply a well-formed result.
    let inb_leaf = LeafState::Occupied(LeafPayload {
        sync_state: vec![f(1), f(2)],
        identity_digest: [4u8; 32],
    });
    let old_root = path.compute_root(&h, &params, key, &inb_leaf).unwrap();
    let inb_req = SyncRequest {
        operation: SmtOperation::Membership {
            key,
            payload: occ_payload(&inb_leaf),
        },
        witness: SmtWitness {
            leaf: inb_leaf.clone(),
            path: path.clone(),
        },
        public_inputs: PublicInputs {
            old_root,
            new_root: old_root,
            op_kind_tag: 0,
            asset_id: key,
            value_digest: h.hash_leaf(&inb_leaf.encode()).unwrap(),
        },
    };
    let inb_res = prover.prove_sync_op(&inb_req).unwrap();

    // A request carrying an OVER-BOUND payload but the same public inputs: the
    // facade's value_digest check (`hash_leaf(..) == Ok(..)`) sees an Err and
    // returns false WITHOUT panicking.
    let over_payload = LeafPayload {
        sync_state: (0..40).map(|i| f(i + 1)).collect(), // encoding 50 > 31
        identity_digest: [9u8; 32],
    };
    let dos_req = SyncRequest {
        operation: SmtOperation::Membership {
            key,
            payload: over_payload,
        },
        witness: inb_req.witness.clone(),
        public_inputs: inb_res.public_inputs.clone(),
    };
    assert!(
        !prover.verify_sync_op(&dos_req, &inb_res),
        "verify must reject an over-bound request gracefully (no panic)"
    );
}

// ---------------------------------------------------------------------------
// 4. Circuit multi-block leaf sponge mirrors native across block counts.
// ---------------------------------------------------------------------------

/// The leaf pre-image width (hence the number of chained sponge permutations
/// in the circuit) scales with `leaf_max_fields`. An honest Membership must
/// verify for 2-, 3-, and 4-block pre-images: if the circuit's multi-block
/// sponge diverged from native `h_leaf` at any block, `acc_0` would mismatch
/// and the honest proof would FAIL. So these passing roundtrips pin
/// circuit == native across the block-count boundaries.
#[test]
fn honest_membership_verifies_for_each_leaf_block_count() {
    // (leaf_max_fields, leaf_pre_width, blocks): 10->16->2, 20->24->3, 31->32->4.
    for &lmf in &[10u32, 20, 31] {
        let blocks = leaf_pre_width(lmf as usize) / 8;
        assert!(blocks >= 2, "min viable is 2 blocks");
        let h = Poseidon2Gadget::new(lmf as usize);
        let params = SmtParams {
            depth: 4,
            leaf_max_fields: lmf,
        };
        let key = AssetId(3);
        // Occupied encoding = 1 + sync_len + 9 <= lmf  =>  sync_len <= lmf - 10.
        let sync_len = (lmf as usize - 10).min(3);
        let leaf = LeafState::Occupied(LeafPayload {
            sync_state: (0..sync_len).map(|i| f(i as u32 + 1)).collect(),
            identity_digest: [5u8; 32],
        });
        let path = MerklePath {
            siblings: siblings(4),
        };
        let old_root = path.compute_root(&h, &params, key, &leaf).unwrap();
        let prover = StateSyncProver::new(config_lmf(4, lmf));
        let req = SyncRequest {
            operation: SmtOperation::Membership {
                key,
                payload: occ_payload(&leaf),
            },
            witness: SmtWitness {
                leaf: leaf.clone(),
                path,
            },
            public_inputs: PublicInputs {
                old_root,
                new_root: old_root,
                op_kind_tag: 0,
                asset_id: key,
                value_digest: h.hash_leaf(&leaf.encode()).unwrap(),
            },
        };
        let res = prover.prove_sync_op(&req).unwrap();
        assert!(
            prover.verify_sync_op(&req, &res),
            "membership verifies for {blocks}-block leaf sponge (lmf {lmf})"
        );
    }
}

// ---------------------------------------------------------------------------
// 5. R2-1 regression on the new fold layout.
// ---------------------------------------------------------------------------

/// R2-1: an occupied-key non-membership must be rejected circuit-intrinsically.
/// The new fold still reserves lane 0 for the tag (`leaf_pre[0] == tag`), so
/// the circuit's `tag*(tag-2)` residual rejects the Occupied tag (1). Uses an
/// in-bound "long" occupied leaf (encoding 22) to exercise the multi-block
/// pre-image on the new layout.
#[test]
fn r2_1_occupied_nonmembership_rejected_on_new_fold() {
    let h = Poseidon2Gadget::default();
    let max = DEFAULT_LEAF_MAX_FIELDS;
    let params = SmtParams {
        depth: 4,
        ..Default::default()
    };
    let key = AssetId(6);
    let long_occ = LeafState::Occupied(LeafPayload {
        sync_state: (0..12).map(|i| f(i as u32 + 1)).collect(), // encoding 22, in-bound
        identity_digest: [4u8; 32],
    });
    // The tag lane is preserved in the new fold.
    assert_eq!(
        leaf_fold(&long_occ.encode(), max).unwrap()[0],
        f(1),
        "leaf_pre[0] == Occupied tag (R2-1 domain separation preserved)"
    );

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
        leaf: long_occ,
        path,
    };

    // Circuit-intrinsic rejection (the tag residual), not just the facade belt.
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
        "circuit must reject occupied-key non-membership (R2-1 tag residual)"
    );

    // Facade rejects too.
    let prover = StateSyncProver::new(config_lmf(4, max as u32));
    let req = SyncRequest {
        operation: op,
        witness,
        public_inputs: pi,
    };
    let res = prover.prove_sync_op(&req).unwrap();
    assert!(
        !prover.verify_sync_op(&req, &res),
        "facade must reject occupied-key non-membership"
    );
}
