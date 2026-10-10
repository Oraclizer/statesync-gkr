//! Extended adversarial verification of the compiler soundness repairs.
//!
//! Fresh-eyes check that the three round-1 fixes actually closed the gaps
//! circuit-intrinsically (the requirement that "soundness properties
//! are enforced INSIDE THE CIRCUIT, not via facade checks", because
//! facade-only breaks under future succinct/PCS/Module-4 verifiers).
//!
//! Round-2 found R2-1 [HIGH]: the NonMembership tag residual was vacuous for
//! long leaves (the original `leaf_fold` wrapped payload into the tag slot).
//! FIXED by `leaf_fold` domain separation (slot 0 = tag alone). These tests
//! pin the fix and add a CIRCUIT-LEVEL grid (`is_accepting` x op-kind x leaf
//! length) - the coverage the composition battery structurally lacked.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOpKind,
    SmtOperation, SmtParams, SmtWitness, compile, generate_witness, is_accepting,
};
use statesync_gkr::primitives::field::{BaseField, PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{
    DEFAULT_LEAF_MAX_FIELDS, Digest, HashGadget, Poseidon2Gadget, leaf_fold,
};
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

/// A genuinely OCCUPIED leaf crafted so that the PRE-R2-1 `leaf_fold`
/// (`s[j % 16]` wrap) cancelled the Occupied tag (1) down to an Empty tag (0):
/// encoding = [1] ++ sync_state(16) ++ keccak(9 limbs), length 26 > 16, so the
/// old fold gave `s[0] = 1 + sync_state[15]`; `sync_state[15] = -1` made it 0.
/// Kept verbatim as the R2-1 regression leaf. (After the collision-resistance fix the fold is
/// lossless - no wrapping at all - so this is simply a long Occupied leaf; its
/// tag lane is 1 unconditionally.)
fn wrapped_occupied() -> LeafState {
    let mut sync = vec![f(1); 16];
    sync[15] = BaseField::ZERO - BaseField::ONE; // -1
    LeafState::Occupied(LeafPayload {
        sync_state: sync,
        identity_digest: [7u8; 32],
    })
}

/// R2-1 regression (confirmed then fixed, circuit-intrinsic
/// incompleteness): the round-1 NonMembership fix's circuit residual
/// `tag*(tag-2) = 0` on `leaf_pre[0]` was VACUOUS for any leaf whose encoding
/// exceeded 16 field elements, because the original `leaf_fold` (`s[j % 16]`)
/// wrapped later payload words back into `leaf_pre[0]`. A genuinely Occupied
/// leaf could then present `leaf_pre[0] in {0,2}` and satisfy the residual, so
/// the circuit alone accepted an occupied leaf as non-membership - the
/// circuit-intrinsic guarantee did not hold for long leaves (composed v0.1
/// stayed sound only via the facade value_digest canonicalization).
///
/// FIXED (option A, `leaf_fold` domain separation): slot 0 now carries the
/// tag alone and the payload folds into slots 1.., so `leaf_pre[0] == tag`
/// for ANY encoding length. The crafted long Occupied leaf below now folds to
/// `leaf_pre[0] == 1` and the CIRCUIT ALONE rejects it. This test pins the
/// fix: the mechanism (tag preserved) and both the circuit-only and composed
/// rejections.
#[test]
fn r2_nonmembership_tag_residual_vacuous_for_long_leaf() {
    let h = Poseidon2Gadget::default();
    let depth = 4usize;
    let params = SmtParams {
        depth: depth as u32,
        ..Default::default()
    };
    let key = AssetId(5);
    let occ = wrapped_occupied();

    // Mechanism (post-fix): domain separation keeps the tag in slot 0 even
    // for this long leaf, so leaf_pre[0] == 1 (Occupied), NOT 0. Before the
    // fix the wrap made it 0; now the tag residual is genuine.
    let pre = leaf_fold(&occ.encode(), DEFAULT_LEAF_MAX_FIELDS).unwrap();
    assert_eq!(
        pre[0],
        BaseField::ONE,
        "domain-separated leaf_fold preserves the Occupied tag (1) in slot 0 \
         even for a long leaf (pre-fix this wrapped to 0)"
    );

    // A real tree where `key` IS occupied by this crafted leaf.
    let path = MerklePath {
        siblings: siblings(depth),
    };
    let old_root = path.compute_root(&h, &params, key, &occ).unwrap();
    let value_digest = h.hash_leaf(&occ.encode()).unwrap();

    let request = SyncRequest {
        operation: SmtOperation::NonMembership { key },
        witness: SmtWitness {
            leaf: occ.clone(),
            path,
        },
        public_inputs: PublicInputs {
            old_root,
            new_root: old_root,
            op_kind_tag: 1,
            asset_id: key,
            value_digest,
        },
    };

    // (a) THE CIRCUIT ALONE now REJECTS the occupied leaf as non-membership:
    // the tag residual is genuine (leaf_pre[0] == 1). This is the
    // required circuit-intrinsic guarantee, now holding for long leaves.
    let template = Poseidon2Gadget::default().round_template();
    let circuit = compile(
        &params,
        SmtOpKind::NonMembership,
        LayerStrategy::A,
        &template,
    )
    .unwrap();
    let cw = generate_witness(
        &params,
        LayerStrategy::A,
        &circuit,
        &request.operation,
        &request.public_inputs,
        &request.witness,
    )
    .unwrap();
    assert!(
        !is_accepting(&cw),
        "R2-1 fix: the circuit alone must REJECT an OCCUPIED long leaf as \
         non-membership (the domain-separated tag residual is now genuine)"
    );

    // (b) The COMPOSED verifier also rejects (belt-and-suspenders: value_digest
    // canonicalization + circuit tag residual + r_vd binding).
    let prover = StateSyncProver::new(config(depth as u32));
    let result = prover.prove_sync_op(&request).unwrap();
    assert!(
        !prover.verify_sync_op(&request, &result),
        "composed verify_sync_op must reject the occupied-leaf non-membership"
    );
}

/// GUARD: the short-leaf case the round-1 repro used is caught by the circuit
/// (leaf_pre[0] == 1 == Occupied tag). Before the R2-1 fix this held only for
/// encoding <= 16; after the domain-separation fix it holds at every length
/// (see the leaf-length grid below), so short and long now behave identically.
#[test]
fn r2_guard_short_occupied_leaf_is_caught_by_circuit() {
    let h = Poseidon2Gadget::default();
    let depth = 4usize;
    let params = SmtParams {
        depth: depth as u32,
        ..Default::default()
    };
    let key = AssetId(5);
    // Short Occupied leaf: encode length 1 + 1 + 9 = 11 <= 16, no wrap.
    let occ = LeafState::Occupied(LeafPayload {
        sync_state: vec![f(42)],
        identity_digest: [9u8; 32],
    });
    let pre = leaf_fold(&occ.encode(), DEFAULT_LEAF_MAX_FIELDS).unwrap();
    assert_eq!(
        pre[0],
        BaseField::ONE,
        "short Occupied leaf: leaf_pre[0] == 1"
    );

    let path = MerklePath {
        siblings: siblings(depth),
    };
    let old_root = path.compute_root(&h, &params, key, &occ).unwrap();
    let value_digest = h.hash_leaf(&occ.encode()).unwrap();
    let request = SyncRequest {
        operation: SmtOperation::NonMembership { key },
        witness: SmtWitness { leaf: occ, path },
        public_inputs: PublicInputs {
            old_root,
            new_root: old_root,
            op_kind_tag: 1,
            asset_id: key,
            value_digest,
        },
    };
    let template = Poseidon2Gadget::default().round_template();
    let circuit = compile(
        &params,
        SmtOpKind::NonMembership,
        LayerStrategy::A,
        &template,
    )
    .unwrap();
    let cw = generate_witness(
        &params,
        LayerStrategy::A,
        &circuit,
        &request.operation,
        &request.public_inputs,
        &request.witness,
    )
    .unwrap();
    assert!(
        !is_accepting(&cw),
        "short Occupied leaf: the circuit tag residual DOES reject (tag==1)"
    );
}

// ---------------------------------------------------------------------------
// [R2-1 follow-up] Circuit-LEVEL equivalence grid.
//
// The composition battery (e2e) only checks `verify_sync_op <=> smt_valid_native`
// on short leaves, so it structurally missed R2-1 (a circuit-only, long-leaf
// gap). These tests drive `is_accepting` on the compiled circuit directly, with
// `value_digest = h_leaf(witness.leaf)` so the r_vd/root bindings pass and the
// tag residual is ISOLATED - across op-kind and leaf length.

/// Compile NonMembership, feed a self-consistent witness for `leaf`
/// (value_digest = h_leaf(leaf)), and return whether the circuit alone accepts.
fn nonmembership_circuit_accepts(depth: usize, key: u64, leaf: LeafState) -> bool {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: depth as u32,
        ..Default::default()
    };
    let key = AssetId(key);
    let path = MerklePath {
        siblings: siblings(depth),
    };
    let old_root = path.compute_root(&h, &params, key, &leaf).unwrap();
    let value_digest = h.hash_leaf(&leaf.encode()).unwrap();
    let op = SmtOperation::NonMembership { key };
    let pi = PublicInputs {
        old_root,
        new_root: old_root,
        op_kind_tag: 1,
        asset_id: key,
        value_digest,
    };
    let witness = SmtWitness { leaf, path };
    let template = Poseidon2Gadget::default().round_template();
    let circuit = compile(
        &params,
        SmtOpKind::NonMembership,
        LayerStrategy::A,
        &template,
    )
    .unwrap();
    let cw = generate_witness(&params, LayerStrategy::A, &circuit, &op, &pi, &witness).unwrap();
    is_accepting(&cw)
}

fn occupied_len(n: usize) -> LeafState {
    LeafState::Occupied(LeafPayload {
        sync_state: (0..n).map(|i| f(i as u32 + 3)).collect(),
        identity_digest: [5u8; 32],
    })
}

#[test]
fn r2_circuit_intrinsic_nonmembership_leaf_length_grid() {
    let (depth, key) = (4usize, 5u64);

    // Valid non-members: the circuit alone accepts (tag in {0, 2}).
    assert!(nonmembership_circuit_accepts(depth, key, LeafState::Empty));
    assert!(nonmembership_circuit_accepts(
        depth,
        key,
        LeafState::Tombstone
    ));

    // Occupied leaves: the circuit ALONE must reject (tag == 1), at EVERY
    // in-bound encoding length - short, the old 16-lane fold boundary, beyond
    // it, and the exact `leaf_max_fields` bound (encoding = len + 10 <= 31).
    // This is the grid that structurally catches R2-1.
    assert!(!nonmembership_circuit_accepts(depth, key, occupied_len(1)));
    for len in [7usize, 15, 16, 20, 21] {
        assert!(
            !nonmembership_circuit_accepts(depth, key, occupied_len(len)),
            "occupied sync_state len {len} must be rejected as non-membership \
             by the circuit alone (tag-lane residual)"
        );
    }
    // The specific R2-1 crafted leaf (payload cancels the tag under the OLD
    // fold) is also rejected now.
    assert!(!nonmembership_circuit_accepts(
        depth,
        key,
        wrapped_occupied()
    ));
}

/// Compile Membership and drive the circuit with an explicit value_digest, to
/// pin the leaf<->value_digest binding (r_vd) at the circuit level.
fn membership_circuit_accepts(
    depth: usize,
    key: u64,
    witness_leaf: LeafState,
    value_digest: Digest<BaseField>,
) -> bool {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: depth as u32,
        ..Default::default()
    };
    let key = AssetId(key);
    let path = MerklePath {
        siblings: siblings(depth),
    };
    let old_root = path.compute_root(&h, &params, key, &witness_leaf).unwrap();
    // Membership op payload is irrelevant to the circuit (it reads leaf_pre +
    // value_digest); use the witness leaf's payload for a well-formed op.
    let payload = match &witness_leaf {
        LeafState::Occupied(p) => p.clone(),
        _ => LeafPayload {
            sync_state: vec![],
            identity_digest: [0u8; 32],
        },
    };
    let op = SmtOperation::Membership { key, payload };
    let pi = PublicInputs {
        old_root,
        new_root: old_root,
        op_kind_tag: 0,
        asset_id: key,
        value_digest,
    };
    let witness = SmtWitness {
        leaf: witness_leaf,
        path,
    };
    let template = Poseidon2Gadget::default().round_template();
    let circuit = compile(&params, SmtOpKind::Membership, LayerStrategy::A, &template).unwrap();
    let cw = generate_witness(&params, LayerStrategy::A, &circuit, &op, &pi, &witness).unwrap();
    is_accepting(&cw)
}

#[test]
fn r2_circuit_membership_value_digest_binding() {
    let (depth, key) = (4usize, 5u64);
    let h = Poseidon2Gadget::default();
    let leaf = occupied_len(3);
    let matching_vd = h.hash_leaf(&leaf.encode()).unwrap();
    // Self-consistent value_digest: accepts.
    assert!(membership_circuit_accepts(
        depth,
        key,
        leaf.clone(),
        matching_vd
    ));
    // Decoupled value_digest (a DIFFERENT leaf's hash): the r_vd residual
    // rejects. `acc_0 = h_leaf(witness.leaf) != value_digest`.
    let other_vd = h.hash_leaf(&occupied_len(9).encode()).unwrap();
    assert!(!membership_circuit_accepts(depth, key, leaf, other_vd));
    // The longest in-bound leaf (encoding = exactly leaf_max_fields) still
    // binds correctly.
    let long = occupied_len(21);
    let long_vd = h.hash_leaf(&long.encode()).unwrap();
    assert!(membership_circuit_accepts(depth, key, long, long_vd));
}
