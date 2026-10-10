//! Adversarial compiler-soundness regression tests.
//!
//! These tests are executable evidence for the independent diagnostic review. The
//! three findings (NonMembership of an occupied key, Update ignoring
//! `witness.leaf`, non-boolean key-bit selector) were CONFIRMED here against
//! the original core, then fixed by the leaf-tag repair; each `bug_*` test now asserts
//! the FIXED (rejecting) behaviour and stands as a regression pin. The finding
//! doc comments below are kept as the historical diagnosis.
//! Naming convention: `bug_*` = a repro that pinned a defect (now the fix);
//! `guard_*` = confirms an existing defence holds (bounds the finding, proves
//! it is not vacuous).

#![allow(clippy::unwrap_used, clippy::expect_used)]

use statesync_gkr::compiler::{
    AssetId, InputLayout, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs,
    SmtOpKind, SmtOperation, SmtParams, SmtWitness, compile, is_accepting, smt_valid_native,
};
use statesync_gkr::gkr::evaluate_circuit;
use statesync_gkr::primitives::field::{BaseField, PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{
    DEFAULT_LEAF_MAX_FIELDS, DIGEST_WIDTH, Digest, HashGadget, Poseidon2Gadget, leaf_pre_width,
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

/// Critical regression: a NonMembership proof is
/// accepted for a key that is genuinely OCCUPIED.
///
/// `smt_valid_native` requires the authenticated leaf to be Empty or
/// Tombstone for NonMembership (smt.rs, `leaf_ok`). Neither the compiled
/// circuit (compile.rs NonMembership path has no leaf-tag constraint) nor
/// the facade (`verify_sync_op`) enforces this. Worse, the facade recomputes
/// `expected_vd` for NonMembership from `request.witness.leaf` itself, so the
/// value_digest check is a tautology and binds nothing.
///
/// An attacker holding a real Occupied leaf with a valid Merkle path can
/// therefore forge a proof that the key is ABSENT.
///
/// This broke Theorem A (`circuit_accept <=> smt_valid`) in the forward
/// direction and was independent of ArithHash strength (a pure logic gap).
/// Fixed by the leaf-tag repair (circuit leaf-tag residual + canonical
/// value_digest); this test now pins the rejection.
#[test]
fn bug_nonmembership_of_occupied_key_is_falsely_accepted() {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: 4,
        ..Default::default()
    };
    let key = AssetId(5);

    // A REAL occupied leaf sitting at `key` with a valid authentication path.
    let payload = LeafPayload {
        sync_state: vec![f(42), f(7)],
        identity_digest: [9u8; 32],
    };
    let occupied = LeafState::Occupied(payload);
    let path = MerklePath {
        siblings: siblings(4),
    };
    // The root of a tree in which `key` IS occupied.
    let old_root = path.compute_root(&h, &params, key, &occupied).unwrap();

    // Forge a NonMembership claim for that same (occupied) key. The prover
    // sets value_digest from its own witness leaf (the tautology).
    let value_digest = h.hash_leaf(&occupied.encode()).unwrap();
    let request = SyncRequest {
        operation: SmtOperation::NonMembership { key },
        witness: SmtWitness {
            leaf: occupied.clone(),
            path,
        },
        public_inputs: PublicInputs {
            old_root,
            new_root: old_root,
            op_kind_tag: 1, // NonMembership
            asset_id: key,
            value_digest,
        },
    };

    // Ground truth: the native meaning standard REJECTS this (leaf is
    // Occupied, not Empty/Tombstone).
    let native = smt_valid_native(
        &h,
        &params,
        &request.operation,
        &request.public_inputs.old_root,
        &request.public_inputs.new_root,
        &request.witness,
    )
    .unwrap();
    assert!(
        !native,
        "native semantics must reject non-membership of an occupied key"
    );

    // The composed prover/verifier, however, ACCEPTS the forgery.
    let prover = StateSyncProver::new(config(4));
    let result = prover.prove_sync_op(&request).unwrap();
    let accepted = prover.verify_sync_op(&request, &result);

    // Fixed: the circuit leaf-tag residual `tag*(tag-2)` plus
    // the canonical value_digest binding now reject the forgery. Regression pin.
    assert!(
        !accepted,
        "regression: NonMembership of an occupied key must be REJECTED \
         (circuit tag*(tag-2) residual + canonical value_digest binding)"
    );
}

/// Spec-alignment regression: the composed
/// verifier ignores `witness.leaf` for Update, but `smt_valid_native`
/// requires `witness.leaf == old_leaf`. So a proof whose `witness.leaf` does
/// not match the operation's `old_leaf` still verifies while the native
/// meaning standard rejects it - a second `circuit_accept <=> smt_valid`
/// misalignment (same root cause as Finding 1: the composed acceptance was
/// never cross-checked clause-by-clause against `smt_valid_native`).
///
/// Impact is benign in isolation (the transition old_leaf -> new_leaf that
/// IS proved remains valid, since the circuit reads `op.old_leaf`), but it
/// breaks the Theorem-A equivalence the FV track will try to discharge. Fix:
/// either drop the redundant `witness.leaf` clause from the Update native
/// semantics, or have the facade check `witness.leaf == op.old_leaf`.
#[test]
fn bug_update_accepts_witness_leaf_mismatching_old_leaf() {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: 4,
        ..Default::default()
    };
    let key = AssetId(9);
    let payload = LeafPayload {
        sync_state: vec![f(100)],
        identity_digest: [3u8; 32],
    };
    let old_leaf = LeafState::Occupied(payload);
    let new_leaf = LeafState::Tombstone;
    let path = MerklePath {
        siblings: siblings(4),
    };
    let old_root = path.compute_root(&h, &params, key, &old_leaf).unwrap();
    let new_root = path.compute_root(&h, &params, key, &new_leaf).unwrap();
    let value_digest = h.hash_leaf(&new_leaf.encode()).unwrap();

    // A witness whose `leaf` field is deliberately WRONG (not == old_leaf).
    let bogus_witness_leaf = LeafState::Empty;
    let request = SyncRequest {
        operation: SmtOperation::Update {
            key,
            old_leaf: old_leaf.clone(),
            new_leaf,
        },
        witness: SmtWitness {
            leaf: bogus_witness_leaf,
            path,
        },
        public_inputs: PublicInputs {
            old_root,
            new_root,
            op_kind_tag: 2,
            asset_id: key,
            value_digest,
        },
    };

    // Native rejects (witness.leaf != old_leaf).
    let native = smt_valid_native(
        &h,
        &params,
        &request.operation,
        &old_root,
        &new_root,
        &request.witness,
    )
    .unwrap();
    assert!(!native, "native rejects a witness.leaf that != old_leaf");

    // Fixed: the facade reconciles the sealed native clause by
    // checking `witness.leaf == op.old_leaf`. Regression pin.
    let prover = StateSyncProver::new(config(4));
    let result = prover.prove_sync_op(&request).unwrap();
    assert!(
        !prover.verify_sync_op(&request, &result),
        "regression: an Update whose witness.leaf != old_leaf must be REJECTED \
         (facade reconciles the sealed native clause)"
    );
}

/// Latent defense-in-depth regression: the circuit never
/// constrains a key-bit selector `s` to be boolean. The level mux is
/// `left = acc + s*(sib-acc)`, `right = sib + s*(acc-sib)`; for `s not in
/// {0,1}` this is an arbitrary affine blend, so a self-consistent
/// accumulator chain built with `s = 2` still makes every residual zero and
/// the circuit ACCEPTS - a "path" no boolean key could ever produce.
///
/// NOT exploitable in the composed v0.1 system: `build_input_vector`
/// reconstructs the key bits as literal `(asset_id >> l) & 1`, so `s` is
/// always boolean and the input-MLE discharge binds it. This finding is
/// therefore latent: it becomes live the moment key bits stop being
/// reconstructed from the public key (a succinct/PCS verifier that reads
/// them from the proof, or any witness-sourced selector). It also means
/// Theorem A does NOT hold circuit-intrinsically over raw input vectors.
///
/// Fix (cheap defense-in-depth): emit `s*(s-1)` as an extra output residual
/// per key bit so booleanity is enforced by the circuit itself.
///
/// This test constructs the raw input vector directly (bypassing the
/// safe reconstruction) to exhibit the circuit-level gap.
#[test]
fn bug_circuit_accepts_nonboolean_keybit_latent() {
    let depth = 2usize;
    let params = SmtParams {
        depth: depth as u32,
        ..Default::default()
    };
    let template = Poseidon2Gadget::default().round_template();
    let circuit = compile(&params, SmtOpKind::Membership, LayerStrategy::A, &template).unwrap();
    let layout = InputLayout::new(SmtOpKind::Membership, depth, DEFAULT_LEAF_MAX_FIELDS);

    // Non-boolean selector at every level.
    let s = BaseField::from_u32(2);
    // s = 2 mux: left = 2*sib - acc, right = 2*acc - sib.
    let mux = |acc: &[BaseField; DIGEST_WIDTH], sib: &[BaseField; DIGEST_WIDTH]| {
        let mut left = [BaseField::ZERO; DIGEST_WIDTH];
        let mut right = [BaseField::ZERO; DIGEST_WIDTH];
        for i in 0..DIGEST_WIDTH {
            left[i] = acc[i] + s * (sib[i] - acc[i]);
            right[i] = sib[i] + s * (acc[i] - sib[i]);
        }
        (left, right)
    };

    // Build a self-consistent accumulator chain under the s=2 mux, using the
    // production Poseidon2 gadget (the same hash the circuit now mirrors), so
    // the leaf/node residuals vanish and the non-boolean key-bit residual is
    // isolated as the sole cause of rejection.
    let h = Poseidon2Gadget::default();
    let mut pre = vec![BaseField::ZERO; leaf_pre_width(DEFAULT_LEAF_MAX_FIELDS)];
    for (j, p) in pre.iter_mut().enumerate() {
        *p = f(2 * j as u32 + 1);
    }
    let acc0 = h.hash_leaf_pre(&pre).0;
    let sib0 = [f(3); DIGEST_WIDTH];
    let (l0, r0) = mux(&acc0, &sib0);
    let acc1 = h.compress(&Digest(l0), &Digest(r0)).0;
    let sib1 = [f(5); DIGEST_WIDTH];
    let (l1, r1) = mux(&acc1, &sib1);
    let acc2 = h.compress(&Digest(l1), &Digest(r1)).0;

    // Lay the raw input vector out per the frozen InputLayout.
    let mut inputs = vec![BaseField::ZERO; 1usize << circuit.input_width_bits];
    let put = |inputs: &mut [BaseField], base: u32, d: &[BaseField; DIGEST_WIDTH]| {
        for (i, &v) in d.iter().enumerate() {
            inputs[base as usize + i] = v;
        }
    };
    for (j, &v) in pre.iter().enumerate() {
        inputs[layout.leaf_pre() as usize + j] = v;
    }
    put(&mut inputs, layout.acc(0), &acc0);
    put(&mut inputs, layout.acc(1), &acc1);
    put(&mut inputs, layout.acc(2), &acc2);
    put(&mut inputs, layout.sib(0), &sib0);
    put(&mut inputs, layout.sib(1), &sib1);
    inputs[layout.key_bit(0) as usize] = s; // non-boolean
    inputs[layout.key_bit(1) as usize] = s; // non-boolean
    put(&mut inputs, layout.root(), &acc2); // root = top accumulator
    put(&mut inputs, layout.value_digest(), &acc0); // vd = leaf pre-hash

    // Fixed: the circuit now emits an `s*(s-1)` residual per key
    // bit, so a non-boolean selector no longer accepts. Regression pin.
    let cw = evaluate_circuit(&circuit, &inputs).unwrap();
    assert!(
        !is_accepting(&cw),
        "regression: the circuit must REJECT a non-boolean key-bit selector \
         (s*(s-1) residual enforces booleanity circuit-intrinsically)"
    );
}

/// GUARD for Finding 1: the finding is NOT vacuous. A genuinely-empty
/// non-membership still verifies (completeness preserved), so the fix must
/// reject only the Occupied case, not break honest non-membership.
#[test]
fn guard_genuine_nonmembership_still_verifies() {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: 4,
        ..Default::default()
    };
    let key = AssetId(6);
    let empty = LeafState::Empty;
    let path = MerklePath {
        siblings: siblings(4),
    };
    let old_root = path.compute_root(&h, &params, key, &empty).unwrap();
    let value_digest = h.hash_leaf(&empty.encode()).unwrap();
    let request = SyncRequest {
        operation: SmtOperation::NonMembership { key },
        witness: SmtWitness { leaf: empty, path },
        public_inputs: PublicInputs {
            old_root,
            new_root: old_root,
            op_kind_tag: 1,
            asset_id: key,
            value_digest,
        },
    };
    let prover = StateSyncProver::new(config(4));
    let result = prover.prove_sync_op(&request).unwrap();
    assert!(
        prover.verify_sync_op(&request, &result),
        "honest empty-slot non-membership must verify"
    );
}
