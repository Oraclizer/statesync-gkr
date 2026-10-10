//! End-to-end pipeline tests: compile -> generate_witness -> gkr::prove ->
//! verify (transcript replay + input-claim discharge). This exercises the
//! whole v0.1 core on the in-circuit Poseidon2 hash.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use statesync_gkr::batching::{BatchProver, WitnessQueue};
use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtParams,
};
use statesync_gkr::compiler::{SmtOperation, SmtWitness, smt_valid_native};
use statesync_gkr::primitives::field::{BaseField, PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{Digest, HashGadget, Poseidon2Gadget};
use statesync_gkr::{StateSyncGkrConfig, StateSyncProver, SyncRequest, SyncResult};
use std::time::Duration;

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

/// Build a valid Membership request over a depth-`d` tree.
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

#[test]
fn membership_end_to_end_roundtrip() {
    let prover = StateSyncProver::new(config(4));
    let request = membership_request(4, 5);
    let result = prover.prove_sync_op(&request).unwrap();
    assert!(prover.verify_sync_op(&request, &result));
}

#[test]
fn rejects_tampered_proof() {
    let prover = StateSyncProver::new(config(4));
    let request = membership_request(4, 5);
    let mut result = prover.prove_sync_op(&request).unwrap();
    // Corrupt a claimed layer evaluation.
    result.proof.layer_proofs[0].eval_x += statesync_gkr::primitives::ChallengeField::from(f(1));
    assert!(!prover.verify_sync_op(&request, &result));
}

#[test]
fn rejects_wrong_witness_at_discharge() {
    let prover = StateSyncProver::new(config(4));
    let request = membership_request(4, 5);
    let result = prover.prove_sync_op(&request).unwrap();
    // A different witness (perturbed sibling) with the SAME proof must fail:
    // the reconstructed input MLE no longer matches the residual claim.
    let mut wrong = request.clone();
    wrong.witness.path.siblings[1] = Digest([f(999); 8]);
    assert!(!prover.verify_sync_op(&wrong, &result));
}

#[test]
fn rejects_tampered_public_input() {
    let prover = StateSyncProver::new(config(4));
    let request = membership_request(4, 5);
    let result = prover.prove_sync_op(&request).unwrap();
    // Flip the public root in the request; the result still carries the
    // original public inputs, so the consistency check trips.
    let mut tampered = request.clone();
    tampered.public_inputs.old_root = Digest([f(123); 8]);
    tampered.public_inputs.new_root = Digest([f(123); 8]);
    assert!(!prover.verify_sync_op(&tampered, &result));
}

#[test]
fn update_end_to_end_roundtrip() {
    let h = Poseidon2Gadget::default();
    let depth = 4usize;
    let params = SmtParams {
        depth: depth as u32,
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
        siblings: siblings(depth),
    };
    let old_root = path.compute_root(&h, &params, key, &old_leaf).unwrap();
    let new_root = path.compute_root(&h, &params, key, &new_leaf).unwrap();
    let value_digest = h.hash_leaf(&new_leaf.encode()).unwrap();
    let request = SyncRequest {
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
    };
    let prover = StateSyncProver::new(config(depth as u32));
    let result = prover.prove_sync_op(&request).unwrap();
    assert!(prover.verify_sync_op(&request, &result));
}

#[test]
fn different_keys_share_one_circuit_kind() {
    // Two different keys of the same kind both prove/verify - the compiled
    // circuit is key-agnostic (the key-bit mux), the batching premise.
    let prover = StateSyncProver::new(config(5));
    for key in [3u64, 20, 17] {
        let request = membership_request(5, key);
        let result = prover.prove_sync_op(&request).unwrap();
        assert!(prover.verify_sync_op(&request, &result), "key {key}");
    }
}

#[test]
fn batched_membership_proves_and_verifies() {
    // Module 3 structure end-to-end: enqueue several same-kind jobs, drain and
    // prove them as one batch over the shared circuit, then verify each proof.
    let prover = StateSyncProver::new(config(4));
    let requests: Vec<SyncRequest> = [3u64, 5, 8]
        .iter()
        .map(|&k| membership_request(4, k))
        .collect();

    let mut queue = WitnessQueue::new();
    for r in &requests {
        queue.push(prover.make_job(r).unwrap());
    }

    let mut batch_prover = BatchProver::default();
    let results = batch_prover.prove_round(&mut queue, Duration::from_millis(200), |kind, jobs| {
        prover.prove_batch(kind, jobs)
    });

    // All three are Membership: one batch, three proofs in FIFO order.
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].proofs.len(), 3);
    assert!(queue.is_empty());

    for (req, proof) in requests.iter().zip(&results[0].proofs) {
        let result = SyncResult {
            public_inputs: req.public_inputs.clone(),
            proof: proof.clone(),
        };
        assert!(prover.verify_sync_op(req, &result));
    }
}

// ---------------------------------------------------------------------------
// Composition-level equivalence battery.
//
// The root-cause test the two confirmed soundness bugs slipped through:
// `verify_sync_op` must accept a request IFF `smt_valid_native` holds for the
// same operation, roots and witness - checked across all three op kinds with
// valid AND adversarial witnesses. This is exactly the R1 refinement
// obligation (composed acceptance <=> the native meaning standard) made
// executable, and it fails on both original regressions before the repairs.

fn nonmembership_request(depth: usize, key: u64, leaf: LeafState) -> SyncRequest {
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

fn update_request(
    depth: usize,
    key: u64,
    old_leaf: LeafState,
    new_leaf: LeafState,
    witness_leaf: LeafState,
) -> SyncRequest {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: depth as u32,
        ..Default::default()
    };
    let key = AssetId(key);
    let path = MerklePath {
        siblings: siblings(depth),
    };
    let old_root = path.compute_root(&h, &params, key, &old_leaf).unwrap();
    let new_root = path.compute_root(&h, &params, key, &new_leaf).unwrap();
    let value_digest = h.hash_leaf(&new_leaf.encode()).unwrap();
    SyncRequest {
        operation: SmtOperation::Update {
            key,
            old_leaf,
            new_leaf,
        },
        witness: SmtWitness {
            leaf: witness_leaf,
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

/// `verify_sync_op(prove(req)) == smt_valid_native(req)` (both directions).
fn assert_equivalence(prover: &StateSyncProver, depth: usize, request: &SyncRequest, label: &str) {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: depth as u32,
        ..Default::default()
    };
    let native = smt_valid_native(
        &h,
        &params,
        &request.operation,
        &request.public_inputs.old_root,
        &request.public_inputs.new_root,
        &request.witness,
    )
    .unwrap();
    let verified = match prover.prove_sync_op(request) {
        Ok(result) => prover.verify_sync_op(request, &result),
        Err(_) => false,
    };
    assert_eq!(
        verified, native,
        "{label}: verify_sync_op ({verified}) must match smt_valid_native ({native})"
    );
}

fn occupied(v: u32) -> LeafState {
    LeafState::Occupied(LeafPayload {
        sync_state: vec![f(v)],
        identity_digest: [v as u8; 32],
    })
}

#[test]
fn composition_equivalence_battery() {
    let depth = 3usize;
    let prover = StateSyncProver::new(config(depth as u32));

    // --- Membership: valid, then a wrong-sibling forgery.
    let m_valid = membership_request(depth, 5);
    assert_equivalence(&prover, depth, &m_valid, "membership valid");
    let mut m_bad = membership_request(depth, 5);
    m_bad.witness.path.siblings[0] = Digest([f(424242); 8]); // path no longer hashes to old_root
    assert_equivalence(&prover, depth, &m_bad, "membership wrong sibling");

    // --- NonMembership: empty valid, tombstone valid, and the original
    //     forgery (a genuinely OCCUPIED key claimed absent).
    assert_equivalence(
        &prover,
        depth,
        &nonmembership_request(depth, 6, LeafState::Empty),
        "non-membership empty",
    );
    assert_equivalence(
        &prover,
        depth,
        &nonmembership_request(depth, 6, LeafState::Tombstone),
        "non-membership tombstone",
    );
    assert_equivalence(
        &prover,
        depth,
        &nonmembership_request(depth, 6, occupied(42)),
        "non-membership of occupied (Finding 1 forgery)",
    );

    // --- Update: valid, the witness.leaf mismatch regression, and a
    //     wrong-sibling forgery.
    assert_equivalence(
        &prover,
        depth,
        &update_request(depth, 3, occupied(100), LeafState::Tombstone, occupied(100)),
        "update valid",
    );
    assert_equivalence(
        &prover,
        depth,
        &update_request(
            depth,
            3,
            occupied(100),
            LeafState::Tombstone,
            LeafState::Empty,
        ),
        "update witness.leaf mismatch (Finding 2)",
    );
    let mut u_bad = update_request(depth, 3, occupied(100), LeafState::Tombstone, occupied(100));
    u_bad.witness.path.siblings[1] = Digest([f(999999); 8]);
    assert_equivalence(&prover, depth, &u_bad, "update wrong sibling");
}

#[test]
fn rejects_op_kind_tag_mismatch() {
    // Cross-op-kind: a proof whose public op_kind_tag disagrees with the
    // operation is rejected (the tag is bound in the S-5 circuit digest and
    // public inputs, and the facade checks it against `op.kind()`).
    let prover = StateSyncProver::new(config(4));
    let mut request = membership_request(4, 5);
    request.public_inputs.op_kind_tag = 1; // claim NonMembership for a Membership op
    let result = prover.prove_sync_op(&request).unwrap();
    assert!(!prover.verify_sync_op(&request, &result));
}
