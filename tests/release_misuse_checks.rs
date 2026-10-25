//! Misuse checks that hold in every build profile, release included: the
//! prepared prover entry points refuse a request of another operation kind,
//! and the leaf hash refuses a pre-image of the wrong width.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOpKind, SmtParams,
};
use statesync_gkr::compiler::{SmtOperation, SmtWitness};
use statesync_gkr::primitives::field::{BaseField, PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{Digest, HashGadget, Poseidon2Gadget, leaf_pre_width};
use statesync_gkr::{StateSyncGkrConfig, StateSyncProver, SyncError, SyncRequest};

const DEPTH: u32 = 4;

fn f(x: u32) -> BaseField {
    BaseField::from_u32(x)
}

fn prover() -> StateSyncProver {
    StateSyncProver::new(StateSyncGkrConfig {
        smt: SmtParams {
            depth: DEPTH,
            ..Default::default()
        },
        layer_strategy: LayerStrategy::A,
        batching: Default::default(),
    })
}

fn membership_request(key: u64) -> SyncRequest {
    let hasher = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: DEPTH,
        ..Default::default()
    };
    let key = AssetId(key);
    let payload = LeafPayload {
        sync_state: vec![f(42), f(7)],
        identity_digest: [9u8; 32],
    };
    let leaf = LeafState::Occupied(payload.clone());
    let path = MerklePath {
        siblings: (0..DEPTH).map(|i| Digest([f(i * 13 + 1); 8])).collect(),
    };
    let old_root = path.compute_root(&hasher, &params, key, &leaf).unwrap();
    let value_digest = hasher.hash_leaf(&leaf.encode()).unwrap();
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
fn prepared_entry_points_refuse_another_operation_kind() {
    let prover = prover();
    let request = membership_request(5);
    let other = prover.prepare(SmtOpKind::NonMembership).unwrap();
    let refused = |result: Result<(), SyncError>| {
        matches!(
            result,
            Err(SyncError::KindMismatch {
                prepared: SmtOpKind::NonMembership,
                requested: SmtOpKind::Membership,
            })
        )
    };
    assert!(refused(
        prover.prove_sync_op_prepared(&other, &request).map(|_| ())
    ));
    assert!(refused(
        prover.make_job_prepared(&other, &request).map(|_| ())
    ));

    // The matching kind still proves, and the proof verifies.
    let matching = prover.prepare(SmtOpKind::Membership).unwrap();
    let result = prover.prove_sync_op_prepared(&matching, &request).unwrap();
    assert!(prover.verify_sync_op_prepared(&matching, &request, &result));
    assert!(prover.make_job_prepared(&matching, &request).is_ok());
}

#[test]
fn leaf_hash_accepts_exactly_the_leaf_pre_image_width() {
    let gadget = Poseidon2Gadget::default();
    let width = leaf_pre_width(gadget.leaf_max_fields());
    let digest = gadget.hash_leaf_pre(&vec![BaseField::ZERO; width]);
    assert_eq!(digest, gadget.hash_leaf_pre(&vec![BaseField::ZERO; width]));
}

#[test]
#[should_panic(expected = "leaf pre-image width differs from leaf_pre_width")]
fn leaf_hash_refuses_a_wider_pre_image() {
    let gadget = Poseidon2Gadget::default();
    let width = leaf_pre_width(gadget.leaf_max_fields());
    let _ = gadget.hash_leaf_pre(&vec![BaseField::ZERO; width + 8]);
}

#[test]
#[should_panic(expected = "leaf pre-image width differs from leaf_pre_width")]
fn leaf_hash_refuses_a_narrower_pre_image() {
    let gadget = Poseidon2Gadget::default();
    let width = leaf_pre_width(gadget.leaf_max_fields());
    let _ = gadget.hash_leaf_pre(&vec![BaseField::ZERO; width - 8]);
}
