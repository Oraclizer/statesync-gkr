//! Executable witnesses for the verifier-acceptance refinement boundary.
//!
//! These tests call the production `verify_sync_op` entry. They do not claim
//! that Rust execution has been imported into Isabelle. They pin the concrete
//! checks whose successful trace is related to `gkr_chain_bad` by
//! `Verifier_Acceptance_Refinement.thy`.

#![allow(clippy::unwrap_used)]

use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOperation,
    SmtParams, SmtWitness,
};
use statesync_gkr::primitives::field::{BaseField, ChallengeField, PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{Digest, HashGadget, Poseidon2Gadget};
use statesync_gkr::sumcheck::RoundPoly;
use statesync_gkr::{StateSyncGkrConfig, StateSyncProver, SyncRequest};

fn f(x: u32) -> BaseField {
    BaseField::from_u32(x)
}

fn membership_request() -> SyncRequest {
    let depth = 4usize;
    let params = SmtParams {
        depth: depth as u32,
        ..Default::default()
    };
    let hasher = Poseidon2Gadget::default();
    let key = AssetId(5);
    let payload = LeafPayload {
        sync_state: vec![f(42), f(7)],
        identity_digest: [9u8; 32],
    };
    let leaf = LeafState::Occupied(payload.clone());
    let path = MerklePath {
        siblings: (0..depth)
            .map(|i| Digest([f(i as u32 * 13 + 1); 8]))
            .collect(),
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

fn prover() -> StateSyncProver {
    StateSyncProver::new(StateSyncGkrConfig {
        smt: SmtParams {
            depth: 4,
            ..Default::default()
        },
        layer_strategy: LayerStrategy::A,
        batching: Default::default(),
    })
}

#[test]
fn honest_production_acceptance_is_inhabited() {
    let prover = prover();
    let request = membership_request();
    let result = prover.prove_sync_op(&request).unwrap();
    assert!(prover.verify_sync_op(&request, &result));
}

#[test]
fn public_input_binding_is_load_bearing() {
    let prover = prover();
    let request = membership_request();
    let result = prover.prove_sync_op(&request).unwrap();
    let mut tampered = request;
    tampered.public_inputs.old_root = Digest([f(123); 8]);
    tampered.public_inputs.new_root = Digest([f(123); 8]);
    assert!(!prover.verify_sync_op(&tampered, &result));
}

#[test]
fn sumcheck_consistency_is_load_bearing() {
    let prover = prover();
    let request = membership_request();
    let mut result = prover.prove_sync_op(&request).unwrap();
    let round = &result.proof.layer_proofs[0].sumcheck.round_polys[0];
    let mut coeffs = round.coeffs().to_vec();
    coeffs[0] += ChallengeField::ONE;
    result.proof.layer_proofs[0].sumcheck.round_polys[0] = RoundPoly::from_coeffs(coeffs);
    assert!(!prover.verify_sync_op(&request, &result));
}

#[test]
fn carry_reconstruction_is_load_bearing() {
    let prover = prover();
    let request = membership_request();
    let mut result = prover.prove_sync_op(&request).unwrap();
    result.proof.layer_proofs[0].eval_x += ChallengeField::ONE;
    assert!(!prover.verify_sync_op(&request, &result));
}

#[test]
fn final_input_mle_discharge_is_load_bearing() {
    let prover = prover();
    let request = membership_request();
    let result = prover.prove_sync_op(&request).unwrap();
    let mut wrong_witness = request;
    wrong_witness.witness.path.siblings[1] = Digest([f(999); 8]);
    assert!(!prover.verify_sync_op(&wrong_witness, &result));
}
