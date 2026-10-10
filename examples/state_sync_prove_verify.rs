//! Minimal reusable-core example: construct one membership request, prove it,
//! verify it, then demonstrate rejection after proof tampering.

use std::process::ExitCode;

use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOperation,
    SmtParams, SmtWitness,
};
use statesync_gkr::primitives::ChallengeField;
use statesync_gkr::primitives::field::{BaseField, PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{Digest, HashGadget, Poseidon2Gadget};
use statesync_gkr::{StateSyncGkrConfig, StateSyncProver, SyncRequest};

fn field(value: u32) -> BaseField {
    BaseField::from_u32(value)
}

fn membership_request(depth: usize) -> Result<SyncRequest, String> {
    let hasher = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: depth as u32,
        ..Default::default()
    };
    let key = AssetId(5);
    let payload = LeafPayload {
        sync_state: vec![field(42), field(7)],
        identity_digest: [9_u8; 32],
    };
    let leaf = LeafState::Occupied(payload.clone());
    let path = MerklePath {
        siblings: (0..depth)
            .map(|index| Digest([field(index as u32 * 13 + 1); 8]))
            .collect(),
    };
    let old_root = path
        .compute_root(&hasher, &params, key, &leaf)
        .map_err(|error| format!("root construction failed: {error:?}"))?;
    let value_digest = hasher
        .hash_leaf(&leaf.encode())
        .map_err(|error| format!("leaf hashing failed: {error:?}"))?;

    Ok(SyncRequest {
        operation: SmtOperation::Membership { key, payload },
        witness: SmtWitness { leaf, path },
        public_inputs: PublicInputs {
            old_root,
            new_root: old_root,
            op_kind_tag: 0,
            asset_id: key,
            value_digest,
        },
    })
}

fn run() -> Result<(), String> {
    let depth = 4;
    let prover = StateSyncProver::new(StateSyncGkrConfig {
        smt: SmtParams {
            depth,
            ..Default::default()
        },
        layer_strategy: LayerStrategy::A,
        batching: Default::default(),
    });
    let request = membership_request(depth as usize)?;
    let mut result = prover
        .prove_sync_op(&request)
        .map_err(|error| format!("proving failed: {error:?}"))?;

    if !prover.verify_sync_op(&request, &result) {
        return Err("the honest proof was rejected".to_owned());
    }
    println!("honest-proof=PASS");

    let first_layer = result
        .proof
        .layer_proofs
        .first_mut()
        .ok_or_else(|| "the proof contains no layer proof".to_owned())?;
    first_layer.eval_x += ChallengeField::from(field(1));
    if prover.verify_sync_op(&request, &result) {
        return Err("the tampered proof was accepted".to_owned());
    }
    println!("tampered-proof=REJECTED");
    println!("secondary-finalized=false");
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("quickstart=FAIL: {error}");
            ExitCode::FAILURE
        }
    }
}
