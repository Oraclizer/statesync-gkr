//! Canonical proof digest dump - the cross-build determinism anchor.
//!
//! Proves one fixed request per op kind (plus a production-size
//! membership at d=24) through the prepared v0.2 pipe and prints one
//! digest line each. Two builds of this binary - e.g. scalar vs
//! `-Ctarget-cpu=native` (AVX2/AVX-512) - MUST print byte-identical
//! output: field arithmetic is mathematically identical across vector
//! backends, and the transcript convention is frozen (S-5). CI runs both
//! and diffs (ADR-0001 determinism gate, cross-process half; the
//! in-process half lives in tests/batch_v02.rs).
//!
//! The digest absorbs the proof's complete value sequence (with length
//! framing) into a fresh domain-separated transcript and squeezes one
//! challenge - equal iff the proof value sequences are equal. Twin of
//! `proof_digest` in tests/batch_v02.rs (keep in sync).
//!
//! Run: `cargo run --release --bin proof_digest`.

#![allow(clippy::expect_used, clippy::unwrap_used)]

use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOpKind,
    SmtOperation, SmtParams, SmtWitness,
};
use statesync_gkr::gkr::GkrProof;
use statesync_gkr::primitives::Transcript;
use statesync_gkr::primitives::field::{BaseField, PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{Digest, HashGadget, Poseidon2Gadget};
use statesync_gkr::{StateSyncGkrConfig, StateSyncProver, SyncRequest};

fn f(x: u32) -> BaseField {
    BaseField::from_u32(x)
}

fn siblings(depth: usize) -> Vec<Digest<BaseField>> {
    (0..depth)
        .map(|i| Digest([f(i as u32 * 13 + 1); 8]))
        .collect()
}

fn membership_request(depth: u32) -> SyncRequest {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth,
        ..Default::default()
    };
    let key = AssetId(5);
    let payload = LeafPayload {
        sync_state: vec![f(42), f(7)],
        identity_digest: [9u8; 32],
    };
    let leaf = LeafState::Occupied(payload.clone());
    let path = MerklePath {
        siblings: siblings(depth as usize),
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

fn nonmembership_request(depth: u32) -> SyncRequest {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth,
        ..Default::default()
    };
    let key = AssetId(6);
    let leaf = LeafState::Empty;
    let path = MerklePath {
        siblings: siblings(depth as usize),
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

fn update_request(depth: u32) -> SyncRequest {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth,
        ..Default::default()
    };
    let key = AssetId(9);
    let old_leaf = LeafState::Occupied(LeafPayload {
        sync_state: vec![f(100)],
        identity_digest: [3u8; 32],
    });
    let new_leaf = LeafState::Tombstone;
    let path = MerklePath {
        siblings: siblings(depth as usize),
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

/// See the module doc; twin of the test-side helper.
fn proof_digest(proof: &GkrProof) -> statesync_gkr::primitives::field::ChallengeField {
    let mut t = Transcript::new(b"ssgkr/proof-digest/v0");
    t.observe_base(f(proof.layer_proofs.len() as u32));
    for lp in &proof.layer_proofs {
        t.observe_base(f(lp.sumcheck.round_polys.len() as u32));
        for rp in &lp.sumcheck.round_polys {
            t.observe_base(f(rp.coeffs().len() as u32));
            for c in rp.coeffs() {
                t.observe_ext(*c);
            }
        }
        t.observe_ext(lp.eval_x);
        t.observe_ext(lp.eval_y);
    }
    t.sample_challenge()
}

fn main() {
    // Small circuits for all three kinds + one production-size membership.
    let cases: Vec<(&str, u32, SyncRequest)> = vec![
        ("membership", 4, membership_request(4)),
        ("nonmembership", 4, nonmembership_request(4)),
        ("update", 4, update_request(4)),
        ("membership", 24, membership_request(24)),
    ];
    for (label, depth, req) in cases {
        let prover = StateSyncProver::new(StateSyncGkrConfig {
            smt: SmtParams {
                depth,
                ..Default::default()
            },
            layer_strategy: LayerStrategy::A,
            ..Default::default()
        });
        let kind: SmtOpKind = req.operation.kind();
        let prepared = prover.prepare(kind).expect("prepare");
        let result = prover
            .prove_sync_op_prepared(&prepared, &req)
            .expect("prove");
        assert!(
            prover.verify_sync_op_prepared(&prepared, &req, &result),
            "honest proof must verify before digesting"
        );
        println!(
            "kind={label} d={depth} digest={:?}",
            proof_digest(&result.proof)
        );
    }
}
