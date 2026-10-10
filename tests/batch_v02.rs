//! v0.2 throughput gates (ADR-0001): determinism, canonical proof digest,
//! and pointwise agreement of every batch path with the single-proof path.
//!
//! These tests are the EXECUTABLE side of the Theorem D re-instantiation
//! (`formal/isabelle/GKR_Protocol/GKR_Batching.thy`, v0.2 pipe interpretation): the
//! locale's two obligations - length preservation and per-position
//! agreement with the single-proof pipeline - are pinned here bit-for-bit
//! on the real compiled circuits, across op kinds, batch sizes, prepared
//! vs unprepared paths, and worker counts.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use statesync_gkr::batching::{BatchProver, ProveJob, WitnessQueue};
use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOpKind,
    SmtOperation, SmtParams, SmtWitness,
};
use statesync_gkr::gkr::GkrProof;
use statesync_gkr::primitives::Transcript;
use statesync_gkr::primitives::field::{BaseField, ChallengeField, PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{Digest, HashGadget, Poseidon2Gadget};
use statesync_gkr::{StateSyncGkrConfig, StateSyncProver, SyncRequest};
use std::collections::HashMap;
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

fn membership_request(depth: usize, key: u64) -> SyncRequest {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: depth as u32,
        ..Default::default()
    };
    let key = AssetId(key);
    let payload = LeafPayload {
        sync_state: vec![f(42), f(key.0 as u32)],
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

fn nonmembership_request(depth: usize, key: u64) -> SyncRequest {
    let h = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: depth as u32,
        ..Default::default()
    };
    let key = AssetId(key);
    let leaf = LeafState::Empty;
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

fn request_for(kind: SmtOpKind, depth: usize, key: u64) -> SyncRequest {
    match kind {
        SmtOpKind::Membership => membership_request(depth, key),
        SmtOpKind::NonMembership => nonmembership_request(depth, key),
        SmtOpKind::Update => update_request(depth, key),
    }
}

const KINDS: [SmtOpKind; 3] = [
    SmtOpKind::Membership,
    SmtOpKind::NonMembership,
    SmtOpKind::Update,
];

/// Canonical proof digest: absorb the proof's complete value sequence
/// (with length framing) into a fresh domain-separated transcript and
/// squeeze one challenge. Two proofs digest equal iff their value
/// sequences are equal, so cross-build runs (scalar vs AVX) can compare a
/// single line instead of megabytes. Kept in sync with the copy in
/// src/bin/proof_digest.rs (test-side twin).
fn proof_digest(proof: &GkrProof) -> ChallengeField {
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

#[test]
fn batch_of_one_equals_single_proof_for_every_kind() {
    // Theorem D pointwise agreement at N = 1, per kind: the batch path and
    // the single path emit the SAME proof (bit-for-bit, PartialEq).
    let prover = StateSyncProver::new(config(4));
    for kind in KINDS {
        let req = request_for(kind, 4, 5);
        let single = prover.prove_sync_op(&req).unwrap();
        let job = prover.make_job(&req).unwrap();
        let batch = prover.prove_batch(kind, std::slice::from_ref(&job));
        assert_eq!(batch.len(), 1, "{kind:?}: length obligation");
        assert_eq!(
            batch[0], single.proof,
            "{kind:?}: batch(1) proof must equal the single-path proof"
        );
    }
}

#[test]
fn prepared_paths_equal_v01_paths_across_kinds_and_sizes() {
    // The v0.2 prepared pipe (compile+derive once) is pointwise the v0.1
    // pipe (compile per batch), which is pointwise the single path.
    let prover = StateSyncProver::new(config(4));
    for kind in KINDS {
        let prepared = prover.prepare(kind).unwrap();
        // Single path vs prepared single path.
        let req = request_for(kind, 4, 5);
        let single = prover.prove_sync_op(&req).unwrap();
        let single_prep = prover.prove_sync_op_prepared(&prepared, &req).unwrap();
        assert_eq!(
            single.proof, single_prep.proof,
            "{kind:?}: single==prepared"
        );
        assert_eq!(single.public_inputs, single_prep.public_inputs);

        // make_job vs make_job_prepared: identical jobs.
        let job = prover.make_job(&req).unwrap();
        let job_prep = prover.make_job_prepared(&prepared, &req).unwrap();
        assert_eq!(job.witness, job_prep.witness, "{kind:?}: job witness");
        assert_eq!(job.public_inputs, job_prep.public_inputs);

        // Batch sizes 1 and 3: v0.1 batch == v0.2 prepared batch.
        for n in [1usize, 3] {
            let jobs: Vec<ProveJob> = (0..n)
                .map(|i| {
                    prover
                        .make_job_prepared(&prepared, &request_for(kind, 4, 5 + i as u64))
                        .unwrap()
                })
                .collect();
            let v01 = prover.prove_batch(kind, &jobs);
            let v02 = prover.prove_batch_prepared(&prepared, &jobs);
            assert_eq!(v01.len(), n);
            assert_eq!(v01, v02, "{kind:?} n={n}: prepared batch == v0.1 batch");
        }
    }
}

#[test]
fn parallel_proofs_invariant_under_worker_count() {
    // Determinism requirement: worker count and scheduling cannot reach proof
    // bytes - the parallel pipe equals the sequential pipe element-for-
    // element under every pool size (1, 2, 4, 8).
    let prover = StateSyncProver::new(config(4));
    let prepared = prover.prepare(SmtOpKind::Membership).unwrap();
    let jobs: Vec<ProveJob> = (0..6)
        .map(|i| {
            prover
                .make_job_prepared(&prepared, &membership_request(4, 3 + i as u64))
                .unwrap()
        })
        .collect();
    let sequential = prover.prove_batch_prepared(&prepared, &jobs);
    for workers in [1usize, 2, 4, 8] {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(workers)
            .build()
            .unwrap();
        let parallel = pool.install(|| prover.prove_batch_parallel(&prepared, &jobs));
        assert_eq!(
            parallel, sequential,
            "workers={workers}: parallel proofs must be bit-identical to sequential"
        );
    }
}

#[test]
fn proof_digest_deterministic_across_all_paths() {
    // The canonical digest is stable across repeated proving and across
    // every prove path (single, prepared, batch, parallel) - the in-process
    // anchor the cross-build (scalar vs AVX) CI comparison relies on.
    let prover = StateSyncProver::new(config(4));
    let prepared = prover.prepare(SmtOpKind::Membership).unwrap();
    let req = membership_request(4, 5);

    let d1 = proof_digest(&prover.prove_sync_op(&req).unwrap().proof);
    let d2 = proof_digest(&prover.prove_sync_op(&req).unwrap().proof);
    assert_eq!(d1, d2, "same request, same proof digest (determinism)");

    let d3 = proof_digest(
        &prover
            .prove_sync_op_prepared(&prepared, &req)
            .unwrap()
            .proof,
    );
    let job = prover.make_job_prepared(&prepared, &req).unwrap();
    let d4 = proof_digest(&prover.prove_batch_prepared(&prepared, std::slice::from_ref(&job))[0]);
    let d5 = proof_digest(&prover.prove_batch_parallel(&prepared, std::slice::from_ref(&job))[0]);
    assert_eq!(d1, d3, "prepared path digest");
    assert_eq!(d1, d4, "batch path digest");
    assert_eq!(d1, d5, "parallel path digest");

    // And the digest DOES react to proof changes (non-vacuity).
    let mut tampered = prover.prove_sync_op(&req).unwrap();
    tampered.proof.layer_proofs[0].eval_x += ChallengeField::from(f(1));
    assert_ne!(
        d1,
        proof_digest(&tampered.proof),
        "digest reacts to tampering"
    );
}

#[test]
fn prepared_verifier_agrees_with_succinct_and_reference() {
    // Honest accept and tamper-class rejects agree verdict-for-verdict
    // across all three verify entries (succinct, reference table, prepared).
    let prover = StateSyncProver::new(config(4));
    for kind in KINDS {
        let prepared = prover.prepare(kind).unwrap();
        let req = request_for(kind, 4, 5);
        let result = prover.prove_sync_op(&req).unwrap();

        assert!(
            prover.verify_sync_op(&req, &result),
            "{kind:?} honest succinct"
        );
        assert!(
            prover.verify_sync_op_reference(&req, &result),
            "{kind:?} honest reference"
        );
        assert!(
            prover.verify_sync_op_prepared(&prepared, &req, &result),
            "{kind:?} honest prepared"
        );

        let mut tampered = result;
        tampered.proof.layer_proofs[0].eval_x += ChallengeField::from(f(1));
        assert!(
            !prover.verify_sync_op(&req, &tampered),
            "{kind:?} tamper succinct"
        );
        assert!(
            !prover.verify_sync_op_reference(&req, &tampered),
            "{kind:?} tamper reference"
        );
        assert!(
            !prover.verify_sync_op_prepared(&prepared, &req, &tampered),
            "{kind:?} tamper prepared"
        );
    }
}

#[test]
fn prepared_verifier_rejects_kind_mismatch() {
    let prover = StateSyncProver::new(config(4));
    let prepared_memb = prover.prepare(SmtOpKind::Membership).unwrap();
    let req = update_request(4, 9);
    let result = prover.prove_sync_op(&req).unwrap();
    assert!(
        prover.verify_sync_op(&req, &result),
        "honest update verifies"
    );
    assert!(
        !prover.verify_sync_op_prepared(&prepared_memb, &req, &result),
        "membership-prepared verifier must reject an update proof early"
    );
}

#[test]
fn module3_round_with_prepared_parallel_injection() {
    // Module 3 assembly (the v0.2 wiring): the deadline scheduler drains
    // per-kind lanes and the injected closure proves each batch on the
    // prepared circuit in parallel. Every emitted proof verifies against
    // the prepared verifier, and queue order is preserved.
    let prover = StateSyncProver::new(config(4));
    let mut prepared: HashMap<SmtOpKind, statesync_gkr::PreparedSync> = HashMap::new();
    for kind in KINDS {
        prepared.insert(kind, prover.prepare(kind).unwrap());
    }

    let memb_reqs: Vec<SyncRequest> = (0..5).map(|i| membership_request(4, 3 + i)).collect();
    let upd_reqs: Vec<SyncRequest> = (0..3).map(|i| update_request(4, 9 + i)).collect();

    let mut queue = WitnessQueue::new();
    for r in &memb_reqs {
        queue.push(
            prover
                .make_job_prepared(&prepared[&SmtOpKind::Membership], r)
                .unwrap(),
        );
    }
    for r in &upd_reqs {
        queue.push(
            prover
                .make_job_prepared(&prepared[&SmtOpKind::Update], r)
                .unwrap(),
        );
    }

    let mut bp = BatchProver::default();
    let results = bp.prove_round(&mut queue, Duration::from_millis(200), |kind, jobs| {
        prover.prove_batch_parallel(&prepared[&kind], jobs)
    });
    assert!(queue.is_empty(), "round drains all lanes");
    let total: usize = results.iter().map(|r| r.proofs.len()).sum();
    assert_eq!(total, 8, "one proof per queued job");

    // Verify each batch's proofs in queue order against the originating
    // requests (Theorem D: element-wise the single-proof pipeline).
    for batch in &results {
        let (reqs, kind) = if batch.proofs.len() == memb_reqs.len() {
            (&memb_reqs, SmtOpKind::Membership)
        } else {
            (&upd_reqs, SmtOpKind::Update)
        };
        for (req, proof) in reqs.iter().zip(&batch.proofs) {
            let result = statesync_gkr::SyncResult {
                public_inputs: req.public_inputs.clone(),
                proof: proof.clone(),
            };
            assert!(
                prover.verify_sync_op_prepared(&prepared[&kind], req, &result),
                "batched proof verifies as a single proof ({kind:?})"
            );
        }
    }
}
