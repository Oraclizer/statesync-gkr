//! External measurement driver. The released prover source is unchanged.
//! Timings have explicit phase denominators; each invocation is one RSS cell.

use std::hint::black_box;
use std::path::PathBuf;
use std::time::Instant;

use sha2::{Digest as ShaDigest, Sha256};
use rayon::prelude::*;
use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs,
    SmtOperation, SmtParams, SmtWitness,
};
use statesync_gkr::primitives::field::{BaseField, ChallengeField, PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{Digest, HashGadget, Poseidon2Gadget};
use statesync_gkr::{PreparedSync, StateSyncGkrConfig, StateSyncProver, SyncRequest, SyncResult};

const SEED: u64 = 0x5353474b52202026;

fn argument(name: &str, default: &str) -> String {
    let xs: Vec<_> = std::env::args().collect();
    xs.windows(2).find(|x| x[0] == name).map(|x| x[1].clone()).unwrap_or_else(|| default.into())
}

fn splitmix(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e3779b97f4a7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}

fn field(state: &mut u64) -> BaseField {
    BaseField::from_u32((splitmix(state) & 0x00ff_ffff) as u32)
}

fn fixture(depth: u32, label: &str, index: usize) -> SyncRequest {
    let kind_tag = match label { "membership" => 0, "nonmembership" => 1, "update" => 2, _ => panic!("unknown kind") };
    let mut seed = SEED ^ ((depth as u64) << 32) ^ ((kind_tag as u64) << 56) ^ index as u64;
    // Unique keys within this cell and below the base-field alias boundary.
    let key = AssetId(index as u64 + 1);
    assert!(key.0 < 1u64 << depth.min(24));
    let path = MerklePath { siblings: (0..depth).map(|_| Digest(core::array::from_fn(|_| field(&mut seed)))).collect() };
    let identity: [u8; 32] = core::array::from_fn(|_| splitmix(&mut seed) as u8);
    let payload = LeafPayload { sync_state: vec![field(&mut seed), field(&mut seed)], identity_digest: identity };
    let occupied = LeafState::Occupied(payload.clone());
    let params = SmtParams { depth, ..Default::default() };
    let hasher = Poseidon2Gadget::default();
    let (operation, old_leaf, new_leaf) = match label {
        "membership" => (SmtOperation::Membership { key, payload }, occupied.clone(), occupied),
        "nonmembership" => (SmtOperation::NonMembership { key }, LeafState::Empty, LeafState::Empty),
        "update" => {
            let new_payload = LeafPayload { sync_state: vec![field(&mut seed), field(&mut seed)], identity_digest: identity };
            let new_leaf = LeafState::Occupied(new_payload);
            (SmtOperation::Update { key, old_leaf: occupied.clone(), new_leaf: new_leaf.clone() }, occupied, new_leaf)
        }
        _ => unreachable!(),
    };
    let old_root = path.compute_root(&hasher, &params, key, &old_leaf).expect("valid old path");
    let new_root = path.compute_root(&hasher, &params, key, &new_leaf).expect("valid new path");
    let value_digest = hasher.hash_leaf(&new_leaf.encode()).expect("in-bound leaf encoding");
    SyncRequest {
        operation,
        witness: SmtWitness { leaf: old_leaf, path },
        public_inputs: PublicInputs { old_root, new_root, op_kind_tag: kind_tag, asset_id: key, value_digest },
    }
}

fn hash(bytes: &[u8]) -> String {
    Sha256::digest(bytes).iter().map(|b| format!("{b:02x}")).collect()
}

fn checked_bytes(prover: &StateSyncProver, prepared: &PreparedSync, request: &SyncRequest, result: &SyncResult) -> Vec<u8> {
    assert!(prover.verify_sync_op_prepared(prepared, request, result), "positive proof rejected");
    let bytes = prover.encode_sync_result(prepared, result).expect("canonical encoding");
    assert!(prover.verify_encoded_sync_op(prepared, request, &bytes), "encoded positive rejected");
    bytes
}

fn main() {
    let kind = argument("--kind", "membership");
    let phase = argument("--phase", "controls");
    let depth: u32 = argument("--depth", "24").parse().expect("depth");
    let workers: usize = argument("--workers", "1").parse().expect("workers");
    let samples: usize = argument("--samples", "3").parse().expect("samples");
    let batch: usize = argument("--batch", "192").parse().expect("batch");
    let run = argument("--run", "0");
    let mode = argument("--mode", "unspecified");
    let proof_dir = PathBuf::from(argument("--proof-dir", "proofs"));
    let expected_path = argument("--expected", "");
    let expected_hashes: Vec<String> = if expected_path.is_empty() { Vec::new() } else {
        std::fs::read_to_string(expected_path).expect("reference hashes").lines().map(str::to_owned).collect()
    };
    assert!([24, 28, 32].contains(&depth));
    assert!([1, 2, 4, 8, 16, 32, 48, 64, 96, 128, 192, 384].contains(&workers));
    assert!(samples > 0 && batch >= workers && batch <= 768);
    let config = StateSyncGkrConfig { smt: SmtParams { depth, ..Default::default() }, layer_strategy: LayerStrategy::A, ..Default::default() };
    let prover = StateSyncProver::new(config);
    let request_count = if phase == "verify" { 4 } else { batch };
    let requests: Vec<_> = (0..request_count).map(|i| fixture(depth, &kind, i)).collect();
    let operation_kind = requests[0].operation.kind();
    let prepare_started = Instant::now();
    let prepared = prover.prepare(operation_kind).expect("prepare");
    let prepare_ns = prepare_started.elapsed().as_nanos();
    let pool = rayon::ThreadPoolBuilder::new().num_threads(workers).build().expect("thread pool");
    println!("record,mode,run,kind,depth,phase,workers,batch,sample,elapsed_ns,proof_bytes,proof_sha256");
    println!("setup,{mode},{run},{kind},{depth},prepare,{workers},1,0,{prepare_ns},0,");

    if phase == "controls" {
        std::fs::create_dir_all(&proof_dir).expect("proof directory");
        let mut hashes = Vec::with_capacity(requests.len());
        for (i, request) in requests.iter().enumerate() {
            let result = prover.prove_sync_op_prepared(&prepared, request).expect("prove");
            let bytes = checked_bytes(&prover, &prepared, request, &result);
            let mut corrupt = result.clone();
            corrupt.proof.layer_proofs[0].eval_x += ChallengeField::ONE;
            assert!(!prover.verify_sync_op_prepared(&prepared, request, &corrupt), "tampered proof accepted");
            let mut wrong_request = request.clone();
            wrong_request.public_inputs.value_digest.0[0] += BaseField::ONE;
            assert!(!prover.verify_sync_op_prepared(&prepared, &wrong_request, &result), "wrong request accepted");
            let mut wrong_root = request.clone();
            wrong_root.public_inputs.old_root.0[0] += BaseField::ONE;
            assert!(!prover.verify_sync_op_prepared(&prepared, &wrong_root, &result), "wrong root accepted");
            println!("control,{mode},{run},{kind},{depth},{phase},{workers},{batch},{i},0,{},{}", bytes.len(), hash(&bytes));
            hashes.push(hash(&bytes));
            if i == 0 {
                std::fs::write(proof_dir.join(format!("{mode}-{kind}-d{depth}.bin")), bytes).expect("save canonical proof");
            }
        }
        std::fs::write(proof_dir.join(format!("{mode}-{kind}-d{depth}.hashes")), hashes.join("\n") + "\n").expect("save reference hashes");
        return;
    }

    if phase == "fresh" || phase == "prepared" {
        for i in 0..5 + samples {
            let rotation = run.parse::<usize>().unwrap_or(0) * 67;
            let request = &requests[(i + rotation) % requests.len()];
            let started = Instant::now();
            let result = if phase == "fresh" { prover.prove_sync_op(black_box(request)) } else { prover.prove_sync_op_prepared(black_box(&prepared), black_box(request)) }.expect("prove");
            let elapsed = started.elapsed().as_nanos();
            if i >= 5 { println!("timing,{mode},{run},{kind},{depth},{phase},{workers},1,{},{},0,", i - 5, elapsed); }
            assert!(prover.verify_sync_op_prepared(&prepared, request, &result));
            drop(black_box(result));
        }
        return;
    }

    if phase == "verify" {
        let results: Vec<_> = requests.iter().map(|request| prover.prove_sync_op_prepared(&prepared, request).expect("proof for verify")).collect();
        for (request, result) in requests.iter().zip(&results) { checked_bytes(&prover, &prepared, request, result); }
        for i in 0..5 + samples {
            let index = i % requests.len();
            let started = Instant::now();
            let accepted = black_box(prover.verify_sync_op_prepared(black_box(&prepared), black_box(&requests[index]), black_box(&results[index])));
            let elapsed = started.elapsed().as_nanos();
            assert!(accepted);
            if i >= 5 { println!("timing,{mode},{run},{kind},{depth},{phase},{workers},1,{},{},0,", i - 5, elapsed); }
        }
        return;
    }

    assert!(["seq-prove", "parallel", "stream", "stream-parallel-witness"].contains(&phase.as_str()), "unknown phase");
    let jobs: Vec<_> = requests.iter().map(|request| prover.make_job_prepared(&prepared, request).expect("prepared job")).collect();
    // Hashes only are retained; no second batch of full proofs is kept resident.
    let baseline_hashes: Vec<String> = if expected_hashes.is_empty() {
        prover.prove_batch_prepared(&prepared, &jobs).into_iter().zip(&requests).map(|(proof, request)| {
            let result = SyncResult { public_inputs: request.public_inputs.clone(), proof };
            hash(&checked_bytes(&prover, &prepared, request, &result))
        }).collect()
    } else {
        assert!(expected_hashes.len() >= requests.len(), "reference hash count");
        expected_hashes.into_iter().take(requests.len()).collect()
    };
    // A batch request-to-proof cell holds just its newly generated witness batch.
    // Keep no duplicate pre-generated witness batch resident for that phase.
    let jobs = if phase.starts_with("stream") { drop(jobs); None } else { Some(jobs) };
    for i in 0..1 + samples {
        let started = Instant::now();
        let proofs = if phase == "seq-prove" { prover.prove_batch_prepared(black_box(&prepared), black_box(jobs.as_deref().expect("prepared jobs"))) }
        else if phase == "parallel" { pool.install(|| prover.prove_batch_parallel(black_box(&prepared), black_box(jobs.as_deref().expect("prepared jobs")))) }
        else if phase == "stream-parallel-witness" {
            let stream_jobs: Vec<_> = pool.install(|| requests.par_iter().map(|request| prover.make_job_prepared(&prepared, black_box(request)).expect("parallel caller witness")).collect());
            pool.install(|| prover.prove_batch_parallel(black_box(&prepared), black_box(&stream_jobs)))
        }
        else {
            let stream_jobs: Vec<_> = requests.iter().map(|request| prover.make_job_prepared(&prepared, black_box(request)).expect("stream witness")).collect();
            pool.install(|| prover.prove_batch_parallel(black_box(&prepared), black_box(&stream_jobs)))
        };
        let elapsed = started.elapsed().as_nanos();
        assert_eq!(proofs.len(), requests.len());
        if i >= 1 { println!("timing,{mode},{run},{kind},{depth},{phase},{workers},{batch},{},{},0,", i - 1, elapsed); }
        for (index, (proof, request)) in proofs.into_iter().zip(&requests).enumerate() {
            let result = SyncResult { public_inputs: request.public_inputs.clone(), proof };
            // The saved baseline's full envelope was already accepted by both
            // verifiers in controls. Encoding includes every public-input limb
            // and proof coefficient/evaluation. Matching its canonical SHA256
            // reuses that positive result without duplicate verifier work.
            let bytes = prover.encode_sync_result(&prepared, &result).expect("canonical batch encoding");
            assert_eq!(hash(&bytes), baseline_hashes[index], "batch proof differs from verified sequential baseline");
        }
    }
}
