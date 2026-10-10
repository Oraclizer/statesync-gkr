//! Module-1 measurement harness (structure-invariant; config only).
//!
//! Zero external deps: a `std::time` median/variance harness replaces
//! criterion, which cannot build on this GNU target (its `clap`/`windows-sys`
//! chain needs a `dlltool` sub-tool the bundled binutils lacks). This machine
//! (Core Ultra X9, AVX2, NO AVX-512) yields RELATIVE / structural-fit numbers
//! only; publishable absolutes come from the controlled AVX-512 server run.
//!
//! Post-2d core: in-circuit Poseidon2 (the production hash, replacing the
//! 2c-era ArithHash placeholder) over the SPARSE Libra-style booking oracle
//! (O(#gates + 2^s) per layer, replacing the dense O(2^{2s}) factor tables).
//! The 2c run of this same harness is the pre-2d floor REPORT.md compares
//! against.
//!
//! Run: `cargo run --release --bin measure`.

// Measurement tool (not shipped, not the prover): `expect`/`unwrap` on
// deterministic fixtures is fine here and keeps the harness readable.
#![allow(clippy::expect_used, clippy::unwrap_used)]

use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOpKind,
    SmtOperation, SmtParams, SmtWitness, compile, compile_with_hints, generate_witness,
};
use statesync_gkr::gkr::DerivedRegularWiring;
use statesync_gkr::gkr::GateKind;
use statesync_gkr::primitives::field::{BaseField, ChallengeField, PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{
    DEFAULT_LEAF_MAX_FIELDS, Digest, HashGadget, Poseidon2Gadget,
};
use statesync_gkr::{StateSyncGkrConfig, StateSyncProver, SyncRequest};
use std::hint::black_box;
use std::time::{Duration, Instant};

const DEPTHS: [u32; 3] = [24, 28, 32];
const EF_BYTES: usize = std::mem::size_of::<ChallengeField>();

fn f(x: u32) -> BaseField {
    BaseField::from_u32(x)
}

fn siblings(depth: usize) -> Vec<Digest<BaseField>> {
    (0..depth)
        .map(|i| Digest([f(i as u32 * 13 + 1); 8]))
        .collect()
}

fn membership_request(depth: u32) -> SyncRequest {
    let h = Poseidon2Gadget::new(DEFAULT_LEAF_MAX_FIELDS);
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
    let old_root = path
        .compute_root(&h, &params, key, &leaf)
        .unwrap_or(Digest::zero());
    let value_digest = h.hash_leaf(&leaf.encode()).expect("in-bound leaf encoding");
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

fn update_request(depth: u32) -> SyncRequest {
    let h = Poseidon2Gadget::new(DEFAULT_LEAF_MAX_FIELDS);
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
    let old_root = path
        .compute_root(&h, &params, key, &old_leaf)
        .unwrap_or(Digest::zero());
    let new_root = path
        .compute_root(&h, &params, key, &new_leaf)
        .unwrap_or(Digest::zero());
    let value_digest = h
        .hash_leaf(&new_leaf.encode())
        .expect("in-bound leaf encoding");
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

fn nonmembership_request(depth: u32) -> SyncRequest {
    let h = Poseidon2Gadget::new(DEFAULT_LEAF_MAX_FIELDS);
    let params = SmtParams {
        depth,
        ..Default::default()
    };
    let key = AssetId(6);
    let leaf = LeafState::Empty;
    let path = MerklePath {
        siblings: siblings(depth as usize),
    };
    let old_root = path
        .compute_root(&h, &params, key, &leaf)
        .unwrap_or(Digest::zero());
    let value_digest = h.hash_leaf(&leaf.encode()).expect("in-bound leaf encoding");
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

/// median, min, and coefficient of variation (stddev/mean, a determinism proxy).
struct Stat {
    median: Duration,
    min: Duration,
    cv_pct: f64,
}

fn bench<F: FnMut()>(warmup: usize, iters: usize, mut op: F) -> Stat {
    for _ in 0..warmup {
        op();
    }
    let mut xs: Vec<Duration> = Vec::with_capacity(iters);
    for _ in 0..iters {
        let t = Instant::now();
        op();
        xs.push(t.elapsed());
    }
    xs.sort();
    let median = xs[xs.len() / 2];
    let min = xs[0];
    let mean = xs.iter().map(|d| d.as_secs_f64()).sum::<f64>() / xs.len() as f64;
    let var = xs
        .iter()
        .map(|d| (d.as_secs_f64() - mean).powi(2))
        .sum::<f64>()
        / xs.len() as f64;
    let cv_pct = if mean > 0.0 {
        100.0 * var.sqrt() / mean
    } else {
        0.0
    };
    Stat {
        median,
        min,
        cv_pct,
    }
}

fn ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1000.0
}

/// Field elements carried by a GKR proof (the on-wire, pre-wrap size).
fn proof_field_elems(proof: &statesync_gkr::gkr::GkrProof) -> usize {
    proof
        .layer_proofs
        .iter()
        .map(|lp| {
            let rounds: usize = lp
                .sumcheck
                .round_polys
                .iter()
                .map(|rp| rp.coeffs().len())
                .sum();
            rounds + 2 // eval_x, eval_y
        })
        .sum()
}

fn main() {
    let template = Poseidon2Gadget::new(DEFAULT_LEAF_MAX_FIELDS).round_template();
    let strat = LayerStrategy::A;

    println!("# SS-GKR 2d measurement (strategy A, in-circuit Poseidon2, sparse oracle)");
    println!("# machine: Core Ultra X9, AVX2, no AVX-512 -> RELATIVE numbers only");
    println!("# EF (KoalaBear deg-4) = {EF_BYTES} bytes/elem\n");

    println!(
        "{:<12} {:>3} {:>8} {:>7} {:>8} {:>8} {:>9} {:>8} {:>9} {:>7} {:>8} {:>10} {:>10} {:>7} {:>10}",
        "kind",
        "d",
        "in_w",
        "s_bits",
        "layers",
        "gates",
        "compile",
        "witness",
        "gkr_prove",
        "verify",
        "v_setup",
        "gkr_verify",
        "verify_ref",
        "cv%",
        "oracle_KB"
    );
    for &d in &DEPTHS {
        for (label, req) in [
            ("membership", membership_request(d)),
            ("update", update_request(d)),
        ] {
            let params = SmtParams {
                depth: d,
                ..Default::default()
            };
            let kind: SmtOpKind = req.operation.kind();
            let circuit = compile(&params, kind, strat, &template).expect("compile");
            let s = circuit.input_width_bits;
            let in_w: u32 = 1u32 << s;
            let layers = circuit.layers.len();
            let gates: usize = circuit.layers.iter().map(|l| l.gates.len()).sum();
            // Sparse-oracle peak (Libra-style booking, 2d): per layer, phase 1
            // holds four 2^{s_in} EF tables (lin/pow/vx/amul) plus the Mul gate
            // list (~32 B/gate); the dense 2^{2s} factor tables are gone. Max
            // over layers. (2c's dense peak for comparison: 6 * 2^{2s} * 16 B.)
            let oracle_kb = circuit
                .layers
                .iter()
                .enumerate()
                .map(|(i, layer)| {
                    let s_in = if i + 1 < circuit.layers.len() {
                        circuit.layers[i + 1].width_bits
                    } else {
                        circuit.input_width_bits
                    };
                    let muls = layer
                        .gates
                        .iter()
                        .filter(|g| matches!(g.kind, GateKind::Mul))
                        .count() as u64;
                    (4u64 << s_in) * EF_BYTES as u64 + muls * 32
                })
                .max()
                .unwrap_or(0) as f64
                / 1024.0;

            let prover = StateSyncProver::new(StateSyncGkrConfig {
                smt: params,
                layer_strategy: strat,
                ..Default::default()
            });

            let c = bench(2, 40, || {
                black_box(compile(&params, kind, strat, &template).expect("compile"));
            });
            let w = bench(2, 40, || {
                black_box(
                    generate_witness(
                        &params,
                        strat,
                        &circuit,
                        &req.operation,
                        &req.public_inputs,
                        &req.witness,
                    )
                    .expect("witness"),
                );
            });
            let full = bench(2, 10, || {
                black_box(prover.prove_sync_op(black_box(&req)).expect("prove"));
            });
            let result = prover.prove_sync_op(&req).expect("prove");
            // verify = the production path (succinct derived wiring, full
            // cost incl. its per-call setup); v_setup = the amortizable
            // verifier setup alone (compile_with_hints + derive, cacheable
            // across a batch exactly like the prover's compile); gkr_verify
            // = verify - v_setup (the per-proof marginal cost); verify_ref =
            // the O(#gates) TableWiring reference on the SAME circuit.
            let v = bench(3, 30, || {
                black_box(prover.verify_sync_op(black_box(&req), black_box(&result)));
            });
            let vs = bench(2, 20, || {
                let (circuit, hints) =
                    compile_with_hints(&params, kind, strat, &template).expect("compile");
                black_box(DerivedRegularWiring::derive(&circuit, &hints));
            });
            let vr = bench(1, 10, || {
                black_box(prover.verify_sync_op_reference(black_box(&req), black_box(&result)));
            });
            // gkr_prove is derived: full prove minus the (amortizable) compile
            // and witness shares.
            let gkr = ms(full.median) - ms(c.median) - ms(w.median);
            let gkr_v = ms(v.median) - ms(vs.median);

            println!(
                "{label:<12} {d:>3} {in_w:>8} {s:>7} {layers:>8} {gates:>8} {:>8.3} {:>8.3} {:>9.3} {:>7.3} {:>8.3} {:>10.3} {:>10.3} {:>7.1} {:>10.1}",
                ms(c.median),
                ms(w.median),
                gkr.max(0.0),
                ms(v.median),
                ms(vs.median),
                gkr_v.max(0.0),
                ms(vr.median),
                full.cv_pct,
                oracle_kb,
            );
            let _ = (full.min, v.min, vr.min);
        }
    }

    // Proof size (op-kind x depth), pre-wrap.
    println!("\n# proof size (pre-wrap GKR proof)");
    println!("{:<12} {:>3} {:>10} {:>10}", "kind", "d", "elems", "KB");
    for &d in &DEPTHS {
        for (label, req) in [
            ("membership", membership_request(d)),
            ("update", update_request(d)),
        ] {
            let prover = StateSyncProver::new(StateSyncGkrConfig {
                smt: SmtParams {
                    depth: d,
                    ..Default::default()
                },
                layer_strategy: strat,
                ..Default::default()
            });
            let result = prover.prove_sync_op(&req).expect("prove");
            let elems = proof_field_elems(&result.proof);
            let kb = (elems * EF_BYTES) as f64 / 1024.0;
            println!("{label:<12} {d:>3} {elems:>10} {kb:>10.3}");
        }
    }

    // Single-thread throughput (proofs/sec) via batch prove over one shared
    // compiled circuit (v0.1 baseline: compile amortized per batch).
    println!("\n# batch throughput (membership, single thread, v0.1 path, proofs/sec)");
    println!(
        "{:<3} {:>6} {:>12} {:>12}",
        "d", "batch", "total_ms", "proofs/s"
    );
    for &d in &DEPTHS {
        let prover = StateSyncProver::new(StateSyncGkrConfig {
            smt: SmtParams {
                depth: d,
                ..Default::default()
            },
            layer_strategy: strat,
            ..Default::default()
        });
        let req = membership_request(d);
        let job = prover.make_job(&req).expect("job");
        for batch in [8usize, 16, 32] {
            let jobs = vec![job.clone(); batch];
            let t = Instant::now();
            let proofs = black_box(prover.prove_batch(SmtOpKind::Membership, &jobs));
            let el = t.elapsed();
            assert_eq!(proofs.len(), batch);
            let pps = batch as f64 / el.as_secs_f64();
            println!("{d:>3} {batch:>6} {:>12.1} {pps:>12.1}", ms(el));
        }
    }

    // ------------------------------------------------------------------
    // v0.2 measurement grid (ADR-0001): amortized batch x op kind,
    // parallel workers, end-to-end stream, prepared verify.
    // d = 24 (the genesis default; the depth axis is covered by the
    // single-path table above - layer count and marginal costs are
    // depth-flat by construction).
    // ------------------------------------------------------------------
    let d = 24u32;
    let prover = StateSyncProver::new(StateSyncGkrConfig {
        smt: SmtParams {
            depth: d,
            ..Default::default()
        },
        layer_strategy: strat,
        ..Default::default()
    });
    let cores = std::thread::available_parallelism()
        .map(std::num::NonZeroUsize::get)
        .unwrap_or(1);
    println!(
        "\n# v0.2 grid (d=24). cpu: {cores} logical cores, avx2={}, avx512f={} \
         (vector backend fixed at compile time via target-cpu)",
        std::arch::is_x86_feature_detected!("avx2"),
        std::arch::is_x86_feature_detected!("avx512f"),
    );

    // (A) Amortized batch grid: per-item cost of the three request paths -
    // single (compile per request), v0.1 batch (compile per batch), v0.2
    // prepared (compile amortized away entirely). Single thread.
    println!("\n## (A) batch amortization x kind (single thread, per-item ms | proofs/s)");
    println!(
        "{:<14} {:>6} {:>16} {:>16} {:>16}",
        "kind", "batch", "single-path", "v0.1_batch", "v0.2_prepared"
    );
    for (label, req) in [
        ("membership", membership_request(d)),
        ("nonmembership", nonmembership_request(d)),
        ("update", update_request(d)),
    ] {
        let kind = req.operation.kind();
        let prepared = prover.prepare(kind).expect("prepare");
        let job = prover.make_job_prepared(&prepared, &req).expect("job");
        // Single-path per-item cost (compile + witness + prove per request).
        let single = bench(1, 6, || {
            let _ = black_box(prover.prove_sync_op(black_box(&req)).expect("prove"));
        });
        for batch in [1usize, 2, 4, 8, 16, 32] {
            let jobs = vec![job.clone(); batch];
            // v0.1: compile once PER BATCH, then per-job prove.
            let t = Instant::now();
            let p1 = black_box(prover.prove_batch(kind, &jobs));
            let v01 = t.elapsed();
            // v0.2: long-lived prepared state, witness->prove only.
            let t = Instant::now();
            let p2 = black_box(prover.prove_batch_prepared(&prepared, &jobs));
            let v02 = t.elapsed();
            assert_eq!(p1.len(), batch);
            assert_eq!(p2.len(), batch);
            let per = |el: Duration| ms(el) / batch as f64;
            let pps = |el: Duration| batch as f64 / el.as_secs_f64();
            println!(
                "{label:<14} {batch:>6} {:>9.1} | {:>4.1} {:>9.1} | {:>4.1} {:>9.1} | {:>4.1}",
                ms(single.median),
                1000.0 / ms(single.median),
                per(v01),
                pps(v01),
                per(v02),
                pps(v02),
            );
        }
    }

    // (B) Parallel workers (prepared circuit, batch proved via rayon pool).
    // speedup = sequential_total / parallel_total; efficiency = speedup/workers.
    println!("\n## (B) parallel workers (v0.2 prepared, batch=32, rayon pool)");
    println!(
        "{:<14} {:>8} {:>12} {:>12} {:>9} {:>11}",
        "kind", "workers", "total_ms", "proofs/s", "speedup", "efficiency"
    );
    for (label, req) in [
        ("membership", membership_request(d)),
        ("update", update_request(d)),
    ] {
        let kind = req.operation.kind();
        let prepared = prover.prepare(kind).expect("prepare");
        let job = prover.make_job_prepared(&prepared, &req).expect("job");
        let jobs = vec![job.clone(); 32];
        let t = Instant::now();
        let seq = black_box(prover.prove_batch_prepared(&prepared, &jobs));
        let seq_el = t.elapsed();
        assert_eq!(seq.len(), 32);
        for workers in [1usize, 2, 4, 8, cores] {
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(workers)
                .build()
                .expect("pool");
            // Warm once (thread spawn cost), then measure.
            let _ = black_box(pool.install(|| prover.prove_batch_parallel(&prepared, &jobs)));
            let t = Instant::now();
            let par = black_box(pool.install(|| prover.prove_batch_parallel(&prepared, &jobs)));
            let el = t.elapsed();
            assert_eq!(par.len(), 32);
            let speedup = seq_el.as_secs_f64() / el.as_secs_f64();
            println!(
                "{label:<14} {workers:>8} {:>12.1} {:>12.1} {:>9.2} {:>10.1}%",
                ms(el),
                32.0 / el.as_secs_f64(),
                speedup,
                100.0 * speedup / workers as f64,
            );
        }
    }

    // (C) End-to-end stream (the deployment shape): fresh requests ->
    // make_job_prepared (witness generation) -> parallel batch prove, all
    // on the long-lived prepared state, full pool.
    println!("\n## (C) end-to-end stream (requests -> jobs -> parallel prove, full pool)");
    println!(
        "{:<14} {:>6} {:>12} {:>12}",
        "kind", "n", "total_ms", "syncs/s"
    );
    for (label, req) in [
        ("membership", membership_request(d)),
        ("update", update_request(d)),
    ] {
        let kind = req.operation.kind();
        let prepared = prover.prepare(kind).expect("prepare");
        let n = 64usize;
        let t = Instant::now();
        let jobs: Vec<_> = (0..n)
            .map(|_| prover.make_job_prepared(&prepared, &req).expect("job"))
            .collect();
        let proofs = black_box(prover.prove_batch_parallel(&prepared, &jobs));
        let el = t.elapsed();
        assert_eq!(proofs.len(), n);
        println!(
            "{label:<14} {n:>6} {:>12.1} {:>12.1}",
            ms(el),
            n as f64 / el.as_secs_f64()
        );
    }

    // (D) Prepared verify (marginal cost amortized via prepare): batch of
    // 32 verifications on one prepared verifier, single thread.
    println!("\n## (D) prepared verify (batch=32, single thread)");
    println!(
        "{:<14} {:>12} {:>12} {:>14}",
        "kind", "total_ms", "verifies/s", "per-verify_ms"
    );
    for (label, req) in [
        ("membership", membership_request(d)),
        ("update", update_request(d)),
    ] {
        let kind = req.operation.kind();
        let prepared = prover.prepare(kind).expect("prepare");
        let result = prover
            .prove_sync_op_prepared(&prepared, &req)
            .expect("prove");
        let t = Instant::now();
        for _ in 0..32 {
            assert!(black_box(prover.verify_sync_op_prepared(
                &prepared,
                black_box(&req),
                black_box(&result)
            )));
        }
        let el = t.elapsed();
        println!(
            "{label:<14} {:>12.1} {:>12.1} {:>14.2}",
            ms(el),
            32.0 / el.as_secs_f64(),
            ms(el) / 32.0
        );
    }

    // (E) Tail latency (N1 evidence shape; laptop numbers are relative -
    // the publishable tail comes from the controlled server): per-item
    // prove latency distribution on the prepared path, 80 samples.
    println!("\n## (E) per-proof latency tail (v0.2 prepared, single thread, 80 samples)");
    println!(
        "{:<14} {:>9} {:>9} {:>9} {:>9} {:>9}",
        "kind", "p50_ms", "p90_ms", "p95_ms", "p99_ms", "max_ms"
    );
    for (label, req) in [
        ("membership", membership_request(d)),
        ("nonmembership", nonmembership_request(d)),
        ("update", update_request(d)),
    ] {
        let kind = req.operation.kind();
        let prepared = prover.prepare(kind).expect("prepare");
        let mut xs: Vec<Duration> = Vec::with_capacity(80);
        for _ in 0..3 {
            let _ = black_box(
                prover
                    .prove_sync_op_prepared(&prepared, &req)
                    .expect("prove"),
            );
        }
        for _ in 0..80 {
            let t = Instant::now();
            let _ = black_box(
                prover
                    .prove_sync_op_prepared(&prepared, &req)
                    .expect("prove"),
            );
            xs.push(t.elapsed());
        }
        xs.sort();
        let pct = |p: f64| xs[((xs.len() as f64 - 1.0) * p) as usize];
        println!(
            "{label:<14} {:>9.1} {:>9.1} {:>9.1} {:>9.1} {:>9.1}",
            ms(pct(0.50)),
            ms(pct(0.90)),
            ms(pct(0.95)),
            ms(pct(0.99)),
            ms(*xs.last().expect("samples")),
        );
    }
}
