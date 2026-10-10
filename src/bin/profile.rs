//! v0.2 bottleneck profile harness (measurement-first, pre-optimization).
//!
//! Decomposes the single-proof prove cost into its cost classes so the
//! v0.2 throughput work optimizes only what measurement confirms:
//!
//!   - transcript hashing (Poseidon2 duplex): replayed EXACTLY from the
//!     produced proof (same Transcript API call sequence as the prover),
//!   - MLE evaluations (`eval_x`/`eval_y`, 2 per layer),
//!   - oracle-table allocation/zeroing (analytical count x measured
//!     unit cost; the workspace forbids `unsafe`, so no counting
//!     allocator - the count model is derived from `SparseLayerOracle`'s
//!     construction),
//!   - residual = field arithmetic of oracle construction + sumcheck
//!     folding/round evaluation.
//!
//! Plus component microbenchmarks (Poseidon2 compress, field ops) that
//! bound the vectorization (AVX-512) leverage, and a runtime CPU-feature
//! report. Laptop numbers are RELATIVE only (no AVX-512 here).
//!
//! Run: `cargo run --release --bin profile`.

// Measurement tool (not shipped): `expect`/`unwrap` on deterministic
// fixtures keeps the harness readable.
#![allow(clippy::expect_used, clippy::unwrap_used)]

use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOpKind,
    SmtOperation, SmtParams, SmtWitness, compile, generate_witness,
};
use statesync_gkr::gkr::{GateKind, GkrProof, LayeredCircuit, mle::mle_eval_base};
use statesync_gkr::primitives::Transcript;
use statesync_gkr::primitives::field::{BaseField, ChallengeField, PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{
    DEFAULT_LEAF_MAX_FIELDS, Digest, HashGadget, Poseidon2Gadget,
};
use statesync_gkr::{DOMAIN_TAG_V01, StateSyncGkrConfig, StateSyncProver, SyncRequest};
use std::hint::black_box;
use std::time::{Duration, Instant};

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

fn bench<F: FnMut()>(warmup: usize, iters: usize, mut op: F) -> Duration {
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
    xs[xs.len() / 2]
}

fn ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1000.0
}

/// Replay of the facade's S-5 transcript preamble (domain tag, circuit
/// digest, public inputs, claimed outputs). Mirrors the private
/// `observe_circuit_digest`/`observe_public_inputs` in src/lib.rs; if the
/// S-5 sequence ever changes, update BOTH (profiling replica only - the
/// prover never calls this).
fn replay_preamble(
    circuit: &LayeredCircuit<BaseField>,
    kind: SmtOpKind,
    depth: u32,
    commitment: &Digest<BaseField>,
    pi: &PublicInputs,
    outputs: &[BaseField],
) -> Transcript {
    let mut t = Transcript::new(DOMAIN_TAG_V01);
    t.observe_base(BaseField::from_u8(PublicInputs::kind_tag(kind)));
    t.observe_base(BaseField::from_u32(depth));
    t.observe_base(BaseField::from_u32(circuit.input_width_bits as u32));
    t.observe_base(BaseField::from_u32(circuit.layers.len() as u32));
    for layer in &circuit.layers {
        t.observe_base(BaseField::from_u32(layer.width_bits as u32));
        t.observe_base(BaseField::from_u32(layer.gates.len() as u32));
        t.observe_base(BaseField::from_u32(layer.consts.len() as u32));
    }
    t.observe_digest(commitment);
    t.observe_digest(&pi.old_root);
    t.observe_digest(&pi.new_root);
    t.observe_base(BaseField::from_u8(pi.op_kind_tag));
    t.observe_base(BaseField::from_u32(pi.asset_id.0 as u32));
    t.observe_base(BaseField::from_u32((pi.asset_id.0 >> 32) as u32));
    t.observe_digest(&pi.value_digest);
    t.observe_many(outputs);
    t
}

/// Replay the prover's ENTIRE transcript interaction (preamble + z0 draw +
/// per-round poly observation/challenge + per-layer eval observation +
/// carry challenge), driven by the actual produced proof, so the measured
/// cost is exactly the Fiat-Shamir hashing share of `prove`.
fn replay_full_transcript(
    circuit: &LayeredCircuit<BaseField>,
    kind: SmtOpKind,
    depth: u32,
    commitment: &Digest<BaseField>,
    pi: &PublicInputs,
    outputs: &[BaseField],
    proof: &GkrProof,
) {
    let mut t = replay_preamble(circuit, kind, depth, commitment, pi, outputs);
    for _ in 0..circuit.layers[0].width_bits {
        let _ = black_box(t.sample_challenge());
    }
    let n = proof.layer_proofs.len();
    for (i, lp) in proof.layer_proofs.iter().enumerate() {
        for rp in &lp.sumcheck.round_polys {
            for c in rp.coeffs() {
                t.observe_ext(*c);
            }
            let _ = black_box(t.sample_challenge());
        }
        t.observe_ext(lp.eval_x);
        t.observe_ext(lp.eval_y);
        if i + 1 < n {
            let _ = black_box(t.sample_challenge());
        }
    }
}

/// Analytical allocation count of the sparse oracle per proof: vectors of
/// `ChallengeField` zero-initialized (or clone/collect-initialized) during
/// `SparseLayerOracle::new` + `build_phase2`, in ELEMENTS. Derived from
/// reduce.rs: per layer, `w` (2^{s_out}) + lin_x/pow_x/amul_x/v_embed/vx
/// (5 x 2^{s_in}) + beta_y/mulx_y (2 x 2^{s_in}).
fn oracle_alloc_elems(circuit: &LayeredCircuit<BaseField>) -> u64 {
    let n = circuit.layers.len();
    let mut elems: u64 = 0;
    for (i, layer) in circuit.layers.iter().enumerate() {
        let s_in = if i + 1 < n {
            circuit.layers[i + 1].width_bits
        } else {
            circuit.input_width_bits
        };
        elems += (1u64 << layer.width_bits) + 7 * (1u64 << s_in);
    }
    elems
}

fn count_gates(circuit: &LayeredCircuit<BaseField>) -> (usize, usize) {
    let total: usize = circuit.layers.iter().map(|l| l.gates.len()).sum();
    let muls: usize = circuit
        .layers
        .iter()
        .flat_map(|l| l.gates.iter())
        .filter(|g| matches!(g.kind, GateKind::Mul))
        .count();
    (total, muls)
}

fn main() {
    println!("# SS-GKR v0.2 bottleneck profile (single proof, strategy A)");
    println!("# machine: relative numbers only (publishable absolutes = controlled server)");
    println!(
        "# cpu features: avx2={} avx512f={} (plonky3 vector backend is chosen at COMPILE time via target-cpu)",
        std::arch::is_x86_feature_detected!("avx2"),
        std::arch::is_x86_feature_detected!("avx512f"),
    );

    // --- component microbenchmarks -------------------------------------
    let h = Poseidon2Gadget::new(DEFAULT_LEAF_MAX_FIELDS);
    let a = Digest([f(123); 8]);
    let b = Digest([f(456); 8]);
    // h_node = one truncated Poseidon2 permutation (compress) + copies.
    let n_comp = 20_000u32;
    let t_comp = bench(2, 15, || {
        let mut acc = a;
        for _ in 0..n_comp {
            acc = h.compress(&acc, &b);
        }
        let _ = black_box(acc);
    });
    let perm_ns = t_comp.as_secs_f64() * 1e9 / n_comp as f64;

    // Extension-field (deg-4) and base-field multiply unit costs.
    let n_mul = 2_000_000u32;
    let mut x = ChallengeField::from_u32(3);
    let y = ChallengeField::from_u32(5);
    let t_efmul = bench(2, 15, || {
        let mut acc = x;
        for _ in 0..n_mul {
            acc = acc * y + x;
        }
        let _ = black_box(acc);
    });
    let ef_madd_ns = t_efmul.as_secs_f64() * 1e9 / n_mul as f64;
    x += ChallengeField::from_u32(1);

    let mut bx = f(3);
    let by = f(5);
    let t_bmul = bench(2, 15, || {
        let mut acc = bx;
        for _ in 0..n_mul {
            acc = acc * by + bx;
        }
        let _ = black_box(acc);
    });
    let b_madd_ns = t_bmul.as_secs_f64() * 1e9 / n_mul as f64;
    bx += f(1);

    // Zero-init allocation unit cost (vec![ZERO; 2^10] alloc+zero+drop).
    let n_alloc = 2_000u32;
    let t_alloc = bench(2, 15, || {
        for _ in 0..n_alloc {
            black_box(vec![ChallengeField::ZERO; 1 << 10]);
        }
    });
    let alloc_ns_per_elem = t_alloc.as_secs_f64() * 1e9 / (n_alloc as f64 * 1024.0);

    println!("\n## component unit costs (median)");
    println!("poseidon2 compress (~1 permutation): {perm_ns:>9.1} ns");
    println!("EF (deg-4) mul+add:                  {ef_madd_ns:>9.2} ns");
    println!("base mul+add:                        {b_madd_ns:>9.2} ns");
    println!("EF vec zero-init (per elem):         {alloc_ns_per_elem:>9.2} ns");

    // --- per-op stage decomposition ------------------------------------
    println!("\n## prove decomposition (d=24, median ms; share of gkr_prove)");
    println!(
        "{:<14} {:>9} {:>9} {:>10} {:>11} {:>9} {:>10} {:>10} {:>9}",
        "kind",
        "compile",
        "witness",
        "gkr_prove",
        "transcript",
        "mle_ev",
        "alloc_est",
        "residual",
        "tr_%"
    );

    let d = 24u32;
    let template = Poseidon2Gadget::new(DEFAULT_LEAF_MAX_FIELDS).round_template();
    let strat = LayerStrategy::A;
    for (label, req) in [
        ("membership", membership_request(d)),
        ("nonmembership", nonmembership_request(d)),
        ("update", update_request(d)),
    ] {
        let params = SmtParams {
            depth: d,
            ..Default::default()
        };
        let kind = req.operation.kind();
        let circuit = compile(&params, kind, strat, &template).expect("compile");
        let witness = generate_witness(
            &params,
            strat,
            &circuit,
            &req.operation,
            &req.public_inputs,
            &req.witness,
        )
        .expect("witness");
        let outputs = witness.layer_values[0].clone();
        let prover = StateSyncProver::new(StateSyncGkrConfig {
            smt: params,
            layer_strategy: strat,
            ..Default::default()
        });
        let result = prover.prove_sync_op(&req).expect("prove");
        let proof = &result.proof;
        let commitment = statesync_gkr::wrap::commitment::full_circuit_commitment(
            &circuit, kind, &params, strat,
        );

        let t_compile = bench(2, 30, || {
            black_box(compile(&params, kind, strat, &template).expect("compile"));
        });
        let t_witness = bench(2, 30, || {
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
        let t_full = bench(2, 12, || {
            black_box(prover.prove_sync_op(black_box(&req)).expect("prove"));
        });
        let gkr_ms = ms(t_full) - ms(t_compile) - ms(t_witness);

        // Fiat-Shamir share: the full transcript interaction replayed from
        // the actual proof.
        let t_transcript = bench(2, 12, || {
            replay_full_transcript(
                &circuit,
                kind,
                d,
                &commitment,
                &req.public_inputs,
                &outputs,
                proof,
            );
        });

        // MLE-evaluation share: eval_x/eval_y per layer at real points.
        // Points drawn once (fixed), evaluations measured on the real
        // layer-below witness vectors.
        let mut t_probe =
            replay_preamble(&circuit, kind, d, &commitment, &req.public_inputs, &outputs);
        let eval_jobs: Vec<(usize, Vec<ChallengeField>)> = (0..circuit.layers.len())
            .map(|i| {
                let s_in = if i + 1 < circuit.layers.len() {
                    circuit.layers[i + 1].width_bits
                } else {
                    circuit.input_width_bits
                };
                let pt: Vec<ChallengeField> =
                    (0..s_in).map(|_| t_probe.sample_challenge()).collect();
                (i, pt)
            })
            .collect();
        let t_mle = bench(1, 8, || {
            for (i, pt) in &eval_jobs {
                let v_below = &witness.layer_values[i + 1];
                let _ = black_box(mle_eval_base(v_below, pt));
                let _ = black_box(mle_eval_base(v_below, pt));
            }
        });

        // Oracle allocation estimate (analytical count x measured unit).
        let alloc_elems = oracle_alloc_elems(&circuit);
        let alloc_ms = alloc_elems as f64 * alloc_ns_per_elem / 1e6;

        let residual = gkr_ms - ms(t_transcript) - ms(t_mle) - alloc_ms;
        let tr_pct = 100.0 * ms(t_transcript) / gkr_ms;

        println!(
            "{label:<14} {:>9.3} {:>9.3} {:>10.3} {:>11.3} {:>9.3} {:>10.3} {:>10.3} {:>8.1}%",
            ms(t_compile),
            ms(t_witness),
            gkr_ms,
            ms(t_transcript),
            ms(t_mle),
            alloc_ms,
            residual,
            tr_pct,
        );

        let (gates, muls) = count_gates(&circuit);
        let rounds: usize = proof
            .layer_proofs
            .iter()
            .map(|lp| lp.sumcheck.round_polys.len())
            .sum();
        println!(
            "  [structure] layers={} gates={} muls={} sumcheck_rounds={} oracle_alloc_elems={} (~{:.1} MB zeroed/proof)",
            circuit.layers.len(),
            gates,
            muls,
            rounds,
            alloc_elems,
            alloc_elems as f64 * 16.0 / 1e6,
        );
    }

    println!(
        "\n# reading: `transcript` is the Fiat-Shamir hashing share (Poseidon2 duplex).\n\
         # `residual` = oracle-construction + sumcheck folding field arithmetic\n\
         # (the AVX-512 field-vectorization target). Batch amortization can only\n\
         # share compile (and the verifier's derive) - every other stage above is\n\
         # (challenge, witness)-dependent per job, so its lever is parallelism,\n\
         # not sharing (ADR-0001)."
    );
}
