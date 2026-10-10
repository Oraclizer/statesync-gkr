//! v0.3 external-proof-boundary checks: inner-proof-v1 encoding
//! round-trip + full reject taxonomy, golden vectors, the full circuit
//! commitment, the wrap relation/pipeline, and the KoalaBear -> BN254
//! field bridge.
//!
//! Golden vectors: tests/vectors/inner-proof-v1/*.bin are the COMMITTED
//! canonical bytes of one honest proof per op kind at the default config
//! (d = 24). Proofs are deterministic, so these bytes are stable
//! across builds and machines (the cross-build digest CI leg guards the
//! same property); any byte change here is a protocol/encoding change
//! and must bump a version axis. Regenerate ONLY on an intentional
//! version bump: `cargo test --release generate_golden_vectors -- --ignored`.
//!
//! (Batch-size vectors are deliberately absent: ADR-0001 fixes a batch to
//! a sequence of ordinary inner proofs, bit-identical to the single path
//! - pinned by tests/batch_v02.rs - so batched bytes ARE these bytes.)

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOpKind,
    SmtOperation, SmtParams, SmtWitness,
};
use statesync_gkr::gkr::{Gate, GateKind, Layer, LayeredCircuit};
use statesync_gkr::primitives::field::{BaseField, PrimeCharacteristicRing, PrimeField32};
use statesync_gkr::primitives::hash::{Digest, HashGadget, Poseidon2Gadget};
use statesync_gkr::wrap::commitment::full_circuit_commitment;
use statesync_gkr::wrap::encoding::{
    DecodeError, MAGIC, PROOF_ENCODING_VERSION, ROUND_POLY_COEFFS, decode_inner_proof,
    encode_inner_proof,
};
use statesync_gkr::wrap::statement::{
    BN254_R_BE, Bn254Fr, WRAP_STATEMENT_VERSION, pack_digest, unpack_digest, wrap_statement_v1,
};
use statesync_gkr::wrap::{MockWrapBackend, WrapBackend, WrapInput};
use statesync_gkr::{StateSyncGkrConfig, StateSyncProver, SyncRequest};
use std::path::PathBuf;

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

fn kind_slug(kind: SmtOpKind) -> &'static str {
    match kind {
        SmtOpKind::Membership => "membership",
        SmtOpKind::NonMembership => "nonmembership",
        SmtOpKind::Update => "update",
    }
}

/// Prove one request and produce (prover, prepared, request, canonical bytes).
fn encoded_fixture(
    kind: SmtOpKind,
    depth: usize,
) -> (
    StateSyncProver,
    statesync_gkr::PreparedSync,
    SyncRequest,
    Vec<u8>,
) {
    let prover = StateSyncProver::new(config(depth as u32));
    let prepared = prover.prepare(kind).expect("prepare");
    let request = request_for(kind, depth, 5);
    let result = prover
        .prove_sync_op_prepared(&prepared, &request)
        .expect("prove");
    let bytes = prover
        .encode_sync_result(&prepared, &result)
        .expect("encode");
    (prover, prepared, request, bytes)
}

fn vector_path(kind: SmtOpKind) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/vectors/inner-proof-v1")
        .join(format!("{}-d24.bin", kind_slug(kind)))
}

// ---------------------------------------------------------------------
// Round-trip + verification through the encoded boundary
// ---------------------------------------------------------------------

#[test]
fn encode_decode_roundtrip_all_kinds() {
    for kind in KINDS {
        let (prover, prepared, request, bytes) = encoded_fixture(kind, 24);

        // decode(encode) recovers the exact envelope values...
        let env = decode_inner_proof(&bytes).expect("decode");
        assert_eq!(
            env.identity,
            prover.circuit_identity(&prepared).unwrap(),
            "{kind:?}: identity survives the round-trip"
        );
        assert_eq!(env.public_inputs, request.public_inputs);
        // ...and encode(decode) is byte-identical (canonical form).
        let re = encode_inner_proof(&env).expect("re-encode");
        assert_eq!(re, bytes, "{kind:?}: canonical bytes are a fixed point");

        // The encoded proof verifies end-to-end through the boundary.
        assert!(
            prover.verify_encoded_sync_op(&prepared, &request, &bytes),
            "{kind:?}: encoded honest proof verifies"
        );
    }
}

#[test]
fn encoded_proof_rejects_any_single_byte_flip_in_identity_and_statement() {
    let (prover, prepared, request, bytes) = encoded_fixture(SmtOpKind::Membership, 24);
    // Flip one byte in every identity/statement position (offsets 17..166):
    // each flip must kill acceptance (decode reject, identity mismatch, or
    // cryptographic reject) - never survive.
    for at in 17..166 {
        let mut t = bytes.clone();
        t[at] ^= 1;
        assert!(
            !prover.verify_encoded_sync_op(&prepared, &request, &t),
            "byte {at}: flipped identity/statement byte must not verify"
        );
    }
}

#[test]
fn encoded_proof_rejects_tampered_payload() {
    let (prover, prepared, request, bytes) = encoded_fixture(SmtOpKind::Update, 24);
    // A payload coefficient deep inside the proof (well past the statement).
    let at = 500;
    let mut t = bytes.clone();
    t[at] ^= 1;
    assert!(!prover.verify_encoded_sync_op(&prepared, &request, &t));
}

#[test]
fn encoded_proof_rejects_cross_kind() {
    let (prover, _, _, bytes) = encoded_fixture(SmtOpKind::Membership, 24);
    let prepared_nm = prover.prepare(SmtOpKind::NonMembership).unwrap();
    let request_nm = nonmembership_request(24, 5);
    assert!(!prover.verify_encoded_sync_op(&prepared_nm, &request_nm, &bytes));
}

// ---------------------------------------------------------------------
// Decoder reject taxonomy - every error code is reachable and exact
// ---------------------------------------------------------------------

#[test]
fn decode_reject_taxonomy_is_complete() {
    let (_, _, _, bytes) = encoded_fixture(SmtOpKind::Membership, 24);

    // HeaderTooShort
    assert_eq!(
        decode_inner_proof(&bytes[..10]),
        Err(DecodeError::HeaderTooShort { have: 10 })
    );
    // BadMagic
    let mut t = bytes.clone();
    t[0] ^= 1;
    assert_eq!(decode_inner_proof(&t), Err(DecodeError::BadMagic));
    // UnsupportedProofEncodingVersion
    let mut t = bytes.clone();
    t[8] = 9;
    assert_eq!(
        decode_inner_proof(&t),
        Err(DecodeError::UnsupportedProofEncodingVersion(9))
    );
    // UnsupportedProtocolVersion
    let mut t = bytes.clone();
    t[10] = 9;
    assert_eq!(
        decode_inner_proof(&t),
        Err(DecodeError::UnsupportedProtocolVersion(9))
    );
    // UnsupportedProofKind
    let mut t = bytes.clone();
    t[12] = 7;
    assert_eq!(
        decode_inner_proof(&t),
        Err(DecodeError::UnsupportedProofKind(7))
    );
    // DeclaredLengthMismatch (truncate the buffer, keep the header intact)
    let t = &bytes[..bytes.len() - 1];
    assert_eq!(
        decode_inner_proof(t),
        Err(DecodeError::DeclaredLengthMismatch {
            declared: bytes.len() as u32,
            actual: bytes.len() - 1,
        })
    );
    // UnknownOpKindTag (identity section)
    let mut t = bytes.clone();
    t[17] = 3;
    assert_eq!(
        decode_inner_proof(&t),
        Err(DecodeError::UnknownOpKindTag(3))
    );
    // UnsupportedCircuitVersion
    let mut t = bytes.clone();
    t[22] = 9;
    assert_eq!(
        decode_inner_proof(&t),
        Err(DecodeError::UnsupportedCircuitVersion(9))
    );
    // UnsupportedLeafEncodingVersion
    let mut t = bytes.clone();
    t[24] = 9;
    assert_eq!(
        decode_inner_proof(&t),
        Err(DecodeError::UnsupportedLeafEncodingVersion(9))
    );
    // UnsupportedLayerStrategy
    let mut t = bytes.clone();
    t[28] = 1;
    assert_eq!(
        decode_inner_proof(&t),
        Err(DecodeError::UnsupportedLayerStrategy(1))
    );
    // OpKindMismatch (statement tag differs; membership fixture has tag 0)
    let mut t = bytes.clone();
    t[125] = 1;
    assert_eq!(
        decode_inner_proof(&t),
        Err(DecodeError::OpKindMismatch {
            identity: 0,
            statement: 1,
        })
    );
    // NonCanonicalFieldElement: set the first commitment limb to p.
    let mut t = bytes.clone();
    t[29..33].copy_from_slice(&BaseField::ORDER_U32.to_le_bytes());
    assert_eq!(
        decode_inner_proof(&t),
        Err(DecodeError::NonCanonicalFieldElement { offset: 29 })
    );
    // BadRoundPolyArity: first round poly's count byte lives right after
    // layer_count (u32) + first rp_count (u32) = offset 174.
    let mut t = bytes.clone();
    assert_eq!(t[174] as usize, ROUND_POLY_COEFFS, "layout anchor");
    t[174] = 4;
    assert_eq!(
        decode_inner_proof(&t),
        Err(DecodeError::BadRoundPolyArity {
            layer: 0,
            round: 0,
            got: 4,
        })
    );
    // OversizedCount: blow up the first layer's rp_count beyond the buffer.
    let mut t = bytes.clone();
    t[170..174].copy_from_slice(&u32::MAX.to_le_bytes());
    assert_eq!(
        decode_inner_proof(&t),
        Err(DecodeError::OversizedCount { offset: 170 })
    );
    // TrailingBytes: append one byte AND patch the declared total so the
    // header stays consistent (isolating the trailing-byte check).
    let mut t = bytes.clone();
    t.push(0);
    let total = (t.len() as u32).to_le_bytes();
    t[13..17].copy_from_slice(&total);
    assert!(matches!(
        decode_inner_proof(&t),
        Err(DecodeError::TrailingBytes { extra: _ }) | Err(DecodeError::OversizedCount { .. })
    ));
    // Truncated: cut inside the statement AND patch the declared total.
    // The cursor reads new_root element-wise from offset 93; the first
    // element that no longer fits starts at 97.
    let mut t = bytes[..100].to_vec();
    let total = (t.len() as u32).to_le_bytes();
    t[13..17].copy_from_slice(&total);
    assert_eq!(
        decode_inner_proof(&t),
        Err(DecodeError::Truncated { offset: 97 })
    );
}

// ---------------------------------------------------------------------
// Golden vectors (committed canonical bytes)
// ---------------------------------------------------------------------

/// Regenerates the committed vectors. Run ONLY on an intentional version
/// bump; a diff under an unchanged version is a frozen-boundary breach.
#[test]
#[ignore = "generator - run manually on an intentional version bump only"]
fn generate_golden_vectors() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/vectors/inner-proof-v1");
    std::fs::create_dir_all(&dir).unwrap();
    for kind in KINDS {
        let (_, _, _, bytes) = encoded_fixture(kind, 24);
        std::fs::write(vector_path(kind), &bytes).unwrap();
    }
}

#[test]
fn golden_vectors_are_stable_and_verify() {
    for kind in KINDS {
        let path = vector_path(kind);
        let committed = std::fs::read(&path).unwrap_or_else(|_| {
            panic!(
                "missing golden vector {} - generate once with \
                 `cargo test --release generate_golden_vectors -- --ignored`",
                path.display()
            )
        });
        let (prover, prepared, request, fresh) = encoded_fixture(kind, 24);
        assert_eq!(
            fresh, committed,
            "{kind:?}: canonical bytes drifted from the committed golden \
             vector - protocol/encoding change without a version bump"
        );
        assert!(prover.verify_encoded_sync_op(&prepared, &request, &committed));
    }
}

// ---------------------------------------------------------------------
// Full circuit commitment
// ---------------------------------------------------------------------

#[test]
fn commitment_matches_between_prepared_and_direct() {
    let prover = StateSyncProver::new(config(24));
    for kind in KINDS {
        let prepared = prover.prepare(kind).unwrap();
        let identity = prover.circuit_identity(&prepared).unwrap();
        assert_eq!(
            &identity.full_circuit_commitment,
            prepared.circuit_commitment()
        );
    }
}

#[test]
fn commitment_separates_kind_depth_and_config() {
    let prover24 = StateSyncProver::new(config(24));
    let prover28 = StateSyncProver::new(config(28));
    let m24 = *prover24
        .prepare(SmtOpKind::Membership)
        .unwrap()
        .circuit_commitment();
    let n24 = *prover24
        .prepare(SmtOpKind::NonMembership)
        .unwrap()
        .circuit_commitment();
    let m28 = *prover28
        .prepare(SmtOpKind::Membership)
        .unwrap()
        .circuit_commitment();
    assert_ne!(m24, n24, "kind separates");
    assert_ne!(m24, m28, "depth separates");

    let mut cfg_small_leaf = config(24);
    cfg_small_leaf.smt.leaf_max_fields = 20;
    let m24_lmf20 = *StateSyncProver::new(cfg_small_leaf)
        .prepare(SmtOpKind::Membership)
        .unwrap()
        .circuit_commitment();
    assert_ne!(m24, m24_lmf20, "leaf_max_fields separates");
}

#[test]
fn commitment_binds_every_gate_and_constant() {
    // A tiny synthetic circuit; the commitment must react to ANY change
    // in a gate field, a constant, or ordering (shape stays identical
    // in every variant, so the v0.1 shape digest alone would NOT react).
    let base = LayeredCircuit {
        layers: vec![Layer {
            width_bits: 1,
            gates: vec![
                Gate {
                    kind: GateKind::Lin,
                    out: 0,
                    in1: 0,
                    in2: 0,
                    coeff: f(2),
                },
                Gate {
                    kind: GateKind::Mul,
                    out: 1,
                    in1: 0,
                    in2: 1,
                    coeff: f(3),
                },
            ],
            consts: vec![(0, f(7)), (1, f(9))],
        }],
        input_width_bits: 1,
    };
    let params = SmtParams {
        depth: 1,
        leaf_max_fields: 31,
    };
    let c = |circ: &LayeredCircuit<BaseField>| {
        full_circuit_commitment(circ, SmtOpKind::Membership, &params, LayerStrategy::A)
    };
    let anchor = c(&base);

    let mut coeff_flip = base.clone();
    coeff_flip.layers[0].gates[0].coeff = f(5);
    assert_ne!(anchor, c(&coeff_flip), "gate coefficient binds");

    let mut wire_flip = base.clone();
    wire_flip.layers[0].gates[1].in2 = 0;
    assert_ne!(anchor, c(&wire_flip), "gate wiring binds");

    let mut kind_flip = base.clone();
    kind_flip.layers[0].gates[0].kind = GateKind::Pow3;
    assert_ne!(anchor, c(&kind_flip), "gate kind binds");

    let mut const_flip = base.clone();
    const_flip.layers[0].consts[1] = (1, f(10));
    assert_ne!(anchor, c(&const_flip), "constant value binds");

    let mut reorder = base.clone();
    reorder.layers[0].gates.swap(0, 1);
    assert_ne!(
        anchor,
        c(&reorder),
        "emission order binds (canonical order)"
    );
}

// ---------------------------------------------------------------------
// Wrap relation + pipeline (MockWrapBackend echoes the statement)
// ---------------------------------------------------------------------

#[test]
fn wrap_relation_accepts_honest_and_rejects_tampered() {
    let (prover, prepared, request, bytes) = encoded_fixture(SmtOpKind::Membership, 24);
    let statement = prover
        .wrap_relation(&prepared, &request, &bytes)
        .expect("honest proof satisfies the wrap relation");
    // The statement is exactly the frozen packing of identity + publics.
    let identity = prover.circuit_identity(&prepared).unwrap();
    assert_eq!(
        statement,
        wrap_statement_v1(&identity, &request.public_inputs)
    );

    let mut t = bytes.clone();
    t[400] ^= 1;
    assert!(prover.wrap_relation(&prepared, &request, &t).is_none());
}

#[test]
fn wrap_pipeline_runs_the_mock_backend_end_to_end() {
    let (prover, prepared, request, bytes) = encoded_fixture(SmtOpKind::Update, 24);
    let wrapped = prover
        .wrap_sync_op(&MockWrapBackend, &prepared, &request, &bytes)
        .expect("wrap pipeline");
    assert_eq!(wrapped.backend, "mock");
    let identity = prover.circuit_identity(&prepared).unwrap();
    assert_eq!(
        wrapped.statement,
        wrap_statement_v1(&identity, &request.public_inputs)
    );
    // The mock's bytes are loudly not a proof.
    assert_eq!(wrapped.bytes, b"MOCK-WRAP-NOT-A-PROOF".to_vec());

    // The pipeline refuses to even invoke a backend on a tampered input.
    let mut t = bytes.clone();
    t[300] ^= 1;
    assert!(
        prover
            .wrap_sync_op(&MockWrapBackend, &prepared, &request, &t)
            .is_err()
    );
}

#[test]
fn mock_backend_rejects_undecodable_input() {
    let request = membership_request(24, 5);
    let input = WrapInput {
        encoded_inner: b"garbage",
        operation: &request.operation,
        witness: &request.witness,
    };
    assert!(MockWrapBackend.wrap(&input).is_err());
}

// ---------------------------------------------------------------------
// Field bridge (KoalaBear -> BN254, 31-bit stride)
// ---------------------------------------------------------------------

#[test]
fn digest_packing_roundtrips_and_stays_canonical() {
    // Boundary digest: every limb at p - 1 (the largest canonical residue).
    let max = Digest([f(BaseField::ORDER_U32 - 1); 8]);
    let packed = pack_digest(&max);
    assert_eq!(unpack_digest(&packed), Some(max));

    // The maximal packed value stays strictly below the BN254 modulus r
    // (big-endian lexicographic compare).
    let be = packed.to_be_bytes();
    assert!(be < BN254_R_BE, "max packed digest < r");
    // ...and below 2^248 (top byte zero), the packing's own bound.
    assert_eq!(be[0], 0);

    // A varied digest round-trips too.
    let d = Digest([
        f(1),
        f(0),
        f(12345),
        f(BaseField::ORDER_U32 - 1),
        f(7),
        f(0),
        f(2),
        f(99),
    ]);
    assert_eq!(unpack_digest(&pack_digest(&d)), Some(d));
}

#[test]
fn digest_unpacking_rejects_non_canonical_values() {
    // A digit >= p: craft bytes whose first 31-bit window is exactly p.
    let mut bad = [0u8; 32];
    bad[..4].copy_from_slice(&BaseField::ORDER_U32.to_le_bytes());
    assert_eq!(unpack_digest(&Bn254Fr(bad)), None, "digit >= p rejected");

    // A set bit above position 247.
    let mut high = [0u8; 32];
    high[31] = 1;
    assert_eq!(unpack_digest(&Bn254Fr(high)), None, "bit 248+ rejected");
}

#[test]
fn wrap_statement_layout_is_the_frozen_one() {
    let (prover, prepared, request, _) = encoded_fixture(SmtOpKind::Membership, 24);
    let identity = prover.circuit_identity(&prepared).unwrap();
    let st = wrap_statement_v1(&identity, &request.public_inputs);

    // fr[0] header word: version axes + config, little-endian layout.
    let h = st.frs[0].0;
    assert_eq!(u16::from_le_bytes([h[0], h[1]]), WRAP_STATEMENT_VERSION);
    assert_eq!(u16::from_le_bytes([h[2], h[3]]), 1, "protocol_version");
    assert_eq!(u16::from_le_bytes([h[4], h[5]]), 1, "circuit_version");
    assert_eq!(u16::from_le_bytes([h[6], h[7]]), 1, "leaf_encoding_version");
    assert_eq!(u16::from_le_bytes([h[8], h[9]]), 31, "leaf_max_fields");
    assert_eq!(h[10], 0, "strategy A");
    assert_eq!(h[11], 0, "membership tag");
    assert_eq!(
        u32::from_le_bytes([h[12], h[13], h[14], h[15]]),
        24,
        "depth"
    );
    assert!(h[16..].iter().all(|&b| b == 0));

    // fr[1..6]: packed digests / asset id, in frozen order.
    assert_eq!(
        unpack_digest(&st.frs[1]),
        Some(identity.full_circuit_commitment)
    );
    assert_eq!(
        unpack_digest(&st.frs[2]),
        Some(request.public_inputs.old_root)
    );
    assert_eq!(
        unpack_digest(&st.frs[3]),
        Some(request.public_inputs.new_root)
    );
    assert_eq!(
        u64::from_le_bytes(st.frs[4].0[..8].try_into().unwrap()),
        request.public_inputs.asset_id.0
    );
    assert!(st.frs[4].0[8..].iter().all(|&b| b == 0));
    assert_eq!(
        unpack_digest(&st.frs[5]),
        Some(request.public_inputs.value_digest)
    );
}

// ---------------------------------------------------------------------
// Envelope constants sanity (frozen values)
// ---------------------------------------------------------------------

#[test]
fn frozen_constants_hold() {
    assert_eq!(MAGIC, *b"SSGKRPRF");
    assert_eq!(PROOF_ENCODING_VERSION, 1);
    assert_eq!(ROUND_POLY_COEFFS, 5, "degree bound 4 + 1");
}
