//! Fixed-profile pinned adapter differential and fail-closed battery.

#![allow(clippy::expect_used, clippy::panic, clippy::unwrap_used)]

use std::sync::OnceLock;
use std::time::Instant;

use sha2::{Digest as _, Sha256};
use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOpKind,
    SmtOperation, SmtParams, SmtWitness,
};
use statesync_gkr::gkr::{Layer, LayerHints, LayeredCircuit, WiringHints};
use statesync_gkr::primitives::field::{BaseField, PrimeCharacteristicRing, PrimeField32};
use statesync_gkr::primitives::hash::{Digest, HashGadget, Poseidon2Gadget};
use statesync_gkr::wrap::commitment::full_circuit_commitment;
use statesync_gkr::wrap::prepared::{
    OFFSET_CIRCUIT_VERSION, OFFSET_CONFIG_PROFILE, OFFSET_DEPTH, OFFSET_FULL_CIRCUIT_COMMITMENT,
    OFFSET_HEADER_RESERVED, OFFSET_LEAF_MAX_FIELDS, OFFSET_LEAF_VERSION, OFFSET_OPERATION_KIND,
    OFFSET_PROTOCOL_VERSION, OFFSET_SCHEMA_VERSION, OFFSET_STRATEGY_ID,
    PINNED_D24_A_MEMBERSHIP_CIRCUIT_COMMITMENT, PINNED_D24_A_MEMBERSHIP_FRAMED_DIGEST,
    PINNED_D24_A_MEMBERSHIP_MATERIAL_BYTES, PREPARED_GATE_BYTES, PREPARED_HEADER_BYTES,
    PREPARED_HINT_BYTES, PREPARED_LAYER_HEADER_BYTES, PREPARED_MATERIAL_DIGEST_DOMAIN,
    PreparedMaterialError, PreparedMaterialV1, ValidatedPreparedMaterialV1,
    canonical_prepared_material_v1, circuit_commitment_bytes, encode_prepared_material_v1,
    prepared_material_digest, validate_pinned_d24_a_membership_material,
    verify_prepared_material_digest,
};
use statesync_gkr::wrap::settlement::CanonicalRawStatement;
use statesync_gkr::{PreparedSync, StateSyncGkrConfig, StateSyncProver, SyncRequest};

static MATERIAL: OnceLock<PreparedMaterialV1> = OnceLock::new();
static BYTES: OnceLock<Vec<u8>> = OnceLock::new();

fn material() -> &'static PreparedMaterialV1 {
    MATERIAL.get_or_init(|| canonical_prepared_material_v1().expect("canonical material"))
}

fn canonical_bytes() -> &'static [u8] {
    BYTES
        .get_or_init(|| encode_prepared_material_v1(material()).expect("canonical encode"))
        .as_slice()
}

fn fixed_config() -> StateSyncGkrConfig {
    StateSyncGkrConfig {
        smt: SmtParams {
            depth: 24,
            ..Default::default()
        },
        layer_strategy: LayerStrategy::A,
        batching: Default::default(),
    }
}

fn fixed_prover() -> StateSyncProver {
    StateSyncProver::new(fixed_config())
}

fn f(value: u32) -> BaseField {
    BaseField::from_u32(value)
}

fn membership_request() -> SyncRequest {
    let params = SmtParams {
        depth: 24,
        ..Default::default()
    };
    let key = AssetId(5);
    let payload = LeafPayload {
        sync_state: vec![f(42), f(7)],
        identity_digest: [9u8; 32],
    };
    let leaf = LeafState::Occupied(payload.clone());
    let path = MerklePath {
        siblings: (0..24)
            .map(|index| Digest([f(index * 13 + 1); 8]))
            .collect(),
    };
    let hasher = Poseidon2Gadget::default();
    let old_root = path
        .compute_root(&hasher, &params, key, &leaf)
        .expect("membership root");
    let value_digest = hasher.hash_leaf(&leaf.encode()).expect("leaf digest");
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

fn u32_at(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(bytes[offset..offset + 4].try_into().expect("u32 slice"))
}

fn put_u32(bytes: &mut [u8], offset: usize, value: u32) {
    bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
}

fn first_record_offsets(bytes: &[u8]) -> (usize, usize, usize) {
    let mut cursor = PREPARED_HEADER_BYTES;
    let (mut gate, mut constant, mut hint) = (None, None, None);
    while cursor < bytes.len() && (gate.is_none() || constant.is_none() || hint.is_none()) {
        let gates = u32_at(bytes, cursor + 4) as usize;
        let consts = u32_at(bytes, cursor + 8) as usize;
        let gate_hints = u32_at(bytes, cursor + 12) as usize;
        let const_hints = u32_at(bytes, cursor + 16) as usize;
        let gate_start = cursor + PREPARED_LAYER_HEADER_BYTES;
        let const_start = gate_start + gates * PREPARED_GATE_BYTES;
        let gate_hint_start = const_start + consts * 8;
        let const_hint_start = gate_hint_start + gate_hints * PREPARED_HINT_BYTES;
        gate = gate.or((gates > 0).then_some(gate_start));
        constant = constant.or((consts > 0).then_some(const_start));
        hint = hint.or((gate_hints > 0).then_some(gate_hint_start));
        hint = hint.or((const_hints > 0).then_some(const_hint_start));
        cursor = const_hint_start + const_hints * PREPARED_HINT_BYTES;
    }
    (
        gate.expect("gate record"),
        constant.expect("constant record"),
        hint.expect("hint record"),
    )
}

fn independent_prepared_digest(bytes: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(PREPARED_MATERIAL_DIGEST_DOMAIN);
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
    hasher.finalize().into()
}

fn adapter_error(bytes: &[u8]) -> PreparedMaterialError {
    match fixed_prover().prepare_pinned_d24_a_membership(bytes) {
        Ok(_) => panic!("mutated material did not fail closed"),
        Err(error) => error,
    }
}

fn cheap_alternate_material() -> Vec<u8> {
    let mut cheap = material().clone();
    cheap.circuit = LayeredCircuit {
        layers: vec![Layer {
            width_bits: 0,
            gates: Vec::new(),
            consts: Vec::new(),
        }],
        input_width_bits: 0,
    };
    cheap.hints = WiringHints {
        layers: vec![LayerHints::default()],
    };
    cheap.full_circuit_commitment =
        full_circuit_commitment(&cheap.circuit, cheap.kind, &cheap.params, cheap.strategy);
    encode_prepared_material_v1(&cheap).expect("cheap material encode")
}

#[test]
fn fixed_constants_match_regenerated_canonical_material() {
    assert_eq!(
        canonical_bytes().len(),
        PINNED_D24_A_MEMBERSHIP_MATERIAL_BYTES
    );
    assert_eq!(
        prepared_material_digest(canonical_bytes()),
        PINNED_D24_A_MEMBERSHIP_FRAMED_DIGEST
    );
    assert_eq!(
        independent_prepared_digest(canonical_bytes()),
        PINNED_D24_A_MEMBERSHIP_FRAMED_DIGEST
    );
    assert_eq!(
        circuit_commitment_bytes(&material().full_circuit_commitment),
        PINNED_D24_A_MEMBERSHIP_CIRCUIT_COMMITMENT
    );
}

#[test]
fn canonical_prepare_and_pinned_adapter_are_observationally_identical() {
    let prover = fixed_prover();
    let fresh = prover
        .prepare(SmtOpKind::Membership)
        .expect("fresh prepare");
    let pinned = prover
        .prepare_pinned_d24_a_membership(canonical_bytes())
        .expect("pinned adapter");

    assert_eq!(fresh.kind(), pinned.kind());
    assert_eq!(fresh.circuit_commitment(), pinned.circuit_commitment());

    let request = membership_request();
    let fresh_result = prover
        .prove_sync_op_prepared(&fresh, &request)
        .expect("fresh proof");
    let pinned_result = prover
        .prove_sync_op_prepared(&pinned, &request)
        .expect("pinned proof");
    assert_eq!(fresh_result.public_inputs, pinned_result.public_inputs);
    assert_eq!(fresh_result.proof, pinned_result.proof);

    let fresh_inner = prover
        .encode_sync_result(&fresh, &fresh_result)
        .expect("fresh inner proof");
    let pinned_inner = prover
        .encode_sync_result(&pinned, &pinned_result)
        .expect("pinned inner proof");
    assert_eq!(fresh_inner, pinned_inner);

    let fresh_statement = prover
        .wrap_relation(&fresh, &request, &fresh_inner)
        .expect("fresh statement");
    let pinned_statement = prover
        .wrap_relation(&pinned, &request, &pinned_inner)
        .expect("pinned statement");
    let fresh_raw = CanonicalRawStatement::from_statement(&fresh_statement).expect("fresh raw192");
    let pinned_raw =
        CanonicalRawStatement::from_statement(&pinned_statement).expect("pinned raw192");
    assert_eq!(fresh_raw.as_bytes(), pinned_raw.as_bytes());

    assert!(prover.verify_sync_op_prepared(&fresh, &request, &fresh_result));
    assert!(prover.verify_sync_op_prepared(&pinned, &request, &pinned_result));
    assert!(prover.verify_encoded_sync_op(&fresh, &request, &fresh_inner));
    assert!(prover.verify_encoded_sync_op(&pinned, &request, &pinned_inner));
}

#[test]
fn existing_nonmembership_and_other_config_prepare_paths_remain_live() {
    let fixed = fixed_prover();
    assert!(fixed.prepare(SmtOpKind::NonMembership).is_ok());

    let other = StateSyncProver::new(StateSyncGkrConfig {
        smt: SmtParams {
            depth: 23,
            ..Default::default()
        },
        layer_strategy: LayerStrategy::A,
        batching: Default::default(),
    });
    assert!(other.prepare(SmtOpKind::Membership).is_ok());
    assert!(matches!(
        other.prepare_pinned_d24_a_membership(canonical_bytes()),
        Err(PreparedMaterialError::ConfigMismatch)
    ));
}

#[test]
fn length_and_transport_shape_fail_before_construction() {
    for truncated in [
        &[][..],
        &canonical_bytes()[..PREPARED_HEADER_BYTES],
        &canonical_bytes()[..canonical_bytes().len() - 1],
    ] {
        assert!(matches!(
            adapter_error(truncated),
            PreparedMaterialError::UnexpectedEof { .. }
        ));
    }

    for suffix in [&[0u8][..], b"suffix".as_slice()] {
        let mut trailing = canonical_bytes().to_vec();
        trailing.extend_from_slice(suffix);
        assert_eq!(
            adapter_error(&trailing),
            PreparedMaterialError::TrailingBytes {
                extra: suffix.len()
            }
        );
    }
}

#[test]
fn pinned_digest_rejects_every_fixed_profile_mutation() {
    let (gate, constant, hint) = first_record_offsets(canonical_bytes());
    let cases = [
        ("wrong framed digest", 0usize),
        (
            "wrong full circuit commitment",
            OFFSET_FULL_CIRCUIT_COMMITMENT,
        ),
        ("layer mutation", PREPARED_HEADER_BYTES),
        ("gate mutation", gate + 16),
        ("constant mutation", constant + 4),
        ("hint mutation", hint),
        ("wrong depth", OFFSET_DEPTH),
        ("wrong strategy", OFFSET_STRATEGY_ID),
        ("wrong operation", OFFSET_OPERATION_KIND),
        ("wrong leaf bound", OFFSET_LEAF_MAX_FIELDS),
        ("wrong config profile", OFFSET_CONFIG_PROFILE),
        ("wrong protocol version", OFFSET_PROTOCOL_VERSION),
        ("wrong circuit version", OFFSET_CIRCUIT_VERSION),
        ("wrong leaf version", OFFSET_LEAF_VERSION),
        ("wrong schema version", OFFSET_SCHEMA_VERSION),
        ("nonzero reserved", OFFSET_HEADER_RESERVED),
    ];
    for (label, offset) in cases {
        let mut bytes = canonical_bytes().to_vec();
        bytes[offset] ^= 1;
        assert_eq!(
            adapter_error(&bytes),
            PreparedMaterialError::PreparedDigestMismatch,
            "{label}"
        );
    }

    let mut noncanonical = canonical_bytes().to_vec();
    put_u32(&mut noncanonical, gate + 16, BaseField::ORDER_U32);
    assert_eq!(
        adapter_error(&noncanonical),
        PreparedMaterialError::PreparedDigestMismatch
    );
}

#[test]
fn self_consistent_attacker_digest_and_cheap_circuit_cannot_reanchor_adapter() {
    let mut malicious = cheap_alternate_material();
    malicious.resize(PINNED_D24_A_MEMBERSHIP_MATERIAL_BYTES, 0);
    let attacker_digest = prepared_material_digest(&malicious);
    verify_prepared_material_digest(&malicious, &attacker_digest)
        .expect("attacker material is self-consistent under its own digest");
    assert_ne!(attacker_digest, PINNED_D24_A_MEMBERSHIP_FRAMED_DIGEST);
    assert_eq!(
        adapter_error(&malicious),
        PreparedMaterialError::PreparedDigestMismatch
    );
}

#[test]
fn public_api_has_no_caller_supplied_anchor_or_wiring() {
    let _validator: fn(&[u8]) -> Result<ValidatedPreparedMaterialV1, PreparedMaterialError> =
        validate_pinned_d24_a_membership_material;
    let _adapter: fn(&StateSyncProver, &[u8]) -> Result<PreparedSync, PreparedMaterialError> =
        StateSyncProver::prepare_pinned_d24_a_membership;
}

#[test]
fn pinned_hot_path_call_graph_contains_no_compile_or_fallback() {
    let prepared_source = include_str!("../crates/wrap/src/prepared.rs");
    let start = prepared_source
        .find("pub fn validate_pinned_d24_a_membership_material")
        .expect("pinned validator source");
    let end = prepared_source[start..]
        .find("/// Framed SHA-256 digest")
        .map(|offset| start + offset)
        .expect("pinned validator end");
    let validator = &prepared_source[start..end];
    assert!(!validator.contains("compile_with_hints("));
    assert!(!validator.contains("canonical_prepared_material_v1("));
    assert!(!validator.contains("validate_prepared_material_v1("));
    assert!(!validator.contains("full_circuit_commitment("));
    assert!(!validator.contains("encode_prepared_material_v1("));
    assert!(!validator.contains("#[cfg"));
    assert!(validator.contains("DecodeMode::PinnedRuntime"));

    let core_start = prepared_source
        .find("fn decode_prepared_material_v1_with_mode")
        .expect("shared decoder core");
    let core_end = prepared_source[core_start..]
        .find("/// Validate bytes against")
        .map(|offset| core_start + offset)
        .expect("shared decoder core end");
    let core = &prepared_source[core_start..core_end];
    assert_eq!(core.matches("validate_circuit_structure(").count(), 1);
    assert_eq!(core.matches("full_circuit_commitment(").count(), 1);
    assert_eq!(core.matches("encode_prepared_material_v1(").count(), 1);
    assert!(core.contains("if matches!(mode, DecodeMode::Full)"));

    let facade_source = include_str!("../src/lib.rs");
    let start = facade_source
        .find("pub fn prepare_pinned_d24_a_membership")
        .expect("pinned adapter source");
    let end = facade_source[start..]
        .find("/// Prove one request against prepared state")
        .map(|offset| start + offset)
        .expect("pinned adapter end");
    let adapter = &facade_source[start..end];
    assert!(!adapter.contains("compile_with_hints("));
    assert!(!adapter.contains("canonical_prepared_material_v1("));
    assert!(!adapter.contains(".prepare("));
    assert!(adapter.contains("PINNED_D24_A_MEMBERSHIP_CIRCUIT_COMMITMENT"));
    assert!(!adapter.contains("commitment: material.full_circuit_commitment"));
    assert!(!adapter.contains("#[cfg"));
}

#[test]
#[ignore = "manual host-native cold/warm metric; requires SSGKR_PREPARED_MATERIAL_PATH"]
fn host_native_prepare_or_adapter_metric() {
    let path = std::env::var("SSGKR_PREPARED_MATERIAL_PATH").expect("SSGKR_PREPARED_MATERIAL_PATH");
    let mode = std::env::var("SSGKR_G2_METRIC_MODE").expect("SSGKR_G2_METRIC_MODE");
    let bytes = std::fs::read(path).expect("prepared material bytes");
    assert_eq!(bytes.len(), PINNED_D24_A_MEMBERSHIP_MATERIAL_BYTES);
    let prover = fixed_prover();

    let started = Instant::now();
    let kind = match mode.as_str() {
        "prepare-cold" => prover
            .prepare(SmtOpKind::Membership)
            .expect("prepare")
            .kind(),
        "prepare-warm" => {
            let warm = prover.prepare(SmtOpKind::Membership).expect("warm prepare");
            std::hint::black_box(warm.kind());
            let started = Instant::now();
            let measured = prover.prepare(SmtOpKind::Membership).expect("prepare");
            println!(
                "metric_mode={mode} elapsed_ns={} output_length={}",
                started.elapsed().as_nanos(),
                bytes.len()
            );
            std::hint::black_box(measured.kind());
            return;
        }
        "adapter-cold" => prover
            .prepare_pinned_d24_a_membership(&bytes)
            .expect("adapter")
            .kind(),
        "adapter-warm" => {
            let warm = prover
                .prepare_pinned_d24_a_membership(&bytes)
                .expect("warm adapter");
            std::hint::black_box(warm.kind());
            let started = Instant::now();
            let measured = prover
                .prepare_pinned_d24_a_membership(&bytes)
                .expect("adapter");
            println!(
                "metric_mode={mode} elapsed_ns={} output_length={}",
                started.elapsed().as_nanos(),
                bytes.len()
            );
            std::hint::black_box(measured.kind());
            return;
        }
        _ => panic!("unknown metric mode: {mode}"),
    };
    std::hint::black_box(kind);
    println!(
        "metric_mode={mode} elapsed_ns={} output_length={}",
        started.elapsed().as_nanos(),
        bytes.len()
    );
}
