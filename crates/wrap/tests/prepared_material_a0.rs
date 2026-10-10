//! A0 positive and malicious-input battery for PreparedMaterialV1.

#![allow(clippy::panic)]

use std::sync::OnceLock;

use sha2::{Digest as _, Sha256};
use ssgkr_primitives::field::{BaseField, PrimeField32};
use ssgkr_protocol::{Layer, LayerHints, LayeredCircuit, WiringHints};
use ssgkr_wrap::commitment::full_circuit_commitment;
use ssgkr_wrap::prepared::{
    GeneratorProvenanceV1, OFFSET_CIRCUIT_VERSION, OFFSET_DEPTH, OFFSET_HEADER_RESERVED,
    OFFSET_LAYER_COUNT, OFFSET_LEAF_MAX_FIELDS, OFFSET_LEAF_VERSION, OFFSET_OPERATION_KIND,
    OFFSET_PROTOCOL_VERSION, OFFSET_SCHEMA_VERSION, OFFSET_STRATEGY_ARG, OFFSET_STRATEGY_ID,
    OFFSET_TOTAL_LENGTH, PREPARED_GATE_BYTES, PREPARED_HEADER_BYTES, PREPARED_LAYER_HEADER_BYTES,
    PreparedBindingLifecycleAuditV1, PreparedMaterialBindingAuditV1,
    PreparedMaterialBindingCoreAuditV1, PreparedMaterialError, PreparedMaterialV1,
    canonical_prepared_material_v1, circuit_commitment_bytes, decode_prepared_material_v1,
    encode_prepared_material_v1, prepared_material_digest, raw_sha256,
    validate_prepared_material_v1, validate_prepared_material_v1_against,
    verify_compiled_a0_material_digest, verify_generator_provenance,
    verify_prepared_material_digest,
};

static MATERIAL: OnceLock<PreparedMaterialV1> = OnceLock::new();
static BYTES: OnceLock<Vec<u8>> = OnceLock::new();

fn must_ok<T, E: std::fmt::Debug>(result: Result<T, E>, context: &str) -> T {
    match result {
        Ok(value) => value,
        Err(error) => panic!("{context}: {error:?}"),
    }
}

fn material() -> &'static PreparedMaterialV1 {
    MATERIAL.get_or_init(|| must_ok(canonical_prepared_material_v1(), "exact A0 compile"))
}

fn canonical_bytes() -> &'static [u8] {
    BYTES
        .get_or_init(|| must_ok(encode_prepared_material_v1(material()), "canonical encode"))
        .as_slice()
}

fn decode_error(bytes: &[u8]) -> PreparedMaterialError {
    match decode_prepared_material_v1(bytes) {
        Ok(_) => panic!("mutated material did not fail closed"),
        Err(error) => error,
    }
}

fn u32_at(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes([
        bytes[offset],
        bytes[offset + 1],
        bytes[offset + 2],
        bytes[offset + 3],
    ])
}

fn put_u32(bytes: &mut [u8], offset: usize, value: u32) {
    bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
}

fn first_layer_offsets(bytes: &[u8]) -> (usize, usize, usize) {
    let layer = PREPARED_HEADER_BYTES;
    let gates = u32_at(bytes, layer + 4) as usize;
    let consts = u32_at(bytes, layer + 8) as usize;
    let gate_start = layer + PREPARED_LAYER_HEADER_BYTES;
    let const_start = gate_start + gates * PREPARED_GATE_BYTES;
    let gate_hint_start = const_start + consts * 8;
    (gate_start, const_start, gate_hint_start)
}

fn material_with_mutated_hint() -> Vec<u8> {
    let mut bytes = canonical_bytes().to_vec();
    let (_, _, hint) = first_layer_offsets(&bytes);
    if bytes[hint] == 0 {
        bytes[hint] = 1;
    } else {
        let family = u32_at(&bytes, hint + 4);
        put_u32(&mut bytes, hint + 4, family.wrapping_add(1));
    }
    must_ok(
        decode_prepared_material_v1(&bytes),
        "hint mutation remains self-canonical",
    );
    bytes
}

fn cheap_circuit_material_bytes() -> Vec<u8> {
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
    let bytes = must_ok(
        encode_prepared_material_v1(&cheap),
        "canonical cheap-circuit encode",
    );
    must_ok(
        decode_prepared_material_v1(&bytes),
        "cheap circuit remains self-canonical",
    );
    bytes
}

fn provenance() -> GeneratorProvenanceV1 {
    GeneratorProvenanceV1 {
        source_commit: "0123456789abcdef0123456789abcdef01234567".to_owned(),
        schema_profile: "PreparedMaterialV1/d24/Membership/A".to_owned(),
        exact_command: "generate-prepared-material-v1 --output material.bin".to_owned(),
        target: "x86_64-pc-windows-msvc".to_owned(),
        generator_binary_sha256: [1; 32],
        input_manifest_sha256: [2; 32],
        input_lock_sha256: [3; 32],
        input_toolchain_sha256: [4; 32],
        output_byte_length: canonical_bytes().len() as u64,
        output_sha256: raw_sha256(canonical_bytes()),
        clean_tree: true,
    }
}

fn binding() -> PreparedMaterialBindingAuditV1 {
    let core = PreparedMaterialBindingCoreAuditV1 {
        guest_image_id: [0x42; 32],
        prepared_digest: prepared_material_digest(canonical_bytes()),
        prepared_schema_version: 1,
        full_circuit_commitment: circuit_commitment_bytes(&material().full_circuit_commitment),
        operation_kind: 0,
        generator_provenance_digest: must_ok(provenance().digest(), "canonical provenance"),
    };
    PreparedMaterialBindingAuditV1::new(core, 100, PreparedBindingLifecycleAuditV1::Active)
}

#[test]
fn p1_canonical_acceptance_rederives_wiring_and_reencodes_exactly() {
    let validated = must_ok(
        validate_prepared_material_v1(canonical_bytes()),
        "P1 acceptance",
    );
    assert_eq!(
        must_ok(
            encode_prepared_material_v1(&validated.material),
            "re-encode",
        ),
        canonical_bytes()
    );
    assert_eq!(
        validated.material.full_circuit_commitment,
        material().full_circuit_commitment
    );
    for (layer, source) in validated.material.circuit.layers.iter().enumerate() {
        assert_eq!(
            validated.derived_wiring.expand_gates(layer).len(),
            source.gates.len()
        );
        assert_eq!(
            validated.derived_wiring.expand_consts(layer).len(),
            source.consts.len()
        );
    }
}

#[test]
fn p2_deterministic_regeneration_is_byte_equal() {
    let independently_compiled = must_ok(canonical_prepared_material_v1(), "second exact compile");
    let regenerated = must_ok(
        encode_prepared_material_v1(&independently_compiled),
        "second encode",
    );
    assert_eq!(regenerated, canonical_bytes());
    assert_eq!(raw_sha256(&regenerated), raw_sha256(canonical_bytes()));
}

#[test]
fn p3_generator_output_framed_sha_equality() {
    let declared = prepared_material_digest(canonical_bytes());
    must_ok(
        verify_prepared_material_digest(canonical_bytes(), &declared),
        "declared digest",
    );
    must_ok(
        verify_compiled_a0_material_digest(canonical_bytes()),
        "compiled expected digest",
    );
    assert_ne!(declared, raw_sha256(canonical_bytes()));
}

#[test]
fn p4_route_manifest_audit_tuple_equality() {
    let binding = binding();
    must_ok(
        binding.validate(&binding.core.guest_image_id, 100),
        "active effective tuple",
    );
    assert_eq!(binding.route_id, binding.core.route_id());
}

#[test]
fn m1_magic_flip_is_bad_magic() {
    let mut bytes = canonical_bytes().to_vec();
    bytes[0] ^= 1;
    assert_eq!(decode_error(&bytes), PreparedMaterialError::BadMagic);
}

#[test]
fn m2_schema_zero_and_two_are_unsupported() {
    for version in [0u16, 2u16] {
        let mut bytes = canonical_bytes().to_vec();
        bytes[OFFSET_SCHEMA_VERSION..OFFSET_SCHEMA_VERSION + 2]
            .copy_from_slice(&version.to_le_bytes());
        assert_eq!(
            decode_error(&bytes),
            PreparedMaterialError::UnsupportedSchema { found: version }
        );
    }
}

#[test]
fn m3_truncations_fail_as_unexpected_eof() {
    let (gate, _, hint) = first_layer_offsets(canonical_bytes());
    for end in [
        0,
        7,
        39,
        PREPARED_HEADER_BYTES - 1,
        gate,
        hint,
        canonical_bytes().len() - 1,
    ] {
        assert!(matches!(
            decode_prepared_material_v1(&canonical_bytes()[..end]),
            Err(PreparedMaterialError::UnexpectedEof { .. })
        ));
    }
}

#[test]
fn m4_trailing_zero_is_rejected() {
    let mut bytes = canonical_bytes().to_vec();
    bytes.push(0);
    assert!(matches!(
        decode_prepared_material_v1(&bytes),
        Err(PreparedMaterialError::TrailingBytes { extra: 1 })
    ));
}

#[test]
fn m5_absurd_lengths_and_counts_fail_before_allocation() {
    let mut length = canonical_bytes().to_vec();
    length[OFFSET_TOTAL_LENGTH..OFFSET_TOTAL_LENGTH + 8]
        .copy_from_slice(&u64::from(u32::MAX).to_le_bytes());
    assert_eq!(decode_error(&length), PreparedMaterialError::BudgetExceeded);

    let mut layers = canonical_bytes().to_vec();
    put_u32(&mut layers, OFFSET_LAYER_COUNT, u32::MAX);
    assert_eq!(decode_error(&layers), PreparedMaterialError::BudgetExceeded);

    let mut gates = canonical_bytes().to_vec();
    put_u32(&mut gates, PREPARED_HEADER_BYTES + 4, u32::MAX);
    assert_eq!(decode_error(&gates), PreparedMaterialError::BudgetExceeded);
}

#[test]
fn m6_wrong_endian_depth_is_config_mismatch() {
    let mut bytes = canonical_bytes().to_vec();
    bytes[OFFSET_DEPTH..OFFSET_DEPTH + 4].reverse();
    assert_eq!(decode_error(&bytes), PreparedMaterialError::ConfigMismatch);
}

#[test]
fn m7_noncanonical_field_limb_is_rejected() {
    let mut bytes = canonical_bytes().to_vec();
    let (gate, _, _) = first_layer_offsets(&bytes);
    put_u32(&mut bytes, gate + 16, BaseField::ORDER_U32);
    assert!(matches!(
        decode_prepared_material_v1(&bytes),
        Err(PreparedMaterialError::NonCanonicalField { offset }) if offset == gate + 16
    ));
}

#[test]
fn m8_nonzero_reserved_bytes_are_rejected() {
    for offset in [
        OFFSET_HEADER_RESERVED,
        PREPARED_HEADER_BYTES + 20,
        PREPARED_HEADER_BYTES + PREPARED_LAYER_HEADER_BYTES + 1,
    ] {
        let mut bytes = canonical_bytes().to_vec();
        bytes[offset] = 1;
        assert!(matches!(
            decode_prepared_material_v1(&bytes),
            Err(PreparedMaterialError::NonCanonicalEncoding { offset: found }) if found == offset
        ));
    }
}

#[test]
fn m9_update_tag_is_operation_kind_mismatch() {
    let mut bytes = canonical_bytes().to_vec();
    bytes[OFFSET_OPERATION_KIND] = 1;
    assert_eq!(
        decode_error(&bytes),
        PreparedMaterialError::OperationKindMismatch { found: 1 }
    );
}

#[test]
fn m10_leaf_strategy_or_strategy_argument_mismatch() {
    for (offset, value) in [
        (OFFSET_LEAF_MAX_FIELDS, 30u32),
        (OFFSET_STRATEGY_ID, 1u32),
        (OFFSET_STRATEGY_ARG, 1u32),
    ] {
        let mut bytes = canonical_bytes().to_vec();
        if offset == OFFSET_STRATEGY_ID {
            bytes[offset] = value as u8;
        } else {
            put_u32(&mut bytes, offset, value);
        }
        assert_eq!(decode_error(&bytes), PreparedMaterialError::ConfigMismatch);
    }
}

#[test]
fn m11_gate_coefficient_flip_breaks_commitment() {
    let mut bytes = canonical_bytes().to_vec();
    let (gate, _, _) = first_layer_offsets(&bytes);
    let coefficient = u32_at(&bytes, gate + 16);
    put_u32(
        &mut bytes,
        gate + 16,
        if coefficient + 1 == BaseField::ORDER_U32 {
            0
        } else {
            coefficient + 1
        },
    );
    assert_eq!(
        decode_error(&bytes),
        PreparedMaterialError::CircuitCommitmentMismatch
    );
}

#[test]
fn m12_gate_reordering_breaks_commitment() {
    let mut bytes = canonical_bytes().to_vec();
    let (gate, _, _) = first_layer_offsets(&bytes);
    assert!(u32_at(&bytes, PREPARED_HEADER_BYTES + 4) >= 2);
    bytes[gate..gate + 2 * PREPARED_GATE_BYTES].rotate_left(PREPARED_GATE_BYTES);
    assert_eq!(
        decode_error(&bytes),
        PreparedMaterialError::CircuitCommitmentMismatch
    );
}

#[test]
fn m13_wiring_hint_mutation_is_wiring_mismatch() {
    let bytes = material_with_mutated_hint();
    assert_eq!(
        validate_prepared_material_v1_against(&bytes, material()).map(|_| ()),
        Err(PreparedMaterialError::WiringMismatch)
    );
}

#[test]
fn m14_canonical_cheap_circuit_material_fails_both_digest_gates() {
    let substituted = cheap_circuit_material_bytes();
    let expected = prepared_material_digest(canonical_bytes());
    assert_eq!(
        verify_prepared_material_digest(&substituted, &expected),
        Err(PreparedMaterialError::PreparedDigestMismatch)
    );
    let attacker_digest = prepared_material_digest(&substituted);
    must_ok(
        verify_prepared_material_digest(&substituted, &attacker_digest),
        "self digest exists",
    );
    assert_eq!(
        verify_compiled_a0_material_digest(&substituted),
        Err(PreparedMaterialError::PreparedDigestMismatch)
    );
}

#[test]
fn m15_unframed_or_alternate_domain_digest_is_rejected() {
    let raw = raw_sha256(canonical_bytes());
    assert_eq!(
        verify_prepared_material_digest(canonical_bytes(), &raw),
        Err(PreparedMaterialError::PreparedDigestMismatch)
    );
    let alternate: [u8; 32] =
        Sha256::digest([b"alternate-domain".as_slice(), canonical_bytes()].concat()).into();
    assert_eq!(
        verify_prepared_material_digest(canonical_bytes(), &alternate),
        Err(PreparedMaterialError::PreparedDigestMismatch)
    );
}

#[test]
fn m16_protocol_circuit_and_leaf_versions_are_unsupported() {
    for offset in [
        OFFSET_PROTOCOL_VERSION,
        OFFSET_CIRCUIT_VERSION,
        OFFSET_LEAF_VERSION,
    ] {
        let mut bytes = canonical_bytes().to_vec();
        bytes[offset..offset + 2].copy_from_slice(&2u16.to_le_bytes());
        assert!(matches!(
            decode_prepared_material_v1(&bytes),
            Err(PreparedMaterialError::UnsupportedVersion { found: 2, .. })
        ));
    }
}

#[test]
fn m17_generator_provenance_substitution_is_rejected() {
    let expected = provenance();
    for field in 0..3 {
        let mut actual = expected.clone();
        match field {
            0 => actual.source_commit.replace_range(0..1, "f"),
            1 => actual.generator_binary_sha256[0] ^= 1,
            2 => actual.input_lock_sha256[0] ^= 1,
            _ => unreachable!(),
        }
        assert_eq!(
            verify_generator_provenance(&actual, &expected),
            Err(PreparedMaterialError::ProvenanceMismatch)
        );
    }
}

#[test]
fn m18_guest_image_substitution_is_rejected() {
    let binding = binding();
    let mut image = binding.core.guest_image_id;
    image[0] ^= 1;
    assert_eq!(
        binding.validate(&image, 100),
        Err(PreparedMaterialError::GuestImageMismatch)
    );
}

#[test]
fn m19_pre_effective_height_is_rejected() {
    let binding = binding();
    assert_eq!(
        binding.validate(&binding.core.guest_image_id, 99),
        Err(PreparedMaterialError::RouteNotEffective)
    );
}

#[test]
fn m20_revoked_and_past_cutoff_routes_are_rejected() {
    let mut revoked = binding();
    revoked.lifecycle = PreparedBindingLifecycleAuditV1::Revoked;
    assert_eq!(
        revoked.validate(&revoked.core.guest_image_id, 100),
        Err(PreparedMaterialError::RouteRevoked)
    );

    let mut draining = binding();
    draining.lifecycle = PreparedBindingLifecycleAuditV1::Draining { cutoff: 110 };
    must_ok(
        draining.validate(&draining.core.guest_image_id, 110),
        "cutoff is inclusive",
    );
    assert_eq!(
        draining.validate(&draining.core.guest_image_id, 111),
        Err(PreparedMaterialError::SupersededRoute)
    );
}

#[test]
fn m21_stale_outer_route_id_is_rejected() {
    let mut binding = binding();
    binding.core.prepared_digest[0] ^= 1;
    assert_eq!(
        binding.validate(&binding.core.guest_image_id, 100),
        Err(PreparedMaterialError::RouteIdMismatch)
    );
}

#[test]
fn sampled_single_byte_changes_always_change_framed_digest() {
    let baseline = prepared_material_digest(canonical_bytes());
    let stride = (canonical_bytes().len() / 257).max(1);
    for index in (0..canonical_bytes().len()).step_by(stride).take(257) {
        let mut mutated = canonical_bytes().to_vec();
        mutated[index] ^= 1;
        assert_ne!(
            prepared_material_digest(&mutated),
            baseline,
            "offset {index}"
        );
    }
}

#[test]
fn generic_decoder_keeps_full_commitment_and_reencode_validation() {
    let source = include_str!("../src/prepared.rs");
    let Some(public_start) = source.find("pub fn decode_prepared_material_v1") else {
        panic!("generic decoder missing");
    };
    let Some(core_start) = source.find("fn decode_prepared_material_v1_with_mode") else {
        panic!("shared decoder core missing");
    };
    assert!(source[public_start..core_start].contains("DecodeMode::Full"));

    let Some(core_end) = source[core_start..]
        .find("/// Validate bytes against")
        .map(|offset| core_start + offset)
    else {
        panic!("shared decoder core end missing");
    };
    let core = &source[core_start..core_end];
    assert!(core.contains("full_circuit_commitment("));
    assert!(core.contains("encode_prepared_material_v1("));
}
