//! PreparedMaterialV1 canonical circuit-and-hints material for the A0
//! sound-binding spike.
//!
//! This module is outside the G2-frozen root facade. It does not construct
//! PreparedSync, accept caller-supplied derived wiring, build a guest, or
//! activate a route. Its only payload is the compiled circuit plus
//! WiringHints; DerivedRegularWiring is always reconstructed locally.

use std::cmp::Ordering;

use sha2::{Digest as _, Sha256};
use ssgkr_compiler::{LayerStrategy, PublicInputs, SmtOpKind, SmtParams, compile_with_hints};
use ssgkr_primitives::field::{BaseField, PrimeCharacteristicRing, PrimeField32};
use ssgkr_primitives::hash::{
    DEFAULT_LEAF_MAX_FIELDS, DIGEST_WIDTH, Digest, HashGadget, Poseidon2Gadget,
};
use ssgkr_protocol::{
    DerivedRegularWiring, FamilyTag, Gate, GateKind, Layer, LayerHints, LayeredCircuit, WiringHints,
};

use crate::commitment::full_circuit_commitment;

/// Canonical material magic.
pub const PREPARED_MATERIAL_MAGIC: [u8; 8] = *b"SSGKRPM1";
/// Fixed 32-byte payload domain. Trailing zero bytes are part of the wire.
pub const PREPARED_MATERIAL_DOMAIN: [u8; 32] = *b"ssgkr/prepared-material/v1\0\0\0\0\0\0";
/// Framed SHA-256 domain, intentionally outside the payload.
pub const PREPARED_MATERIAL_DIGEST_DOMAIN: &[u8] = b"ssgkr/prepared-material-digest/v1";
/// Audit-only external binding domain.
pub const PREPARED_BINDING_AUDIT_DOMAIN: &[u8] = b"ssgkr/prepared-material-binding-audit/v1";
/// Generator provenance-record digest domain.
pub const GENERATOR_PROVENANCE_DOMAIN: &[u8] = b"ssgkr/prepared-material-provenance/v1";

/// Prepared-material schema version.
pub const PREPARED_MATERIAL_SCHEMA_VERSION: u16 = 1;
/// StateSync-GKR protocol profile version.
pub const PREPARED_PROTOCOL_PROFILE_VERSION: u16 = 1;
/// Compiler/circuit profile version.
pub const PREPARED_CIRCUIT_PROFILE_VERSION: u16 = 1;
/// Leaf encoding profile version.
pub const PREPARED_LEAF_PROFILE_VERSION: u16 = 1;
/// KoalaBear canonical-u32 field profile.
pub const PREPARED_FIELD_PROFILE_KOALABEAR_U32: u8 = 1;
/// Poseidon2-KoalaBear width-16 hash/transcript profile.
pub const PREPARED_HASH_PROFILE_POSEIDON2_KOALABEAR_16: u8 = 1;
/// GKR sparse-MLE PCS/verifier profile.
pub const PREPARED_PCS_PROFILE_GKR_SPARSE_MLE_V1: u8 = 1;
/// Exact A0 configuration profile: d24, default leaf bound, strategy A.
pub const PREPARED_CONFIG_PROFILE_D24_A: u8 = 1;
/// Strategy-A identifier.
pub const PREPARED_STRATEGY_A: u8 = 0;
/// Membership operation tag.
pub const PREPARED_OP_MEMBERSHIP: u8 = 0;
/// Exact A0 tree depth.
pub const PREPARED_DEPTH: u32 = 24;
/// Exact A0 leaf encoding bound.
pub const PREPARED_LEAF_MAX_FIELDS: u32 = DEFAULT_LEAF_MAX_FIELDS as u32;

/// Exact byte length of the reviewed d24/A/Membership material.
pub const PINNED_D24_A_MEMBERSHIP_MATERIAL_BYTES: usize = 7_772_516;
/// Fixed framed digest of the reviewed d24/A/Membership material.
pub const PINNED_D24_A_MEMBERSHIP_FRAMED_DIGEST: [u8; 32] = [
    0xfb, 0x04, 0x2c, 0x62, 0xe3, 0x91, 0x48, 0xb4, 0x02, 0x40, 0xa1, 0x05, 0x1c, 0xf6, 0xeb, 0x2e,
    0x6f, 0x2e, 0x45, 0xac, 0xa5, 0xdd, 0x91, 0x2a, 0xee, 0x5b, 0x38, 0x5f, 0xc8, 0xe0, 0xc6, 0xdf,
];
/// Fixed full circuit commitment of the reviewed d24/A/Membership material.
pub const PINNED_D24_A_MEMBERSHIP_CIRCUIT_COMMITMENT: [u8; 32] = [
    0xab, 0xde, 0x24, 0x1a, 0x4b, 0xf8, 0xa8, 0x4d, 0x0f, 0xb7, 0xd3, 0x48, 0xa7, 0xd3, 0xec, 0x5b,
    0x68, 0xfe, 0x46, 0x0d, 0xa3, 0xbe, 0x14, 0x3b, 0xd6, 0xd6, 0x7f, 0x32, 0x2b, 0xda, 0x2f, 0x07,
];

/// Header byte length.
pub const PREPARED_HEADER_BYTES: usize = 148;
/// Per-layer header byte length.
pub const PREPARED_LAYER_HEADER_BYTES: usize = 24;
/// Per-gate record byte length.
pub const PREPARED_GATE_BYTES: usize = 20;
/// Per-constant record byte length.
pub const PREPARED_CONST_BYTES: usize = 8;
/// Per-hint record byte length.
pub const PREPARED_HINT_BYTES: usize = 12;

/// Byte offset of the schema version.
pub const OFFSET_SCHEMA_VERSION: usize = 40;
/// Byte offset of the protocol version.
pub const OFFSET_PROTOCOL_VERSION: usize = 42;
/// Byte offset of the circuit version.
pub const OFFSET_CIRCUIT_VERSION: usize = 44;
/// Byte offset of the leaf version.
pub const OFFSET_LEAF_VERSION: usize = 46;
/// Byte offset of the operation tag.
pub const OFFSET_OPERATION_KIND: usize = 51;
/// Byte offset of the config profile.
pub const OFFSET_CONFIG_PROFILE: usize = 52;
/// Byte offset of the strategy identifier.
pub const OFFSET_STRATEGY_ID: usize = 53;
/// Byte offset of the two-byte header reserved field.
pub const OFFSET_HEADER_RESERVED: usize = 54;
/// Byte offset of the strategy argument.
pub const OFFSET_STRATEGY_ARG: usize = 56;
/// Byte offset of the depth.
pub const OFFSET_DEPTH: usize = 60;
/// Byte offset of leaf_max_fields.
pub const OFFSET_LEAF_MAX_FIELDS: usize = 64;
/// Byte offset of input_width_bits.
pub const OFFSET_INPUT_WIDTH_BITS: usize = 68;
/// Byte offset of the layer count.
pub const OFFSET_LAYER_COUNT: usize = 72;
/// Byte offset of the declared total length.
pub const OFFSET_TOTAL_LENGTH: usize = 76;
/// Byte offset of the encoded full circuit commitment.
pub const OFFSET_FULL_CIRCUIT_COMMITMENT: usize = 116;

const MAX_MATERIAL_BYTES: usize = 1 << 30;
const MAX_LAYERS: usize = 4_096;
const MAX_TOTAL_GATES: usize = 64_000_000;
const MAX_TOTAL_CONSTS: usize = 16_000_000;
const MAX_LAYER_RECORDS: usize = 16_000_000;
const MAX_WIDTH_BITS: usize = 30;

/// Fixed profile/version axes used in fail-closed errors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreparedProfileAxis {
    /// Protocol semantics.
    Protocol,
    /// Circuit/compiler semantics.
    Circuit,
    /// Leaf encoding.
    Leaf,
    /// Base field encoding.
    Field,
    /// Hash/transcript selection.
    Hash,
    /// PCS/verifier selection.
    Pcs,
}

/// Fail-closed codec, validation, provenance and audit-binding errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PreparedMaterialError {
    /// A checked size calculation overflowed.
    LengthOverflow,
    /// A count or byte size exceeds the fixed A0 budget.
    BudgetExceeded,
    /// A structural count cannot fit its wire integer.
    CountOverflow,
    /// The buffer ended before a required byte.
    UnexpectedEof {
        /// First byte offset that could not be read.
        offset: usize,
    },
    /// The magic is not the fixed v1 magic.
    BadMagic,
    /// The fixed domain differs.
    BadDomain,
    /// The schema version is not exactly v1.
    UnsupportedSchema {
        /// Version found.
        found: u16,
    },
    /// A semantic version axis is unsupported.
    UnsupportedVersion {
        /// Axis that failed.
        axis: PreparedProfileAxis,
        /// Version found.
        found: u16,
    },
    /// A named profile identifier is not the compiled profile.
    WrongProfile {
        /// Axis that failed.
        axis: PreparedProfileAxis,
        /// Identifier found.
        found: u8,
    },
    /// The operation is not Membership.
    OperationKindMismatch {
        /// Operation tag found.
        found: u8,
    },
    /// Depth, leaf bound, config profile or strategy differs.
    ConfigMismatch,
    /// A reserved field, tag or alternate representation is non-canonical.
    NonCanonicalEncoding {
        /// Byte offset of the first invalid field.
        offset: usize,
    },
    /// A field element is not a canonical KoalaBear residue.
    NonCanonicalField {
        /// Byte offset of the offending element.
        offset: usize,
    },
    /// The declared total length disagrees with the scanned layout.
    DeclaredLengthMismatch,
    /// Bytes remain after the exact declared payload.
    TrailingBytes {
        /// Number of extra bytes.
        extra: usize,
    },
    /// Circuit indices, widths, unary conventions or hint shapes are invalid.
    InvalidCircuit,
    /// Stored, recomputed or compiled-expected commitments differ.
    CircuitCommitmentMismatch,
    /// Hints or locally rederived wiring differ from the reference form.
    WiringMismatch,
    /// The framed material digest differs from the expected digest.
    PreparedDigestMismatch,
    /// Generator provenance differs from the expected reviewed record.
    ProvenanceMismatch,
    /// A provenance text value contains a forbidden control character.
    NonCanonicalProvenance,
    /// Audit binding contains a stale or substituted route ID.
    RouteIdMismatch,
    /// Audit binding names another guest image.
    GuestImageMismatch,
    /// Audit binding is used before its effective height.
    RouteNotEffective,
    /// Audit binding is revoked.
    RouteRevoked,
    /// Audit binding is past its draining cutoff.
    SupersededRoute,
}

/// Canonical circuit-and-hints material. No derived wiring is stored.
#[derive(Clone, Debug)]
pub struct PreparedMaterialV1 {
    /// Exact public circuit configuration.
    pub params: SmtParams,
    /// Exact operation kind.
    pub kind: SmtOpKind,
    /// Exact layer strategy.
    pub strategy: LayerStrategy,
    /// Canonically compiled circuit.
    pub circuit: LayeredCircuit<BaseField>,
    /// Canonical compiler hints.
    pub hints: WiringHints,
    /// Full circuit commitment. Generic decode recomputes it; the pinned
    /// runtime matches it to the compiled commitment before use.
    pub full_circuit_commitment: Digest<BaseField>,
}

#[derive(Clone, Copy, Debug)]
enum DecodeMode {
    Full,
    PinnedRuntime,
}

/// A validated material object and its locally reconstructed wiring.
#[derive(Clone, Debug)]
pub struct ValidatedPreparedMaterialV1 {
    /// Strictly decoded canonical material.
    pub material: PreparedMaterialV1,
    /// Framed SHA-256 digest of the exact bytes.
    pub framed_digest: [u8; 32],
    /// Locally rederived wiring. It never came from the caller.
    pub derived_wiring: DerivedRegularWiring,
}

/// Canonical generator provenance record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratorProvenanceV1 {
    /// Exact source commit.
    pub source_commit: String,
    /// Exact schema/profile label.
    pub schema_profile: String,
    /// Exact invoked command and arguments.
    pub exact_command: String,
    /// Exact compilation target.
    pub target: String,
    /// SHA-256 of the generator executable.
    pub generator_binary_sha256: [u8; 32],
    /// SHA-256 of root Cargo.toml.
    pub input_manifest_sha256: [u8; 32],
    /// SHA-256 of root Cargo.lock.
    pub input_lock_sha256: [u8; 32],
    /// SHA-256 of rust-toolchain.toml.
    pub input_toolchain_sha256: [u8; 32],
    /// Exact output byte length.
    pub output_byte_length: u64,
    /// SHA-256 of the raw output bytes.
    pub output_sha256: [u8; 32],
    /// Whether tracked files were clean at generation time.
    pub clean_tree: bool,
}

impl GeneratorProvenanceV1 {
    /// Render a stable UTF-8 line record without serde or host layout.
    pub fn to_canonical_text(&self) -> Result<String, PreparedMaterialError> {
        for value in [
            &self.source_commit,
            &self.schema_profile,
            &self.exact_command,
            &self.target,
        ] {
            if value
                .bytes()
                .any(|b| matches!(b, b'\0' | b'\n' | b'\r' | 0x1b))
            {
                return Err(PreparedMaterialError::NonCanonicalProvenance);
            }
        }
        Ok(format!(
            concat!(
                "record=PreparedMaterialGeneratorProvenanceV1\n",
                "source_commit={}\n",
                "schema_profile={}\n",
                "exact_command={}\n",
                "target={}\n",
                "generator_binary_sha256={}\n",
                "input_manifest_sha256={}\n",
                "input_lock_sha256={}\n",
                "input_toolchain_sha256={}\n",
                "output_byte_length={}\n",
                "output_sha256={}\n",
                "clean_tree={}\n"
            ),
            self.source_commit,
            self.schema_profile,
            self.exact_command,
            self.target,
            hex(&self.generator_binary_sha256),
            hex(&self.input_manifest_sha256),
            hex(&self.input_lock_sha256),
            hex(&self.input_toolchain_sha256),
            self.output_byte_length,
            hex(&self.output_sha256),
            self.clean_tree,
        ))
    }

    /// Hash the canonical record under its own provenance domain.
    pub fn digest(&self) -> Result<[u8; 32], PreparedMaterialError> {
        let text = self.to_canonical_text()?;
        Ok(sha256_parts(&[
            GENERATOR_PROVENANCE_DOMAIN,
            &(text.len() as u64).to_le_bytes(),
            text.as_bytes(),
        ]))
    }
}

/// Compare every provenance field exactly.
pub fn verify_generator_provenance(
    actual: &GeneratorProvenanceV1,
    expected: &GeneratorProvenanceV1,
) -> Result<(), PreparedMaterialError> {
    if actual == expected {
        Ok(())
    } else {
        Err(PreparedMaterialError::ProvenanceMismatch)
    }
}

/// Immutable external tuple used only by the A0 host-native attack battery.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedMaterialBindingCoreAuditV1 {
    /// Guest image identifier, external to the material payload.
    pub guest_image_id: [u8; 32],
    /// Framed prepared-material digest.
    pub prepared_digest: [u8; 32],
    /// Exact prepared schema.
    pub prepared_schema_version: u16,
    /// Full circuit commitment as eight canonical LE u32 limbs.
    pub full_circuit_commitment: [u8; 32],
    /// Exact operation tag.
    pub operation_kind: u8,
    /// Digest of the reviewed generator provenance record.
    pub generator_provenance_digest: [u8; 32],
}

impl PreparedMaterialBindingCoreAuditV1 {
    /// Compute the non-circular immutable audit route ID.
    pub fn route_id(&self) -> [u8; 32] {
        sha256_parts(&[
            PREPARED_BINDING_AUDIT_DOMAIN,
            &self.guest_image_id,
            &self.prepared_digest,
            &self.prepared_schema_version.to_le_bytes(),
            &self.full_circuit_commitment,
            &[self.operation_kind],
            &self.generator_provenance_digest,
        ])
    }
}

/// Mutable lifecycle used only by the A0 audit binding tests.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreparedBindingLifecycleAuditV1 {
    /// New audit acceptance is active.
    Active,
    /// Accept only through the inclusive cutoff.
    Draining {
        /// Inclusive cutoff height.
        cutoff: u64,
    },
    /// New audit acceptance is revoked.
    Revoked,
}

/// Complete A0 audit binding with immutable and mutable portions separated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedMaterialBindingAuditV1 {
    /// Stored immutable content address.
    pub route_id: [u8; 32],
    /// Immutable tuple.
    pub core: PreparedMaterialBindingCoreAuditV1,
    /// First accepted height.
    pub effective_height: u64,
    /// Mutable lifecycle.
    pub lifecycle: PreparedBindingLifecycleAuditV1,
}

impl PreparedMaterialBindingAuditV1 {
    /// Construct an audit binding with its recomputed route ID.
    pub fn new(
        core: PreparedMaterialBindingCoreAuditV1,
        effective_height: u64,
        lifecycle: PreparedBindingLifecycleAuditV1,
    ) -> Self {
        let route_id = core.route_id();
        Self {
            route_id,
            core,
            effective_height,
            lifecycle,
        }
    }

    /// Validate immutable equality and the external lifecycle.
    pub fn validate(
        &self,
        actual_guest_image_id: &[u8; 32],
        acceptance_height: u64,
    ) -> Result<(), PreparedMaterialError> {
        if self.route_id != self.core.route_id() {
            return Err(PreparedMaterialError::RouteIdMismatch);
        }
        if actual_guest_image_id != &self.core.guest_image_id {
            return Err(PreparedMaterialError::GuestImageMismatch);
        }
        if acceptance_height < self.effective_height {
            return Err(PreparedMaterialError::RouteNotEffective);
        }
        match self.lifecycle {
            PreparedBindingLifecycleAuditV1::Active => Ok(()),
            PreparedBindingLifecycleAuditV1::Draining { cutoff } if acceptance_height <= cutoff => {
                Ok(())
            }
            PreparedBindingLifecycleAuditV1::Draining { .. } => {
                Err(PreparedMaterialError::SupersededRoute)
            }
            PreparedBindingLifecycleAuditV1::Revoked => Err(PreparedMaterialError::RouteRevoked),
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct Header {
    input_width_bits: usize,
    layer_count: usize,
    total_length: usize,
    total_gates: usize,
    total_consts: usize,
    total_gate_hints: usize,
    total_const_hints: usize,
    full_circuit_commitment: Digest<BaseField>,
}

#[derive(Clone, Copy, Debug)]
struct LayerCounts {
    width_bits: usize,
    gates: usize,
    consts: usize,
    gate_hints: usize,
    const_hints: usize,
}

/// Compile the exact d24, strategy-A, Membership A0 profile.
pub fn canonical_prepared_material_v1() -> Result<PreparedMaterialV1, PreparedMaterialError> {
    let params = SmtParams {
        depth: PREPARED_DEPTH,
        leaf_max_fields: PREPARED_LEAF_MAX_FIELDS,
    };
    let kind = SmtOpKind::Membership;
    let strategy = LayerStrategy::A;
    let hasher = Poseidon2Gadget::new(PREPARED_LEAF_MAX_FIELDS as usize);
    let (circuit, hints) = compile_with_hints(&params, kind, strategy, &hasher.round_template())
        .map_err(|_| PreparedMaterialError::InvalidCircuit)?;
    let commitment = full_circuit_commitment(&circuit, kind, &params, strategy);
    Ok(PreparedMaterialV1 {
        params,
        kind,
        strategy,
        circuit,
        hints,
        full_circuit_commitment: commitment,
    })
}

/// Encode one exact-profile material object into canonical bytes.
pub fn encode_prepared_material_v1(
    material: &PreparedMaterialV1,
) -> Result<Vec<u8>, PreparedMaterialError> {
    validate_exact_profile(material.params, material.kind, material.strategy)?;
    validate_circuit_structure(&material.circuit, &material.hints)?;
    let recomputed = full_circuit_commitment(
        &material.circuit,
        material.kind,
        &material.params,
        material.strategy,
    );
    if recomputed != material.full_circuit_commitment {
        return Err(PreparedMaterialError::CircuitCommitmentMismatch);
    }

    let counts = material_counts(material)?;
    let total_length = encoded_length(&counts)?;
    if total_length > MAX_MATERIAL_BYTES {
        return Err(PreparedMaterialError::BudgetExceeded);
    }
    let mut out = Vec::with_capacity(total_length);
    out.extend_from_slice(&PREPARED_MATERIAL_MAGIC);
    out.extend_from_slice(&PREPARED_MATERIAL_DOMAIN);
    out.extend_from_slice(&PREPARED_MATERIAL_SCHEMA_VERSION.to_le_bytes());
    out.extend_from_slice(&PREPARED_PROTOCOL_PROFILE_VERSION.to_le_bytes());
    out.extend_from_slice(&PREPARED_CIRCUIT_PROFILE_VERSION.to_le_bytes());
    out.extend_from_slice(&PREPARED_LEAF_PROFILE_VERSION.to_le_bytes());
    out.push(PREPARED_FIELD_PROFILE_KOALABEAR_U32);
    out.push(PREPARED_HASH_PROFILE_POSEIDON2_KOALABEAR_16);
    out.push(PREPARED_PCS_PROFILE_GKR_SPARSE_MLE_V1);
    out.push(PREPARED_OP_MEMBERSHIP);
    out.push(PREPARED_CONFIG_PROFILE_D24_A);
    out.push(PREPARED_STRATEGY_A);
    out.extend_from_slice(&0u16.to_le_bytes());
    out.extend_from_slice(&0u32.to_le_bytes());
    out.extend_from_slice(&material.params.depth.to_le_bytes());
    out.extend_from_slice(&material.params.leaf_max_fields.to_le_bytes());
    put_usize_u32(&mut out, material.circuit.input_width_bits)?;
    put_usize_u32(&mut out, material.circuit.layers.len())?;
    out.extend_from_slice(&(total_length as u64).to_le_bytes());
    out.extend_from_slice(&(counts.total_gates as u64).to_le_bytes());
    out.extend_from_slice(&(counts.total_consts as u64).to_le_bytes());
    out.extend_from_slice(&(counts.total_gate_hints as u64).to_le_bytes());
    out.extend_from_slice(&(counts.total_const_hints as u64).to_le_bytes());
    put_digest(&mut out, &material.full_circuit_commitment);

    for (layer, hints) in material.circuit.layers.iter().zip(&material.hints.layers) {
        put_usize_u32(&mut out, layer.width_bits)?;
        put_usize_u32(&mut out, layer.gates.len())?;
        put_usize_u32(&mut out, layer.consts.len())?;
        put_usize_u32(&mut out, hints.gates.len())?;
        put_usize_u32(&mut out, hints.consts.len())?;
        out.extend_from_slice(&0u32.to_le_bytes());

        for gate in &layer.gates {
            out.push(gate_kind_tag(gate.kind));
            out.extend_from_slice(&[0u8; 3]);
            out.extend_from_slice(&gate.out.to_le_bytes());
            out.extend_from_slice(&gate.in1.to_le_bytes());
            out.extend_from_slice(&gate.in2.to_le_bytes());
            put_fe(&mut out, gate.coeff);
        }
        for &(wire, value) in &layer.consts {
            out.extend_from_slice(&wire.to_le_bytes());
            put_fe(&mut out, value);
        }
        for hint in &hints.gates {
            put_hint(&mut out, *hint);
        }
        for hint in &hints.consts {
            put_hint(&mut out, *hint);
        }
    }
    if out.len() != total_length {
        return Err(PreparedMaterialError::DeclaredLengthMismatch);
    }
    Ok(out)
}

/// Strictly decode exact-profile bytes and enforce their self-contained
/// commitment and canonical fixed point.
pub fn decode_prepared_material_v1(
    bytes: &[u8],
) -> Result<PreparedMaterialV1, PreparedMaterialError> {
    decode_prepared_material_v1_with_mode(bytes, DecodeMode::Full)
}

fn decode_prepared_material_v1_with_mode(
    bytes: &[u8],
    mode: DecodeMode,
) -> Result<PreparedMaterialV1, PreparedMaterialError> {
    let header = preflight(bytes)?;
    let mut rd = Reader::new(bytes);
    read_and_validate_header(&mut rd)?;

    let mut layers = Vec::with_capacity(header.layer_count);
    let mut hint_layers = Vec::with_capacity(header.layer_count);
    for _ in 0..header.layer_count {
        let counts = read_layer_header(&mut rd)?;
        let mut gates = Vec::with_capacity(counts.gates);
        let mut consts = Vec::with_capacity(counts.consts);
        let mut gate_hints = Vec::with_capacity(counts.gate_hints);
        let mut const_hints = Vec::with_capacity(counts.const_hints);

        for _ in 0..counts.gates {
            let kind_at = rd.offset();
            let kind = match rd.u8()? {
                0 => GateKind::Lin,
                1 => GateKind::Mul,
                2 => GateKind::Pow3,
                _ => {
                    return Err(PreparedMaterialError::NonCanonicalEncoding { offset: kind_at });
                }
            };
            rd.zeroes(3)?;
            gates.push(Gate {
                kind,
                out: rd.u32()?,
                in1: rd.u32()?,
                in2: rd.u32()?,
                coeff: rd.fe()?,
            });
        }
        for _ in 0..counts.consts {
            consts.push((rd.u32()?, rd.fe()?));
        }
        for _ in 0..counts.gate_hints {
            gate_hints.push(rd.hint()?);
        }
        for _ in 0..counts.const_hints {
            const_hints.push(rd.hint()?);
        }
        layers.push(Layer {
            width_bits: counts.width_bits,
            gates,
            consts,
        });
        hint_layers.push(LayerHints {
            gates: gate_hints,
            consts: const_hints,
        });
    }
    if rd.remaining() != 0 {
        return Err(PreparedMaterialError::TrailingBytes {
            extra: rd.remaining(),
        });
    }

    let material = PreparedMaterialV1 {
        params: SmtParams {
            depth: PREPARED_DEPTH,
            leaf_max_fields: PREPARED_LEAF_MAX_FIELDS,
        },
        kind: SmtOpKind::Membership,
        strategy: LayerStrategy::A,
        circuit: LayeredCircuit {
            layers,
            input_width_bits: header.input_width_bits,
        },
        hints: WiringHints {
            layers: hint_layers,
        },
        full_circuit_commitment: header.full_circuit_commitment,
    };
    validate_circuit_structure(&material.circuit, &material.hints)?;
    if matches!(mode, DecodeMode::Full) {
        let recomputed = full_circuit_commitment(
            &material.circuit,
            material.kind,
            &material.params,
            material.strategy,
        );
        if recomputed != material.full_circuit_commitment {
            return Err(PreparedMaterialError::CircuitCommitmentMismatch);
        }
        let reencoded = encode_prepared_material_v1(&material)?;
        if reencoded != bytes {
            return Err(PreparedMaterialError::NonCanonicalEncoding { offset: 0 });
        }
    }
    Ok(material)
}

/// Validate bytes against an independently compiled expected material,
/// rederive wiring, and compare it with the materialized reference.
pub fn validate_prepared_material_v1_against(
    bytes: &[u8],
    expected: &PreparedMaterialV1,
) -> Result<ValidatedPreparedMaterialV1, PreparedMaterialError> {
    let material = decode_prepared_material_v1(bytes)?;
    if material.full_circuit_commitment != expected.full_circuit_commitment
        || material.circuit != expected.circuit
    {
        return Err(PreparedMaterialError::CircuitCommitmentMismatch);
    }
    if !hints_equal(&material.hints, &expected.hints) {
        return Err(PreparedMaterialError::WiringMismatch);
    }
    let derived = DerivedRegularWiring::derive(&material.circuit, &material.hints);
    verify_exact_repartition(&material.circuit, &derived)?;

    let expected_bytes = encode_prepared_material_v1(expected)?;
    let expected_digest = prepared_material_digest(&expected_bytes);
    let actual_digest = prepared_material_digest(bytes);
    if actual_digest != expected_digest {
        return Err(PreparedMaterialError::PreparedDigestMismatch);
    }
    Ok(ValidatedPreparedMaterialV1 {
        material,
        framed_digest: actual_digest,
        derived_wiring: derived,
    })
}

/// Full A0 validation using a fresh canonical compile as the expected anchor.
pub fn validate_prepared_material_v1(
    bytes: &[u8],
) -> Result<ValidatedPreparedMaterialV1, PreparedMaterialError> {
    let expected = canonical_prepared_material_v1()?;
    validate_prepared_material_v1_against(bytes, &expected)
}

/// Validate only the reviewed d24, strategy-A, Membership material without
/// compiling a fresh circuit. All expected anchors are owned by this crate;
/// callers can supply only the candidate bytes.
pub fn validate_pinned_d24_a_membership_material(
    bytes: &[u8],
) -> Result<ValidatedPreparedMaterialV1, PreparedMaterialError> {
    if bytes.len() < PINNED_D24_A_MEMBERSHIP_MATERIAL_BYTES {
        return Err(PreparedMaterialError::UnexpectedEof {
            offset: bytes.len(),
        });
    }
    if bytes.len() > PINNED_D24_A_MEMBERSHIP_MATERIAL_BYTES {
        return Err(PreparedMaterialError::TrailingBytes {
            extra: bytes.len() - PINNED_D24_A_MEMBERSHIP_MATERIAL_BYTES,
        });
    }

    let framed_digest = prepared_material_digest(bytes);
    if framed_digest != PINNED_D24_A_MEMBERSHIP_FRAMED_DIGEST {
        return Err(PreparedMaterialError::PreparedDigestMismatch);
    }

    let material = decode_prepared_material_v1_with_mode(bytes, DecodeMode::PinnedRuntime)?;
    if circuit_commitment_bytes(&material.full_circuit_commitment)
        != PINNED_D24_A_MEMBERSHIP_CIRCUIT_COMMITMENT
    {
        return Err(PreparedMaterialError::CircuitCommitmentMismatch);
    }
    let derived_wiring = DerivedRegularWiring::derive(&material.circuit, &material.hints);
    verify_exact_repartition(&material.circuit, &derived_wiring)?;

    Ok(ValidatedPreparedMaterialV1 {
        material,
        framed_digest,
        derived_wiring,
    })
}

/// Framed SHA-256 digest of exact canonical bytes.
pub fn prepared_material_digest(bytes: &[u8]) -> [u8; 32] {
    sha256_parts(&[
        PREPARED_MATERIAL_DIGEST_DOMAIN,
        &(bytes.len() as u64).to_le_bytes(),
        bytes,
    ])
}

/// Raw SHA-256 helper used by generator provenance.
pub fn raw_sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

/// Verify a supplied digest against the fixed framed definition.
pub fn verify_prepared_material_digest(
    bytes: &[u8],
    expected: &[u8; 32],
) -> Result<(), PreparedMaterialError> {
    if &prepared_material_digest(bytes) == expected {
        Ok(())
    } else {
        Err(PreparedMaterialError::PreparedDigestMismatch)
    }
}

/// Verify bytes against the digest of a fresh exact-profile compile.
pub fn verify_compiled_a0_material_digest(bytes: &[u8]) -> Result<(), PreparedMaterialError> {
    let expected = canonical_prepared_material_v1()?;
    let expected_bytes = encode_prepared_material_v1(&expected)?;
    verify_prepared_material_digest(bytes, &prepared_material_digest(&expected_bytes))
}

/// Canonical LE bytes of a full circuit commitment.
pub fn circuit_commitment_bytes(commitment: &Digest<BaseField>) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, value) in commitment.0.iter().enumerate() {
        let start = i * 4;
        out[start..start + 4].copy_from_slice(&value.as_canonical_u32().to_le_bytes());
    }
    out
}

fn validate_exact_profile(
    params: SmtParams,
    kind: SmtOpKind,
    strategy: LayerStrategy,
) -> Result<(), PreparedMaterialError> {
    if params.depth != PREPARED_DEPTH || params.leaf_max_fields != PREPARED_LEAF_MAX_FIELDS {
        return Err(PreparedMaterialError::ConfigMismatch);
    }
    if kind != SmtOpKind::Membership {
        return Err(PreparedMaterialError::OperationKindMismatch {
            found: PublicInputs::kind_tag(kind),
        });
    }
    if strategy != LayerStrategy::A {
        return Err(PreparedMaterialError::ConfigMismatch);
    }
    Ok(())
}

fn validate_circuit_structure(
    circuit: &LayeredCircuit<BaseField>,
    hints: &WiringHints,
) -> Result<(), PreparedMaterialError> {
    if circuit.layers.is_empty()
        || circuit.layers.len() > MAX_LAYERS
        || circuit.input_width_bits > MAX_WIDTH_BITS
        || hints.layers.len() != circuit.layers.len()
    {
        return Err(PreparedMaterialError::InvalidCircuit);
    }
    for (li, (layer, layer_hints)) in circuit.layers.iter().zip(&hints.layers).enumerate() {
        if layer.width_bits > MAX_WIDTH_BITS
            || layer.gates.len() > MAX_LAYER_RECORDS
            || layer.consts.len() > MAX_LAYER_RECORDS
            || layer_hints.gates.len() != layer.gates.len()
            || layer_hints.consts.len() != layer.consts.len()
        {
            return Err(PreparedMaterialError::InvalidCircuit);
        }
        let in_bits = if li + 1 < circuit.layers.len() {
            circuit.layers[li + 1].width_bits
        } else {
            circuit.input_width_bits
        };
        if in_bits > MAX_WIDTH_BITS {
            return Err(PreparedMaterialError::InvalidCircuit);
        }
        let out_limit = 1u64
            .checked_shl(layer.width_bits as u32)
            .ok_or(PreparedMaterialError::InvalidCircuit)?;
        let in_limit = 1u64
            .checked_shl(in_bits as u32)
            .ok_or(PreparedMaterialError::InvalidCircuit)?;
        for gate in &layer.gates {
            if u64::from(gate.out) >= out_limit
                || u64::from(gate.in1) >= in_limit
                || u64::from(gate.in2) >= in_limit
                || gate.out >= BaseField::ORDER_U32
                || gate.in1 >= BaseField::ORDER_U32
                || gate.in2 >= BaseField::ORDER_U32
                || (matches!(gate.kind, GateKind::Lin | GateKind::Pow3) && gate.in1 != gate.in2)
            {
                return Err(PreparedMaterialError::InvalidCircuit);
            }
        }
        for &(wire, _) in &layer.consts {
            if u64::from(wire) >= out_limit || wire >= BaseField::ORDER_U32 {
                return Err(PreparedMaterialError::InvalidCircuit);
            }
        }
    }
    Ok(())
}

fn verify_exact_repartition(
    circuit: &LayeredCircuit<BaseField>,
    derived: &DerivedRegularWiring,
) -> Result<(), PreparedMaterialError> {
    for (li, layer) in circuit.layers.iter().enumerate() {
        let mut source_gates: Vec<_> = layer.gates.iter().map(gate_key).collect();
        let mut derived_gates: Vec<_> = derived.expand_gates(li).iter().map(gate_key).collect();
        source_gates.sort_unstable();
        derived_gates.sort_unstable();
        if source_gates != derived_gates {
            return Err(PreparedMaterialError::WiringMismatch);
        }

        let mut source_consts: Vec<_> = layer
            .consts
            .iter()
            .map(|&(wire, value)| (wire, value.as_canonical_u32()))
            .collect();
        let mut derived_consts: Vec<_> = derived
            .expand_consts(li)
            .iter()
            .map(|&(wire, value)| (wire, value.as_canonical_u32()))
            .collect();
        source_consts.sort_unstable();
        derived_consts.sort_unstable();
        if source_consts != derived_consts {
            return Err(PreparedMaterialError::WiringMismatch);
        }
    }
    Ok(())
}

fn gate_key(gate: &Gate<BaseField>) -> (u8, u32, u32, u32, u32) {
    (
        gate_kind_tag(gate.kind),
        gate.out,
        gate.in1,
        gate.in2,
        gate.coeff.as_canonical_u32(),
    )
}

fn hints_equal(left: &WiringHints, right: &WiringHints) -> bool {
    left.layers.len() == right.layers.len()
        && left
            .layers
            .iter()
            .zip(&right.layers)
            .all(|(a, b)| a.gates == b.gates && a.consts == b.consts)
}

#[derive(Clone, Copy, Debug)]
struct MaterialCounts {
    layers: usize,
    total_gates: usize,
    total_consts: usize,
    total_gate_hints: usize,
    total_const_hints: usize,
}

fn material_counts(material: &PreparedMaterialV1) -> Result<MaterialCounts, PreparedMaterialError> {
    let mut out = MaterialCounts {
        layers: material.circuit.layers.len(),
        total_gates: 0,
        total_consts: 0,
        total_gate_hints: 0,
        total_const_hints: 0,
    };
    for (layer, hints) in material.circuit.layers.iter().zip(&material.hints.layers) {
        out.total_gates = checked_add(out.total_gates, layer.gates.len())?;
        out.total_consts = checked_add(out.total_consts, layer.consts.len())?;
        out.total_gate_hints = checked_add(out.total_gate_hints, hints.gates.len())?;
        out.total_const_hints = checked_add(out.total_const_hints, hints.consts.len())?;
    }
    if out.layers > MAX_LAYERS
        || out.total_gates > MAX_TOTAL_GATES
        || out.total_consts > MAX_TOTAL_CONSTS
        || out.total_gate_hints != out.total_gates
        || out.total_const_hints != out.total_consts
    {
        return Err(PreparedMaterialError::BudgetExceeded);
    }
    Ok(out)
}

fn encoded_length(counts: &MaterialCounts) -> Result<usize, PreparedMaterialError> {
    let mut total = PREPARED_HEADER_BYTES;
    total = checked_add(
        total,
        checked_mul(PREPARED_LAYER_HEADER_BYTES, counts.layers)?,
    )?;
    total = checked_add(total, checked_mul(PREPARED_GATE_BYTES, counts.total_gates)?)?;
    total = checked_add(
        total,
        checked_mul(PREPARED_CONST_BYTES, counts.total_consts)?,
    )?;
    total = checked_add(
        total,
        checked_mul(PREPARED_HINT_BYTES, counts.total_gate_hints)?,
    )?;
    checked_add(
        total,
        checked_mul(PREPARED_HINT_BYTES, counts.total_const_hints)?,
    )
}

fn preflight(bytes: &[u8]) -> Result<Header, PreparedMaterialError> {
    if bytes.len() > MAX_MATERIAL_BYTES {
        return Err(PreparedMaterialError::BudgetExceeded);
    }
    let mut rd = Reader::new(bytes);
    let header = read_and_validate_header(&mut rd)?;
    if header.layer_count > MAX_LAYERS
        || header.total_gates > MAX_TOTAL_GATES
        || header.total_consts > MAX_TOTAL_CONSTS
        || header.total_gate_hints != header.total_gates
        || header.total_const_hints != header.total_consts
    {
        return Err(PreparedMaterialError::BudgetExceeded);
    }
    if header.total_length != bytes.len() {
        return Err(PreparedMaterialError::DeclaredLengthMismatch);
    }

    let mut total_gates = 0usize;
    let mut total_consts = 0usize;
    let mut total_gate_hints = 0usize;
    let mut total_const_hints = 0usize;
    for _ in 0..header.layer_count {
        let counts = read_layer_header(&mut rd)?;
        if counts.width_bits > MAX_WIDTH_BITS
            || counts.gates > MAX_LAYER_RECORDS
            || counts.consts > MAX_LAYER_RECORDS
            || counts.gate_hints != counts.gates
            || counts.const_hints != counts.consts
        {
            return Err(PreparedMaterialError::BudgetExceeded);
        }
        total_gates = checked_add(total_gates, counts.gates)?;
        total_consts = checked_add(total_consts, counts.consts)?;
        total_gate_hints = checked_add(total_gate_hints, counts.gate_hints)?;
        total_const_hints = checked_add(total_const_hints, counts.const_hints)?;
        let body = checked_add(
            checked_add(
                checked_mul(counts.gates, PREPARED_GATE_BYTES)?,
                checked_mul(counts.consts, PREPARED_CONST_BYTES)?,
            )?,
            checked_add(
                checked_mul(counts.gate_hints, PREPARED_HINT_BYTES)?,
                checked_mul(counts.const_hints, PREPARED_HINT_BYTES)?,
            )?,
        )?;
        rd.skip(body)?;
    }
    if total_gates != header.total_gates
        || total_consts != header.total_consts
        || total_gate_hints != header.total_gate_hints
        || total_const_hints != header.total_const_hints
    {
        return Err(PreparedMaterialError::DeclaredLengthMismatch);
    }
    if rd.remaining() != 0 {
        return Err(PreparedMaterialError::TrailingBytes {
            extra: rd.remaining(),
        });
    }
    Ok(header)
}

fn read_and_validate_header(rd: &mut Reader<'_>) -> Result<Header, PreparedMaterialError> {
    if rd.take(8)? != PREPARED_MATERIAL_MAGIC {
        return Err(PreparedMaterialError::BadMagic);
    }
    if rd.take(32)? != PREPARED_MATERIAL_DOMAIN {
        return Err(PreparedMaterialError::BadDomain);
    }
    let schema = rd.u16()?;
    if schema != PREPARED_MATERIAL_SCHEMA_VERSION {
        return Err(PreparedMaterialError::UnsupportedSchema { found: schema });
    }
    check_version(
        PreparedProfileAxis::Protocol,
        rd.u16()?,
        PREPARED_PROTOCOL_PROFILE_VERSION,
    )?;
    check_version(
        PreparedProfileAxis::Circuit,
        rd.u16()?,
        PREPARED_CIRCUIT_PROFILE_VERSION,
    )?;
    check_version(
        PreparedProfileAxis::Leaf,
        rd.u16()?,
        PREPARED_LEAF_PROFILE_VERSION,
    )?;
    check_profile(
        PreparedProfileAxis::Field,
        rd.u8()?,
        PREPARED_FIELD_PROFILE_KOALABEAR_U32,
    )?;
    check_profile(
        PreparedProfileAxis::Hash,
        rd.u8()?,
        PREPARED_HASH_PROFILE_POSEIDON2_KOALABEAR_16,
    )?;
    check_profile(
        PreparedProfileAxis::Pcs,
        rd.u8()?,
        PREPARED_PCS_PROFILE_GKR_SPARSE_MLE_V1,
    )?;
    let op = rd.u8()?;
    if op != PREPARED_OP_MEMBERSHIP {
        return Err(PreparedMaterialError::OperationKindMismatch { found: op });
    }
    if rd.u8()? != PREPARED_CONFIG_PROFILE_D24_A || rd.u8()? != PREPARED_STRATEGY_A {
        return Err(PreparedMaterialError::ConfigMismatch);
    }
    rd.zeroes(2)?;
    if rd.u32()? != 0 || rd.u32()? != PREPARED_DEPTH || rd.u32()? != PREPARED_LEAF_MAX_FIELDS {
        return Err(PreparedMaterialError::ConfigMismatch);
    }
    let input_width_bits =
        usize::try_from(rd.u32()?).map_err(|_| PreparedMaterialError::CountOverflow)?;
    let layer_count =
        usize::try_from(rd.u32()?).map_err(|_| PreparedMaterialError::CountOverflow)?;
    let total_length =
        usize::try_from(rd.u64()?).map_err(|_| PreparedMaterialError::BudgetExceeded)?;
    if total_length > MAX_MATERIAL_BYTES {
        return Err(PreparedMaterialError::BudgetExceeded);
    }
    if rd.len() < total_length {
        return Err(PreparedMaterialError::UnexpectedEof { offset: rd.len() });
    }
    if rd.len() > total_length {
        return Err(PreparedMaterialError::TrailingBytes {
            extra: rd.len() - total_length,
        });
    }
    let total_gates = usize_from_u64(rd.u64()?)?;
    let total_consts = usize_from_u64(rd.u64()?)?;
    let total_gate_hints = usize_from_u64(rd.u64()?)?;
    let total_const_hints = usize_from_u64(rd.u64()?)?;
    let full_circuit_commitment = rd.digest()?;
    Ok(Header {
        input_width_bits,
        layer_count,
        total_length,
        total_gates,
        total_consts,
        total_gate_hints,
        total_const_hints,
        full_circuit_commitment,
    })
}

fn read_layer_header(rd: &mut Reader<'_>) -> Result<LayerCounts, PreparedMaterialError> {
    let width_bits =
        usize::try_from(rd.u32()?).map_err(|_| PreparedMaterialError::CountOverflow)?;
    let gates = usize::try_from(rd.u32()?).map_err(|_| PreparedMaterialError::CountOverflow)?;
    let consts = usize::try_from(rd.u32()?).map_err(|_| PreparedMaterialError::CountOverflow)?;
    let gate_hints =
        usize::try_from(rd.u32()?).map_err(|_| PreparedMaterialError::CountOverflow)?;
    let const_hints =
        usize::try_from(rd.u32()?).map_err(|_| PreparedMaterialError::CountOverflow)?;
    rd.zeroes(4)?;
    Ok(LayerCounts {
        width_bits,
        gates,
        consts,
        gate_hints,
        const_hints,
    })
}

fn check_version(
    axis: PreparedProfileAxis,
    found: u16,
    expected: u16,
) -> Result<(), PreparedMaterialError> {
    if found == expected {
        Ok(())
    } else {
        Err(PreparedMaterialError::UnsupportedVersion { axis, found })
    }
}

fn check_profile(
    axis: PreparedProfileAxis,
    found: u8,
    expected: u8,
) -> Result<(), PreparedMaterialError> {
    if found == expected {
        Ok(())
    } else {
        Err(PreparedMaterialError::WrongProfile { axis, found })
    }
}

fn usize_from_u64(value: u64) -> Result<usize, PreparedMaterialError> {
    usize::try_from(value).map_err(|_| PreparedMaterialError::BudgetExceeded)
}

fn put_usize_u32(out: &mut Vec<u8>, value: usize) -> Result<(), PreparedMaterialError> {
    let value = u32::try_from(value).map_err(|_| PreparedMaterialError::CountOverflow)?;
    out.extend_from_slice(&value.to_le_bytes());
    Ok(())
}

fn put_fe(out: &mut Vec<u8>, value: BaseField) {
    out.extend_from_slice(&value.as_canonical_u32().to_le_bytes());
}

fn put_digest(out: &mut Vec<u8>, digest: &Digest<BaseField>) {
    for value in &digest.0 {
        put_fe(out, *value);
    }
}

fn put_hint(out: &mut Vec<u8>, hint: Option<FamilyTag>) {
    match hint {
        Some(tag) => {
            out.push(1);
            out.extend_from_slice(&[0u8; 3]);
            out.extend_from_slice(&tag.family.to_le_bytes());
            out.extend_from_slice(&tag.block.to_le_bytes());
        }
        None => out.extend_from_slice(&[0u8; PREPARED_HINT_BYTES]),
    }
}

fn gate_kind_tag(kind: GateKind) -> u8 {
    match kind {
        GateKind::Lin => 0,
        GateKind::Mul => 1,
        GateKind::Pow3 => 2,
    }
}

fn checked_add(left: usize, right: usize) -> Result<usize, PreparedMaterialError> {
    left.checked_add(right)
        .ok_or(PreparedMaterialError::LengthOverflow)
}

fn checked_mul(left: usize, right: usize) -> Result<usize, PreparedMaterialError> {
    left.checked_mul(right)
        .ok_or(PreparedMaterialError::LengthOverflow)
}

fn sha256_parts(parts: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for part in parts {
        hasher.update(part);
    }
    hasher.finalize().into()
}

fn hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(char::from(HEX[usize::from(byte >> 4)]));
        out.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    out
}

struct Reader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn len(&self) -> usize {
        self.bytes.len()
    }

    fn offset(&self) -> usize {
        self.offset
    }

    fn remaining(&self) -> usize {
        self.bytes.len().saturating_sub(self.offset)
    }

    fn take(&mut self, count: usize) -> Result<&'a [u8], PreparedMaterialError> {
        let end = self
            .offset
            .checked_add(count)
            .ok_or(PreparedMaterialError::LengthOverflow)?;
        if end > self.bytes.len() {
            return Err(PreparedMaterialError::UnexpectedEof {
                offset: self.offset,
            });
        }
        let result = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(result)
    }

    fn skip(&mut self, count: usize) -> Result<(), PreparedMaterialError> {
        self.take(count).map(|_| ())
    }

    fn zeroes(&mut self, count: usize) -> Result<(), PreparedMaterialError> {
        let at = self.offset;
        if self.take(count)?.iter().any(|byte| *byte != 0) {
            return Err(PreparedMaterialError::NonCanonicalEncoding { offset: at });
        }
        Ok(())
    }

    fn u8(&mut self) -> Result<u8, PreparedMaterialError> {
        Ok(self.take(1)?[0])
    }

    fn u16(&mut self) -> Result<u16, PreparedMaterialError> {
        let bytes = self.take(2)?;
        Ok(u16::from_le_bytes([bytes[0], bytes[1]]))
    }

    fn u32(&mut self) -> Result<u32, PreparedMaterialError> {
        let bytes = self.take(4)?;
        Ok(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    fn u64(&mut self) -> Result<u64, PreparedMaterialError> {
        let bytes = self.take(8)?;
        Ok(u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]))
    }

    fn fe(&mut self) -> Result<BaseField, PreparedMaterialError> {
        let at = self.offset;
        let value = self.u32()?;
        if value >= BaseField::ORDER_U32 {
            return Err(PreparedMaterialError::NonCanonicalField { offset: at });
        }
        Ok(BaseField::from_u32(value))
    }

    fn digest(&mut self) -> Result<Digest<BaseField>, PreparedMaterialError> {
        let mut values = [BaseField::ZERO; DIGEST_WIDTH];
        for value in &mut values {
            *value = self.fe()?;
        }
        Ok(Digest(values))
    }

    fn hint(&mut self) -> Result<Option<FamilyTag>, PreparedMaterialError> {
        let at = self.offset;
        let present = self.u8()?;
        self.zeroes(3)?;
        let family = self.u32()?;
        let block = self.u32()?;
        match present.cmp(&1) {
            Ordering::Equal => Ok(Some(FamilyTag { family, block })),
            Ordering::Less if family == 0 && block == 0 => Ok(None),
            _ => Err(PreparedMaterialError::NonCanonicalEncoding { offset: at }),
        }
    }
}
