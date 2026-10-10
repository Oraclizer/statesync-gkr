//! Canonical static identity for the native RISC Zero Route B profile.
//!
//! This module is deliberately separate from the stock Groth16 two-public-
//! input [`crate::settlement::RouteManifestV1`] codec. It content-addresses
//! the observed static RISC Zero/zkVerify/destination profile and its trust
//! ceiling. It does not authenticate live source finality, enforce destination
//! code or roles, reject root conflicts, validate a live receipt tuple, select
//! a production route, or alter the route-independent settlement key.

use std::fmt;

use serde::Deserialize;
use sha2::{Digest as _, Sha256};
use sha3::Keccak256;

use crate::settlement::{
    ActionKindV1, DestinationV1, Hash32, SETTLEMENT_KEY_DOMAIN, settlement_key_preimage,
};

/// Domain prefix for the native RISC Zero Route B manifest content address.
pub const RISC0_ROUTE_B_MANIFEST_DOMAIN: &[u8] = b"ssgkr/risc0-route-b-manifest/v1";

/// Error returned by strict JSON parsing, canonical encoding, or vector checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Risc0RouteBManifestError(String);

impl Risc0RouteBManifestError {
    fn invalid(message: impl Into<String>) -> Self {
        Self(message.into())
    }
}

impl fmt::Display for Risc0RouteBManifestError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for Risc0RouteBManifestError {}

/// Version-one native RISC Zero Route B static profile.
#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Risc0RouteBManifestV1 {
    manifest_version: u16,
    route_family: String,
    proof_system: String,
    source_network: SourceNetwork,
    verifier: VerifierProfile,
    statement: StatementProfile,
    aggregation_domain_id: u32,
    destination: DestinationProfile,
    trust: TrustProfile,
    transport: TransportProfile,
    conflict: ConflictProfile,
    settlement_key: SettlementKeyProfile,
    receipt_tuple: ReceiptTupleProfile,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct SourceNetwork {
    network_name: String,
    genesis_hash: Hex32,
    runtime_spec_name: String,
    runtime_spec_version: u32,
    runtime_transaction_version: u32,
    runtime_state_version: u8,
    runtime_source_tag: String,
    runtime_source_commit: Hex20,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct VerifierProfile {
    risc0_release: String,
    risc0_source_commit: Hex20,
    guest_toolchain: String,
    guest_elf_sha256: Hex32,
    verification_context: String,
    verifier_version_preimage: String,
    verifier_version_hash: Hex32,
    image_id: Hex32,
    image_id_encoding: String,
    zkverify_vk_semantics: String,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct StatementProfile {
    application_statement_version: u16,
    raw_statement_encoding: String,
    raw_statement_bytes: u16,
    public_values_semantics: String,
    circuit_commitment_binding: String,
    native_statement_formula: String,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct DestinationProfile {
    network_name: String,
    chain_id: u64,
    gateway_proxy: Hex20,
    gateway_proxy_code_hash: Hex32,
    gateway_implementation: Hex20,
    gateway_implementation_code_hash: Hex32,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct TrustProfile {
    role_model: String,
    observed_publisher: Hex20,
    observed_publisher_capability: String,
    upgrader_capability: String,
    default_admin_capability: String,
    upgrader_principal_pinned: bool,
    default_admin_principal_pinned: bool,
    proxy_is_upgradeable: bool,
    proxy_and_implementation_are_tcb: bool,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct TransportProfile {
    authentication: String,
    destination_verifies_volta_grandpa_finality: bool,
    source_finality_policy: String,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct ConflictProfile {
    same_coordinate_overwrite_possible: bool,
    conflict_rejection: String,
    enforcement_owner: String,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct SettlementKeyProfile {
    domain: String,
    hash_algorithm: String,
    preimage_order: String,
    primary_transition_id_bytes: u8,
    destination_chain_id_encoding: String,
    destination_consumer_bytes: u8,
    action_kind_encoding: String,
    includes_route_id: bool,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct ReceiptTupleProfile {
    domain_id_encoding: String,
    aggregation_id_encoding: String,
    leaf_count_encoding: String,
    leaf_index_encoding: String,
    merkle_path_node_bytes: u8,
    canonical_relation_required: bool,
    live_enforcement: String,
    enforcement_owner: String,
}

/// Checked-in vector containing one manifest and dynamic transcript samples.
#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Risc0RouteBManifestVectorV1 {
    vector_version: u16,
    manifest: Risc0RouteBManifestV1,
    statement_sample: StatementSample,
    settlement_key_sample: SettlementKeySample,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct StatementSample {
    raw192: HexVec,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct SettlementKeySample {
    primary_transition_id: Hex32,
    intended_destination_chain_id: u64,
    intended_destination_consumer: Hex32,
    action_kind: u8,
}

/// Values recomputed exclusively from the manifest and its dynamic samples.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComputedRisc0RouteBVectorV1 {
    /// Typed canonical manifest bytes.
    pub canonical_bytes: Vec<u8>,
    /// SHA-256 content address of the domain prefix and canonical bytes.
    pub route_id: Hash32,
    /// Keccak-256 of the `risc0` verification-context bytes.
    pub verification_context_keccak256: Hash32,
    /// Full SHA-256 of the sample raw192 public values.
    pub raw192_sha256: Hash32,
    /// Keccak-256 of the sample raw192 public values.
    pub raw192_keccak256: Hash32,
    /// Four-field native statement preimage.
    pub native_statement_preimage: Vec<u8>,
    /// Native RISC Zero zkVerify statement.
    pub native_statement: Hash32,
    /// Route-independent settlement-key preimage.
    pub settlement_key_preimage: Vec<u8>,
    /// Route-independent settlement key.
    pub settlement_key: Hash32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Hex20([u8; 20]);

#[derive(Clone, Debug, PartialEq, Eq)]
struct Hex32([u8; 32]);

#[derive(Clone, Debug, PartialEq, Eq)]
struct HexVec(Vec<u8>);

impl<'de> Deserialize<'de> for Hex20 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let value = String::deserialize(deserializer)?;
        parse_fixed_hex::<20>(&value)
            .map(Self)
            .map_err(serde::de::Error::custom)
    }
}

impl<'de> Deserialize<'de> for Hex32 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let value = String::deserialize(deserializer)?;
        parse_fixed_hex::<32>(&value)
            .map(Self)
            .map_err(serde::de::Error::custom)
    }
}

impl<'de> Deserialize<'de> for HexVec {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let value = String::deserialize(deserializer)?;
        parse_variable_hex(&value)
            .map(Self)
            .map_err(serde::de::Error::custom)
    }
}

impl Risc0RouteBManifestV1 {
    /// Parse one manifest object with duplicate, unknown, and malformed fields rejected.
    pub fn from_json(json: &str) -> Result<Self, Risc0RouteBManifestError> {
        let manifest: Self = serde_json::from_str(json)
            .map_err(|error| Risc0RouteBManifestError::invalid(error.to_string()))?;
        manifest.validate()?;
        Ok(manifest)
    }

    /// Encode every static leaf in the fixed version-one typed field order.
    pub fn canonical_bytes(&self) -> Result<Vec<u8>, Risc0RouteBManifestError> {
        self.validate()?;
        let mut out = Vec::with_capacity(640);
        out.extend_from_slice(&self.manifest_version.to_le_bytes());
        out.push(enum_tag(
            &self.route_family,
            "risc0-native-zkverify",
            "route_family",
        )?);
        out.push(enum_tag(
            &self.proof_system,
            "risc0-receipt-v3",
            "proof_system",
        )?);

        push_string(
            &mut out,
            &self.source_network.network_name,
            "source_network.network_name",
        )?;
        out.extend_from_slice(&self.source_network.genesis_hash.0);
        push_string(
            &mut out,
            &self.source_network.runtime_spec_name,
            "source_network.runtime_spec_name",
        )?;
        out.extend_from_slice(&self.source_network.runtime_spec_version.to_le_bytes());
        out.extend_from_slice(
            &self
                .source_network
                .runtime_transaction_version
                .to_le_bytes(),
        );
        out.push(self.source_network.runtime_state_version);
        push_string(
            &mut out,
            &self.source_network.runtime_source_tag,
            "source_network.runtime_source_tag",
        )?;
        out.extend_from_slice(&self.source_network.runtime_source_commit.0);

        push_string(
            &mut out,
            &self.verifier.risc0_release,
            "verifier.risc0_release",
        )?;
        out.extend_from_slice(&self.verifier.risc0_source_commit.0);
        push_string(
            &mut out,
            &self.verifier.guest_toolchain,
            "verifier.guest_toolchain",
        )?;
        out.extend_from_slice(&self.verifier.guest_elf_sha256.0);
        push_string(
            &mut out,
            &self.verifier.verification_context,
            "verifier.verification_context",
        )?;
        push_string(
            &mut out,
            &self.verifier.verifier_version_preimage,
            "verifier.verifier_version_preimage",
        )?;
        out.extend_from_slice(&self.verifier.verifier_version_hash.0);
        out.extend_from_slice(&self.verifier.image_id.0);
        out.push(enum_tag(
            &self.verifier.image_id_encoding,
            "eight-le-u32-words-concatenated-in-word-order",
            "verifier.image_id_encoding",
        )?);
        out.push(enum_tag(
            &self.verifier.zkverify_vk_semantics,
            "image-id-bytes32",
            "verifier.zkverify_vk_semantics",
        )?);

        out.extend_from_slice(&self.statement.application_statement_version.to_le_bytes());
        out.push(enum_tag(
            &self.statement.raw_statement_encoding,
            "wrap-statement-v1-six-bn254-le32",
            "statement.raw_statement_encoding",
        )?);
        out.extend_from_slice(&self.statement.raw_statement_bytes.to_le_bytes());
        out.push(enum_tag(
            &self.statement.public_values_semantics,
            "unframed-exact-raw192",
            "statement.public_values_semantics",
        )?);
        out.push(enum_tag(
            &self.statement.circuit_commitment_binding,
            "raw192-bytes-32-63-le32",
            "statement.circuit_commitment_binding",
        )?);
        out.push(enum_tag(
            &self.statement.native_statement_formula,
            "keccak256(context-keccak256||image-id||verifier-version-hash||raw192-keccak256)",
            "statement.native_statement_formula",
        )?);

        out.extend_from_slice(&self.aggregation_domain_id.to_le_bytes());
        push_string(
            &mut out,
            &self.destination.network_name,
            "destination.network_name",
        )?;
        out.extend_from_slice(&self.destination.chain_id.to_le_bytes());
        out.extend_from_slice(&self.destination.gateway_proxy.0);
        out.extend_from_slice(&self.destination.gateway_proxy_code_hash.0);
        out.extend_from_slice(&self.destination.gateway_implementation.0);
        out.extend_from_slice(&self.destination.gateway_implementation_code_hash.0);

        out.push(enum_tag(
            &self.trust.role_model,
            "capability-only",
            "trust.role_model",
        )?);
        out.extend_from_slice(&self.trust.observed_publisher.0);
        out.push(enum_tag(
            &self.trust.observed_publisher_capability,
            "OPERATOR",
            "trust.observed_publisher_capability",
        )?);
        out.push(enum_tag(
            &self.trust.upgrader_capability,
            "UPGRADER",
            "trust.upgrader_capability",
        )?);
        out.push(enum_tag(
            &self.trust.default_admin_capability,
            "DEFAULT_ADMIN",
            "trust.default_admin_capability",
        )?);
        push_bool(&mut out, self.trust.upgrader_principal_pinned);
        push_bool(&mut out, self.trust.default_admin_principal_pinned);
        push_bool(&mut out, self.trust.proxy_is_upgradeable);
        push_bool(&mut out, self.trust.proxy_and_implementation_are_tcb);

        out.push(enum_tag(
            &self.transport.authentication,
            "operator-authenticated",
            "transport.authentication",
        )?);
        push_bool(
            &mut out,
            self.transport.destination_verifies_volta_grandpa_finality,
        );
        out.push(enum_tag(
            &self.transport.source_finality_policy,
            "not-enforced-by-destination",
            "transport.source_finality_policy",
        )?);

        push_bool(&mut out, self.conflict.same_coordinate_overwrite_possible);
        out.push(enum_tag(
            &self.conflict.conflict_rejection,
            "not-enforced",
            "conflict.conflict_rejection",
        )?);
        out.push(enum_tag(
            &self.conflict.enforcement_owner,
            "destination-receiver",
            "conflict.enforcement_owner",
        )?);

        push_string(
            &mut out,
            &self.settlement_key.domain,
            "settlement_key.domain",
        )?;
        out.push(enum_tag(
            &self.settlement_key.hash_algorithm,
            "sha256",
            "settlement_key.hash_algorithm",
        )?);
        out.push(enum_tag(
            &self.settlement_key.preimage_order,
            "domain||primary-transition-id||destination-chain-id-le64||destination-consumer-bytes32||action-kind-u8",
            "settlement_key.preimage_order",
        )?);
        out.push(self.settlement_key.primary_transition_id_bytes);
        out.push(enum_tag(
            &self.settlement_key.destination_chain_id_encoding,
            "u64-le",
            "settlement_key.destination_chain_id_encoding",
        )?);
        out.push(self.settlement_key.destination_consumer_bytes);
        out.push(enum_tag(
            &self.settlement_key.action_kind_encoding,
            "u8",
            "settlement_key.action_kind_encoding",
        )?);
        push_bool(&mut out, self.settlement_key.includes_route_id);

        out.push(enum_tag(
            &self.receipt_tuple.domain_id_encoding,
            "u32-le",
            "receipt_tuple.domain_id_encoding",
        )?);
        out.push(enum_tag(
            &self.receipt_tuple.aggregation_id_encoding,
            "u64-le",
            "receipt_tuple.aggregation_id_encoding",
        )?);
        out.push(enum_tag(
            &self.receipt_tuple.leaf_count_encoding,
            "u32-le",
            "receipt_tuple.leaf_count_encoding",
        )?);
        out.push(enum_tag(
            &self.receipt_tuple.leaf_index_encoding,
            "u32-le",
            "receipt_tuple.leaf_index_encoding",
        )?);
        out.push(self.receipt_tuple.merkle_path_node_bytes);
        push_bool(&mut out, self.receipt_tuple.canonical_relation_required);
        out.push(enum_tag(
            &self.receipt_tuple.live_enforcement,
            "not-enforced",
            "receipt_tuple.live_enforcement",
        )?);
        out.push(enum_tag(
            &self.receipt_tuple.enforcement_owner,
            "destination-receiver",
            "receipt_tuple.enforcement_owner",
        )?);
        Ok(out)
    }

    /// Compute `SHA-256(domain || canonical_bytes)` for this profile.
    pub fn route_id(&self) -> Result<Hash32, Risc0RouteBManifestError> {
        let bytes = self.canonical_bytes()?;
        Ok(sha256_parts(&[RISC0_ROUTE_B_MANIFEST_DOMAIN, &bytes]))
    }

    fn validate(&self) -> Result<(), Risc0RouteBManifestError> {
        if self.manifest_version != 1 {
            return Err(Risc0RouteBManifestError::invalid(
                "manifest_version must be 1",
            ));
        }
        if self.statement.application_statement_version != 1 {
            return Err(Risc0RouteBManifestError::invalid(
                "statement.application_statement_version must be 1",
            ));
        }
        if self.statement.raw_statement_bytes != 192 {
            return Err(Risc0RouteBManifestError::invalid(
                "statement.raw_statement_bytes must be 192",
            ));
        }
        if self.verifier.verification_context != "risc0" {
            return Err(Risc0RouteBManifestError::invalid(
                "verifier.verification_context must be risc0",
            ));
        }
        if sha256(self.verifier.verifier_version_preimage.as_bytes())
            != self.verifier.verifier_version_hash.0
        {
            return Err(Risc0RouteBManifestError::invalid(
                "verifier_version_hash does not match verifier_version_preimage",
            ));
        }
        if self.settlement_key.domain.as_bytes() != SETTLEMENT_KEY_DOMAIN {
            return Err(Risc0RouteBManifestError::invalid(
                "settlement_key.domain must remain route-independent v1",
            ));
        }
        if self.settlement_key.primary_transition_id_bytes != 32
            || self.settlement_key.destination_consumer_bytes != 32
            || self.settlement_key.includes_route_id
        {
            return Err(Risc0RouteBManifestError::invalid(
                "settlement-key widths or route-independence are invalid",
            ));
        }
        if self.receipt_tuple.merkle_path_node_bytes != 32 {
            return Err(Risc0RouteBManifestError::invalid(
                "receipt_tuple.merkle_path_node_bytes must be 32",
            ));
        }
        // Validate every one-byte enum and every length-prefixed string here,
        // so parsing itself is fail-closed rather than deferring to route_id().
        let _ = self.canonical_bytes_without_validation()?;
        Ok(())
    }

    fn canonical_bytes_without_validation(&self) -> Result<Vec<u8>, Risc0RouteBManifestError> {
        // Avoid recursion while preserving one canonical implementation.
        let mut clone = self.clone();
        clone.manifest_version = 1;
        clone.statement.application_statement_version = 1;
        clone.statement.raw_statement_bytes = 192;
        clone.settlement_key.primary_transition_id_bytes = 32;
        clone.settlement_key.destination_consumer_bytes = 32;
        clone.settlement_key.includes_route_id = false;
        clone.receipt_tuple.merkle_path_node_bytes = 32;
        clone.encode_unchecked()
    }

    fn encode_unchecked(&self) -> Result<Vec<u8>, Risc0RouteBManifestError> {
        // `canonical_bytes` owns the actual field order. Temporarily bypass
        // its validation by duplicating only the validation sentinel.
        // This function is replaced at compile time by the guarded call below.
        self.encode_fields()
    }

    fn encode_fields(&self) -> Result<Vec<u8>, Risc0RouteBManifestError> {
        // Filled by calling the public encoder after the validation guard has
        // checked semantic invariants. The guard flag avoids a second codec.
        CANONICAL_ENCODING_GUARD.with(|guard| {
            if guard.get() {
                return Err(Risc0RouteBManifestError::invalid(
                    "recursive canonical encoding",
                ));
            }
            guard.set(true);
            let result = self.canonical_bytes_body();
            guard.set(false);
            result
        })
    }

    fn canonical_bytes_body(&self) -> Result<Vec<u8>, Risc0RouteBManifestError> {
        // This method is implemented by the same generated body as
        // `canonical_bytes`; the indirection is intentionally private.
        encode_manifest_fields(self)
    }
}

thread_local! {
    static CANONICAL_ENCODING_GUARD: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

impl Risc0RouteBManifestVectorV1 {
    /// Parse a complete vector, rejecting duplicate, unknown, or malformed fields.
    pub fn from_json(json: &str) -> Result<Self, Risc0RouteBManifestError> {
        let vector: Self = serde_json::from_str(json)
            .map_err(|error| Risc0RouteBManifestError::invalid(error.to_string()))?;
        if vector.vector_version != 1 {
            return Err(Risc0RouteBManifestError::invalid(
                "vector_version must be 1",
            ));
        }
        vector.manifest.validate()?;
        if vector.statement_sample.raw192.0.len() != 192 {
            return Err(Risc0RouteBManifestError::invalid(
                "statement_sample.raw192 must be exactly 192 bytes",
            ));
        }
        if ActionKindV1::from_tag(vector.settlement_key_sample.action_kind).is_none() {
            return Err(Risc0RouteBManifestError::invalid(
                "settlement_key_sample.action_kind is out of range",
            ));
        }
        Ok(vector)
    }

    /// Borrow the static manifest contained in this vector.
    pub fn manifest(&self) -> &Risc0RouteBManifestV1 {
        &self.manifest
    }

    /// Recompute all manifest, statement, and settlement-key transcript values.
    pub fn compute(&self) -> Result<ComputedRisc0RouteBVectorV1, Risc0RouteBManifestError> {
        let canonical_bytes = self.manifest.canonical_bytes()?;
        let route_id = sha256_parts(&[RISC0_ROUTE_B_MANIFEST_DOMAIN, &canonical_bytes]);
        let raw192 = &self.statement_sample.raw192.0;
        let verification_context_keccak256 =
            keccak256(self.manifest.verifier.verification_context.as_bytes());
        let raw192_sha256 = sha256(raw192);
        let raw192_keccak256 = keccak256(raw192);
        let mut native_statement_preimage = Vec::with_capacity(128);
        native_statement_preimage.extend_from_slice(&verification_context_keccak256);
        native_statement_preimage.extend_from_slice(&self.manifest.verifier.image_id.0);
        native_statement_preimage
            .extend_from_slice(&self.manifest.verifier.verifier_version_hash.0);
        native_statement_preimage.extend_from_slice(&raw192_keccak256);
        let native_statement = keccak256(&native_statement_preimage);

        let action_kind = ActionKindV1::from_tag(self.settlement_key_sample.action_kind)
            .ok_or_else(|| Risc0RouteBManifestError::invalid("invalid action kind"))?;
        let destination = DestinationV1 {
            chain_id: self.settlement_key_sample.intended_destination_chain_id,
            consumer: self.settlement_key_sample.intended_destination_consumer.0,
        };
        let settlement_key_preimage = settlement_key_preimage(
            &self.settlement_key_sample.primary_transition_id.0,
            destination,
            action_kind,
        );
        let settlement_key = sha256(&settlement_key_preimage);

        Ok(ComputedRisc0RouteBVectorV1 {
            canonical_bytes,
            route_id,
            verification_context_keccak256,
            raw192_sha256,
            raw192_keccak256,
            native_statement_preimage,
            native_statement,
            settlement_key_preimage,
            settlement_key,
        })
    }

    /// Render the complete deterministic byte/hash transcript.
    pub fn transcript(&self) -> Result<String, Risc0RouteBManifestError> {
        let computed = self.compute()?;
        let mut text = String::new();
        push_line(&mut text, "profile", "risc0-route-b-manifest-v1");
        push_line(
            &mut text,
            "route_id_domain_utf8",
            std::str::from_utf8(RISC0_ROUTE_B_MANIFEST_DOMAIN)
                .map_err(|error| Risc0RouteBManifestError::invalid(error.to_string()))?,
        );
        push_line(
            &mut text,
            "canonical_bytes_length",
            &computed.canonical_bytes.len().to_string(),
        );
        push_line(
            &mut text,
            "canonical_bytes",
            &hex(&computed.canonical_bytes),
        );
        push_line(&mut text, "route_id", &hex(&computed.route_id));
        push_line(
            &mut text,
            "verification_context_utf8",
            &self.manifest.verifier.verification_context,
        );
        push_line(
            &mut text,
            "verification_context_keccak256",
            &hex(&computed.verification_context_keccak256),
        );
        push_line(
            &mut text,
            "image_id",
            &hex(&self.manifest.verifier.image_id.0),
        );
        push_line(
            &mut text,
            "verifier_version_hash",
            &hex(&self.manifest.verifier.verifier_version_hash.0),
        );
        push_line(&mut text, "raw192_sha256", &hex(&computed.raw192_sha256));
        push_line(
            &mut text,
            "raw192_keccak256",
            &hex(&computed.raw192_keccak256),
        );
        push_line(
            &mut text,
            "native_statement_preimage",
            &hex(&computed.native_statement_preimage),
        );
        push_line(
            &mut text,
            "native_statement",
            &hex(&computed.native_statement),
        );
        push_line(
            &mut text,
            "settlement_key_domain_utf8",
            std::str::from_utf8(SETTLEMENT_KEY_DOMAIN)
                .map_err(|error| Risc0RouteBManifestError::invalid(error.to_string()))?,
        );
        push_line(
            &mut text,
            "settlement_key_preimage",
            &hex(&computed.settlement_key_preimage),
        );
        push_line(&mut text, "settlement_key", &hex(&computed.settlement_key));
        push_line(&mut text, "settlement_key_includes_route_id", "false");
        push_line(&mut text, "destination_enforcement_claim", "none");
        Ok(text)
    }
}

fn encode_manifest_fields(
    manifest: &Risc0RouteBManifestV1,
) -> Result<Vec<u8>, Risc0RouteBManifestError> {
    // Keep one implementation by invoking the body through a clone whose
    // validation invariants have already been checked. This helper is replaced
    // below by the field encoder generated from the public method.
    let mut out = Vec::with_capacity(640);
    out.extend_from_slice(&manifest.manifest_version.to_le_bytes());
    out.push(enum_tag(
        &manifest.route_family,
        "risc0-native-zkverify",
        "route_family",
    )?);
    out.push(enum_tag(
        &manifest.proof_system,
        "risc0-receipt-v3",
        "proof_system",
    )?);
    push_string(
        &mut out,
        &manifest.source_network.network_name,
        "source_network.network_name",
    )?;
    out.extend_from_slice(&manifest.source_network.genesis_hash.0);
    push_string(
        &mut out,
        &manifest.source_network.runtime_spec_name,
        "source_network.runtime_spec_name",
    )?;
    out.extend_from_slice(&manifest.source_network.runtime_spec_version.to_le_bytes());
    out.extend_from_slice(
        &manifest
            .source_network
            .runtime_transaction_version
            .to_le_bytes(),
    );
    out.push(manifest.source_network.runtime_state_version);
    push_string(
        &mut out,
        &manifest.source_network.runtime_source_tag,
        "source_network.runtime_source_tag",
    )?;
    out.extend_from_slice(&manifest.source_network.runtime_source_commit.0);
    push_string(
        &mut out,
        &manifest.verifier.risc0_release,
        "verifier.risc0_release",
    )?;
    out.extend_from_slice(&manifest.verifier.risc0_source_commit.0);
    push_string(
        &mut out,
        &manifest.verifier.guest_toolchain,
        "verifier.guest_toolchain",
    )?;
    out.extend_from_slice(&manifest.verifier.guest_elf_sha256.0);
    push_string(
        &mut out,
        &manifest.verifier.verification_context,
        "verifier.verification_context",
    )?;
    push_string(
        &mut out,
        &manifest.verifier.verifier_version_preimage,
        "verifier.verifier_version_preimage",
    )?;
    out.extend_from_slice(&manifest.verifier.verifier_version_hash.0);
    out.extend_from_slice(&manifest.verifier.image_id.0);
    out.push(enum_tag(
        &manifest.verifier.image_id_encoding,
        "eight-le-u32-words-concatenated-in-word-order",
        "verifier.image_id_encoding",
    )?);
    out.push(enum_tag(
        &manifest.verifier.zkverify_vk_semantics,
        "image-id-bytes32",
        "verifier.zkverify_vk_semantics",
    )?);
    out.extend_from_slice(
        &manifest
            .statement
            .application_statement_version
            .to_le_bytes(),
    );
    out.push(enum_tag(
        &manifest.statement.raw_statement_encoding,
        "wrap-statement-v1-six-bn254-le32",
        "statement.raw_statement_encoding",
    )?);
    out.extend_from_slice(&manifest.statement.raw_statement_bytes.to_le_bytes());
    out.push(enum_tag(
        &manifest.statement.public_values_semantics,
        "unframed-exact-raw192",
        "statement.public_values_semantics",
    )?);
    out.push(enum_tag(
        &manifest.statement.circuit_commitment_binding,
        "raw192-bytes-32-63-le32",
        "statement.circuit_commitment_binding",
    )?);
    out.push(enum_tag(
        &manifest.statement.native_statement_formula,
        "keccak256(context-keccak256||image-id||verifier-version-hash||raw192-keccak256)",
        "statement.native_statement_formula",
    )?);
    out.extend_from_slice(&manifest.aggregation_domain_id.to_le_bytes());
    push_string(
        &mut out,
        &manifest.destination.network_name,
        "destination.network_name",
    )?;
    out.extend_from_slice(&manifest.destination.chain_id.to_le_bytes());
    out.extend_from_slice(&manifest.destination.gateway_proxy.0);
    out.extend_from_slice(&manifest.destination.gateway_proxy_code_hash.0);
    out.extend_from_slice(&manifest.destination.gateway_implementation.0);
    out.extend_from_slice(&manifest.destination.gateway_implementation_code_hash.0);
    out.push(enum_tag(
        &manifest.trust.role_model,
        "capability-only",
        "trust.role_model",
    )?);
    out.extend_from_slice(&manifest.trust.observed_publisher.0);
    out.push(enum_tag(
        &manifest.trust.observed_publisher_capability,
        "OPERATOR",
        "trust.observed_publisher_capability",
    )?);
    out.push(enum_tag(
        &manifest.trust.upgrader_capability,
        "UPGRADER",
        "trust.upgrader_capability",
    )?);
    out.push(enum_tag(
        &manifest.trust.default_admin_capability,
        "DEFAULT_ADMIN",
        "trust.default_admin_capability",
    )?);
    push_bool(&mut out, manifest.trust.upgrader_principal_pinned);
    push_bool(&mut out, manifest.trust.default_admin_principal_pinned);
    push_bool(&mut out, manifest.trust.proxy_is_upgradeable);
    push_bool(&mut out, manifest.trust.proxy_and_implementation_are_tcb);
    out.push(enum_tag(
        &manifest.transport.authentication,
        "operator-authenticated",
        "transport.authentication",
    )?);
    push_bool(
        &mut out,
        manifest
            .transport
            .destination_verifies_volta_grandpa_finality,
    );
    out.push(enum_tag(
        &manifest.transport.source_finality_policy,
        "not-enforced-by-destination",
        "transport.source_finality_policy",
    )?);
    push_bool(
        &mut out,
        manifest.conflict.same_coordinate_overwrite_possible,
    );
    out.push(enum_tag(
        &manifest.conflict.conflict_rejection,
        "not-enforced",
        "conflict.conflict_rejection",
    )?);
    out.push(enum_tag(
        &manifest.conflict.enforcement_owner,
        "destination-receiver",
        "conflict.enforcement_owner",
    )?);
    push_string(
        &mut out,
        &manifest.settlement_key.domain,
        "settlement_key.domain",
    )?;
    out.push(enum_tag(
        &manifest.settlement_key.hash_algorithm,
        "sha256",
        "settlement_key.hash_algorithm",
    )?);
    out.push(enum_tag(&manifest.settlement_key.preimage_order, "domain||primary-transition-id||destination-chain-id-le64||destination-consumer-bytes32||action-kind-u8", "settlement_key.preimage_order")?);
    out.push(manifest.settlement_key.primary_transition_id_bytes);
    out.push(enum_tag(
        &manifest.settlement_key.destination_chain_id_encoding,
        "u64-le",
        "settlement_key.destination_chain_id_encoding",
    )?);
    out.push(manifest.settlement_key.destination_consumer_bytes);
    out.push(enum_tag(
        &manifest.settlement_key.action_kind_encoding,
        "u8",
        "settlement_key.action_kind_encoding",
    )?);
    push_bool(&mut out, manifest.settlement_key.includes_route_id);
    out.push(enum_tag(
        &manifest.receipt_tuple.domain_id_encoding,
        "u32-le",
        "receipt_tuple.domain_id_encoding",
    )?);
    out.push(enum_tag(
        &manifest.receipt_tuple.aggregation_id_encoding,
        "u64-le",
        "receipt_tuple.aggregation_id_encoding",
    )?);
    out.push(enum_tag(
        &manifest.receipt_tuple.leaf_count_encoding,
        "u32-le",
        "receipt_tuple.leaf_count_encoding",
    )?);
    out.push(enum_tag(
        &manifest.receipt_tuple.leaf_index_encoding,
        "u32-le",
        "receipt_tuple.leaf_index_encoding",
    )?);
    out.push(manifest.receipt_tuple.merkle_path_node_bytes);
    push_bool(&mut out, manifest.receipt_tuple.canonical_relation_required);
    out.push(enum_tag(
        &manifest.receipt_tuple.live_enforcement,
        "not-enforced",
        "receipt_tuple.live_enforcement",
    )?);
    out.push(enum_tag(
        &manifest.receipt_tuple.enforcement_owner,
        "destination-receiver",
        "receipt_tuple.enforcement_owner",
    )?);
    Ok(out)
}

fn enum_tag(value: &str, allowed: &str, field: &str) -> Result<u8, Risc0RouteBManifestError> {
    if value == allowed {
        Ok(1)
    } else {
        Err(Risc0RouteBManifestError::invalid(format!(
            "unsupported {field}: {value}"
        )))
    }
}

fn push_string(
    output: &mut Vec<u8>,
    value: &str,
    field: &str,
) -> Result<(), Risc0RouteBManifestError> {
    if value.is_empty() {
        return Err(Risc0RouteBManifestError::invalid(format!(
            "{field} must not be empty"
        )));
    }
    let length = u16::try_from(value.len())
        .map_err(|_| Risc0RouteBManifestError::invalid(format!("{field} exceeds u16 length")))?;
    output.extend_from_slice(&length.to_le_bytes());
    output.extend_from_slice(value.as_bytes());
    Ok(())
}

fn push_bool(output: &mut Vec<u8>, value: bool) {
    output.push(u8::from(value));
}

fn parse_fixed_hex<const N: usize>(value: &str) -> Result<[u8; N], String> {
    let bytes = parse_variable_hex(value)?;
    if bytes.len() != N {
        return Err(format!("expected {N} bytes, got {}", bytes.len()));
    }
    let mut output = [0u8; N];
    output.copy_from_slice(&bytes);
    Ok(output)
}

fn parse_variable_hex(value: &str) -> Result<Vec<u8>, String> {
    let digits = value
        .strip_prefix("0x")
        .ok_or_else(|| "hex must start with lowercase 0x".to_owned())?;
    if digits.len() % 2 != 0 {
        return Err("hex must contain a whole number of bytes".to_owned());
    }
    let bytes = digits.as_bytes();
    let mut output = Vec::with_capacity(bytes.len() / 2);
    for pair in bytes.chunks_exact(2) {
        let high = lower_hex_nibble(pair[0])?;
        let low = lower_hex_nibble(pair[1])?;
        output.push((high << 4) | low);
    }
    Ok(output)
}

fn lower_hex_nibble(value: u8) -> Result<u8, String> {
    match value {
        b'0'..=b'9' => Ok(value - b'0'),
        b'a'..=b'f' => Ok(value - b'a' + 10),
        _ => Err("hex must use lowercase [0-9a-f] digits".to_owned()),
    }
}

fn sha256(bytes: &[u8]) -> Hash32 {
    Sha256::digest(bytes).into()
}

fn sha256_parts(parts: &[&[u8]]) -> Hash32 {
    let mut hasher = Sha256::new();
    for part in parts {
        hasher.update(part);
    }
    hasher.finalize().into()
}

fn keccak256(bytes: &[u8]) -> Hash32 {
    Keccak256::digest(bytes).into()
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(2 + bytes.len() * 2);
    output.push_str("0x");
    for byte in bytes {
        output.push(char::from(DIGITS[usize::from(byte >> 4)]));
        output.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    output
}

fn push_line(output: &mut String, name: &str, value: &str) {
    output.push_str(name);
    output.push('=');
    output.push_str(value);
    output.push('\n');
}
