//! Deterministic destination receipt-root authority and registry oracle.
//!
//! This module fixes the bytes signed by an approved receipt-root quorum and
//! the state-transition rules a destination implementation must reproduce. It
//! recovers the frozen ECDSA fixtures with EVM-compatible rules but does not
//! read a live chain or claim to be a deployed contract. A deployed EVM
//! implementation must reproduce the same recovery and state-machine results.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use k256::ecdsa::{RecoveryId, Signature, VerifyingKey};
use serde::Deserialize;
use sha3::{Digest as _, Keccak256};

use crate::settlement::{
    ActionKindV1, CanonicalRawStatement, DestinationV1, Hash32, PrimaryFinalityRecordV1,
    PrimaryRecordState, ReceiptEvidenceV1, RouteProofIdentityV1, WrapSettlementClaimV1,
    preclaim_hash, settlement_key,
};
use crate::statement::Bn254Fr;

/// Domain tag for receipt-root quorum authorization digests.
///
/// This is intentionally distinct from the primary-finality-record domain.
pub const RECEIPT_ROOT_QUORUM_DOMAIN: &[u8] = b"SSGKR_RECEIPT_ROOT_QUORUM_V1";
/// Domain tag for destination registry coordinate identifiers.
pub const RECEIPT_ROOT_COORDINATE_DOMAIN: &[u8] = b"SSGKR_RECEIPT_ROOT_COORDINATE_V1";
/// Domain tag for the source-network content identity.
pub const SOURCE_NETWORK_DOMAIN: &[u8] = b"SSGKR_SOURCE_NETWORK_V1";
/// Domain tag for the source-runtime content identity.
pub const SOURCE_RUNTIME_DOMAIN: &[u8] = b"SSGKR_SOURCE_RUNTIME_V1";
/// Cross-language hash function fixed by this reference profile.
pub const RECEIPT_ROOT_HASH_ALGORITHM: &str = "keccak256";
/// Cross-language integer encoding fixed by this reference profile.
pub const RECEIPT_ROOT_INTEGER_ENCODING: &str = "fixed-width-big-endian";
/// First authorization nonce accepted by a fresh registry.
pub const INITIAL_AUTHORIZATION_NONCE: u64 = 1;
/// Exact byte length of [`ReceiptRootAuthorizationV1::canonical_preimage`].
pub const AUTHORIZATION_PREIMAGE_BYTES: usize = 260;
const ROOT_REGISTRY_STATE_DOMAIN: &[u8] = b"SSGKR_RECEIPT_ROOT_STATE_V1";
const REPLAY_REGISTRY_STATE_DOMAIN: &[u8] = b"SSGKR_DESTINATION_REPLAY_STATE_V1";
const SYSTEM_STATE_DOMAIN: &[u8] = b"SSGKR_DESTINATION_SYSTEM_STATE_V1";

/// EVM-compatible recovered signer identity.
pub type SignerIdentity = [u8; 20];

/// Recover an EVM address from a direct 32-byte digest and compact `r||s||v`.
pub fn recover_evm_signer(
    digest: &Hash32,
    compact_signature: &[u8; 65],
) -> Result<SignerIdentity, ReceiptRootPolicyError> {
    let signature = Signature::from_slice(&compact_signature[..64])
        .map_err(|_| ReceiptRootPolicyError::InvalidSignature)?;
    if signature.normalize_s().is_some() {
        return Err(ReceiptRootPolicyError::HighSignatureS);
    }
    if !matches!(compact_signature[64], 27 | 28) {
        return Err(ReceiptRootPolicyError::InvalidRecoveryId);
    }
    let recovery_byte = compact_signature[64] - 27;
    let recovery_id = RecoveryId::try_from(recovery_byte)
        .map_err(|_| ReceiptRootPolicyError::InvalidRecoveryId)?;
    let verifying_key = VerifyingKey::recover_from_prehash(digest, &signature, recovery_id)
        .map_err(|_| ReceiptRootPolicyError::SignatureRecoveryFailed)?;
    let encoded = verifying_key.to_encoded_point(false);
    let encoded_bytes = encoded.as_bytes();
    let hashed_key = keccak256(&encoded_bytes[1..]);
    let mut signer = [0u8; 20];
    signer.copy_from_slice(&hashed_key[12..]);
    if signer == [0u8; 20] {
        return Err(ReceiptRootPolicyError::ZeroAttester);
    }
    Ok(signer)
}

/// Hash the published statement into the native one-leaf receipt root.
pub fn one_leaf_receipt_root(statement: &Hash32) -> Hash32 {
    keccak256(statement)
}

/// Derive the source-network identity from its name and genesis hash.
pub fn source_network_id(network_name: &str, genesis_hash: &Hash32) -> Hash32 {
    let mut bytes = Vec::with_capacity(SOURCE_NETWORK_DOMAIN.len() + network_name.len() + 32);
    bytes.extend_from_slice(SOURCE_NETWORK_DOMAIN);
    bytes.extend_from_slice(network_name.as_bytes());
    bytes.extend_from_slice(genesis_hash);
    keccak256(&bytes)
}

/// Derive the runtime identity from exact version fields and live code hash.
pub fn source_runtime_id(
    spec_name: &str,
    spec_version: u32,
    transaction_version: u32,
    state_version: u8,
    runtime_code_hash: &Hash32,
) -> Result<Hash32, String> {
    let name_length = u16::try_from(spec_name.len())
        .map_err(|_| "runtime spec name exceeds u16 bytes".to_owned())?;
    let mut bytes = Vec::with_capacity(SOURCE_RUNTIME_DOMAIN.len() + spec_name.len() + 43);
    bytes.extend_from_slice(SOURCE_RUNTIME_DOMAIN);
    bytes.extend_from_slice(&name_length.to_be_bytes());
    bytes.extend_from_slice(spec_name.as_bytes());
    bytes.extend_from_slice(&spec_version.to_be_bytes());
    bytes.extend_from_slice(&transaction_version.to_be_bytes());
    bytes.push(state_version);
    bytes.extend_from_slice(runtime_code_hash);
    Ok(keccak256(&bytes))
}

/// Exact receipt-root authorization signed by the configured authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReceiptRootAuthorizationV1 {
    /// Configured signer-set epoch.
    pub signer_set_epoch: u64,
    /// Content identity for the source network.
    pub source_network_id: Hash32,
    /// Exact source genesis hash.
    pub source_genesis_hash: Hash32,
    /// Pinned runtime version or code identity.
    pub source_runtime_id: Hash32,
    /// Pinned verifier-context hash.
    pub verification_context_hash: Hash32,
    /// Aggregation domain.
    pub domain_id: u32,
    /// Source block number containing the aggregation publication.
    pub source_block_number: u64,
    /// Exact source block hash.
    pub source_block_hash: Hash32,
    /// Aggregation identifier within the domain.
    pub aggregation_id: u64,
    /// Published aggregation root.
    pub root: Hash32,
    /// Canonical number of leaves committed by the root.
    pub leaf_count: u32,
    /// Strictly increasing authorization sequence for new coordinates.
    pub authorization_nonce: u64,
}

impl ReceiptRootAuthorizationV1 {
    /// Return the fixed-width signing preimage.
    ///
    /// Integers are unsigned, fixed width, and big endian so an EVM adapter can
    /// reproduce the bytes without ABI dynamic-value ambiguity.
    pub fn canonical_preimage(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(AUTHORIZATION_PREIMAGE_BYTES);
        bytes.extend_from_slice(RECEIPT_ROOT_QUORUM_DOMAIN);
        bytes.extend_from_slice(&self.signer_set_epoch.to_be_bytes());
        bytes.extend_from_slice(&self.source_network_id);
        bytes.extend_from_slice(&self.source_genesis_hash);
        bytes.extend_from_slice(&self.source_runtime_id);
        bytes.extend_from_slice(&self.verification_context_hash);
        bytes.extend_from_slice(&self.domain_id.to_be_bytes());
        bytes.extend_from_slice(&self.source_block_number.to_be_bytes());
        bytes.extend_from_slice(&self.source_block_hash);
        bytes.extend_from_slice(&self.aggregation_id.to_be_bytes());
        bytes.extend_from_slice(&self.root);
        bytes.extend_from_slice(&self.leaf_count.to_be_bytes());
        bytes.extend_from_slice(&self.authorization_nonce.to_be_bytes());
        debug_assert_eq!(bytes.len(), AUTHORIZATION_PREIMAGE_BYTES);
        bytes
    }

    /// Return `keccak256(canonical_preimage)` for EVM signature recovery.
    pub fn signing_digest(&self) -> Hash32 {
        keccak256(&self.canonical_preimage())
    }

    /// Return the non-overwrite registry coordinate.
    pub fn coordinate(&self) -> ReceiptRootCoordinateV1 {
        ReceiptRootCoordinateV1 {
            source_network_id: self.source_network_id,
            domain_id: self.domain_id,
            aggregation_id: self.aggregation_id,
        }
    }
}

/// Coordinate at which exactly one root and leaf count may be registered.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ReceiptRootCoordinateV1 {
    /// Content identity for the source network.
    pub source_network_id: Hash32,
    /// Aggregation domain.
    pub domain_id: u32,
    /// Aggregation identifier within the domain.
    pub aggregation_id: u64,
}

impl ReceiptRootCoordinateV1 {
    /// Return a domain-separated coordinate identifier.
    pub fn coordinate_id(&self) -> Hash32 {
        let mut bytes = Vec::with_capacity(RECEIPT_ROOT_COORDINATE_DOMAIN.len() + 44);
        bytes.extend_from_slice(RECEIPT_ROOT_COORDINATE_DOMAIN);
        bytes.extend_from_slice(&self.source_network_id);
        bytes.extend_from_slice(&self.domain_id.to_be_bytes());
        bytes.extend_from_slice(&self.aggregation_id.to_be_bytes());
        keccak256(&bytes)
    }
}

/// Sorted signer-set policy for one source/runtime/context/domain profile.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiptRootAuthorityPolicyV1 {
    /// Exact active signer-set epoch.
    pub signer_set_epoch: u64,
    /// Strictly ascending configured signer identities.
    pub configured_signers: Vec<SignerIdentity>,
    /// Minimum distinct configured signers required.
    pub threshold: u16,
    /// Content identity for the source network.
    pub source_network_id: Hash32,
    /// Exact source genesis hash.
    pub source_genesis_hash: Hash32,
    /// Pinned runtime version or code identity.
    pub source_runtime_id: Hash32,
    /// Pinned verifier-context hash.
    pub verification_context_hash: Hash32,
    /// Exact aggregation domain.
    pub domain_id: u32,
}

impl ReceiptRootAuthorityPolicyV1 {
    fn validate(&self) -> Result<(), ReceiptRootPolicyError> {
        if self.threshold == 0 || usize::from(self.threshold) > self.configured_signers.len() {
            return Err(ReceiptRootPolicyError::InvalidThreshold);
        }
        if self.configured_signers.contains(&[0u8; 20]) {
            return Err(ReceiptRootPolicyError::ZeroConfiguredSigner);
        }
        for pair in self.configured_signers.windows(2) {
            if pair[0] == pair[1] {
                return Err(ReceiptRootPolicyError::DuplicateConfiguredSigner);
            }
            if pair[0] > pair[1] {
                return Err(ReceiptRootPolicyError::ConfiguredSignersNotSorted);
            }
        }
        Ok(())
    }

    fn validate_attesters(
        &self,
        attesting_signers: &[SignerIdentity],
    ) -> Result<(), ReceiptRootPolicyError> {
        self.validate()?;
        if attesting_signers.contains(&[0u8; 20]) {
            return Err(ReceiptRootPolicyError::ZeroAttester);
        }
        for pair in attesting_signers.windows(2) {
            if pair[0] == pair[1] {
                return Err(ReceiptRootPolicyError::DuplicateAttester);
            }
            if pair[0] > pair[1] {
                return Err(ReceiptRootPolicyError::AttestersNotSorted);
            }
        }
        if attesting_signers
            .iter()
            .any(|signer| self.configured_signers.binary_search(signer).is_err())
        {
            return Err(ReceiptRootPolicyError::UnauthorizedAttester);
        }
        if attesting_signers.len() < usize::from(self.threshold) {
            return Err(ReceiptRootPolicyError::BelowThreshold);
        }
        Ok(())
    }

    fn validate_new_authorization(
        &self,
        authorization: &ReceiptRootAuthorizationV1,
    ) -> Result<(), ReceiptRootPolicyError> {
        if authorization.signer_set_epoch != self.signer_set_epoch {
            return Err(ReceiptRootPolicyError::StaleSignerSetEpoch);
        }
        if authorization.source_network_id != self.source_network_id
            || authorization.source_genesis_hash != self.source_genesis_hash
            || authorization.source_runtime_id != self.source_runtime_id
            || authorization.verification_context_hash != self.verification_context_hash
            || authorization.domain_id != self.domain_id
        {
            return Err(ReceiptRootPolicyError::AuthorityContextMismatch);
        }
        if authorization.leaf_count != 1 {
            return Err(ReceiptRootPolicyError::InvalidLeafCount);
        }
        Ok(())
    }
}

/// Immutable registry value for one accepted coordinate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegisteredReceiptRootV1 {
    /// Exact signed authorization. Any changed signed field conflicts.
    pub authorization: ReceiptRootAuthorizationV1,
    /// Signing digest retained for audit and exact retry comparison.
    pub signing_digest: Hash32,
    /// Sorted distinct signer identities that satisfied the quorum.
    pub attesting_signers: Vec<SignerIdentity>,
}

/// Result of a successful non-overwriting registration attempt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RootRegistrationOutcome {
    /// A previously empty coordinate was populated.
    Registered,
}

/// Fail-closed errors produced by the semantic authority oracle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReceiptRootPolicyError {
    /// Threshold is zero or exceeds the configured signer count.
    InvalidThreshold,
    /// A zero configured address could alias failed EVM recovery.
    ZeroConfiguredSigner,
    /// Configured signers are not strictly ascending.
    ConfiguredSignersNotSorted,
    /// The configured signer list repeats an identity.
    DuplicateConfiguredSigner,
    /// Signature bytes are not a valid secp256k1 `(r,s)` pair.
    InvalidSignature,
    /// Signature `s` is not in the canonical lower half of the curve order.
    HighSignatureS,
    /// Compact recovery byte is not EVM `27` or `28`.
    InvalidRecoveryId,
    /// The compact signature cannot recover a secp256k1 public key.
    SignatureRecoveryFailed,
    /// The authorization uses a signer-set epoch other than the active one.
    StaleSignerSetEpoch,
    /// Source, genesis, runtime, context, or domain differs from policy.
    AuthorityContextMismatch,
    /// This safe profile accepts exactly one leaf.
    InvalidLeafCount,
    /// A recovered zero address is invalid and normally means EVM recovery failed.
    ZeroAttester,
    /// Recovered signer identities are not strictly ascending.
    AttestersNotSorted,
    /// A recovered signer identity is repeated.
    DuplicateAttester,
    /// A recovered signer is not in the configured set.
    UnauthorizedAttester,
    /// Fewer distinct configured identities attested than required.
    BelowThreshold,
    /// A new coordinate did not use the exact next authorization nonce.
    UnexpectedAuthorizationNonce,
    /// The exact signed authorization was already registered.
    AuthorizationReplay,
    /// The coordinate already holds different signed metadata.
    RootConflict,
    /// A state or event-equivalent counter cannot be incremented safely.
    ArithmeticOverflow,
}

impl fmt::Display for ReceiptRootPolicyError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for ReceiptRootPolicyError {}

/// Stateful reference authority and non-overwriting coordinate registry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceReceiptRootRegistry {
    policy: ReceiptRootAuthorityPolicyV1,
    roots: BTreeMap<ReceiptRootCoordinateV1, RegisteredReceiptRootV1>,
    next_authorization_nonce: u64,
    accepted_transition_count: u64,
    emitted_events: Vec<RootRegistrationEventV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RootRegistrationEventV1 {
    coordinate: ReceiptRootCoordinateV1,
    signing_digest: Hash32,
    attesting_signers: Vec<SignerIdentity>,
}

impl ReferenceReceiptRootRegistry {
    /// Construct an empty registry after validating signer ordering/threshold.
    pub fn new(policy: ReceiptRootAuthorityPolicyV1) -> Result<Self, ReceiptRootPolicyError> {
        policy.validate()?;
        Ok(Self {
            policy,
            roots: BTreeMap::new(),
            next_authorization_nonce: INITIAL_AUTHORIZATION_NONCE,
            accepted_transition_count: 0,
            emitted_events: Vec::new(),
        })
    }

    /// Validate recovered signer identities and register without overwriting.
    ///
    /// ECDSA recovery is intentionally outside this function. The destination
    /// contract must recover identities over [`ReceiptRootAuthorizationV1::signing_digest`]
    /// and pass the strictly sorted result here.
    pub fn register(
        &mut self,
        authorization: ReceiptRootAuthorizationV1,
        attesting_signers: &[SignerIdentity],
    ) -> Result<RootRegistrationOutcome, ReceiptRootPolicyError> {
        self.policy.validate_attesters(attesting_signers)?;
        let coordinate = authorization.coordinate();
        if let Some(existing) = self.roots.get(&coordinate) {
            if existing.authorization == authorization {
                return Err(ReceiptRootPolicyError::AuthorizationReplay);
            }
            return Err(ReceiptRootPolicyError::RootConflict);
        }
        self.policy.validate_new_authorization(&authorization)?;
        if authorization.authorization_nonce != self.next_authorization_nonce {
            return Err(ReceiptRootPolicyError::UnexpectedAuthorizationNonce);
        }
        let next_authorization_nonce = self
            .next_authorization_nonce
            .checked_add(1)
            .ok_or(ReceiptRootPolicyError::ArithmeticOverflow)?;
        let next_transition_count = self
            .accepted_transition_count
            .checked_add(1)
            .ok_or(ReceiptRootPolicyError::ArithmeticOverflow)?;
        let event = RootRegistrationEventV1 {
            coordinate,
            signing_digest: authorization.signing_digest(),
            attesting_signers: attesting_signers.to_vec(),
        };
        self.roots.insert(
            coordinate,
            RegisteredReceiptRootV1 {
                authorization,
                signing_digest: authorization.signing_digest(),
                attesting_signers: attesting_signers.to_vec(),
            },
        );
        self.next_authorization_nonce = next_authorization_nonce;
        self.accepted_transition_count = next_transition_count;
        self.emitted_events.push(event);
        Ok(RootRegistrationOutcome::Registered)
    }

    /// Recover compact direct-digest signatures and register their identities.
    pub fn register_signatures(
        &mut self,
        authorization: ReceiptRootAuthorizationV1,
        compact_signatures: &[[u8; 65]],
    ) -> Result<RootRegistrationOutcome, ReceiptRootPolicyError> {
        let digest = authorization.signing_digest();
        let attesters = compact_signatures
            .iter()
            .map(|signature| recover_evm_signer(&digest, signature))
            .collect::<Result<Vec<_>, _>>()?;
        self.register(authorization, &attesters)
    }

    /// Number of occupied coordinates.
    pub fn len(&self) -> usize {
        self.roots.len()
    }

    /// Whether the registry contains no coordinates.
    pub fn is_empty(&self) -> bool {
        self.roots.is_empty()
    }

    /// Exact nonce required for the next new coordinate.
    pub fn next_authorization_nonce(&self) -> u64 {
        self.next_authorization_nonce
    }

    /// Count of successful registry transitions, used as an event-equivalent oracle.
    pub fn accepted_transition_count(&self) -> u64 {
        self.accepted_transition_count
    }

    /// Canonical whole-state digest including policy, records, signers and events.
    pub fn state_digest(&self) -> Hash32 {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(ROOT_REGISTRY_STATE_DOMAIN);
        bytes.extend_from_slice(&self.policy.signer_set_epoch.to_be_bytes());
        bytes.extend_from_slice(&self.policy.threshold.to_be_bytes());
        bytes.extend_from_slice(&(self.policy.configured_signers.len() as u64).to_be_bytes());
        for signer in &self.policy.configured_signers {
            bytes.extend_from_slice(signer);
        }
        bytes.extend_from_slice(&self.policy.source_network_id);
        bytes.extend_from_slice(&self.policy.source_genesis_hash);
        bytes.extend_from_slice(&self.policy.source_runtime_id);
        bytes.extend_from_slice(&self.policy.verification_context_hash);
        bytes.extend_from_slice(&self.policy.domain_id.to_be_bytes());
        bytes.extend_from_slice(&self.next_authorization_nonce.to_be_bytes());
        bytes.extend_from_slice(&self.accepted_transition_count.to_be_bytes());
        bytes.extend_from_slice(&(self.roots.len() as u64).to_be_bytes());
        for (coordinate, record) in &self.roots {
            bytes.extend_from_slice(&coordinate.coordinate_id());
            bytes.extend_from_slice(&record.authorization.canonical_preimage());
            bytes.extend_from_slice(&record.signing_digest);
            bytes.extend_from_slice(&(record.attesting_signers.len() as u64).to_be_bytes());
            for signer in &record.attesting_signers {
                bytes.extend_from_slice(signer);
            }
        }
        bytes.extend_from_slice(&(self.emitted_events.len() as u64).to_be_bytes());
        for event in &self.emitted_events {
            bytes.extend_from_slice(&event.coordinate.coordinate_id());
            bytes.extend_from_slice(&event.signing_digest);
            bytes.extend_from_slice(&(event.attesting_signers.len() as u64).to_be_bytes());
            for signer in &event.attesting_signers {
                bytes.extend_from_slice(signer);
            }
        }
        keccak256(&bytes)
    }

    /// Return the immutable value at one coordinate.
    pub fn registered_root(
        &self,
        coordinate: &ReceiptRootCoordinateV1,
    ) -> Option<&RegisteredReceiptRootV1> {
        self.roots.get(coordinate)
    }
}

/// State snapshot for atomic claim and settlement replay checks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReplayStateSnapshot {
    /// Number of consumed delivery claims.
    pub consumed_claims: usize,
    /// Number of consumed route-independent settlement keys.
    pub consumed_settlements: usize,
    /// Count of accepted transitions, used as an event-equivalent oracle.
    pub accepted_transition_count: u64,
}

/// Replay rejection produced before either key is inserted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DestinationReplayError {
    /// The delivery claim was already consumed.
    ClaimReplay,
    /// The route-independent settlement key was already consumed.
    SettlementReplay,
    /// The event-equivalent accepted-transition counter is exhausted.
    ArithmeticOverflow,
}

/// Atomic reference replay registry for destination consumption.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ReferenceDestinationReplayRegistry {
    consumed_claims: BTreeSet<Hash32>,
    consumed_settlements: BTreeSet<Hash32>,
    accepted_transition_count: u64,
    emitted_events: Vec<DestinationReplayEventV1>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DestinationReplayEventV1 {
    claim_id: Hash32,
    settlement_key: Hash32,
}

impl ReferenceDestinationReplayRegistry {
    /// Consume a claim and settlement key together after checking both.
    pub fn consume(
        &mut self,
        claim_id: Hash32,
        settlement_key: Hash32,
    ) -> Result<(), DestinationReplayError> {
        if self.consumed_claims.contains(&claim_id) {
            return Err(DestinationReplayError::ClaimReplay);
        }
        if self.consumed_settlements.contains(&settlement_key) {
            return Err(DestinationReplayError::SettlementReplay);
        }
        let next_transition_count = self
            .accepted_transition_count
            .checked_add(1)
            .ok_or(DestinationReplayError::ArithmeticOverflow)?;
        let event = DestinationReplayEventV1 {
            claim_id,
            settlement_key,
        };
        self.consumed_claims.insert(claim_id);
        self.consumed_settlements.insert(settlement_key);
        self.accepted_transition_count = next_transition_count;
        self.emitted_events.push(event);
        Ok(())
    }

    /// Return an observable state snapshot for mutation tests.
    pub fn snapshot(&self) -> ReplayStateSnapshot {
        ReplayStateSnapshot {
            consumed_claims: self.consumed_claims.len(),
            consumed_settlements: self.consumed_settlements.len(),
            accepted_transition_count: self.accepted_transition_count,
        }
    }

    /// Canonical whole-state digest including exact consumed IDs and events.
    pub fn state_digest(&self) -> Hash32 {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(REPLAY_REGISTRY_STATE_DOMAIN);
        bytes.extend_from_slice(&self.accepted_transition_count.to_be_bytes());
        bytes.extend_from_slice(&(self.consumed_claims.len() as u64).to_be_bytes());
        for claim_id in &self.consumed_claims {
            bytes.extend_from_slice(claim_id);
        }
        bytes.extend_from_slice(&(self.consumed_settlements.len() as u64).to_be_bytes());
        for settlement_key in &self.consumed_settlements {
            bytes.extend_from_slice(settlement_key);
        }
        bytes.extend_from_slice(&(self.emitted_events.len() as u64).to_be_bytes());
        for event in &self.emitted_events {
            bytes.extend_from_slice(&event.claim_id);
            bytes.extend_from_slice(&event.settlement_key);
        }
        keccak256(&bytes)
    }
}

/// Validate one attachment against an already authenticated root.
pub fn validate_receipt_attachment(
    receipt: &ReceiptEvidenceV1,
    authenticated_root: Hash32,
) -> Result<(), crate::settlement::ContractError> {
    if receipt.leaf_count != 1 || receipt.leaf_index != 0 || !receipt.merkle_path.is_empty() {
        return Err(crate::settlement::ContractError::InvalidMerklePath);
    }
    let computed = one_leaf_receipt_root(&receipt.statement_leaf);
    if computed != authenticated_root {
        return Err(crate::settlement::ContractError::ReceiptRootMismatch);
    }
    Ok(())
}

/// Strict JSON cross-language vector for the quorum digest and registry key.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiptRootQuorumVectorV1 {
    vector_version: u16,
    hash_algorithm: String,
    integer_encoding: String,
    source_identity: VectorSourceIdentity,
    authorization: VectorAuthorization,
    configured_signers: Vec<Hex20>,
    threshold: u16,
    attesting_signers: Vec<Hex20>,
    attesting_signatures: Vec<Hex65>,
    receipt_fixture: VectorReceiptFixture,
    pfr_only_digest: Hex32,
    pfr_only_signer: Hex20,
    pfr_only_signature: Hex65,
    settlement_claim_fixture: VectorSettlementClaimFixture,
    negative_cases: Vec<VectorNegativeCase>,
    expected: VectorExpected,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct VectorSourceIdentity {
    network_name: String,
    genesis_hash: Hex32,
    runtime_spec_name: String,
    runtime_spec_version: u32,
    runtime_transaction_version: u32,
    runtime_state_version: u8,
    runtime_code_hash: Hex32,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct VectorAuthorization {
    signer_set_epoch: u64,
    source_network_id: Hex32,
    source_genesis_hash: Hex32,
    source_runtime_id: Hex32,
    verification_context_hash: Hex32,
    domain_id: u32,
    source_block_number: u64,
    source_block_hash: Hex32,
    aggregation_id: u64,
    root: Hex32,
    leaf_count: u32,
    authorization_nonce: u64,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct VectorReceiptFixture {
    statement: Hex32,
    leaf_index: u32,
    merkle_path: Vec<Hex32>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct VectorNegativeCase {
    id: String,
    initial_state: VectorInitialState,
    operation: VectorOperation,
    field: VectorField,
    value: VectorMutationValue,
    expected_error: String,
    before_state_digest: Hex32,
    after_state_digest: Hex32,
}

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum VectorInitialState {
    Empty,
    Registered,
    Consumed,
}

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum VectorOperation {
    ConstructPolicy,
    RegisterRecovered,
    RegisterEvmCall,
    RecoverSignature,
    RegisterAuthorization,
    ValidateAttachment,
    ConsumeReplay,
    RegisterOverflow,
    ConsumeOverflow,
    ValidateSettlementFixture,
}

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum VectorField {
    ConfiguredSigners,
    Threshold,
    AttestingSigners,
    Signatures,
    Authorization,
    SignerSetEpoch,
    SourceNetworkId,
    LeafCount,
    AuthorizationNonce,
    AcceptedRoot,
    ReceiptAttachment,
    ReplayKeys,
    RootCounters,
    ReplayCounter,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "kind", content = "data", rename_all = "snake_case")]
enum VectorMutationValue {
    SignerArray(Vec<Hex20>),
    SignatureArray(Vec<Hex65>),
    U16(u16),
    U32(u32),
    U64(u64),
    Hex32(Hex32),
    Preset(VectorPreset),
    Authorization(VectorAuthorization),
    Attachment(VectorAttachmentCall),
    Replay(VectorReplayCall),
    RootOverflow(VectorRootOverflowCall),
    ReplayOverflow(VectorReplayOverflowCall),
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(rename_all = "snake_case")]
enum VectorPreset {
    ExactAuthorization,
    ConflictingRootAuthorization,
    ReusedNextCoordinateNonce,
    SkippedNextCoordinateNonce,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct VectorAttachmentCall {
    statement: Hex32,
    authenticated_root: Hex32,
    leaf_count: u32,
    leaf_index: u32,
    merkle_path: Vec<Hex32>,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct VectorReplayCall {
    claim_id: Hex32,
    settlement_key: Hex32,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct VectorRootOverflowCall {
    next_authorization_nonce: u64,
    root_transition_count: u64,
    authorization: VectorAuthorization,
    attesting_signers: Vec<Hex20>,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct VectorReplayOverflowCall {
    replay_transition_count: u64,
    claim_id: Hex32,
    settlement_key: Hex32,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct VectorSettlementClaimFixture {
    raw_statement: Hex192,
    route_id: Hex32,
    primary_transition_id: Hex32,
    source: Hex32,
    destination_chain_id: u64,
    destination_consumer: Hex32,
    action_kind: String,
    checkpoint: u64,
    session_id: Hex32,
    bvc_id: Hex32,
    accepted_root: Hex32,
    state: String,
    signer_set_epoch: u64,
    issuance_height: u64,
    supersedes_record_id: Option<Hex32>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct VectorExpected {
    canonical_preimage: HexVec,
    signing_digest: Hex32,
    coordinate_id: Hex32,
    registration_result: String,
    authorization_replay_error: String,
    coordinate_conflict_error: String,
    root_registry_before: u64,
    root_registry_after: u64,
    root_transition_count_before: u64,
    root_transition_count_after: u64,
    next_nonce_before: u64,
    next_nonce_after: u64,
    replay_claim_error: String,
    replay_settlement_error: String,
    replay_claims_before: u64,
    replay_claims_after: u64,
    replay_settlements_before: u64,
    replay_settlements_after: u64,
    replay_transition_count_before: u64,
    replay_transition_count_after: u64,
    raw_statement_sha256: Hex32,
    preclaim_hash: Hex32,
    primary_finality_record_id: Hex32,
    claim_id: Hex32,
    settlement_key: Hex32,
    raw_accepted_root: Hex32,
}

/// Frozen expected state transitions and rejection labels in the vector.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiptRootVectorExpectedOutcomeV1 {
    /// Successful registration label.
    pub registration_result: String,
    /// Exact-authorization replay label.
    pub authorization_replay_error: String,
    /// Same-coordinate changed-metadata label.
    pub coordinate_conflict_error: String,
    /// Registry size before successful registration.
    pub root_registry_before: u64,
    /// Registry size after successful registration.
    pub root_registry_after: u64,
    /// Event-equivalent transition count before registration.
    pub root_transition_count_before: u64,
    /// Event-equivalent transition count after registration.
    pub root_transition_count_after: u64,
    /// Required nonce before registration.
    pub next_nonce_before: u64,
    /// Required nonce after registration.
    pub next_nonce_after: u64,
    /// Claim replay rejection label.
    pub replay_claim_error: String,
    /// Settlement-key replay rejection label.
    pub replay_settlement_error: String,
    /// Replay claim count before/after the honest transition.
    pub replay_claim_counts: (u64, u64),
    /// Replay settlement count before/after the honest transition.
    pub replay_settlement_counts: (u64, u64),
    /// Event-equivalent replay transition count before/after.
    pub replay_transition_counts: (u64, u64),
}

/// One exact mutation/error/state row from the frozen negative matrix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiptRootVectorNegativeCaseV1 {
    /// Stable semantic case identifier.
    pub id: String,
    /// Typed operation name executed by the Rust interpreter.
    pub operation: String,
    /// Typed field selected by the operation.
    pub field: String,
    /// Expected Rust/EVM-parity error label.
    pub expected_error: String,
    /// Canonical digest of complete state before rejection.
    pub before_state_digest: Hash32,
    /// Canonical digest of complete state after rejection.
    pub after_state_digest: Hash32,
}

/// Values recomputed from one cross-language vector.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComputedReceiptRootQuorumVectorV1 {
    /// Derived source-network content identity.
    pub source_network_id: Hash32,
    /// Derived source-runtime content identity.
    pub source_runtime_id: Hash32,
    /// Fixed-width bytes signed by the authority.
    pub canonical_preimage: Vec<u8>,
    /// Keccak signing digest consumed by EVM recovery.
    pub signing_digest: Hash32,
    /// Domain-separated non-overwrite registry coordinate.
    pub coordinate_id: Hash32,
    /// Native one-leaf root derived from the sealed statement.
    pub receipt_root: Hash32,
    /// Canonical destination delivery claim identifier.
    pub claim_id: Hash32,
    /// Existing primary-finality record ID signed by the cross-role fixture.
    pub pfr_role_digest: Hash32,
    /// Route/raw preclaim committed by the existing settlement semantics.
    pub preclaim_hash: Hash32,
    /// Route-independent economic settlement key.
    pub settlement_key: Hash32,
    /// Full raw-statement commitment carried by the PFR.
    pub raw_statement_sha256: Hash32,
    /// Root word parsed directly from canonical raw192 bytes 96..128.
    pub raw_accepted_root: Hash32,
}

impl ReceiptRootQuorumVectorV1 {
    /// Strictly parse a vector and reject duplicate/unknown fields or bad hex.
    pub fn from_json(json: &str) -> Result<Self, String> {
        serde_json::from_str(json).map_err(|error| error.to_string())
    }

    /// Return the typed authorization represented by the vector.
    pub fn authorization(&self) -> ReceiptRootAuthorizationV1 {
        ReceiptRootAuthorizationV1 {
            signer_set_epoch: self.authorization.signer_set_epoch,
            source_network_id: self.authorization.source_network_id.0,
            source_genesis_hash: self.authorization.source_genesis_hash.0,
            source_runtime_id: self.authorization.source_runtime_id.0,
            verification_context_hash: self.authorization.verification_context_hash.0,
            domain_id: self.authorization.domain_id,
            source_block_number: self.authorization.source_block_number,
            source_block_hash: self.authorization.source_block_hash.0,
            aggregation_id: self.authorization.aggregation_id,
            root: self.authorization.root.0,
            leaf_count: self.authorization.leaf_count,
            authorization_nonce: self.authorization.authorization_nonce,
        }
    }

    /// Return the configured policy represented by the vector.
    pub fn policy(&self) -> ReceiptRootAuthorityPolicyV1 {
        let authorization = self.authorization();
        ReceiptRootAuthorityPolicyV1 {
            signer_set_epoch: authorization.signer_set_epoch,
            configured_signers: self
                .configured_signers
                .iter()
                .map(|value| value.0)
                .collect(),
            threshold: self.threshold,
            source_network_id: authorization.source_network_id,
            source_genesis_hash: authorization.source_genesis_hash,
            source_runtime_id: authorization.source_runtime_id,
            verification_context_hash: authorization.verification_context_hash,
            domain_id: authorization.domain_id,
        }
    }

    /// Return recovered signer identities represented by the vector.
    pub fn attesting_signers(&self) -> Vec<SignerIdentity> {
        self.attesting_signers.iter().map(|value| value.0).collect()
    }

    /// Return test-only compact ECDSA signatures in signer order.
    pub fn attesting_signatures(&self) -> Vec<[u8; 65]> {
        self.attesting_signatures
            .iter()
            .map(|value| value.0)
            .collect()
    }

    /// Return the sealed statement and exact native one-leaf coordinates.
    pub fn receipt_fixture(&self) -> (Hash32, u32, Vec<Hash32>) {
        (
            self.receipt_fixture.statement.0,
            self.receipt_fixture.leaf_index,
            self.receipt_fixture
                .merkle_path
                .iter()
                .map(|value| value.0)
                .collect(),
        )
    }

    /// Return the canonical raw192 carried by the existing settlement fixture.
    pub fn settlement_raw_statement(&self) -> Result<CanonicalRawStatement, String> {
        CanonicalRawStatement::from_bytes(self.settlement_claim_fixture.raw_statement.0)
            .map_err(|error| format!("invalid settlement raw statement: {error:?}"))
    }

    /// Return the test-only primary-finality-role signer and signature.
    pub fn pfr_only_attestation(&self) -> (SignerIdentity, [u8; 65]) {
        (self.pfr_only_signer.0, self.pfr_only_signature.0)
    }

    /// Return the separate primary-finality-domain fixture digest.
    pub fn pfr_only_digest(&self) -> Hash32 {
        self.pfr_only_digest.0
    }

    /// Return replay keys recomputed from the existing settlement claim model.
    pub fn replay_keys(&self) -> Result<(Hash32, Hash32), String> {
        let computed = self.compute()?;
        Ok((computed.claim_id, computed.settlement_key))
    }

    /// Return frozen reference outcomes and before/after counters.
    pub fn expected_outcome(&self) -> ReceiptRootVectorExpectedOutcomeV1 {
        ReceiptRootVectorExpectedOutcomeV1 {
            registration_result: self.expected.registration_result.clone(),
            authorization_replay_error: self.expected.authorization_replay_error.clone(),
            coordinate_conflict_error: self.expected.coordinate_conflict_error.clone(),
            root_registry_before: self.expected.root_registry_before,
            root_registry_after: self.expected.root_registry_after,
            root_transition_count_before: self.expected.root_transition_count_before,
            root_transition_count_after: self.expected.root_transition_count_after,
            next_nonce_before: self.expected.next_nonce_before,
            next_nonce_after: self.expected.next_nonce_after,
            replay_claim_error: self.expected.replay_claim_error.clone(),
            replay_settlement_error: self.expected.replay_settlement_error.clone(),
            replay_claim_counts: (
                self.expected.replay_claims_before,
                self.expected.replay_claims_after,
            ),
            replay_settlement_counts: (
                self.expected.replay_settlements_before,
                self.expected.replay_settlements_after,
            ),
            replay_transition_counts: (
                self.expected.replay_transition_count_before,
                self.expected.replay_transition_count_after,
            ),
        }
    }

    /// Return the complete frozen EVM-parity negative matrix.
    pub fn negative_cases(&self) -> Vec<ReceiptRootVectorNegativeCaseV1> {
        self.negative_cases
            .iter()
            .map(|case| ReceiptRootVectorNegativeCaseV1 {
                id: case.id.clone(),
                operation: format!("{:?}", case.operation),
                field: format!("{:?}", case.field),
                expected_error: case.expected_error.clone(),
                before_state_digest: case.before_state_digest.0,
                after_state_digest: case.after_state_digest.0,
            })
            .collect()
    }

    /// Execute every typed negative row and compare exact error and full state.
    pub fn verify_negative_cases(&self) -> Result<(), String> {
        for case in &self.negative_cases {
            let observation = self.execute_negative_case(case)?;
            if observation.expected_error != case.expected_error
                || observation.before_state_digest != case.before_state_digest.0
                || observation.after_state_digest != case.after_state_digest.0
            {
                return Err(format!(
                    "negative case {} mismatch: error={}, before=0x{}, after=0x{}",
                    case.id,
                    observation.expected_error,
                    encode_hex(&observation.before_state_digest),
                    encode_hex(&observation.after_state_digest)
                ));
            }
        }
        Ok(())
    }

    /// Execute every typed negative row and return canonical observations.
    pub fn negative_case_observations(
        &self,
    ) -> Result<Vec<ReceiptRootVectorNegativeCaseV1>, String> {
        self.negative_cases
            .iter()
            .map(|case| {
                let observation = self.execute_negative_case(case)?;
                Ok(ReceiptRootVectorNegativeCaseV1 {
                    id: case.id.clone(),
                    operation: format!("{:?}", case.operation),
                    field: format!("{:?}", case.field),
                    expected_error: observation.expected_error,
                    before_state_digest: observation.before_state_digest,
                    after_state_digest: observation.after_state_digest,
                })
            })
            .collect()
    }

    fn execute_negative_case(
        &self,
        case: &VectorNegativeCase,
    ) -> Result<ReceiptRootVectorNegativeCaseV1, String> {
        let authorization = self.authorization();
        let signatures = self.attesting_signatures();
        let mut roots = ReferenceReceiptRootRegistry::new(self.policy())
            .map_err(|error| format!("honest policy rejected: {error:?}"))?;
        let mut replay = ReferenceDestinationReplayRegistry::default();
        if matches!(
            case.initial_state,
            VectorInitialState::Registered | VectorInitialState::Consumed
        ) {
            roots
                .register_signatures(authorization, &signatures)
                .map_err(|error| format!("negative prestate registration failed: {error:?}"))?;
        }
        if case.initial_state == VectorInitialState::Consumed {
            let (claim_id, settlement_key) = self.replay_keys()?;
            replay
                .consume(claim_id, settlement_key)
                .map_err(|error| format!("negative prestate consume failed: {error:?}"))?;
        }

        match &case.value {
            VectorMutationValue::RootOverflow(value) => {
                roots.next_authorization_nonce = value.next_authorization_nonce;
                roots.accepted_transition_count = value.root_transition_count;
            }
            VectorMutationValue::ReplayOverflow(value) => {
                replay.accepted_transition_count = value.replay_transition_count;
            }
            _ => {}
        }

        let before_roots = roots.clone();
        let before_replay = replay.clone();
        let before_state_digest = system_state_digest(&roots, &replay);
        let result: Result<(), String> = match (case.operation, case.field, &case.value) {
            (
                VectorOperation::ConstructPolicy,
                VectorField::ConfiguredSigners,
                VectorMutationValue::SignerArray(values),
            ) => {
                let mut policy = self.policy();
                policy.configured_signers = values.iter().map(|value| value.0).collect();
                ReferenceReceiptRootRegistry::new(policy)
                    .map(|_| ())
                    .map_err(|error| format!("{error:?}"))
            }
            (
                VectorOperation::ConstructPolicy,
                VectorField::Threshold,
                VectorMutationValue::U16(value),
            ) => {
                let mut policy = self.policy();
                policy.threshold = *value;
                ReferenceReceiptRootRegistry::new(policy)
                    .map(|_| ())
                    .map_err(|error| format!("{error:?}"))
            }
            (
                VectorOperation::RegisterRecovered,
                VectorField::AttestingSigners,
                VectorMutationValue::SignerArray(values),
            ) => roots
                .register(
                    authorization,
                    &values.iter().map(|value| value.0).collect::<Vec<_>>(),
                )
                .map(|_| ())
                .map_err(|error| format!("{error:?}")),
            (
                VectorOperation::RegisterEvmCall,
                VectorField::Signatures,
                VectorMutationValue::SignatureArray(values),
            ) => {
                let recovered = values
                    .iter()
                    .map(|value| {
                        recover_evm_signer(&authorization.signing_digest(), &value.0)
                            .unwrap_or([0u8; 20])
                    })
                    .collect::<Vec<_>>();
                roots
                    .register(authorization, &recovered)
                    .map(|_| ())
                    .map_err(|error| format!("{error:?}"))
            }
            (
                VectorOperation::RecoverSignature,
                VectorField::Signatures,
                VectorMutationValue::SignatureArray(values),
            ) => {
                if values.len() != 1 {
                    Err("SignatureArrayLength".to_owned())
                } else {
                    recover_evm_signer(&authorization.signing_digest(), &values[0].0)
                        .map(|_| ())
                        .map_err(|error| format!("{error:?}"))
                }
            }
            (
                VectorOperation::RegisterAuthorization,
                VectorField::Authorization,
                VectorMutationValue::Authorization(value),
            ) => roots
                .register(vector_authorization(value), &self.attesting_signers())
                .map(|_| ())
                .map_err(|error| format!("{error:?}")),
            (
                VectorOperation::RegisterAuthorization,
                VectorField::Authorization,
                VectorMutationValue::Preset(preset),
            ) => {
                let mut changed = authorization;
                match preset {
                    VectorPreset::ExactAuthorization => {}
                    VectorPreset::ConflictingRootAuthorization => changed.root[0] ^= 1,
                    VectorPreset::ReusedNextCoordinateNonce => changed.aggregation_id += 1,
                    VectorPreset::SkippedNextCoordinateNonce => {
                        changed.aggregation_id += 1;
                        changed.authorization_nonce = 3;
                    }
                }
                roots
                    .register(changed, &self.attesting_signers())
                    .map(|_| ())
                    .map_err(|error| format!("{error:?}"))
            }
            (VectorOperation::RegisterAuthorization, field, value) => {
                let mut changed = authorization;
                match (field, value) {
                    (VectorField::SignerSetEpoch, VectorMutationValue::U64(value)) => {
                        changed.signer_set_epoch = *value;
                    }
                    (VectorField::SourceNetworkId, VectorMutationValue::Hex32(value)) => {
                        changed.source_network_id = value.0;
                    }
                    (VectorField::LeafCount, VectorMutationValue::U32(value)) => {
                        changed.leaf_count = *value;
                    }
                    (VectorField::AuthorizationNonce, VectorMutationValue::U64(value)) => {
                        changed.authorization_nonce = *value;
                    }
                    _ => return Err("invalid typed authorization mutation".to_owned()),
                }
                roots
                    .register(changed, &self.attesting_signers())
                    .map(|_| ())
                    .map_err(|error| format!("{error:?}"))
            }
            (
                VectorOperation::ValidateAttachment,
                VectorField::ReceiptAttachment,
                VectorMutationValue::Attachment(value),
            ) => validate_receipt_attachment(
                &vector_receipt(&authorization, value),
                value.authenticated_root.0,
            )
            .map_err(|error| format!("{error:?}")),
            (
                VectorOperation::ConsumeReplay,
                VectorField::ReplayKeys,
                VectorMutationValue::Replay(value),
            ) => replay
                .consume(value.claim_id.0, value.settlement_key.0)
                .map_err(|error| format!("{error:?}")),
            (
                VectorOperation::RegisterOverflow,
                VectorField::RootCounters,
                VectorMutationValue::RootOverflow(value),
            ) => roots
                .register(
                    vector_authorization(&value.authorization),
                    &value
                        .attesting_signers
                        .iter()
                        .map(|value| value.0)
                        .collect::<Vec<_>>(),
                )
                .map(|_| ())
                .map_err(|error| format!("{error:?}")),
            (
                VectorOperation::ConsumeOverflow,
                VectorField::ReplayCounter,
                VectorMutationValue::ReplayOverflow(value),
            ) => replay
                .consume(value.claim_id.0, value.settlement_key.0)
                .map_err(|error| format!("{error:?}")),
            (
                VectorOperation::ValidateSettlementFixture,
                VectorField::AcceptedRoot,
                VectorMutationValue::Hex32(value),
            ) => {
                let raw = self.settlement_raw_statement()?;
                if raw.accepted_root() == value.0 {
                    Ok(())
                } else {
                    Err("AcceptedRootMismatch".to_owned())
                }
            }
            _ => Err("TypedMutationMismatch".to_owned()),
        };
        let expected_error = result
            .err()
            .ok_or_else(|| format!("negative case {} unexpectedly succeeded", case.id))?;
        if roots != before_roots || replay != before_replay {
            return Err(format!("negative case {} changed complete state", case.id));
        }
        let after_state_digest = system_state_digest(&roots, &replay);
        Ok(ReceiptRootVectorNegativeCaseV1 {
            id: case.id.clone(),
            operation: format!("{:?}", case.operation),
            field: format!("{:?}", case.field),
            expected_error,
            before_state_digest,
            after_state_digest,
        })
    }

    /// Recompute the cross-language outputs without trusting expected values.
    pub fn compute(&self) -> Result<ComputedReceiptRootQuorumVectorV1, String> {
        if self.vector_version != 1
            || self.hash_algorithm != RECEIPT_ROOT_HASH_ALGORITHM
            || self.integer_encoding != RECEIPT_ROOT_INTEGER_ENCODING
        {
            return Err("unsupported receipt-root vector profile".to_owned());
        }
        let authorization = self.authorization();
        let derived_network_id = source_network_id(
            &self.source_identity.network_name,
            &self.source_identity.genesis_hash.0,
        );
        let derived_runtime_id = source_runtime_id(
            &self.source_identity.runtime_spec_name,
            self.source_identity.runtime_spec_version,
            self.source_identity.runtime_transaction_version,
            self.source_identity.runtime_state_version,
            &self.source_identity.runtime_code_hash.0,
        )?;
        let statement = self.receipt_fixture.statement.0;
        let receipt_root = one_leaf_receipt_root(&statement);
        let signing_digest = authorization.signing_digest();
        let raw = self.settlement_raw_statement()?;
        let raw_accepted_root = raw.accepted_root();
        if self.settlement_claim_fixture.accepted_root.0 != raw_accepted_root {
            return Err(
                "settlement accepted_root label does not match canonical raw192".to_owned(),
            );
        }
        let route_id = self.settlement_claim_fixture.route_id.0;
        let preclaim = preclaim_hash(&route_id, &raw);
        let action_kind = raw
            .action_kind()
            .map_err(|error| format!("invalid raw action kind: {error:?}"))?;
        if self.settlement_claim_fixture.action_kind != "membership"
            || action_kind != ActionKindV1::Membership
        {
            return Err(
                "settlement action kind does not match canonical raw192 byte 11".to_owned(),
            );
        }
        let state = match self.settlement_claim_fixture.state.as_str() {
            "committed" => PrimaryRecordState::Committed,
            _ => return Err("unsupported primary record state".to_owned()),
        };
        let pfr = PrimaryFinalityRecordV1 {
            primary_transition_id: self.settlement_claim_fixture.primary_transition_id.0,
            route_id,
            raw_statement_sha256: raw.full_sha256(),
            preclaim_hash: preclaim,
            source: self.settlement_claim_fixture.source.0,
            intended_destination: DestinationV1 {
                chain_id: self.settlement_claim_fixture.destination_chain_id,
                consumer: self.settlement_claim_fixture.destination_consumer.0,
            },
            action_kind,
            checkpoint: self.settlement_claim_fixture.checkpoint,
            session_id: self.settlement_claim_fixture.session_id.0,
            bvc_id: self.settlement_claim_fixture.bvc_id.0,
            accepted_root: raw_accepted_root,
            state,
            signer_set_epoch: self.settlement_claim_fixture.signer_set_epoch,
            issuance_height: self.settlement_claim_fixture.issuance_height,
            supersedes_record_id: self
                .settlement_claim_fixture
                .supersedes_record_id
                .map(|value| value.0),
        };
        let pfr_role_digest = pfr.record_id();
        let claim = WrapSettlementClaimV1::new(route_id, pfr_role_digest, raw);
        Ok(ComputedReceiptRootQuorumVectorV1 {
            source_network_id: derived_network_id,
            source_runtime_id: derived_runtime_id,
            canonical_preimage: authorization.canonical_preimage(),
            signing_digest,
            coordinate_id: authorization.coordinate().coordinate_id(),
            receipt_root,
            claim_id: claim.claim_id(),
            pfr_role_digest,
            preclaim_hash: preclaim,
            settlement_key: settlement_key(&pfr),
            raw_statement_sha256: raw.full_sha256(),
            raw_accepted_root,
        })
    }

    /// Compare every checked-in expected value with an independent recompute.
    pub fn verify_expected(&self) -> Result<(), String> {
        let computed = self.compute()?;
        let recovered_attesters = self
            .attesting_signatures()
            .iter()
            .map(|signature| recover_evm_signer(&computed.signing_digest, signature))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| error.to_string())?;
        let recovered_pfr_signer =
            recover_evm_signer(&computed.pfr_role_digest, &self.pfr_only_signature.0)
                .map_err(|error| error.to_string())?;
        let receipt_domain_cross_role =
            recover_evm_signer(&computed.signing_digest, &self.pfr_only_signature.0);
        if self.authorization.source_genesis_hash.0 != self.source_identity.genesis_hash.0
            || self.authorization.source_network_id.0 != computed.source_network_id
            || self.authorization.source_runtime_id.0 != computed.source_runtime_id
            || computed.canonical_preimage.len() != AUTHORIZATION_PREIMAGE_BYTES
            || computed.canonical_preimage != self.expected.canonical_preimage.0
            || computed.signing_digest != self.expected.signing_digest.0
            || computed.coordinate_id != self.expected.coordinate_id.0
            || computed.receipt_root != self.authorization.root.0
            || computed.pfr_role_digest != self.pfr_only_digest.0
            || computed.raw_statement_sha256 != self.expected.raw_statement_sha256.0
            || computed.preclaim_hash != self.expected.preclaim_hash.0
            || computed.pfr_role_digest != self.expected.primary_finality_record_id.0
            || computed.claim_id != self.expected.claim_id.0
            || computed.settlement_key != self.expected.settlement_key.0
            || computed.raw_accepted_root != self.expected.raw_accepted_root.0
            || self.receipt_fixture.leaf_index != 0
            || !self.receipt_fixture.merkle_path.is_empty()
            || recovered_attesters != self.attesting_signers()
            || recovered_attesters.len() != self.attesting_signatures.len()
            || recovered_pfr_signer != self.pfr_only_signer.0
            || receipt_domain_cross_role == Ok(self.pfr_only_signer.0)
        {
            return Err(
                "receipt-root vector expected values do not match recomputation".to_owned(),
            );
        }
        self.verify_negative_cases()?;
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Hex20([u8; 20]);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Hex32([u8; 32]);

#[derive(Clone, Debug, PartialEq, Eq)]
struct HexVec(Vec<u8>);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Hex65([u8; 65]);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Hex192([u8; 192]);

impl<'de> Deserialize<'de> for Hex20 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let value = String::deserialize(deserializer)?;
        parse_fixed_hex(&value)
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
        parse_fixed_hex(&value)
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
        parse_hex(&value)
            .map(Self)
            .map_err(serde::de::Error::custom)
    }
}

impl<'de> Deserialize<'de> for Hex65 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let value = String::deserialize(deserializer)?;
        parse_fixed_hex(&value)
            .map(Self)
            .map_err(serde::de::Error::custom)
    }
}

impl<'de> Deserialize<'de> for Hex192 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let value = String::deserialize(deserializer)?;
        parse_fixed_hex(&value)
            .map(Self)
            .map_err(serde::de::Error::custom)
    }
}

fn vector_authorization(value: &VectorAuthorization) -> ReceiptRootAuthorizationV1 {
    ReceiptRootAuthorizationV1 {
        signer_set_epoch: value.signer_set_epoch,
        source_network_id: value.source_network_id.0,
        source_genesis_hash: value.source_genesis_hash.0,
        source_runtime_id: value.source_runtime_id.0,
        verification_context_hash: value.verification_context_hash.0,
        domain_id: value.domain_id,
        source_block_number: value.source_block_number,
        source_block_hash: value.source_block_hash.0,
        aggregation_id: value.aggregation_id,
        root: value.root.0,
        leaf_count: value.leaf_count,
        authorization_nonce: value.authorization_nonce,
    }
}

fn vector_receipt(
    authorization: &ReceiptRootAuthorizationV1,
    value: &VectorAttachmentCall,
) -> ReceiptEvidenceV1 {
    ReceiptEvidenceV1 {
        source_block_hash: authorization.source_block_hash,
        source_block_height: authorization.source_block_number,
        zkverify_network_id: authorization.source_network_id,
        zkverify_runtime_id: authorization.source_runtime_id,
        zkverify_context_hash: authorization.verification_context_hash,
        domain_id: authorization.domain_id,
        aggregation_id: authorization.aggregation_id,
        statement_leaf: value.statement.0,
        leaf_count: value.leaf_count,
        leaf_index: value.leaf_index,
        merkle_path: value.merkle_path.iter().map(|item| item.0).collect(),
        claim_id: [0u8; 32],
        proof_identity: RouteProofIdentityV1 {
            program_vk_projection: Bn254Fr([0u8; 32]),
            groth16_vk_hash: [0u8; 32],
            groth16_setup_id: [0u8; 32],
        },
    }
}

fn system_state_digest(
    roots: &ReferenceReceiptRootRegistry,
    replay: &ReferenceDestinationReplayRegistry,
) -> Hash32 {
    let mut bytes = Vec::with_capacity(SYSTEM_STATE_DOMAIN.len() + 64);
    bytes.extend_from_slice(SYSTEM_STATE_DOMAIN);
    bytes.extend_from_slice(&roots.state_digest());
    bytes.extend_from_slice(&replay.state_digest());
    keccak256(&bytes)
}

fn encode_hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(char::from(DIGITS[usize::from(byte >> 4)]));
        output.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    output
}

fn parse_fixed_hex<const N: usize>(value: &str) -> Result<[u8; N], String> {
    let bytes = parse_hex(value)?;
    bytes
        .try_into()
        .map_err(|_| format!("expected exactly {N} hex bytes"))
}

fn parse_hex(value: &str) -> Result<Vec<u8>, String> {
    let digits = value
        .strip_prefix("0x")
        .ok_or_else(|| "hex value must start with 0x".to_owned())?;
    if digits.len() % 2 != 0 || digits.bytes().any(|byte| !byte.is_ascii_hexdigit()) {
        return Err("hex value must contain complete hexadecimal bytes".to_owned());
    }
    if digits.bytes().any(|byte| byte.is_ascii_uppercase()) {
        return Err("hex value must use lowercase digits".to_owned());
    }
    digits
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let text = std::str::from_utf8(pair).map_err(|error| error.to_string())?;
            u8::from_str_radix(text, 16).map_err(|error| error.to_string())
        })
        .collect()
}

fn keccak256(bytes: &[u8]) -> Hash32 {
    Keccak256::digest(bytes).into()
}

#[cfg(test)]
mod overflow_tests {
    use super::*;

    fn policy() -> ReceiptRootAuthorityPolicyV1 {
        ReceiptRootAuthorityPolicyV1 {
            signer_set_epoch: 1,
            configured_signers: vec![[1u8; 20], [2u8; 20]],
            threshold: 2,
            source_network_id: [3u8; 32],
            source_genesis_hash: [4u8; 32],
            source_runtime_id: [5u8; 32],
            verification_context_hash: [6u8; 32],
            domain_id: 2,
        }
    }

    fn authorization(nonce: u64) -> ReceiptRootAuthorizationV1 {
        ReceiptRootAuthorizationV1 {
            signer_set_epoch: 1,
            source_network_id: [3u8; 32],
            source_genesis_hash: [4u8; 32],
            source_runtime_id: [5u8; 32],
            verification_context_hash: [6u8; 32],
            domain_id: 2,
            source_block_number: 7,
            source_block_hash: [8u8; 32],
            aggregation_id: 9,
            root: [10u8; 32],
            leaf_count: 1,
            authorization_nonce: nonce,
        }
    }

    #[test]
    fn root_registry_counter_overflows_precede_every_write() -> Result<(), String> {
        for (next_nonce, transition_count, authorization_nonce) in
            [(u64::MAX, 0, u64::MAX), (1, u64::MAX, 1)]
        {
            let mut registry = ReferenceReceiptRootRegistry {
                policy: policy(),
                roots: BTreeMap::new(),
                next_authorization_nonce: next_nonce,
                accepted_transition_count: transition_count,
                emitted_events: Vec::new(),
            };
            let before = (
                registry.roots.clone(),
                registry.next_authorization_nonce,
                registry.accepted_transition_count,
            );
            assert_eq!(
                registry.register(authorization(authorization_nonce), &[[1u8; 20], [2u8; 20]]),
                Err(ReceiptRootPolicyError::ArithmeticOverflow)
            );
            assert_eq!(
                (
                    registry.roots,
                    registry.next_authorization_nonce,
                    registry.accepted_transition_count,
                ),
                before
            );
        }
        Ok(())
    }

    #[test]
    fn replay_counter_overflow_precedes_every_write() {
        let mut registry = ReferenceDestinationReplayRegistry {
            consumed_claims: BTreeSet::new(),
            consumed_settlements: BTreeSet::new(),
            accepted_transition_count: u64::MAX,
            emitted_events: Vec::new(),
        };
        let before = registry.snapshot();
        assert_eq!(
            registry.consume([1u8; 32], [2u8; 32]),
            Err(DestinationReplayError::ArithmeticOverflow)
        );
        assert_eq!(registry.snapshot(), before);
    }
}
