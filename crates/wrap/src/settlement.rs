//! Pure A.6 settlement-contract reference model.
//!
//! This module does not implement a production CDK consumer, D-quencer
//! signature scheme, zkVerify finalized-state transport, Groth16 verifier, or
//! `SECONDARY_FINALIZED` state transition. It fixes the data ownership and
//! fail-closed checks those components must implement. Production
//! authentication is injected through [`PrimaryFinalityVerifier`] and
//! [`FinalizedReceiptRootSource`]; no built-in implementation pretends to
//! discharge either trust boundary.

use std::collections::{BTreeMap, BTreeSet};

use sha2::{Digest as _, Sha256};
use sha3::Keccak256;

use crate::statement::{
    BN254_R_BE, Bn254Fr, WRAP_STATEMENT_FRS, WRAP_STATEMENT_VERSION, WrapStatementV1, unpack_digest,
};

/// SHA-256 or Keccak-256 output used by the reference contract.
pub type Hash32 = [u8; 32];

/// Exact byte length of the frozen six-scalar application statement.
pub const RAW_WRAP_STATEMENT_BYTES: usize = WRAP_STATEMENT_FRS * 32;
/// Canonical settlement envelope magic.
pub const SETTLEMENT_MAGIC: [u8; 8] = *b"SSGKRSTL";
/// Canonical settlement envelope version.
pub const SETTLEMENT_ENVELOPE_VERSION: u16 = 1;
/// Canonical A.6 codec version.
pub const CANONICAL_CODEC_VERSION: u16 = 1;
/// Reference-only binary Keccak Merkle profile.
pub const REFERENCE_MERKLE_PROFILE: u16 = 1;

const ROUTE_MANIFEST_DOMAIN: &[u8] = b"ssgkr/route-manifest/v1";
const PRIMARY_RECORD_DOMAIN: &[u8] = b"ssgkr/primary-finality-record/v1";
const PRECLAIM_DOMAIN: &[u8] = b"ssgkr/wrap-settlement-preclaim/v1";
const CLAIM_DOMAIN: &[u8] = b"ssgkr/wrap-settlement-claim/v1";
/// Domain prefix for the route-independent economic exactly-once key.
pub const SETTLEMENT_KEY_DOMAIN: &[u8] = b"ssgkr/settlement-key/v1";
const DIGEST_ADAPTER_PROFILE: &[u8] = b"ssgkr/raw192-sha256-truncate253-le/v1";
const PUBS_ADAPTER_PROFILE: &[u8] = b"ssgkr/zkverify-pubs-pi0-pi1-le/v1";

/// Frozen raw `WrapStatementV1` bytes after strict canonical validation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CanonicalRawStatement([u8; RAW_WRAP_STATEMENT_BYTES]);

impl CanonicalRawStatement {
    /// Serialize and validate an in-memory application statement.
    pub fn from_statement(statement: &WrapStatementV1) -> Result<Self, ContractError> {
        let mut raw = [0u8; RAW_WRAP_STATEMENT_BYTES];
        for (index, scalar) in statement.frs.iter().enumerate() {
            raw[index * 32..(index + 1) * 32].copy_from_slice(&scalar.0);
        }
        Self::from_bytes(raw)
    }

    /// Validate an exact 192-byte application statement.
    pub fn from_bytes(raw: [u8; RAW_WRAP_STATEMENT_BYTES]) -> Result<Self, ContractError> {
        validate_raw_statement(&raw)?;
        Ok(Self(raw))
    }

    /// Borrow the canonical raw bytes.
    pub fn as_bytes(&self) -> &[u8; RAW_WRAP_STATEMENT_BYTES] {
        &self.0
    }

    /// Return the full, unprojected SHA-256 commitment used by the PFR.
    pub fn full_sha256(&self) -> Hash32 {
        sha256(&self.0)
    }

    /// Return the application operation kind encoded in the frozen header.
    pub fn action_kind(&self) -> Result<ActionKindV1, ContractError> {
        ActionKindV1::from_tag(self.0[11]).ok_or(ContractError::InvalidActionKind)
    }

    /// Return the exact frozen 16-byte version/config header.
    pub fn statement_header(&self) -> [u8; 16] {
        let mut header = [0u8; 16];
        header.copy_from_slice(&self.0[..16]);
        header
    }

    /// Return the accepted new root scalar in canonical little-endian form.
    pub fn accepted_root(&self) -> Hash32 {
        let mut root = [0u8; 32];
        root.copy_from_slice(&self.0[96..128]);
        root
    }

    /// Return the full circuit commitment scalar in canonical LE form.
    pub fn circuit_commitment(&self) -> Hash32 {
        let mut commitment = [0u8; 32];
        commitment.copy_from_slice(&self.0[32..64]);
        commitment
    }
}

/// Economic action bound by the signed PFR and raw statement header.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum ActionKindV1 {
    /// Membership/read transition.
    Membership = 0,
    /// Non-membership/read transition.
    NonMembership = 1,
    /// State update transition.
    Update = 2,
}

impl ActionKindV1 {
    /// Decode the canonical one-byte action tag.
    pub fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::Membership),
            1 => Some(Self::NonMembership),
            2 => Some(Self::Update),
            _ => None,
        }
    }
}

/// Canonical intended destination for one economic transition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DestinationV1 {
    /// Destination chain identifier.
    pub chain_id: u64,
    /// Destination consumer identifier/address, left-padded by its adapter.
    pub consumer: Hash32,
}

impl DestinationV1 {
    fn append_to(self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.chain_id.to_le_bytes());
        out.extend_from_slice(&self.consumer);
    }
}

/// Immutable, content-addressed static route profile.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RouteManifestV1 {
    /// Hash/ID of the vendor name.
    pub vendor_id: Hash32,
    /// Hash/ID of the wrapper proof system.
    pub proof_system_id: Hash32,
    /// Exact released source commit.
    pub source_commit: Hash32,
    /// Exact toolchain or OCI digest.
    pub toolchain_digest: Hash32,
    /// Reproducible guest artifact digest.
    pub guest_artifact_digest: Hash32,
    /// Vendor-defined guest/program VK projection, stock PI[0].
    pub expected_program_vk: Bn254Fr,
    /// Pinned canonical Groth16 VK hash used by the statement adapter.
    pub groth16_vk_hash: Hash32,
    /// Pinned setup/provenance identity.
    pub groth16_setup_id: Hash32,
    /// Public-values digest adapter identity.
    pub digest_adapter_id: Hash32,
    /// zkVerify `Pubs`/statement adapter identity.
    pub pubs_adapter_id: Hash32,
    /// zkVerify source network identity.
    pub zkverify_network_id: Hash32,
    /// Pinned runtime version or code hash.
    pub zkverify_runtime_id: Hash32,
    /// `keccak256(context_bytes)` for the pinned verifier context.
    pub zkverify_context_hash: Hash32,
    /// Pinned verifier-version hash.
    pub verifier_version_hash: Hash32,
    /// Pinned zkVerify aggregation domain.
    pub zkverify_domain_id: u32,
    /// Exact canonical codec version.
    pub canonical_codec_version: u16,
    /// Exact application statement version.
    pub statement_version: u16,
    /// Exact accepted version/config header bytes.
    pub expected_statement_header: [u8; 16],
    /// Exact frozen circuit commitment accepted by this route.
    pub full_circuit_commitment: Hash32,
    /// Exact source domain bound by the PFR.
    pub source: Hash32,
    /// Exact destination chain and consumer.
    pub destination: DestinationV1,
    /// Receipt Merkle profile. Only the reference profile is executable here.
    pub receipt_merkle_profile: u16,
}

impl RouteManifestV1 {
    /// Compute the immutable content address over the canonical fixed-width codec.
    pub fn route_id(&self) -> Hash32 {
        let mut bytes = Vec::with_capacity(32 * 16);
        bytes.extend_from_slice(ROUTE_MANIFEST_DOMAIN);
        bytes.extend_from_slice(&self.vendor_id);
        bytes.extend_from_slice(&self.proof_system_id);
        bytes.extend_from_slice(&self.source_commit);
        bytes.extend_from_slice(&self.toolchain_digest);
        bytes.extend_from_slice(&self.guest_artifact_digest);
        bytes.extend_from_slice(&self.expected_program_vk.0);
        bytes.extend_from_slice(&self.groth16_vk_hash);
        bytes.extend_from_slice(&self.groth16_setup_id);
        bytes.extend_from_slice(&self.digest_adapter_id);
        bytes.extend_from_slice(&self.pubs_adapter_id);
        bytes.extend_from_slice(&self.zkverify_network_id);
        bytes.extend_from_slice(&self.zkverify_runtime_id);
        bytes.extend_from_slice(&self.zkverify_context_hash);
        bytes.extend_from_slice(&self.verifier_version_hash);
        bytes.extend_from_slice(&self.zkverify_domain_id.to_le_bytes());
        bytes.extend_from_slice(&self.canonical_codec_version.to_le_bytes());
        bytes.extend_from_slice(&self.statement_version.to_le_bytes());
        bytes.extend_from_slice(&self.expected_statement_header);
        bytes.extend_from_slice(&self.full_circuit_commitment);
        bytes.extend_from_slice(&self.source);
        self.destination.append_to(&mut bytes);
        bytes.extend_from_slice(&self.receipt_merkle_profile.to_le_bytes());
        sha256(&bytes)
    }
}

/// Mutable route lifecycle, deliberately excluded from [`RouteManifestV1`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RouteLifecycleState {
    /// New settlement acceptance is enabled.
    Active,
    /// Only settlements through a fixed checkpoint cutoff are accepted.
    Draining,
    /// New settlements are rejected; historical verification remains possible.
    Revoked,
}

/// Mutable policy for new settlement acceptance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NewAcceptancePolicy {
    /// Accept every new checkpoint.
    Accept,
    /// Accept checkpoints at or below this cutoff.
    ThroughCheckpoint(u64),
    /// Reject every new settlement.
    Reject,
}

/// One mutable lifecycle-registry entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RouteLifecycleEntry {
    /// Current operational state.
    pub state: RouteLifecycleState,
    /// Replacement route, if governance has nominated one.
    pub replacement_route: Option<Hash32>,
    /// Explicit new-acceptance policy.
    pub new_acceptance: NewAcceptancePolicy,
    /// Governance revision for audit ordering.
    pub governance_revision: u64,
    /// Primary height at which this lifecycle revision becomes effective.
    pub effective_height: u64,
}

impl RouteLifecycleEntry {
    fn validate(self) -> Result<(), ContractError> {
        let coherent = matches!(
            (self.state, self.new_acceptance),
            (RouteLifecycleState::Active, NewAcceptancePolicy::Accept)
                | (
                    RouteLifecycleState::Draining,
                    NewAcceptancePolicy::ThroughCheckpoint(_)
                )
                | (RouteLifecycleState::Revoked, NewAcceptancePolicy::Reject)
        );
        coherent
            .then_some(())
            .ok_or(ContractError::InvalidLifecycle)
    }

    fn authorize_new(self, checkpoint: u64) -> Result<(), ContractError> {
        self.validate()?;
        match self.new_acceptance {
            NewAcceptancePolicy::Accept => Ok(()),
            NewAcceptancePolicy::ThroughCheckpoint(cutoff) if checkpoint <= cutoff => Ok(()),
            NewAcceptancePolicy::ThroughCheckpoint(_) => Err(ContractError::CheckpointPastCutoff),
            NewAcceptancePolicy::Reject => Err(ContractError::RouteRevoked),
        }
    }
}

/// Primary-finality state certified by the D-quencer quorum.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrimaryRecordState {
    /// Transition is not yet primary-final.
    Prepared,
    /// Transition is quorum-certified and primary-final.
    Committed,
}

/// Canonical signed core of a primary-finality record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrimaryFinalityRecordV1 {
    /// Route-independent primary transition identity.
    pub primary_transition_id: Hash32,
    /// Route used for this proof delivery attempt.
    pub route_id: Hash32,
    /// Full unprojected SHA-256 commitment to raw192.
    pub raw_statement_sha256: Hash32,
    /// Route/raw preclaim bound without a circular record ID.
    pub preclaim_hash: Hash32,
    /// Source domain.
    pub source: Hash32,
    /// Intended destination chain and consumer.
    pub intended_destination: DestinationV1,
    /// Economic/application action kind.
    pub action_kind: ActionKindV1,
    /// Primary checkpoint.
    pub checkpoint: u64,
    /// Session identity.
    pub session_id: Hash32,
    /// BVC context identity.
    pub bvc_id: Hash32,
    /// Accepted application root.
    pub accepted_root: Hash32,
    /// Primary transition state; settlement requires `Committed`.
    pub state: PrimaryRecordState,
    /// D-quencer signer-set epoch.
    pub signer_set_epoch: u64,
    /// Issuance height in the primary domain.
    pub issuance_height: u64,
    /// Append-only correction predecessor, if this record supersedes one.
    pub supersedes_record_id: Option<Hash32>,
}

impl PrimaryFinalityRecordV1 {
    /// Compute the canonical record ID signed by the external verifier seam.
    pub fn record_id(&self) -> Hash32 {
        let mut bytes = Vec::with_capacity(32 * 10);
        bytes.extend_from_slice(PRIMARY_RECORD_DOMAIN);
        bytes.extend_from_slice(&self.primary_transition_id);
        bytes.extend_from_slice(&self.route_id);
        bytes.extend_from_slice(&self.raw_statement_sha256);
        bytes.extend_from_slice(&self.preclaim_hash);
        bytes.extend_from_slice(&self.source);
        self.intended_destination.append_to(&mut bytes);
        bytes.push(self.action_kind as u8);
        bytes.extend_from_slice(&self.checkpoint.to_le_bytes());
        bytes.extend_from_slice(&self.session_id);
        bytes.extend_from_slice(&self.bvc_id);
        bytes.extend_from_slice(&self.accepted_root);
        bytes.push(match self.state {
            PrimaryRecordState::Prepared => 0,
            PrimaryRecordState::Committed => 1,
        });
        bytes.extend_from_slice(&self.signer_set_epoch.to_le_bytes());
        bytes.extend_from_slice(&self.issuance_height.to_le_bytes());
        match self.supersedes_record_id {
            Some(id) => {
                bytes.push(1);
                bytes.extend_from_slice(&id);
            }
            None => bytes.push(0),
        }
        sha256(&bytes)
    }
}

/// Canonical settlement claim core above the frozen S-6 statement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WrapSettlementClaimV1 {
    /// Fixed `SSGKRSTL` magic.
    pub magic: [u8; 8],
    /// Envelope version, currently 1.
    pub envelope_version: u16,
    /// Immutable route content address.
    pub route_id: Hash32,
    /// Canonical PFR identity.
    pub primary_finality_record_id: Hash32,
    /// Exact canonical 192-byte application statement.
    pub application_statement: [u8; RAW_WRAP_STATEMENT_BYTES],
}

impl WrapSettlementClaimV1 {
    /// Construct a canonical claim from a route, PFR and raw statement.
    pub fn new(
        route_id: Hash32,
        primary_finality_record_id: Hash32,
        application_statement: CanonicalRawStatement,
    ) -> Self {
        Self {
            magic: SETTLEMENT_MAGIC,
            envelope_version: SETTLEMENT_ENVELOPE_VERSION,
            route_id,
            primary_finality_record_id,
            application_statement: *application_statement.as_bytes(),
        }
    }

    /// Delivery-deduplication identity. This is not the economic replay key.
    pub fn claim_id(&self) -> Hash32 {
        sha256_parts(&[
            CLAIM_DOMAIN,
            &self.route_id,
            &self.primary_finality_record_id,
            &self.application_statement,
        ])
    }
}

/// Proof/VK/setup identity carried by durable delivery evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RouteProofIdentityV1 {
    /// Observed stock PI[0].
    pub program_vk_projection: Bn254Fr,
    /// Observed canonical Groth16 VK hash.
    pub groth16_vk_hash: Hash32,
    /// Claimed setup/provenance identity. Equality is only an attachment
    /// sanity check; governance must bind the manifest's VK to its setup.
    pub groth16_setup_id: Hash32,
}

/// Durable receipt evidence consumed by the reference evaluator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiptEvidenceV1 {
    /// Source block containing the proof/aggregation receipt.
    pub source_block_hash: Hash32,
    /// Source block height used by the pinned finality policy.
    pub source_block_height: u64,
    /// zkVerify source network.
    pub zkverify_network_id: Hash32,
    /// Pinned runtime version or code hash.
    pub zkverify_runtime_id: Hash32,
    /// Pinned verifier-context hash.
    pub zkverify_context_hash: Hash32,
    /// Aggregation domain.
    pub domain_id: u32,
    /// Aggregation receipt identity.
    pub aggregation_id: u64,
    /// Leaf supplied by the receipt path; the consumer recomputes it.
    pub statement_leaf: Hash32,
    /// Number of leaves in the reference binary tree.
    pub leaf_count: u32,
    /// Zero-based leaf index.
    pub leaf_index: u32,
    /// Bottom-up sibling path.
    pub merkle_path: Vec<Hash32>,
    /// Delivery claim identity; checked but never used for economic replay.
    pub claim_id: Hash32,
    /// Exact proof/VK/setup identity expected by the route.
    pub proof_identity: RouteProofIdentityV1,
}

/// External verifier for D-quencer quorum certificates.
///
/// A production implementation must check signer-set epoch, duplicate
/// signers, quorum threshold, and every signature over `record.record_id()`.
pub trait PrimaryFinalityVerifier {
    /// Return true only for a valid quorum certificate over this exact record.
    fn verify(&self, record: &PrimaryFinalityRecordV1, certificate: &[u8]) -> bool;
}

/// Authenticated finalized source of zkVerify receipt roots.
///
/// A production implementation must authenticate source consensus finality,
/// runtime/context/domain and non-overwriting root registration. A relayer
/// payload by itself is not an implementation of this trait.
pub trait FinalizedReceiptRootSource {
    /// Whether the exact receipt coordinates are finalized under the pinned
    /// source policy.
    fn is_finalized(&self, receipt: &ReceiptEvidenceV1) -> bool;

    /// Return the authenticated root for the exact receipt coordinates.
    fn authenticated_root(&self, receipt: &ReceiptEvidenceV1) -> Option<Hash32>;
}

/// One fully checked authorization result.
///
/// This is evidence for a future CDK L3 consumer. Returning it does not mutate
/// application state and does not declare `SECONDARY_FINALIZED`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SettlementAuthorizationV1 {
    /// Route-independent economic replay key.
    pub settlement_key: Hash32,
    /// Delivery-only claim identity.
    pub claim_id: Hash32,
    /// Primary transition identity.
    pub primary_transition_id: Hash32,
    /// Root authorized by the primary record.
    pub accepted_root: Hash32,
}

/// One evaluation input.
#[derive(Clone, Copy, Debug)]
pub struct SettlementAttemptV1<'a> {
    /// Canonical settlement claim.
    pub claim: &'a WrapSettlementClaimV1,
    /// Signed primary-finality record.
    pub primary_record: &'a PrimaryFinalityRecordV1,
    /// Opaque quorum certificate interpreted by the injected verifier.
    pub primary_certificate: &'a [u8],
    /// Durable receipt/path evidence.
    pub receipt: &'a ReceiptEvidenceV1,
}

/// Fail-closed contract errors exposed by the reference harness.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContractError {
    /// Claim magic or envelope version is not recognized.
    InvalidEnvelope,
    /// One raw scalar, header field, digest packing, or asset scalar is invalid.
    NonCanonicalStatement,
    /// The raw statement contains an unknown action tag.
    InvalidActionKind,
    /// Route is not registered.
    UnknownRoute,
    /// Route content, codec, statement, or Merkle profile is invalid.
    InvalidRouteManifest,
    /// Lifecycle state and acceptance policy disagree.
    InvalidLifecycle,
    /// Lifecycle revisions and effective heights must increase monotonically.
    StaleLifecycleRevision,
    /// Route is revoked for new acceptance.
    RouteRevoked,
    /// Draining-route checkpoint is past its cutoff.
    CheckpointPastCutoff,
    /// Claim/PFR/route binding is inconsistent.
    PrimaryRecordMismatch,
    /// PFR is not in committed state.
    PrimaryRecordNotCommitted,
    /// Quorum certificate or one of its signatures is invalid.
    InvalidPrimaryCertificate,
    /// Source, destination, action, accepted root, or preclaim is inconsistent.
    ApplicationContextMismatch,
    /// Guest/program VK projection is not the route value.
    ProgramVkMismatch,
    /// Groth16 VK is not the route value.
    Groth16VkMismatch,
    /// Groth16 setup/provenance identity is not the route value.
    Groth16SetupMismatch,
    /// Receipt network/runtime/context/domain is not the route profile.
    ReceiptContextMismatch,
    /// Receipt block has not reached authenticated source finality.
    SourceBlockNotFinalized,
    /// Receipt statement leaf differs from the canonical recomputation.
    StatementLeafMismatch,
    /// Leaf count, index, or path shape is invalid.
    InvalidMerklePath,
    /// Merkle path does not reach the authenticated receipt root.
    ReceiptRootMismatch,
    /// Delivery claim identity does not match the canonical claim.
    ClaimIdMismatch,
    /// Same delivery claim was already consumed.
    ClaimAlreadySeen,
    /// Same economic transition was already settled through any route/claim.
    SettlementAlreadyConsumed,
    /// A route with this immutable content address was already registered.
    RouteAlreadyRegistered,
}

/// Pure/reference route registry and replay state.
#[derive(Clone, Debug)]
pub struct ReferenceSettlementConsumer {
    destination: DestinationV1,
    manifests: BTreeMap<Hash32, RouteManifestV1>,
    lifecycle: BTreeMap<Hash32, RouteLifecycleEntry>,
    consumed_claims: BTreeSet<Hash32>,
    consumed_settlements: BTreeSet<Hash32>,
}

impl ReferenceSettlementConsumer {
    /// Create a reference consumer for one fixed destination chain/consumer.
    pub fn new(destination: DestinationV1) -> Self {
        Self {
            destination,
            manifests: BTreeMap::new(),
            lifecycle: BTreeMap::new(),
            consumed_claims: BTreeSet::new(),
            consumed_settlements: BTreeSet::new(),
        }
    }

    /// Register immutable manifest content and an independent lifecycle entry.
    pub fn register_route(
        &mut self,
        manifest: RouteManifestV1,
        lifecycle: RouteLifecycleEntry,
    ) -> Result<Hash32, ContractError> {
        validate_manifest(&manifest)?;
        lifecycle.validate()?;
        let route_id = manifest.route_id();
        if self.manifests.contains_key(&route_id) {
            return Err(ContractError::RouteAlreadyRegistered);
        }
        self.manifests.insert(route_id, manifest);
        self.lifecycle.insert(route_id, lifecycle);
        Ok(route_id)
    }

    /// Mutate only lifecycle state; immutable manifest content is untouched.
    pub fn set_lifecycle(
        &mut self,
        route_id: Hash32,
        lifecycle: RouteLifecycleEntry,
    ) -> Result<(), ContractError> {
        if !self.manifests.contains_key(&route_id) {
            return Err(ContractError::UnknownRoute);
        }
        lifecycle.validate()?;
        let previous = self
            .lifecycle
            .get(&route_id)
            .ok_or(ContractError::InvalidLifecycle)?;
        if lifecycle.governance_revision <= previous.governance_revision
            || lifecycle.effective_height < previous.effective_height
        {
            return Err(ContractError::StaleLifecycleRevision);
        }
        self.lifecycle.insert(route_id, lifecycle);
        Ok(())
    }

    /// Return whether immutable route content remains available for history.
    pub fn is_historically_verifiable(&self, route_id: &Hash32) -> bool {
        self.manifests.contains_key(route_id)
    }

    /// Verify historical evidence without applying current lifecycle/replay policy.
    pub fn verify_historical(
        &self,
        attempt: SettlementAttemptV1<'_>,
        pfr_verifier: &impl PrimaryFinalityVerifier,
        root_source: &impl FinalizedReceiptRootSource,
    ) -> Result<SettlementAuthorizationV1, ContractError> {
        self.validate_attempt(attempt, pfr_verifier, root_source, false)
    }

    /// Authorize one new settlement and consume both delivery and economic keys.
    pub fn authorize_new(
        &mut self,
        attempt: SettlementAttemptV1<'_>,
        pfr_verifier: &impl PrimaryFinalityVerifier,
        root_source: &impl FinalizedReceiptRootSource,
    ) -> Result<SettlementAuthorizationV1, ContractError> {
        let authorization = self.validate_attempt(attempt, pfr_verifier, root_source, true)?;
        if self.consumed_claims.contains(&authorization.claim_id) {
            return Err(ContractError::ClaimAlreadySeen);
        }
        if self
            .consumed_settlements
            .contains(&authorization.settlement_key)
        {
            return Err(ContractError::SettlementAlreadyConsumed);
        }
        self.consumed_claims.insert(authorization.claim_id);
        self.consumed_settlements
            .insert(authorization.settlement_key);
        Ok(authorization)
    }

    fn validate_attempt(
        &self,
        attempt: SettlementAttemptV1<'_>,
        pfr_verifier: &impl PrimaryFinalityVerifier,
        root_source: &impl FinalizedReceiptRootSource,
        enforce_new_acceptance: bool,
    ) -> Result<SettlementAuthorizationV1, ContractError> {
        let claim = attempt.claim;
        if claim.magic != SETTLEMENT_MAGIC || claim.envelope_version != SETTLEMENT_ENVELOPE_VERSION
        {
            return Err(ContractError::InvalidEnvelope);
        }
        let raw = CanonicalRawStatement::from_bytes(claim.application_statement)?;
        let manifest = self
            .manifests
            .get(&claim.route_id)
            .ok_or(ContractError::UnknownRoute)?;
        validate_manifest(manifest)?;
        if manifest.route_id() != claim.route_id {
            return Err(ContractError::InvalidRouteManifest);
        }
        if enforce_new_acceptance {
            let lifecycle = self
                .lifecycle
                .get(&claim.route_id)
                .ok_or(ContractError::InvalidLifecycle)?;
            lifecycle.authorize_new(attempt.primary_record.checkpoint)?;
        }

        let identity = attempt.receipt.proof_identity;
        if identity.program_vk_projection != manifest.expected_program_vk {
            return Err(ContractError::ProgramVkMismatch);
        }
        if identity.groth16_vk_hash != manifest.groth16_vk_hash {
            return Err(ContractError::Groth16VkMismatch);
        }
        if identity.groth16_setup_id != manifest.groth16_setup_id {
            return Err(ContractError::Groth16SetupMismatch);
        }

        let record = attempt.primary_record;
        if record.record_id() != claim.primary_finality_record_id
            || record.route_id != claim.route_id
        {
            return Err(ContractError::PrimaryRecordMismatch);
        }
        if record.state != PrimaryRecordState::Committed {
            return Err(ContractError::PrimaryRecordNotCommitted);
        }
        if !pfr_verifier.verify(record, attempt.primary_certificate) {
            return Err(ContractError::InvalidPrimaryCertificate);
        }
        if record.raw_statement_sha256 != raw.full_sha256()
            || record.preclaim_hash != preclaim_hash(&claim.route_id, &raw)
            || record.source != manifest.source
            || record.intended_destination != manifest.destination
            || record.intended_destination != self.destination
            || record.action_kind != raw.action_kind()?
            || record.accepted_root != raw.accepted_root()
            || manifest.expected_statement_header != raw.statement_header()
            || manifest.full_circuit_commitment != raw.circuit_commitment()
        {
            return Err(ContractError::ApplicationContextMismatch);
        }

        let receipt = attempt.receipt;
        if receipt.zkverify_network_id != manifest.zkverify_network_id
            || receipt.zkverify_runtime_id != manifest.zkverify_runtime_id
            || receipt.zkverify_context_hash != manifest.zkverify_context_hash
            || receipt.domain_id != manifest.zkverify_domain_id
        {
            return Err(ContractError::ReceiptContextMismatch);
        }
        if receipt.claim_id != claim.claim_id() {
            return Err(ContractError::ClaimIdMismatch);
        }
        if !root_source.is_finalized(receipt) {
            return Err(ContractError::SourceBlockNotFinalized);
        }
        let expected_leaf = zkverify_statement_leaf(manifest, &raw);
        if receipt.statement_leaf != expected_leaf {
            return Err(ContractError::StatementLeafMismatch);
        }
        let computed_root = reference_merkle_root(
            receipt.statement_leaf,
            receipt.leaf_count,
            receipt.leaf_index,
            &receipt.merkle_path,
        )?;
        let authenticated_root = root_source
            .authenticated_root(receipt)
            .ok_or(ContractError::ReceiptRootMismatch)?;
        if computed_root != authenticated_root {
            return Err(ContractError::ReceiptRootMismatch);
        }

        Ok(SettlementAuthorizationV1 {
            settlement_key: settlement_key(record),
            claim_id: claim.claim_id(),
            primary_transition_id: record.primary_transition_id,
            accepted_root: record.accepted_root,
        })
    }
}

/// Compute the route/raw preclaim bound by the signed PFR.
pub fn preclaim_hash(route_id: &Hash32, raw: &CanonicalRawStatement) -> Hash32 {
    sha256_parts(&[PRECLAIM_DOMAIN, route_id, raw.as_bytes()])
}

/// Compute the route-independent economic exactly-once key from signed data.
pub fn settlement_key(record: &PrimaryFinalityRecordV1) -> Hash32 {
    sha256(&settlement_key_preimage(
        &record.primary_transition_id,
        record.intended_destination,
        record.action_kind,
    ))
}

/// Assemble the canonical route-independent settlement-key preimage.
///
/// The order is domain, primary transition ID, destination chain ID as LE64,
/// destination consumer bytes32, and the action-kind byte. A route ID is
/// deliberately absent so route rotation cannot change economic identity.
pub fn settlement_key_preimage(
    primary_transition_id: &Hash32,
    intended_destination: DestinationV1,
    action_kind: ActionKindV1,
) -> Vec<u8> {
    let mut bytes =
        Vec::with_capacity(SETTLEMENT_KEY_DOMAIN.len() + 32 + std::mem::size_of::<u64>() + 32 + 1);
    bytes.extend_from_slice(SETTLEMENT_KEY_DOMAIN);
    bytes.extend_from_slice(primary_transition_id);
    intended_destination.append_to(&mut bytes);
    bytes.push(action_kind as u8);
    bytes
}

/// Content ID of the only public-values digest adapter executed here.
pub fn reference_digest_adapter_id() -> Hash32 {
    sha256(DIGEST_ADAPTER_PROFILE)
}

/// Content ID of the only zkVerify `Pubs` adapter executed here.
pub fn reference_pubs_adapter_id() -> Hash32 {
    sha256(PUBS_ADAPTER_PROFILE)
}

/// Full SHA-256 followed by the pinned, non-injective 253-bit truncation.
///
/// The digest is interpreted as an unsigned big-endian integer after clearing
/// the top three bits, then serialized as canonical little-endian PI[1]. No
/// field reduction occurs.
pub fn project_public_values_digest(raw: &CanonicalRawStatement) -> Bn254Fr {
    let mut projected_be = raw.full_sha256();
    projected_be[0] &= 0x1f;
    projected_be.reverse();
    Bn254Fr(projected_be)
}

/// Build ordered zkVerify `Pubs = LE32(PI[0]) || LE32(PI[1])`.
pub fn zkverify_pubs(manifest: &RouteManifestV1, raw: &CanonicalRawStatement) -> [u8; 64] {
    let mut pubs = [0u8; 64];
    pubs[..32].copy_from_slice(&manifest.expected_program_vk.0);
    pubs[32..].copy_from_slice(&project_public_values_digest(raw).0);
    pubs
}

/// Reconstruct the pinned zkVerify statement leaf from route data and raw192.
pub fn zkverify_statement_leaf(manifest: &RouteManifestV1, raw: &CanonicalRawStatement) -> Hash32 {
    let pubs_hash = keccak256(&zkverify_pubs(manifest, raw));
    let mut preimage = [0u8; 128];
    preimage[..32].copy_from_slice(&manifest.zkverify_context_hash);
    preimage[32..64].copy_from_slice(&manifest.groth16_vk_hash);
    preimage[64..96].copy_from_slice(&manifest.verifier_version_hash);
    preimage[96..].copy_from_slice(&pubs_hash);
    keccak256(&preimage)
}

fn validate_manifest(manifest: &RouteManifestV1) -> Result<(), ContractError> {
    if !is_canonical_bn254(&manifest.expected_program_vk.0)
        || manifest.digest_adapter_id != reference_digest_adapter_id()
        || manifest.pubs_adapter_id != reference_pubs_adapter_id()
        || manifest.canonical_codec_version != CANONICAL_CODEC_VERSION
        || manifest.statement_version != WRAP_STATEMENT_VERSION
        || manifest.expected_statement_header[0..2] != WRAP_STATEMENT_VERSION.to_le_bytes()
        || manifest.receipt_merkle_profile != REFERENCE_MERKLE_PROFILE
    {
        return Err(ContractError::InvalidRouteManifest);
    }
    Ok(())
}

fn validate_raw_statement(raw: &[u8; RAW_WRAP_STATEMENT_BYTES]) -> Result<(), ContractError> {
    for scalar in raw.chunks_exact(32) {
        let mut bytes = [0u8; 32];
        bytes.copy_from_slice(scalar);
        if !is_canonical_bn254(&bytes) {
            return Err(ContractError::NonCanonicalStatement);
        }
    }
    if raw[0..2] != WRAP_STATEMENT_VERSION.to_le_bytes()
        || raw[16..32].iter().any(|byte| *byte != 0)
        || raw[136..160].iter().any(|byte| *byte != 0)
    {
        return Err(ContractError::NonCanonicalStatement);
    }
    for index in [1usize, 2, 3, 5] {
        let mut bytes = [0u8; 32];
        bytes.copy_from_slice(&raw[index * 32..(index + 1) * 32]);
        if unpack_digest(&Bn254Fr(bytes)).is_none() {
            return Err(ContractError::NonCanonicalStatement);
        }
    }
    Ok(())
}

fn is_canonical_bn254(le: &[u8; 32]) -> bool {
    let mut be = *le;
    be.reverse();
    be < BN254_R_BE
}

fn reference_merkle_root(
    mut node: Hash32,
    leaf_count: u32,
    leaf_index: u32,
    path: &[Hash32],
) -> Result<Hash32, ContractError> {
    if leaf_count == 0 || !leaf_count.is_power_of_two() || leaf_index >= leaf_count {
        return Err(ContractError::InvalidMerklePath);
    }
    let expected_height = leaf_count.trailing_zeros() as usize;
    if path.len() != expected_height {
        return Err(ContractError::InvalidMerklePath);
    }
    let mut index = leaf_index;
    for sibling in path {
        let mut pair = [0u8; 64];
        if index & 1 == 0 {
            pair[..32].copy_from_slice(&node);
            pair[32..].copy_from_slice(sibling);
        } else {
            pair[..32].copy_from_slice(sibling);
            pair[32..].copy_from_slice(&node);
        }
        node = keccak256(&pair);
        index >>= 1;
    }
    Ok(node)
}

fn sha256(bytes: &[u8]) -> Hash32 {
    Sha256::digest(bytes).into()
}

fn sha256_parts(parts: &[&[u8]]) -> Hash32 {
    let mut hash = Sha256::new();
    for part in parts {
        hash.update(part);
    }
    hash.finalize().into()
}

fn keccak256(bytes: &[u8]) -> Hash32 {
    Keccak256::digest(bytes).into()
}
