//! Non-deployment receipt-gated OSS/OIP/CDK transition reference.
//!
//! This example consumes the frozen Route B manifest and destination-policy
//! vectors through their existing host-only parsers. It mutates only an
//! in-memory application model. It is not an OIP wire codec, a chain adapter,
//! a CDK backend, a deployment client, or evidence of secondary finality.

#![allow(missing_docs)]

use sha2::{Digest as _, Sha256};
use statesync_gkr::wrap::risc0_destination_policy::{
    ReceiptRootAuthorizationV1, ReceiptRootQuorumVectorV1, ReferenceDestinationReplayRegistry,
    ReferenceReceiptRootRegistry, recover_evm_signer, validate_receipt_attachment,
};
use statesync_gkr::wrap::risc0_route_b_manifest::Risc0RouteBManifestVectorV1;
use statesync_gkr::wrap::settlement::{
    CanonicalRawStatement, DestinationV1, Hash32, ReceiptEvidenceV1, RouteProofIdentityV1,
    settlement_key_preimage,
};
use statesync_gkr::wrap::statement::Bn254Fr;

pub const PROFILE: &str = "ssgkr/receipt-gated-local-transition/v1";
pub const OIP_SEMANTIC_VERSION: (u16, u16, u16) = (0, 5, 0);
pub const INNER_PROOF_VERSION: u16 = 1;
pub const TRANSITION_CODEC_VERSION: u16 = 1;
pub const PROGRAM_BINARY_SIZE: u64 = 706_152;

const CANONICAL_DOMAIN: &[u8] = b"SSGKR_RECEIPT_GATED_LOCAL_TRANSITION_V1";
const STATE_DOMAIN: &[u8] = b"SSGKR_LOCAL_APPLICATION_STATE_V1";

const PRODUCT_COMMIT: &str = "b976643b9500bb019cab0518b8da6bd50ada62fa";
const PRODUCT_TREE: &str = "b3e47f9e03c6a15f5db38b1134e2491862f7eb2f";
const READINESS_INDEX_SHA256: &str =
    "d25c6a2124bf3e0d6625efd3d481fe8354f93b5cbe36ef1ade0bdce806f1c118";
const A14_REPORT_SHA256: &str = "8fb774e9f42ecbbaf4fffded2f0ba979bfeb339b4632b99c70b77ea6e4ff798d";
const A14_MANIFEST_SHA256: &str =
    "79b6f4274e72ce8846ba03e3b7134b7a509c7fed459d828b08e0049d8fe9f8b6";
const EVM_COMMIT: &str = "de13557322237865632a748d1ae6848b9a1d1d15";
const EVM_TREE: &str = "a92dc39e0ef5ce4f3aad7ccc3eeae5ca62c3b521";
const LIFECYCLE_EVIDENCE_SHA256: &str =
    "511d1cb85a508433a4bfd49f545d27049f773eac3a081f6a659502023ca90d19";
const LIFECYCLE_VECTOR_SHA256: &str =
    "089bf1681666d5a0150ebea74296f5f392b552a9cfbc19b90875cc88e05a08af";
const ROUTE_VECTOR_SHA256: &str =
    "0fa1531f62bf1f9a6a4bc7c02cb4c5a452ba06fa47ff9b0dc35a5ca04b8d619b";
const DESTINATION_VECTOR_SHA256: &str =
    "29a4528629d471ab9d3efcefec4a494477a93b5866e689fbeb3010b1e7627141";
const PROGRAM_BINARY_SHA256: &str =
    "7dcb6d1ddd47618f65a250361a4b9e3fdb77be1104f51c66225b78e114c7a9ba";
const IMAGE_ID: &str = "dd947fec1fe270c41bc0457912e1e77427c16797ac47dc6a1c825a9323648643";
const RAW_GUEST_ELF_SHA256: &str =
    "ab6fcf8796d12bddec6eb3fb3a6115272eaada997a40014e3a984384b1897f81";
const RAW192_SHA256: &str = "959550f3847e15ae2d69ab027d8ef59621282eeb758746262205fa3f61b38721";
const STATEMENT_LEAF: &str = "b4b058ae36bcc8357241b0c308630d7ba203bd47726edbad5ed16b04afeb8492";
const ROUTE_ID: &str = "27b40b99a41976f061e94124b84cc8c43ee4e5ed6bad2e94267057e1d375f2ef";
const DESTINATION_CHAIN_ID: u64 = 84_532;
const DESTINATION_CONSUMER: &str =
    "0000000000000000000000000807c544d38ae7729f8798388d89be6502a1e8a8";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrozenInputAnchors {
    pub product_commit: [u8; 20],
    pub product_tree: [u8; 20],
    pub readiness_index_sha256: Hash32,
    pub a14_report_sha256: Hash32,
    pub a14_manifest_sha256: Hash32,
    pub evm_commit: [u8; 20],
    pub evm_tree: [u8; 20],
    pub lifecycle_evidence_sha256: Hash32,
    pub lifecycle_vector_sha256: Hash32,
    pub route_vector_sha256: Hash32,
    pub destination_vector_sha256: Hash32,
}

impl FrozenInputAnchors {
    pub fn exact() -> Result<Self, String> {
        Ok(Self {
            product_commit: decode_fixed_hex(PRODUCT_COMMIT)?,
            product_tree: decode_fixed_hex(PRODUCT_TREE)?,
            readiness_index_sha256: decode_fixed_hex(READINESS_INDEX_SHA256)?,
            a14_report_sha256: decode_fixed_hex(A14_REPORT_SHA256)?,
            a14_manifest_sha256: decode_fixed_hex(A14_MANIFEST_SHA256)?,
            evm_commit: decode_fixed_hex(EVM_COMMIT)?,
            evm_tree: decode_fixed_hex(EVM_TREE)?,
            lifecycle_evidence_sha256: decode_fixed_hex(LIFECYCLE_EVIDENCE_SHA256)?,
            lifecycle_vector_sha256: decode_fixed_hex(LIFECYCLE_VECTOR_SHA256)?,
            route_vector_sha256: decode_fixed_hex(ROUTE_VECTOR_SHA256)?,
            destination_vector_sha256: decode_fixed_hex(DESTINATION_VECTOR_SHA256)?,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum LifecycleStatus {
    Active = 1,
    Draining = 2,
    Revoked = 3,
    Replaced = 4,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LifecycleSnapshot {
    pub status: LifecycleStatus,
    pub current_revision: u64,
    pub registered_revision: u64,
    pub draining_from_revision: u64,
    pub registered_at_block: u64,
    pub drain_started_at_block: u64,
    pub consume_until_block: u64,
    pub destination_block: u64,
    pub lineage_abandoned: bool,
    pub replacement_route_id: Hash32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransitionRequest {
    pub anchors: FrozenInputAnchors,
    pub oip_semantic_version: (u16, u16, u16),
    pub inner_proof_version: u16,
    pub transition_codec_version: u16,
    pub route_id: Hash32,
    pub program_binary_size: u64,
    pub program_binary_sha256: Hash32,
    pub image_id: Hash32,
    pub raw_guest_elf_sha256: Hash32,
    pub raw_statement: [u8; 192],
    pub raw192_sha256: Hash32,
    pub statement_leaf: Hash32,
    pub primary_finality_record_id: Hash32,
    pub primary_finality_committed: bool,
    pub pfr_signing_digest: Hash32,
    pub pfr_signer: [u8; 20],
    pub pfr_signature: [u8; 65],
    pub source_network_id: Hash32,
    pub destination_chain_id: u64,
    pub destination_consumer: Hash32,
    pub domain_id: u32,
    pub aggregation_id: u64,
    pub leaf_count: u32,
    pub leaf_index: u32,
    pub merkle_path: Vec<Hash32>,
    pub authenticated_receipt_root: Hash32,
    pub lifecycle: LifecycleSnapshot,
    pub claim_id: Hash32,
    pub settlement_key: Hash32,
    pub expected_predecessor: Hash32,
    pub next_application_state: Hash32,
}

#[derive(Clone, Debug)]
pub struct VerifiedReadOnlyInputs {
    pub route_id: Hash32,
    pub route_vector_sha256: Hash32,
    pub destination_vector_sha256: Hash32,
    pub raw192_sha256: Hash32,
    pub statement_leaf: Hash32,
    pub authorization: ReceiptRootAuthorizationV1,
    pub primary_finality_record_id: Hash32,
    pub pfr_signing_digest: Hash32,
    pub pfr_signer: [u8; 20],
    pub pfr_signature: [u8; 65],
    pub claim_id: Hash32,
    pub settlement_key: Hash32,
    pub accepted_root: Hash32,
    pub raw_statement: [u8; 192],
    pub receipt_roots: ReferenceReceiptRootRegistry,
}

impl VerifiedReadOnlyInputs {
    pub fn load(route_json: &str, destination_json: &str) -> Result<Self, String> {
        let route_vector_sha256 = sha256(route_json.as_bytes());
        let destination_vector_sha256 = sha256(destination_json.as_bytes());
        if route_vector_sha256 != decode_fixed_hex(ROUTE_VECTOR_SHA256)?
            || destination_vector_sha256 != decode_fixed_hex(DESTINATION_VECTOR_SHA256)?
        {
            return Err("content-addressed vector drift".to_owned());
        }
        let route = Risc0RouteBManifestVectorV1::from_json(route_json)
            .map_err(|error| error.to_string())?;
        let route_computed = route.compute().map_err(|error| error.to_string())?;
        let destination = ReceiptRootQuorumVectorV1::from_json(destination_json)?;
        destination.verify_expected()?;
        let destination_computed = destination.compute()?;
        let raw = destination.settlement_raw_statement()?;
        let (receipt_statement, leaf_index, merkle_path) = destination.receipt_fixture();
        if route_computed.route_id != decode_fixed_hex(ROUTE_ID)?
            || route_computed.raw192_sha256 != destination_computed.raw_statement_sha256
            || route_computed.native_statement != receipt_statement
            || leaf_index != 0
            || !merkle_path.is_empty()
        {
            return Err(
                "Route B and destination-policy fixtures are not exactly linked".to_owned(),
            );
        }
        let mut receipt_roots = ReferenceReceiptRootRegistry::new(destination.policy())
            .map_err(|error| error.to_string())?;
        receipt_roots
            .register_signatures(
                destination.authorization(),
                &destination.attesting_signatures(),
            )
            .map_err(|error| error.to_string())?;
        let (pfr_signer, pfr_signature) = destination.pfr_only_attestation();
        Ok(Self {
            route_id: route_computed.route_id,
            route_vector_sha256,
            destination_vector_sha256,
            raw192_sha256: route_computed.raw192_sha256,
            statement_leaf: route_computed.native_statement,
            authorization: destination.authorization(),
            primary_finality_record_id: destination_computed.pfr_role_digest,
            pfr_signing_digest: destination.pfr_only_digest(),
            pfr_signer,
            pfr_signature,
            claim_id: destination_computed.claim_id,
            settlement_key: destination_computed.settlement_key,
            accepted_root: destination_computed.raw_accepted_root,
            raw_statement: *raw.as_bytes(),
            receipt_roots,
        })
    }

    pub fn honest_request(&self, predecessor: Hash32) -> Result<TransitionRequest, String> {
        Ok(TransitionRequest {
            anchors: FrozenInputAnchors::exact()?,
            oip_semantic_version: OIP_SEMANTIC_VERSION,
            inner_proof_version: INNER_PROOF_VERSION,
            transition_codec_version: TRANSITION_CODEC_VERSION,
            route_id: self.route_id,
            program_binary_size: PROGRAM_BINARY_SIZE,
            program_binary_sha256: decode_fixed_hex(PROGRAM_BINARY_SHA256)?,
            image_id: decode_fixed_hex(IMAGE_ID)?,
            raw_guest_elf_sha256: decode_fixed_hex(RAW_GUEST_ELF_SHA256)?,
            raw_statement: self.raw_statement,
            raw192_sha256: self.raw192_sha256,
            statement_leaf: self.statement_leaf,
            primary_finality_record_id: self.primary_finality_record_id,
            primary_finality_committed: true,
            pfr_signing_digest: self.pfr_signing_digest,
            pfr_signer: self.pfr_signer,
            pfr_signature: self.pfr_signature,
            source_network_id: self.authorization.source_network_id,
            destination_chain_id: DESTINATION_CHAIN_ID,
            destination_consumer: decode_fixed_hex(DESTINATION_CONSUMER)?,
            domain_id: self.authorization.domain_id,
            aggregation_id: self.authorization.aggregation_id,
            leaf_count: self.authorization.leaf_count,
            leaf_index: 0,
            merkle_path: Vec::new(),
            authenticated_receipt_root: self.authorization.root,
            lifecycle: LifecycleSnapshot {
                status: LifecycleStatus::Active,
                current_revision: 1,
                registered_revision: 1,
                draining_from_revision: 0,
                registered_at_block: 100,
                drain_started_at_block: 0,
                consume_until_block: 0,
                destination_block: 101,
                lineage_abandoned: false,
                replacement_route_id: [0u8; 32],
            },
            claim_id: self.claim_id,
            settlement_key: self.settlement_key,
            expected_predecessor: predecessor,
            next_application_state: self.accepted_root,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TransitionError {
    FrozenInput,
    WrongVersion,
    RouteManifest,
    ProgramIdentity,
    NonCanonicalStatement,
    RawStatement,
    StatementLeaf,
    PrimaryFinality,
    SourceBinding,
    DestinationBinding,
    DomainBinding,
    AggregationBinding,
    ReceiptShape,
    ReceiptRoot,
    LifecycleRevision,
    LifecycleCutoff,
    RouteRevoked,
    RouteReplaced,
    LineageAbandoned,
    SettlementKey,
    Predecessor,
    ClaimReplay,
    SettlementReplay,
    ReplayOverflow,
    MalformedEncoding,
    NonCanonicalEncoding,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LocalTransitionCandidate {
    pub candidate_id: Hash32,
    pub accepted_root: Hash32,
    pub secondary_finalized: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LocalTransitionEvent {
    candidate_id: Hash32,
    predecessor: Hash32,
    accepted_root: Hash32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceApplicationState {
    application_state: Hash32,
    replay: ReferenceDestinationReplayRegistry,
    events: Vec<LocalTransitionEvent>,
}

impl ReferenceApplicationState {
    pub fn new(application_state: Hash32) -> Self {
        Self {
            application_state,
            replay: ReferenceDestinationReplayRegistry::default(),
            events: Vec::new(),
        }
    }
    pub fn application_state(&self) -> Hash32 {
        self.application_state
    }
    pub fn event_count(&self) -> usize {
        self.events.len()
    }
    pub fn state_digest(&self) -> Hash32 {
        let mut bytes = Vec::with_capacity(105 + self.events.len() * 96);
        bytes.extend_from_slice(STATE_DOMAIN);
        bytes.extend_from_slice(&self.application_state);
        bytes.extend_from_slice(&self.replay.state_digest());
        bytes.extend_from_slice(&(self.events.len() as u64).to_be_bytes());
        for event in &self.events {
            bytes.extend_from_slice(&event.candidate_id);
            bytes.extend_from_slice(&event.predecessor);
            bytes.extend_from_slice(&event.accepted_root);
        }
        sha256(&bytes)
    }
    pub fn apply(
        &mut self,
        inputs: &VerifiedReadOnlyInputs,
        request: &TransitionRequest,
    ) -> Result<LocalTransitionCandidate, TransitionError> {
        validate_request(self, inputs, request)?;
        let canonical = canonical_bytes(request);
        let decoded = decode_canonical_bytes(&canonical)?;
        if decoded != canonical {
            return Err(TransitionError::NonCanonicalEncoding);
        }
        let candidate_id = sha256(&canonical);
        self.replay
            .consume(request.claim_id, request.settlement_key)
            .map_err(|error| match format!("{error:?}").as_str() {
                "ClaimReplay" => TransitionError::ClaimReplay,
                "SettlementReplay" => TransitionError::SettlementReplay,
                _ => TransitionError::ReplayOverflow,
            })?;
        let predecessor = self.application_state;
        self.application_state = request.next_application_state;
        self.events.push(LocalTransitionEvent {
            candidate_id,
            predecessor,
            accepted_root: request.next_application_state,
        });
        Ok(LocalTransitionCandidate {
            candidate_id,
            accepted_root: request.next_application_state,
            secondary_finalized: false,
        })
    }
}

fn validate_request(
    state: &ReferenceApplicationState,
    inputs: &VerifiedReadOnlyInputs,
    request: &TransitionRequest,
) -> Result<(), TransitionError> {
    if request.anchors != FrozenInputAnchors::exact().map_err(|_| TransitionError::FrozenInput)?
        || request.anchors.route_vector_sha256 != inputs.route_vector_sha256
        || request.anchors.destination_vector_sha256 != inputs.destination_vector_sha256
    {
        return Err(TransitionError::FrozenInput);
    }
    if request.oip_semantic_version != OIP_SEMANTIC_VERSION
        || request.inner_proof_version != INNER_PROOF_VERSION
        || request.transition_codec_version != TRANSITION_CODEC_VERSION
    {
        return Err(TransitionError::WrongVersion);
    }
    if request.route_id != inputs.route_id || request.route_id != hex32(ROUTE_ID)? {
        return Err(TransitionError::RouteManifest);
    }
    if request.program_binary_size != PROGRAM_BINARY_SIZE
        || request.program_binary_sha256 != hex32(PROGRAM_BINARY_SHA256)?
        || request.image_id != hex32(IMAGE_ID)?
        || request.raw_guest_elf_sha256 != hex32(RAW_GUEST_ELF_SHA256)?
    {
        return Err(TransitionError::ProgramIdentity);
    }
    let raw = CanonicalRawStatement::from_bytes(request.raw_statement)
        .map_err(|_| TransitionError::NonCanonicalStatement)?;
    if raw.full_sha256() != request.raw192_sha256
        || request.raw192_sha256 != inputs.raw192_sha256
        || request.raw192_sha256 != hex32(RAW192_SHA256)?
    {
        return Err(TransitionError::RawStatement);
    }
    if request.statement_leaf != inputs.statement_leaf
        || request.statement_leaf != hex32(STATEMENT_LEAF)?
    {
        return Err(TransitionError::StatementLeaf);
    }
    if !request.primary_finality_committed
        || request.primary_finality_record_id != inputs.primary_finality_record_id
        || request.pfr_signing_digest != request.primary_finality_record_id
        || request.pfr_signing_digest != inputs.pfr_signing_digest
        || request.pfr_signer != inputs.pfr_signer
        || request.pfr_signature != inputs.pfr_signature
        || recover_evm_signer(&request.pfr_signing_digest, &request.pfr_signature)
            .map_err(|_| TransitionError::PrimaryFinality)?
            != request.pfr_signer
    {
        return Err(TransitionError::PrimaryFinality);
    }
    let authorization = &inputs.authorization;
    if request.source_network_id != authorization.source_network_id {
        return Err(TransitionError::SourceBinding);
    }
    if request.destination_chain_id != DESTINATION_CHAIN_ID
        || request.destination_consumer != hex32(DESTINATION_CONSUMER)?
    {
        return Err(TransitionError::DestinationBinding);
    }
    if request.domain_id != authorization.domain_id {
        return Err(TransitionError::DomainBinding);
    }
    if request.aggregation_id != authorization.aggregation_id
        || request.leaf_count != authorization.leaf_count
    {
        return Err(TransitionError::AggregationBinding);
    }
    if request.leaf_count != 1 || request.leaf_index != 0 || !request.merkle_path.is_empty() {
        return Err(TransitionError::ReceiptShape);
    }
    let registered = inputs
        .receipt_roots
        .registered_root(&authorization.coordinate())
        .ok_or(TransitionError::ReceiptRoot)?;
    if registered.authorization.root != request.authenticated_receipt_root {
        return Err(TransitionError::ReceiptRoot);
    }
    let receipt = ReceiptEvidenceV1 {
        source_block_hash: authorization.source_block_hash,
        source_block_height: authorization.source_block_number,
        zkverify_network_id: authorization.source_network_id,
        zkverify_runtime_id: authorization.source_runtime_id,
        zkverify_context_hash: authorization.verification_context_hash,
        domain_id: request.domain_id,
        aggregation_id: request.aggregation_id,
        statement_leaf: request.statement_leaf,
        leaf_count: request.leaf_count,
        leaf_index: request.leaf_index,
        merkle_path: request.merkle_path.clone(),
        claim_id: request.claim_id,
        proof_identity: RouteProofIdentityV1 {
            program_vk_projection: Bn254Fr([0u8; 32]),
            groth16_vk_hash: [0u8; 32],
            groth16_setup_id: [0u8; 32],
        },
    };
    validate_receipt_attachment(&receipt, request.authenticated_receipt_root)
        .map_err(|_| TransitionError::ReceiptRoot)?;
    validate_lifecycle(request.lifecycle)?;
    let expected_settlement_key = sha256(&settlement_key_preimage(
        &request.raw192_sha256,
        DestinationV1 {
            chain_id: request.destination_chain_id,
            consumer: request.destination_consumer,
        },
        raw.action_kind()
            .map_err(|_| TransitionError::NonCanonicalStatement)?,
    ));
    if request.claim_id != inputs.claim_id
        || request.settlement_key != inputs.settlement_key
        || request.settlement_key != expected_settlement_key
    {
        return Err(TransitionError::SettlementKey);
    }
    if request.expected_predecessor != state.application_state
        || request.next_application_state != inputs.accepted_root
    {
        return Err(TransitionError::Predecessor);
    }
    Ok(())
}

fn validate_lifecycle(snapshot: LifecycleSnapshot) -> Result<(), TransitionError> {
    if snapshot.lineage_abandoned {
        return Err(TransitionError::LineageAbandoned);
    }
    match snapshot.status {
        LifecycleStatus::Active => {
            if snapshot.current_revision == 0
                || snapshot.registered_revision != snapshot.current_revision
            {
                return Err(TransitionError::LifecycleRevision);
            }
        }
        LifecycleStatus::Draining => {
            if snapshot.draining_from_revision == 0
                || snapshot.registered_revision != snapshot.draining_from_revision
                || snapshot.registered_at_block > snapshot.drain_started_at_block
            {
                return Err(TransitionError::LifecycleRevision);
            }
            if snapshot.destination_block >= snapshot.consume_until_block {
                return Err(TransitionError::LifecycleCutoff);
            }
        }
        LifecycleStatus::Revoked => return Err(TransitionError::RouteRevoked),
        LifecycleStatus::Replaced => return Err(TransitionError::RouteReplaced),
    }
    Ok(())
}

pub fn canonical_bytes(request: &TransitionRequest) -> Vec<u8> {
    let mut out = Vec::with_capacity(900);
    out.extend_from_slice(CANONICAL_DOMAIN);
    out.extend_from_slice(&request.oip_semantic_version.0.to_be_bytes());
    out.extend_from_slice(&request.oip_semantic_version.1.to_be_bytes());
    out.extend_from_slice(&request.oip_semantic_version.2.to_be_bytes());
    out.extend_from_slice(&request.inner_proof_version.to_be_bytes());
    out.extend_from_slice(&request.transition_codec_version.to_be_bytes());
    append_anchors(&mut out, &request.anchors);
    out.extend_from_slice(&request.route_id);
    out.extend_from_slice(&request.program_binary_size.to_be_bytes());
    out.extend_from_slice(&request.program_binary_sha256);
    out.extend_from_slice(&request.image_id);
    out.extend_from_slice(&request.raw_guest_elf_sha256);
    out.extend_from_slice(&request.raw192_sha256);
    out.extend_from_slice(&request.statement_leaf);
    out.extend_from_slice(&request.primary_finality_record_id);
    out.push(u8::from(request.primary_finality_committed));
    out.extend_from_slice(&request.source_network_id);
    out.extend_from_slice(&request.destination_chain_id.to_be_bytes());
    out.extend_from_slice(&request.destination_consumer);
    out.extend_from_slice(&request.domain_id.to_be_bytes());
    out.extend_from_slice(&request.aggregation_id.to_be_bytes());
    out.extend_from_slice(&request.leaf_count.to_be_bytes());
    out.extend_from_slice(&request.leaf_index.to_be_bytes());
    out.extend_from_slice(&(request.merkle_path.len() as u16).to_be_bytes());
    for sibling in &request.merkle_path {
        out.extend_from_slice(sibling);
    }
    out.extend_from_slice(&request.authenticated_receipt_root);
    out.push(request.lifecycle.status as u8);
    out.extend_from_slice(&request.lifecycle.current_revision.to_be_bytes());
    out.extend_from_slice(&request.lifecycle.registered_revision.to_be_bytes());
    out.extend_from_slice(&request.lifecycle.draining_from_revision.to_be_bytes());
    out.extend_from_slice(&request.lifecycle.registered_at_block.to_be_bytes());
    out.extend_from_slice(&request.lifecycle.drain_started_at_block.to_be_bytes());
    out.extend_from_slice(&request.lifecycle.consume_until_block.to_be_bytes());
    out.extend_from_slice(&request.lifecycle.destination_block.to_be_bytes());
    out.push(u8::from(request.lifecycle.lineage_abandoned));
    out.extend_from_slice(&request.lifecycle.replacement_route_id);
    out.extend_from_slice(&request.claim_id);
    out.extend_from_slice(&request.settlement_key);
    out.extend_from_slice(&request.expected_predecessor);
    out.extend_from_slice(&request.next_application_state);
    out
}

fn append_anchors(out: &mut Vec<u8>, anchors: &FrozenInputAnchors) {
    out.extend_from_slice(&anchors.product_commit);
    out.extend_from_slice(&anchors.product_tree);
    out.extend_from_slice(&anchors.readiness_index_sha256);
    out.extend_from_slice(&anchors.a14_report_sha256);
    out.extend_from_slice(&anchors.a14_manifest_sha256);
    out.extend_from_slice(&anchors.evm_commit);
    out.extend_from_slice(&anchors.evm_tree);
    out.extend_from_slice(&anchors.lifecycle_evidence_sha256);
    out.extend_from_slice(&anchors.lifecycle_vector_sha256);
    out.extend_from_slice(&anchors.route_vector_sha256);
    out.extend_from_slice(&anchors.destination_vector_sha256);
}

pub fn decode_canonical_bytes(bytes: &[u8]) -> Result<Vec<u8>, TransitionError> {
    let minimum = CANONICAL_DOMAIN.len()
        + 10
        + 304
        + 32
        + 8
        + 32 * 6
        + 1
        + 32
        + 8
        + 32
        + 4
        + 8
        + 4
        + 4
        + 2
        + 32
        + 1
        + 56
        + 1
        + 32
        + 128;
    if bytes.len() < minimum || !bytes.starts_with(CANONICAL_DOMAIN) {
        return Err(TransitionError::MalformedEncoding);
    }
    let path_len_offset =
        CANONICAL_DOMAIN.len() + 10 + 304 + 32 + 8 + 32 * 6 + 1 + 32 + 8 + 32 + 4 + 8 + 4 + 4;
    let path_len_bytes = bytes
        .get(path_len_offset..path_len_offset + 2)
        .ok_or(TransitionError::MalformedEncoding)?;
    let path_len = usize::from(u16::from_be_bytes([path_len_bytes[0], path_len_bytes[1]]));
    let expected = minimum
        .checked_add(
            path_len
                .checked_mul(32)
                .ok_or(TransitionError::MalformedEncoding)?,
        )
        .ok_or(TransitionError::MalformedEncoding)?;
    if bytes.len() != expected {
        return Err(TransitionError::MalformedEncoding);
    }
    let status_offset = path_len_offset + 2 + path_len * 32 + 32;
    if !matches!(bytes[status_offset], 1..=4) {
        return Err(TransitionError::NonCanonicalEncoding);
    }
    let committed_offset = CANONICAL_DOMAIN.len() + 10 + 304 + 32 + 8 + 32 * 6;
    if bytes[committed_offset] > 1 {
        return Err(TransitionError::NonCanonicalEncoding);
    }
    let abandoned_offset = status_offset + 1 + 56;
    if bytes[abandoned_offset] > 1 {
        return Err(TransitionError::NonCanonicalEncoding);
    }
    Ok(bytes.to_vec())
}

fn sha256(bytes: &[u8]) -> Hash32 {
    Sha256::digest(bytes).into()
}
fn hex32(value: &str) -> Result<Hash32, TransitionError> {
    decode_fixed_hex(value).map_err(|_| TransitionError::FrozenInput)
}

pub fn decode_fixed_hex<const N: usize>(value: &str) -> Result<[u8; N], String> {
    if value.len() != N * 2 || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(format!("expected {} lowercase hex bytes", N));
    }
    if value.bytes().any(|byte| byte.is_ascii_uppercase()) {
        return Err("hex must be lowercase".to_owned());
    }
    let mut out = [0u8; N];
    for (index, slot) in out.iter_mut().enumerate() {
        let start = index * 2;
        *slot =
            u8::from_str_radix(&value[start..start + 2], 16).map_err(|error| error.to_string())?;
    }
    Ok(out)
}

pub fn encode_hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(char::from(DIGITS[usize::from(byte >> 4)]));
        output.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    output
}

fn run() -> Result<(), String> {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() != 3 {
        return Err(
            "usage: receipt_gated_transition_v1 <route-vector> <destination-vector>".to_owned(),
        );
    }
    let route_json = std::fs::read_to_string(&args[1]).map_err(|error| error.to_string())?;
    let destination_json = std::fs::read_to_string(&args[2]).map_err(|error| error.to_string())?;
    let inputs = VerifiedReadOnlyInputs::load(&route_json, &destination_json)?;
    let request = inputs.honest_request([0x11; 32])?;
    let canonical = canonical_bytes(&request);
    println!("profile={PROFILE}");
    println!("oip_semantic_version=0.5.0");
    println!("canonical_bytes=0x{}", encode_hex(&canonical));
    println!("candidate_id=0x{}", encode_hex(&sha256(&canonical)));
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("ERROR: {error}");
        std::process::exit(1);
    }
}
