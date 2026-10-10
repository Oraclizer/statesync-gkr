//! Executable settlement-contract and attack-rejection battery.

use sha2::{Digest as _, Sha256};
use sha3::Keccak256;

use statesync_gkr::wrap::encoding::decode_inner_proof;
use statesync_gkr::wrap::settlement::{
    ActionKindV1, CANONICAL_CODEC_VERSION, CanonicalRawStatement, ContractError, DestinationV1,
    FinalizedReceiptRootSource, Hash32, NewAcceptancePolicy, PrimaryFinalityRecordV1,
    PrimaryFinalityVerifier, PrimaryRecordState, REFERENCE_MERKLE_PROFILE, ReceiptEvidenceV1,
    ReferenceSettlementConsumer, RouteLifecycleEntry, RouteLifecycleState, RouteManifestV1,
    RouteProofIdentityV1, SettlementAttemptV1, SettlementAuthorizationV1, WrapSettlementClaimV1,
    preclaim_hash, project_public_values_digest, reference_digest_adapter_id,
    reference_pubs_adapter_id, settlement_key, zkverify_pubs, zkverify_statement_leaf,
};
use statesync_gkr::wrap::statement::{Bn254Fr, WRAP_STATEMENT_VERSION, wrap_statement_v1};

#[derive(Clone, Copy, Debug)]
struct TestPfrVerifier;

impl PrimaryFinalityVerifier for TestPfrVerifier {
    fn verify(&self, record: &PrimaryFinalityRecordV1, certificate: &[u8]) -> bool {
        record.signer_set_epoch == 7
            && certificate.len() == 33
            && certificate[0] == 1
            && certificate[1..] == record.record_id()
    }
}

#[derive(Clone, Debug)]
struct TestRootSource {
    finalized: bool,
    source_block_hash: Hash32,
    source_block_height: u64,
    zkverify_network_id: Hash32,
    zkverify_runtime_id: Hash32,
    zkverify_context_hash: Hash32,
    domain_id: u32,
    aggregation_id: u64,
    root: Hash32,
}

impl FinalizedReceiptRootSource for TestRootSource {
    fn is_finalized(&self, receipt: &ReceiptEvidenceV1) -> bool {
        self.finalized && self.matches_coordinates(receipt)
    }

    fn authenticated_root(&self, receipt: &ReceiptEvidenceV1) -> Option<Hash32> {
        self.matches_coordinates(receipt).then_some(self.root)
    }
}

impl TestRootSource {
    fn from_receipt(receipt: &ReceiptEvidenceV1) -> Result<Self, String> {
        Ok(Self {
            finalized: true,
            source_block_hash: receipt.source_block_hash,
            source_block_height: receipt.source_block_height,
            zkverify_network_id: receipt.zkverify_network_id,
            zkverify_runtime_id: receipt.zkverify_runtime_id,
            zkverify_context_hash: receipt.zkverify_context_hash,
            domain_id: receipt.domain_id,
            aggregation_id: receipt.aggregation_id,
            root: receipt_root(receipt)?,
        })
    }

    fn matches_coordinates(&self, receipt: &ReceiptEvidenceV1) -> bool {
        self.source_block_hash == receipt.source_block_hash
            && self.source_block_height == receipt.source_block_height
            && self.zkverify_network_id == receipt.zkverify_network_id
            && self.zkverify_runtime_id == receipt.zkverify_runtime_id
            && self.zkverify_context_hash == receipt.zkverify_context_hash
            && self.domain_id == receipt.domain_id
            && self.aggregation_id == receipt.aggregation_id
    }
}

#[derive(Clone, Debug)]
struct Fixture {
    consumer: ReferenceSettlementConsumer,
    manifest: RouteManifestV1,
    route_id: Hash32,
    raw: CanonicalRawStatement,
    record: PrimaryFinalityRecordV1,
    claim: WrapSettlementClaimV1,
    receipt: ReceiptEvidenceV1,
}

impl Fixture {
    fn rebind_record_and_claim(&mut self) {
        self.claim.primary_finality_record_id = self.record.record_id();
        self.receipt.claim_id = self.claim.claim_id();
    }

    fn authorize_with_certificate(
        &mut self,
        certificate: &[u8],
        root: &TestRootSource,
    ) -> Result<SettlementAuthorizationV1, ContractError> {
        let Self {
            consumer,
            record,
            claim,
            receipt,
            ..
        } = self;
        consumer.authorize_new(
            SettlementAttemptV1 {
                claim,
                primary_record: record,
                primary_certificate: certificate,
                receipt,
            },
            &TestPfrVerifier,
            root,
        )
    }

    fn authorize_valid(
        &mut self,
        root: &TestRootSource,
    ) -> Result<SettlementAuthorizationV1, ContractError> {
        let certificate = certificate_for(&self.record, 1);
        self.authorize_with_certificate(&certificate, root)
    }

    fn verify_historical_valid(
        &self,
        root: &TestRootSource,
    ) -> Result<SettlementAuthorizationV1, ContractError> {
        let certificate = certificate_for(&self.record, 1);
        self.consumer.verify_historical(
            SettlementAttemptV1 {
                claim: &self.claim,
                primary_record: &self.record,
                primary_certificate: &certificate,
                receipt: &self.receipt,
            },
            &TestPfrVerifier,
            root,
        )
    }
}

fn id(byte: u8) -> Hash32 {
    [byte; 32]
}

fn certificate_for(record: &PrimaryFinalityRecordV1, verdict: u8) -> [u8; 33] {
    let mut certificate = [0u8; 33];
    certificate[0] = verdict;
    certificate[1..].copy_from_slice(&record.record_id());
    certificate
}

fn receipt_root(receipt: &ReceiptEvidenceV1) -> Result<Hash32, String> {
    if receipt.leaf_count != 2 || receipt.merkle_path.len() != 1 || receipt.leaf_index > 1 {
        return Err("test receipt must use the nontrivial two-leaf profile".into());
    }
    let mut pair = [0u8; 64];
    if receipt.leaf_index == 0 {
        pair[..32].copy_from_slice(&receipt.statement_leaf);
        pair[32..].copy_from_slice(&receipt.merkle_path[0]);
    } else {
        pair[..32].copy_from_slice(&receipt.merkle_path[0]);
        pair[32..].copy_from_slice(&receipt.statement_leaf);
    }
    Ok(Keccak256::digest(pair).into())
}

fn active_lifecycle() -> RouteLifecycleEntry {
    RouteLifecycleEntry {
        state: RouteLifecycleState::Active,
        replacement_route: None,
        new_acceptance: NewAcceptancePolicy::Accept,
        governance_revision: 1,
        effective_height: 1,
    }
}

fn fixture() -> Result<Fixture, String> {
    let envelope = decode_inner_proof(include_bytes!("vectors/inner-proof-v1/update-d24.bin"))
        .map_err(|error| format!("decode fixture: {error:?}"))?;
    let statement = wrap_statement_v1(&envelope.identity, &envelope.public_inputs);
    let raw = CanonicalRawStatement::from_statement(&statement)
        .map_err(|error| format!("canonical raw: {error:?}"))?;
    let destination = DestinationV1 {
        chain_id: 8453,
        consumer: id(0xd0),
    };
    let manifest = RouteManifestV1 {
        vendor_id: id(0x01),
        proof_system_id: id(0x02),
        source_commit: id(0x03),
        toolchain_digest: id(0x04),
        guest_artifact_digest: id(0x05),
        expected_program_vk: Bn254Fr([
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
            0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c,
            0x1d, 0x1e, 0x1f, 0x20,
        ]),
        groth16_vk_hash: id(0x22),
        groth16_setup_id: id(0x23),
        digest_adapter_id: reference_digest_adapter_id(),
        pubs_adapter_id: reference_pubs_adapter_id(),
        zkverify_network_id: id(0x31),
        zkverify_runtime_id: id(0x32),
        zkverify_context_hash: Keccak256::digest(b"groth16").into(),
        verifier_version_hash: Sha256::digest([]).into(),
        zkverify_domain_id: 7,
        canonical_codec_version: CANONICAL_CODEC_VERSION,
        statement_version: WRAP_STATEMENT_VERSION,
        expected_statement_header: raw.statement_header(),
        full_circuit_commitment: raw.circuit_commitment(),
        source: id(0x40),
        destination,
        receipt_merkle_profile: REFERENCE_MERKLE_PROFILE,
    };
    let mut consumer = ReferenceSettlementConsumer::new(destination);
    let route_id = consumer
        .register_route(manifest.clone(), active_lifecycle())
        .map_err(|error| format!("register route: {error:?}"))?;
    let record = PrimaryFinalityRecordV1 {
        primary_transition_id: id(0x50),
        route_id,
        raw_statement_sha256: raw.full_sha256(),
        preclaim_hash: preclaim_hash(&route_id, &raw),
        source: manifest.source,
        intended_destination: destination,
        action_kind: raw
            .action_kind()
            .map_err(|error| format!("action kind: {error:?}"))?,
        checkpoint: 42,
        session_id: id(0x51),
        bvc_id: id(0x52),
        accepted_root: raw.accepted_root(),
        state: PrimaryRecordState::Committed,
        signer_set_epoch: 7,
        issuance_height: 100,
        supersedes_record_id: None,
    };
    let claim = WrapSettlementClaimV1::new(route_id, record.record_id(), raw);
    let leaf = zkverify_statement_leaf(&manifest, &raw);
    let receipt = ReceiptEvidenceV1 {
        source_block_hash: id(0x60),
        source_block_height: 500,
        zkverify_network_id: manifest.zkverify_network_id,
        zkverify_runtime_id: manifest.zkverify_runtime_id,
        zkverify_context_hash: manifest.zkverify_context_hash,
        domain_id: manifest.zkverify_domain_id,
        aggregation_id: 9,
        statement_leaf: leaf,
        leaf_count: 2,
        leaf_index: 1,
        merkle_path: vec![id(0x61)],
        claim_id: claim.claim_id(),
        proof_identity: RouteProofIdentityV1 {
            program_vk_projection: manifest.expected_program_vk,
            groth16_vk_hash: manifest.groth16_vk_hash,
            groth16_setup_id: manifest.groth16_setup_id,
        },
    };
    Ok(Fixture {
        consumer,
        manifest,
        route_id,
        raw,
        record,
        claim,
        receipt,
    })
}

fn independent_pubs_and_leaf(
    manifest: &RouteManifestV1,
    raw: &CanonicalRawStatement,
) -> ([u8; 32], [u8; 64], Hash32) {
    let full_digest: [u8; 32] = Sha256::digest(raw.as_bytes()).into();
    let mut projected_be = full_digest;
    projected_be[0] &= 0x1f;
    let mut pi1_le = projected_be;
    pi1_le.reverse();
    let mut pubs = [0u8; 64];
    pubs[..32].copy_from_slice(&manifest.expected_program_vk.0);
    pubs[32..].copy_from_slice(&pi1_le);
    let pubs_hash: Hash32 = Keccak256::digest(pubs).into();
    let mut statement_preimage = [0u8; 128];
    statement_preimage[..32].copy_from_slice(&manifest.zkverify_context_hash);
    statement_preimage[32..64].copy_from_slice(&manifest.groth16_vk_hash);
    statement_preimage[64..96].copy_from_slice(&manifest.verifier_version_hash);
    statement_preimage[96..].copy_from_slice(&pubs_hash);
    let leaf = Keccak256::digest(statement_preimage).into();
    (pi1_le, pubs, leaf)
}

fn to_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    output
}

fn assert_vector_value(contents: &str, key: &str, bytes: &[u8]) -> Result<(), String> {
    let expected = contents
        .lines()
        .filter_map(|line| line.split_once('='))
        .find_map(|(name, value)| (name == key).then_some(value))
        .ok_or_else(|| format!("golden vector key missing: {key}"))?;
    let actual = to_hex(bytes);
    if actual != expected {
        return Err(format!(
            "golden vector mismatch for {key}: expected {expected}, actual {actual}"
        ));
    }
    Ok(())
}

#[test]
fn update_profile_binds_action_and_new_root_word() -> Result<(), String> {
    let fixture = fixture()?;
    let raw = fixture.raw.as_bytes();
    let mut old_root = [0u8; 32];
    old_root.copy_from_slice(&raw[64..96]);
    let mut new_root = [0u8; 32];
    new_root.copy_from_slice(&raw[96..128]);
    assert_ne!(old_root, new_root);
    assert_eq!(fixture.raw.action_kind(), Ok(ActionKindV1::Update));
    assert_eq!(fixture.raw.accepted_root(), new_root);

    let mut wrong_root = fixture;
    wrong_root.record.accepted_root = old_root;
    wrong_root.rebind_record_and_claim();
    let root = TestRootSource::from_receipt(&wrong_root.receipt)?;
    assert_eq!(
        wrong_root.authorize_valid(&root),
        Err(ContractError::ApplicationContextMismatch)
    );
    Ok(())
}

#[test]
fn manifest_rejects_unknown_adapters_and_enforces_header_policy() -> Result<(), String> {
    let mut fixture = fixture()?;
    let mut unsupported = fixture.manifest.clone();
    unsupported.digest_adapter_id[0] ^= 1;
    assert_eq!(
        fixture
            .consumer
            .register_route(unsupported, active_lifecycle()),
        Err(ContractError::InvalidRouteManifest)
    );

    let mut header_profile = fixture.manifest.clone();
    header_profile.expected_statement_header[2] ^= 1;
    let route_id = fixture
        .consumer
        .register_route(header_profile.clone(), active_lifecycle())
        .map_err(|error| format!("register alternate header: {error:?}"))?;
    let mut record = fixture.record.clone();
    record.route_id = route_id;
    record.preclaim_hash = preclaim_hash(&route_id, &fixture.raw);
    record.issuance_height += 1;
    let claim = WrapSettlementClaimV1::new(route_id, record.record_id(), fixture.raw);
    let mut receipt = fixture.receipt.clone();
    receipt.statement_leaf = zkverify_statement_leaf(&header_profile, &fixture.raw);
    receipt.claim_id = claim.claim_id();
    let certificate = certificate_for(&record, 1);
    let root = TestRootSource::from_receipt(&receipt)?;
    assert_eq!(
        fixture.consumer.authorize_new(
            SettlementAttemptV1 {
                claim: &claim,
                primary_record: &record,
                primary_certificate: &certificate,
                receipt: &receipt,
            },
            &TestPfrVerifier,
            &root,
        ),
        Err(ContractError::ApplicationContextMismatch)
    );
    Ok(())
}

#[test]
fn canonical_codec_two_implementations_match_golden_vector() -> Result<(), String> {
    let fixture = fixture()?;
    let (pi1, pubs, leaf) = independent_pubs_and_leaf(&fixture.manifest, &fixture.raw);
    assert_eq!(project_public_values_digest(&fixture.raw).0, pi1);
    assert_eq!(zkverify_pubs(&fixture.manifest, &fixture.raw), pubs);
    assert_eq!(
        zkverify_statement_leaf(&fixture.manifest, &fixture.raw),
        leaf
    );
    let vector = include_str!("vectors/wrap-settlement-v1-codec.txt");
    assert_vector_value(vector, "raw192", fixture.raw.as_bytes())?;
    assert_vector_value(vector, "sha256", &fixture.raw.full_sha256())?;
    let mut projected_be = fixture.raw.full_sha256();
    projected_be[0] &= 0x1f;
    assert_vector_value(vector, "pi1_be", &projected_be)?;
    assert_vector_value(vector, "pi1_le", &pi1)?;
    assert_vector_value(vector, "pi0_le", &fixture.manifest.expected_program_vk.0)?;
    assert_vector_value(
        vector,
        "context_hash",
        &fixture.manifest.zkverify_context_hash,
    )?;
    assert_vector_value(vector, "vk_hash", &fixture.manifest.groth16_vk_hash)?;
    assert_vector_value(
        vector,
        "version_hash",
        &fixture.manifest.verifier_version_hash,
    )?;
    assert_vector_value(vector, "pubs", &pubs)?;
    assert_vector_value(vector, "pubs_hash", &Keccak256::digest(pubs))?;
    assert_vector_value(vector, "statement_leaf", &leaf)?;
    Ok(())
}

#[test]
fn honest_reference_authorization_passes_once() -> Result<(), String> {
    let mut fixture = fixture()?;
    let root = TestRootSource::from_receipt(&fixture.receipt)?;
    let authorization = fixture
        .authorize_valid(&root)
        .map_err(|error| format!("honest authorization: {error:?}"))?;
    assert_eq!(
        authorization.settlement_key,
        settlement_key(&fixture.record)
    );
    Ok(())
}

#[test]
fn route_rotation_cannot_replay_one_transition() -> Result<(), String> {
    let mut fixture = fixture()?;
    let first_root = TestRootSource::from_receipt(&fixture.receipt)?;
    fixture
        .authorize_valid(&first_root)
        .map_err(|error| format!("first route: {error:?}"))?;

    let mut manifest_b = fixture.manifest.clone();
    manifest_b.vendor_id = id(0x71);
    manifest_b.guest_artifact_digest = id(0x72);
    let route_b = fixture
        .consumer
        .register_route(manifest_b.clone(), active_lifecycle())
        .map_err(|error| format!("second route: {error:?}"))?;
    let mut record_b = fixture.record.clone();
    record_b.route_id = route_b;
    record_b.preclaim_hash = preclaim_hash(&route_b, &fixture.raw);
    record_b.issuance_height += 1;
    let claim_b = WrapSettlementClaimV1::new(route_b, record_b.record_id(), fixture.raw);
    let leaf_b = zkverify_statement_leaf(&manifest_b, &fixture.raw);
    let mut receipt_b = fixture.receipt.clone();
    receipt_b.statement_leaf = leaf_b;
    receipt_b.claim_id = claim_b.claim_id();
    assert_ne!(fixture.claim.claim_id(), claim_b.claim_id());
    assert_eq!(settlement_key(&fixture.record), settlement_key(&record_b));
    let root_b = TestRootSource::from_receipt(&receipt_b)?;
    let certificate_b = certificate_for(&record_b, 1);
    let result = fixture.consumer.authorize_new(
        SettlementAttemptV1 {
            claim: &claim_b,
            primary_record: &record_b,
            primary_certificate: &certificate_b,
            receipt: &receipt_b,
        },
        &TestPfrVerifier,
        &root_b,
    );
    assert_eq!(result, Err(ContractError::SettlementAlreadyConsumed));
    Ok(())
}

#[test]
fn pfr_revision_and_claim_id_change_cannot_replay() -> Result<(), String> {
    let mut fixture = fixture()?;
    let root = TestRootSource::from_receipt(&fixture.receipt)?;
    fixture
        .authorize_valid(&root)
        .map_err(|error| format!("first record: {error:?}"))?;
    let old_record_id = fixture.record.record_id();
    let old_claim_id = fixture.claim.claim_id();
    fixture.record.issuance_height += 1;
    fixture.record.supersedes_record_id = Some(old_record_id);
    fixture.rebind_record_and_claim();
    assert_ne!(old_claim_id, fixture.claim.claim_id());
    let result = fixture.authorize_valid(&root);
    assert_eq!(result, Err(ContractError::SettlementAlreadyConsumed));
    Ok(())
}

#[test]
fn wrong_destination_and_action_kind_are_rejected() -> Result<(), String> {
    let mut destination = fixture()?;
    destination.record.intended_destination.chain_id += 1;
    destination.rebind_record_and_claim();
    let root = TestRootSource::from_receipt(&destination.receipt)?;
    assert_eq!(
        destination.authorize_valid(&root),
        Err(ContractError::ApplicationContextMismatch)
    );

    let mut action = fixture()?;
    action.record.action_kind = ActionKindV1::Membership;
    action.rebind_record_and_claim();
    let root = TestRootSource::from_receipt(&action.receipt)?;
    assert_eq!(
        action.authorize_valid(&root),
        Err(ContractError::ApplicationContextMismatch)
    );
    Ok(())
}

#[test]
fn revoked_route_rejects_new_but_preserves_historical_verification() -> Result<(), String> {
    let mut fixture = fixture()?;
    fixture
        .consumer
        .set_lifecycle(
            fixture.route_id,
            RouteLifecycleEntry {
                state: RouteLifecycleState::Revoked,
                replacement_route: Some(id(0x88)),
                new_acceptance: NewAcceptancePolicy::Reject,
                governance_revision: 2,
                effective_height: 2,
            },
        )
        .map_err(|error| format!("revoke route: {error:?}"))?;
    assert!(
        fixture
            .consumer
            .is_historically_verifiable(&fixture.route_id)
    );
    let root = TestRootSource::from_receipt(&fixture.receipt)?;
    fixture
        .verify_historical_valid(&root)
        .map_err(|error| format!("historical verification: {error:?}"))?;
    assert_eq!(
        fixture.authorize_valid(&root),
        Err(ContractError::RouteRevoked)
    );
    Ok(())
}

#[test]
fn stale_lifecycle_revision_is_rejected() -> Result<(), String> {
    let mut fixture = fixture()?;
    let stale = RouteLifecycleEntry {
        state: RouteLifecycleState::Active,
        replacement_route: None,
        new_acceptance: NewAcceptancePolicy::Accept,
        governance_revision: 1,
        effective_height: 2,
    };
    assert_eq!(
        fixture.consumer.set_lifecycle(fixture.route_id, stale),
        Err(ContractError::StaleLifecycleRevision)
    );
    Ok(())
}

#[test]
fn bad_quorum_or_signature_is_rejected() -> Result<(), String> {
    let mut below_quorum = fixture()?;
    let root = TestRootSource::from_receipt(&below_quorum.receipt)?;
    let below_quorum_certificate = certificate_for(&below_quorum.record, 2);
    assert_eq!(
        below_quorum.authorize_with_certificate(&below_quorum_certificate, &root),
        Err(ContractError::InvalidPrimaryCertificate)
    );
    let mut bad_signature = fixture()?;
    let bad_signature_certificate = certificate_for(&bad_signature.record, 3);
    assert_eq!(
        bad_signature.authorize_with_certificate(&bad_signature_certificate, &root),
        Err(ContractError::InvalidPrimaryCertificate)
    );
    Ok(())
}

#[test]
fn primary_certificate_binds_every_signed_record_field() -> Result<(), String> {
    let mut fixture = fixture()?;
    let certificate = certificate_for(&fixture.record, 1);
    fixture.record.checkpoint += 1;
    fixture.rebind_record_and_claim();
    let root = TestRootSource::from_receipt(&fixture.receipt)?;
    assert_eq!(
        fixture.authorize_with_certificate(&certificate, &root),
        Err(ContractError::InvalidPrimaryCertificate)
    );
    Ok(())
}

#[test]
fn receipt_runtime_domain_and_context_mismatches_are_rejected() -> Result<(), String> {
    for field in 0..3 {
        let mut fixture = fixture()?;
        match field {
            0 => fixture.receipt.zkverify_runtime_id[0] ^= 1,
            1 => fixture.receipt.domain_id += 1,
            _ => fixture.receipt.zkverify_context_hash[0] ^= 1,
        }
        let root = TestRootSource::from_receipt(&fixture.receipt)?;
        assert_eq!(
            fixture.authorize_valid(&root),
            Err(ContractError::ReceiptContextMismatch)
        );
    }
    Ok(())
}

#[test]
fn statement_leaf_and_endian_word_order_mismatches_are_rejected() -> Result<(), String> {
    let mut leaf = fixture()?;
    leaf.receipt.statement_leaf[0] ^= 1;
    let root = TestRootSource::from_receipt(&leaf.receipt)?;
    assert_eq!(
        leaf.authorize_valid(&root),
        Err(ContractError::StatementLeafMismatch)
    );

    let mut wrong_endian = fixture()?;
    let mut wrong_pi1 = wrong_endian.raw.full_sha256();
    wrong_pi1[0] &= 0x1f;
    let mut wrong_pubs = zkverify_pubs(&wrong_endian.manifest, &wrong_endian.raw);
    wrong_pubs[32..].copy_from_slice(&wrong_pi1);
    let pubs_hash: Hash32 = Keccak256::digest(wrong_pubs).into();
    let mut preimage = [0u8; 128];
    preimage[..32].copy_from_slice(&wrong_endian.manifest.zkverify_context_hash);
    preimage[32..64].copy_from_slice(&wrong_endian.manifest.groth16_vk_hash);
    preimage[64..96].copy_from_slice(&wrong_endian.manifest.verifier_version_hash);
    preimage[96..].copy_from_slice(&pubs_hash);
    wrong_endian.receipt.statement_leaf = Keccak256::digest(preimage).into();
    let root = TestRootSource::from_receipt(&wrong_endian.receipt)?;
    assert_eq!(
        wrong_endian.authorize_valid(&root),
        Err(ContractError::StatementLeafMismatch)
    );

    let mut wrong_order = fixture()?;
    let mut swapped = *wrong_order.raw.as_bytes();
    let mut old_root_word = [0u8; 32];
    old_root_word.copy_from_slice(&swapped[64..96]);
    let mut new_root_word = [0u8; 32];
    new_root_word.copy_from_slice(&swapped[96..128]);
    swapped[64..96].copy_from_slice(&new_root_word);
    swapped[96..128].copy_from_slice(&old_root_word);
    let swapped_raw = CanonicalRawStatement::from_bytes(swapped)
        .map_err(|error| format!("swapped canonical raw: {error:?}"))?;
    let (_, _, wrong_leaf) = independent_pubs_and_leaf(&wrong_order.manifest, &swapped_raw);
    wrong_order.receipt.statement_leaf = wrong_leaf;
    let root = TestRootSource::from_receipt(&wrong_order.receipt)?;
    assert_eq!(
        wrong_order.authorize_valid(&root),
        Err(ContractError::StatementLeafMismatch)
    );
    Ok(())
}

#[test]
fn guest_program_vk_groth16_vk_and_setup_mismatches_are_rejected() -> Result<(), String> {
    let cases = [
        ContractError::ProgramVkMismatch,
        ContractError::Groth16VkMismatch,
        ContractError::Groth16SetupMismatch,
    ];
    for expected in cases {
        let mut fixture = fixture()?;
        match expected {
            ContractError::ProgramVkMismatch => {
                fixture.receipt.proof_identity.program_vk_projection.0[0] ^= 1;
            }
            ContractError::Groth16VkMismatch => {
                fixture.receipt.proof_identity.groth16_vk_hash[0] ^= 1;
            }
            ContractError::Groth16SetupMismatch => {
                fixture.receipt.proof_identity.groth16_setup_id[0] ^= 1;
            }
            _ => return Err("unexpected test case".into()),
        }
        let root = TestRootSource::from_receipt(&fixture.receipt)?;
        assert_eq!(fixture.authorize_valid(&root), Err(expected));
    }
    Ok(())
}

#[test]
fn unfinalized_source_block_is_rejected() -> Result<(), String> {
    let mut fixture = fixture()?;
    let mut root = TestRootSource::from_receipt(&fixture.receipt)?;
    root.finalized = false;
    assert_eq!(
        fixture.authorize_valid(&root),
        Err(ContractError::SourceBlockNotFinalized)
    );
    Ok(())
}

#[test]
fn receipt_coordinates_and_authenticated_root_are_bound() -> Result<(), String> {
    for mutation in 0..2 {
        let mut fixture = fixture()?;
        let root = TestRootSource::from_receipt(&fixture.receipt)?;
        if mutation == 0 {
            fixture.receipt.source_block_hash[0] ^= 1;
        } else {
            fixture.receipt.aggregation_id += 1;
        }
        assert_eq!(
            fixture.authorize_valid(&root),
            Err(ContractError::SourceBlockNotFinalized)
        );
    }

    let mut fixture = fixture()?;
    let mut wrong_root = TestRootSource::from_receipt(&fixture.receipt)?;
    wrong_root.root[0] ^= 1;
    assert_eq!(
        fixture.authorize_valid(&wrong_root),
        Err(ContractError::ReceiptRootMismatch)
    );
    Ok(())
}

#[test]
fn malformed_merkle_coordinates_are_rejected() -> Result<(), String> {
    let mut fixture = fixture()?;
    let mut root = TestRootSource::from_receipt(&fixture.receipt)?;
    fixture.receipt.leaf_count = 3;
    root.root = id(0xff);
    assert_eq!(
        fixture.authorize_valid(&root),
        Err(ContractError::InvalidMerklePath)
    );
    Ok(())
}
