//! Destination receipt-root authority, registry, attachment, and replay battery.

use statesync_gkr::wrap::risc0_destination_policy::{
    AUTHORIZATION_PREIMAGE_BYTES, DestinationReplayError, RECEIPT_ROOT_QUORUM_DOMAIN,
    ReceiptRootPolicyError, ReceiptRootQuorumVectorV1, ReferenceDestinationReplayRegistry,
    ReferenceReceiptRootRegistry, RootRegistrationOutcome, one_leaf_receipt_root,
    recover_evm_signer, validate_receipt_attachment,
};
use statesync_gkr::wrap::settlement::{ContractError, ReceiptEvidenceV1, RouteProofIdentityV1};
use statesync_gkr::wrap::statement::Bn254Fr;

const VECTOR: &str = include_str!("vectors/risc0-route-b-destination-policy-v1.json");

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

fn root_state(
    registry: &ReferenceReceiptRootRegistry,
    authorization: &statesync_gkr::wrap::risc0_destination_policy::ReceiptRootAuthorizationV1,
) -> (usize, u64, u64, Option<Vec<u8>>) {
    (
        registry.len(),
        registry.next_authorization_nonce(),
        registry.accepted_transition_count(),
        registry
            .registered_root(&authorization.coordinate())
            .map(|record| record.authorization.canonical_preimage()),
    )
}

fn receipt_from(
    authorization: &statesync_gkr::wrap::risc0_destination_policy::ReceiptRootAuthorizationV1,
    statement: [u8; 32],
) -> ReceiptEvidenceV1 {
    ReceiptEvidenceV1 {
        source_block_hash: authorization.source_block_hash,
        source_block_height: authorization.source_block_number,
        zkverify_network_id: authorization.source_network_id,
        zkverify_runtime_id: authorization.source_runtime_id,
        zkverify_context_hash: authorization.verification_context_hash,
        domain_id: authorization.domain_id,
        aggregation_id: authorization.aggregation_id,
        statement_leaf: statement,
        leaf_count: 1,
        leaf_index: 0,
        merkle_path: Vec::new(),
        claim_id: [0x44; 32],
        proof_identity: RouteProofIdentityV1 {
            program_vk_projection: Bn254Fr([0; 32]),
            groth16_vk_hash: [0x55; 32],
            groth16_setup_id: [0x66; 32],
        },
    }
}

#[test]
fn vector_recomputes_payload_digest_and_coordinate() -> Result<(), String> {
    let vector = ReceiptRootQuorumVectorV1::from_json(VECTOR)?;
    let computed = vector.compute()?;
    println!("source_network_id={}", hex(&computed.source_network_id));
    println!("source_runtime_id={}", hex(&computed.source_runtime_id));
    println!("canonical_preimage={}", hex(&computed.canonical_preimage));
    println!("signing_digest={}", hex(&computed.signing_digest));
    println!("coordinate_id={}", hex(&computed.coordinate_id));
    println!("receipt_root={}", hex(&computed.receipt_root));
    println!("claim_id={}", hex(&computed.claim_id));
    println!("pfr_role_digest={}", hex(&computed.pfr_role_digest));
    println!("settlement_key={}", hex(&computed.settlement_key));
    vector.verify_expected()?;
    let authorization = vector.authorization();
    let (statement, leaf_index, merkle_path) = vector.receipt_fixture();
    assert_eq!(
        computed.canonical_preimage.len(),
        AUTHORIZATION_PREIMAGE_BYTES
    );
    assert_eq!(leaf_index, 0);
    assert!(merkle_path.is_empty());
    assert_eq!(computed.receipt_root, one_leaf_receipt_root(&statement));
    assert_eq!(computed.receipt_root, authorization.root);
    assert_eq!(
        computed.raw_accepted_root,
        vector.settlement_raw_statement()?.accepted_root()
    );
    assert_eq!(computed.claim_id, vector.replay_keys()?.0);
    assert_ne!(computed.claim_id, vector.replay_keys()?.1);
    assert_eq!(computed.pfr_role_digest, vector.pfr_only_digest());
    assert_eq!(RECEIPT_ROOT_QUORUM_DOMAIN, b"SSGKR_RECEIPT_ROOT_QUORUM_V1");
    assert_ne!(
        RECEIPT_ROOT_QUORUM_DOMAIN,
        b"ssgkr/primary-finality-record/v1"
    );
    Ok(())
}

#[test]
fn registration_replay_conflict_and_every_mutation_leave_state_unchanged() -> Result<(), String> {
    let vector = ReceiptRootQuorumVectorV1::from_json(VECTOR)?;
    let authorization = vector.authorization();
    let attesters = vector.attesting_signers();
    let expected = vector.expected_outcome();
    let mut registry =
        ReferenceReceiptRootRegistry::new(vector.policy()).map_err(|error| error.to_string())?;
    assert_eq!(registry.len() as u64, expected.root_registry_before);
    assert_eq!(
        registry.accepted_transition_count(),
        expected.root_transition_count_before
    );
    assert_eq!(
        registry.next_authorization_nonce(),
        expected.next_nonce_before
    );
    assert_eq!(
        registry.register_signatures(authorization, &vector.attesting_signatures()),
        Ok(RootRegistrationOutcome::Registered)
    );
    assert_eq!(
        format!("{:?}", RootRegistrationOutcome::Registered),
        expected.registration_result
    );
    assert_eq!(registry.len() as u64, expected.root_registry_after);
    assert_eq!(
        registry.accepted_transition_count(),
        expected.root_transition_count_after
    );
    assert_eq!(
        registry.next_authorization_nonce(),
        expected.next_nonce_after
    );

    let sealed = root_state(&registry, &authorization);
    assert_eq!(
        registry.register(authorization, &attesters),
        Err(ReceiptRootPolicyError::AuthorizationReplay)
    );
    assert_eq!(expected.authorization_replay_error, "AuthorizationReplay");
    assert_eq!(root_state(&registry, &authorization), sealed);

    let mut conflict = authorization;
    conflict.root[0] ^= 1;
    assert_eq!(
        registry.register(conflict, &attesters),
        Err(ReceiptRootPolicyError::RootConflict)
    );
    assert_eq!(expected.coordinate_conflict_error, "RootConflict");
    assert_eq!(root_state(&registry, &authorization), sealed);

    for mutation in 0..12 {
        let mut changed = authorization;
        let expected_error = match mutation {
            0 => {
                changed.signer_set_epoch += 1;
                ReceiptRootPolicyError::RootConflict
            }
            1 => {
                changed.source_network_id[0] ^= 1;
                ReceiptRootPolicyError::AuthorityContextMismatch
            }
            2 => {
                changed.source_genesis_hash[0] ^= 1;
                ReceiptRootPolicyError::RootConflict
            }
            3 => {
                changed.source_runtime_id[0] ^= 1;
                ReceiptRootPolicyError::RootConflict
            }
            4 => {
                changed.verification_context_hash[0] ^= 1;
                ReceiptRootPolicyError::RootConflict
            }
            5 => {
                changed.domain_id += 1;
                ReceiptRootPolicyError::AuthorityContextMismatch
            }
            6 => {
                changed.source_block_number += 1;
                ReceiptRootPolicyError::RootConflict
            }
            7 => {
                changed.source_block_hash[0] ^= 1;
                ReceiptRootPolicyError::RootConflict
            }
            8 => {
                changed.aggregation_id += 1;
                ReceiptRootPolicyError::UnexpectedAuthorizationNonce
            }
            9 => {
                changed.root[0] ^= 1;
                ReceiptRootPolicyError::RootConflict
            }
            10 => {
                changed.leaf_count = 2;
                ReceiptRootPolicyError::RootConflict
            }
            11 => {
                changed.authorization_nonce += 1;
                ReceiptRootPolicyError::RootConflict
            }
            _ => unreachable!(),
        };
        assert_eq!(registry.register(changed, &attesters), Err(expected_error));
        assert_eq!(root_state(&registry, &authorization), sealed);
    }

    let (pfr_only_signer, pfr_only_signature) = vector.pfr_only_attestation();
    assert_eq!(
        recover_evm_signer(&vector.pfr_only_digest(), &pfr_only_signature),
        Ok(pfr_only_signer)
    );
    let cross_role_signer =
        recover_evm_signer(&authorization.signing_digest(), &pfr_only_signature)
            .map_err(|error| error.to_string())?;
    assert_ne!(cross_role_signer, pfr_only_signer);
    assert_eq!(
        registry.register(authorization, &[cross_role_signer]),
        Err(ReceiptRootPolicyError::UnauthorizedAttester)
    );
    assert_eq!(root_state(&registry, &authorization), sealed);
    Ok(())
}

#[test]
fn signer_sets_and_strict_next_nonce_fail_closed() -> Result<(), String> {
    let vector = ReceiptRootQuorumVectorV1::from_json(VECTOR)?;
    let authorization = vector.authorization();
    let signers = vector.attesting_signers();

    let mut zero_policy = vector.policy();
    zero_policy.configured_signers[0] = [0u8; 20];
    assert!(matches!(
        ReferenceReceiptRootRegistry::new(zero_policy),
        Err(ReceiptRootPolicyError::ZeroConfiguredSigner)
    ));
    let mut duplicate_policy = vector.policy();
    duplicate_policy.configured_signers[1] = duplicate_policy.configured_signers[0];
    assert!(matches!(
        ReferenceReceiptRootRegistry::new(duplicate_policy),
        Err(ReceiptRootPolicyError::DuplicateConfiguredSigner)
    ));
    let mut unsorted_policy = vector.policy();
    unsorted_policy.configured_signers.swap(0, 1);
    assert!(matches!(
        ReferenceReceiptRootRegistry::new(unsorted_policy),
        Err(ReceiptRootPolicyError::ConfiguredSignersNotSorted)
    ));
    let mut invalid_threshold = vector.policy();
    invalid_threshold.threshold = 4;
    assert!(matches!(
        ReferenceReceiptRootRegistry::new(invalid_threshold),
        Err(ReceiptRootPolicyError::InvalidThreshold)
    ));

    for (attesters, expected) in [
        (vec![[0u8; 20]], ReceiptRootPolicyError::ZeroAttester),
        (
            vec![signers[0], signers[0]],
            ReceiptRootPolicyError::DuplicateAttester,
        ),
        (
            vec![signers[1], signers[0]],
            ReceiptRootPolicyError::AttestersNotSorted,
        ),
        (
            vec![[0xff; 20]],
            ReceiptRootPolicyError::UnauthorizedAttester,
        ),
        (vec![signers[0]], ReceiptRootPolicyError::BelowThreshold),
    ] {
        let mut registry = ReferenceReceiptRootRegistry::new(vector.policy())
            .map_err(|error| error.to_string())?;
        let before = root_state(&registry, &authorization);
        assert_eq!(registry.register(authorization, &attesters), Err(expected));
        assert_eq!(root_state(&registry, &authorization), before);
    }

    for (mutation, expected) in [
        (0, ReceiptRootPolicyError::StaleSignerSetEpoch),
        (1, ReceiptRootPolicyError::AuthorityContextMismatch),
        (2, ReceiptRootPolicyError::InvalidLeafCount),
        (3, ReceiptRootPolicyError::UnexpectedAuthorizationNonce),
    ] {
        let mut changed = authorization;
        match mutation {
            0 => changed.signer_set_epoch = 0,
            1 => changed.source_network_id[0] ^= 1,
            2 => changed.leaf_count = 2,
            3 => changed.authorization_nonce = 2,
            _ => unreachable!(),
        }
        let mut registry = ReferenceReceiptRootRegistry::new(vector.policy())
            .map_err(|error| error.to_string())?;
        let before = root_state(&registry, &authorization);
        assert_eq!(registry.register(changed, &signers), Err(expected));
        assert_eq!(root_state(&registry, &authorization), before);
    }

    let mut registry =
        ReferenceReceiptRootRegistry::new(vector.policy()).map_err(|error| error.to_string())?;
    registry
        .register(authorization, &signers)
        .map_err(|error| error.to_string())?;
    let mut next = authorization;
    next.aggregation_id += 1;
    let sealed = root_state(&registry, &authorization);
    assert_eq!(
        registry.register(next, &signers),
        Err(ReceiptRootPolicyError::UnexpectedAuthorizationNonce)
    );
    assert_eq!(root_state(&registry, &authorization), sealed);
    next.authorization_nonce = 3;
    assert_eq!(
        registry.register(next, &signers),
        Err(ReceiptRootPolicyError::UnexpectedAuthorizationNonce)
    );
    assert_eq!(root_state(&registry, &authorization), sealed);
    next.authorization_nonce = 2;
    assert_eq!(
        registry.register(next, &signers),
        Ok(RootRegistrationOutcome::Registered)
    );
    Ok(())
}

#[test]
fn exact_single_leaf_attachment_is_enforced() -> Result<(), String> {
    let vector = ReceiptRootQuorumVectorV1::from_json(VECTOR)?;
    let authorization = vector.authorization();
    let mut registry =
        ReferenceReceiptRootRegistry::new(vector.policy()).map_err(|error| error.to_string())?;
    registry
        .register(authorization, &vector.attesting_signers())
        .map_err(|error| error.to_string())?;
    let (statement, leaf_index, merkle_path) = vector.receipt_fixture();
    assert_eq!(leaf_index, 0);
    assert!(merkle_path.is_empty());
    let receipt = receipt_from(&authorization, statement);
    validate_receipt_attachment(&receipt, authorization.root)
        .map_err(|error| format!("honest attachment failed: {error:?}"))?;
    let sealed = root_state(&registry, &authorization);

    let mut wrong_statement = receipt.clone();
    wrong_statement.statement_leaf[0] ^= 1;
    assert_eq!(
        validate_receipt_attachment(&wrong_statement, authorization.root),
        Err(ContractError::ReceiptRootMismatch)
    );
    assert_eq!(root_state(&registry, &authorization), sealed);

    let mut wrong_root = authorization.root;
    wrong_root[0] ^= 1;
    assert_eq!(
        validate_receipt_attachment(&receipt, wrong_root),
        Err(ContractError::ReceiptRootMismatch)
    );
    assert_eq!(root_state(&registry, &authorization), sealed);

    let mut wrong_index = receipt.clone();
    wrong_index.leaf_index = 1;
    assert_eq!(
        validate_receipt_attachment(&wrong_index, authorization.root),
        Err(ContractError::InvalidMerklePath)
    );
    assert_eq!(root_state(&registry, &authorization), sealed);

    let mut nonempty_path = receipt.clone();
    nonempty_path.merkle_path.push([0u8; 32]);
    assert_eq!(
        validate_receipt_attachment(&nonempty_path, authorization.root),
        Err(ContractError::InvalidMerklePath)
    );
    assert_eq!(root_state(&registry, &authorization), sealed);

    let mut count_two_empty = receipt.clone();
    count_two_empty.leaf_count = 2;
    assert_eq!(
        validate_receipt_attachment(&count_two_empty, authorization.root),
        Err(ContractError::InvalidMerklePath)
    );
    assert_eq!(root_state(&registry, &authorization), sealed);
    Ok(())
}

#[test]
fn claim_and_settlement_replay_rejections_are_atomic() -> Result<(), String> {
    let vector = ReceiptRootQuorumVectorV1::from_json(VECTOR)?;
    let expected = vector.expected_outcome();
    let (claim_id, settlement_key) = vector.replay_keys()?;
    let mut replay = ReferenceDestinationReplayRegistry::default();
    assert_eq!(
        replay.snapshot().consumed_claims as u64,
        expected.replay_claim_counts.0
    );
    assert_eq!(
        replay.snapshot().consumed_settlements as u64,
        expected.replay_settlement_counts.0
    );
    replay
        .consume(claim_id, settlement_key)
        .map_err(|error| format!("honest replay registration failed: {error:?}"))?;
    let sealed = replay.snapshot();
    assert_eq!(
        sealed.consumed_claims as u64,
        expected.replay_claim_counts.1
    );
    assert_eq!(
        sealed.consumed_settlements as u64,
        expected.replay_settlement_counts.1
    );
    assert_eq!(
        sealed.accepted_transition_count,
        expected.replay_transition_counts.1
    );
    assert_eq!(
        replay.consume(claim_id, [0xaa; 32]),
        Err(DestinationReplayError::ClaimReplay)
    );
    assert_eq!(expected.replay_claim_error, "ClaimReplay");
    assert_eq!(replay.snapshot(), sealed);
    assert_eq!(
        replay.consume([0xbb; 32], settlement_key),
        Err(DestinationReplayError::SettlementReplay)
    );
    assert_eq!(expected.replay_settlement_error, "SettlementReplay");
    assert_eq!(replay.snapshot(), sealed);
    Ok(())
}

#[test]
fn vector_parser_rejects_unknown_duplicate_and_noncanonical_hex() -> Result<(), String> {
    let unknown = VECTOR.replacen(
        "\"vector_version\": 1,",
        "\"vector_version\": 1, \"unknown\": 0,",
        1,
    );
    assert!(ReceiptRootQuorumVectorV1::from_json(&unknown).is_err());
    let duplicate = VECTOR.replacen(
        "\"threshold\": 2,",
        "\"threshold\": 2, \"threshold\": 2,",
        1,
    );
    assert!(ReceiptRootQuorumVectorV1::from_json(&duplicate).is_err());
    let uppercase = VECTOR.replacen("0x2b5a", "0x2B5a", 1);
    assert!(ReceiptRootQuorumVectorV1::from_json(&uppercase).is_err());
    let wrong_accepted_root = VECTOR.replacen(
        "\"accepted_root\": \"0x88957f2aa94f0f483d11f6bbc00b37db9fedd7911eee56e15c1661e148453200\"",
        "\"accepted_root\": \"0x89957f2aa94f0f483d11f6bbc00b37db9fedd7911eee56e15c1661e148453200\"",
        1,
    );
    let mutated = ReceiptRootQuorumVectorV1::from_json(&wrong_accepted_root)?;
    assert_eq!(
        mutated.compute(),
        Err("settlement accepted_root label does not match canonical raw192".to_owned())
    );
    Ok(())
}

#[test]
fn negative_case_id_is_a_label_not_semantic_dispatch() -> Result<(), String> {
    let renamed = VECTOR.replacen(
        "\"id\": \"stale_epoch\"",
        "\"id\": \"renamed_label_only\"",
        1,
    );
    ReceiptRootQuorumVectorV1::from_json(&renamed)?.verify_negative_cases()
}

#[test]
fn frozen_negative_matrix_is_complete_and_state_equivalent() -> Result<(), String> {
    let vector = ReceiptRootQuorumVectorV1::from_json(VECTOR)?;
    let cases = vector.negative_cases();
    let expected_ids = [
        "zero_configured_signer",
        "duplicate_configured_signer",
        "unsorted_configured_signers",
        "invalid_threshold",
        "zero_recovered_signer",
        "duplicate_recovered_signer",
        "unsorted_recovered_signers",
        "nonmember_recovered_signer",
        "below_threshold",
        "zero_r_signature",
        "zero_s_signature",
        "high_s_signature",
        "invalid_recovery_id",
        "cross_role_pfr_domain_signature",
        "stale_epoch",
        "authority_context",
        "invalid_leaf_count",
        "skipped_initial_nonce",
        "exact_authorization_replay",
        "same_coordinate_metadata_conflict",
        "reused_next_coordinate_nonce",
        "skipped_next_coordinate_nonce",
        "wrong_statement",
        "wrong_authenticated_root",
        "wrong_leaf_index",
        "nonempty_one_leaf_path",
        "unsafe_leaf_count_two",
        "claim_replay",
        "settlement_replay",
        "root_nonce_counter_overflow",
        "root_event_counter_overflow",
        "replay_event_counter_overflow",
        "accepted_root_label_mismatch",
    ];
    assert_eq!(cases.len(), expected_ids.len());
    for (case, expected_id) in cases.iter().zip(expected_ids) {
        assert_eq!(case.id, expected_id);
        assert!(!case.operation.is_empty());
        assert!(!case.field.is_empty());
        assert!(!case.expected_error.is_empty());
        assert_eq!(case.before_state_digest, case.after_state_digest);
    }
    vector.verify_negative_cases()?;
    Ok(())
}

#[test]
fn signature_fixture_recovers_and_rejects_evm_parity_mutations() -> Result<(), String> {
    const SECP256K1_HALF_N: [u8; 32] = [
        0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0x5d, 0x57, 0x6e, 0x73, 0x57, 0xa4, 0x50, 0x1d, 0xdf, 0xe9, 0x2f, 0x46, 0x68, 0x1b,
        0x20, 0xa0,
    ];
    let vector = ReceiptRootQuorumVectorV1::from_json(VECTOR)?;
    let digest = vector.authorization().signing_digest();
    let signatures = vector.attesting_signatures();
    let expected_signers = vector.attesting_signers();
    assert_eq!(signatures.len(), expected_signers.len());
    for (signature, expected_signer) in signatures.iter().zip(expected_signers) {
        assert!(signature[..32].iter().any(|byte| *byte != 0));
        assert!(signature[32..64].iter().any(|byte| *byte != 0));
        assert!(signature[32..64] <= SECP256K1_HALF_N[..]);
        assert!(matches!(signature[64], 27 | 28));
        assert_eq!(recover_evm_signer(&digest, signature), Ok(expected_signer));
    }
    let (pfr_signer, pfr_signature) = vector.pfr_only_attestation();
    assert!(pfr_signature[..32].iter().any(|byte| *byte != 0));
    assert!(pfr_signature[32..64].iter().any(|byte| *byte != 0));
    assert!(pfr_signature[32..64] <= SECP256K1_HALF_N[..]);
    assert!(matches!(pfr_signature[64], 27 | 28));
    assert_eq!(
        recover_evm_signer(&vector.pfr_only_digest(), &pfr_signature),
        Ok(pfr_signer)
    );

    vector.verify_negative_cases()?;
    Ok(())
}

#[test]
fn typed_negative_interpreter_executes_every_frozen_row() -> Result<(), String> {
    let vector = ReceiptRootQuorumVectorV1::from_json(VECTOR)?;
    let observations = vector.negative_case_observations()?;
    assert_eq!(observations.len(), 33);
    for case in observations {
        assert_eq!(case.before_state_digest, case.after_state_digest);
        assert!(!case.expected_error.is_empty());
    }
    Ok(())
}
