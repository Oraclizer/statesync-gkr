#![allow(missing_docs)]

#[path = "../examples/receipt_gated_transition_v1.rs"]
#[allow(dead_code)]
mod adapter;

use adapter::{
    LifecycleStatus, ReferenceApplicationState, TransitionError, TransitionRequest,
    VerifiedReadOnlyInputs, canonical_bytes, decode_canonical_bytes,
};
use statesync_gkr::wrap::risc0_destination_policy::ReceiptRootQuorumVectorV1;
use statesync_gkr::wrap::risc0_route_b_manifest::Risc0RouteBManifestVectorV1;

const ROUTE: &str = include_str!("vectors/risc0-route-b-volta-2.0.0-runtime-rebind-v1.json");
const DESTINATION: &str = include_str!("vectors/risc0-route-b-destination-policy-v1.json");
const PREDECESSOR: [u8; 32] = [0x11; 32];

fn fixture() -> Result<(VerifiedReadOnlyInputs, TransitionRequest), String> {
    let inputs = VerifiedReadOnlyInputs::load(ROUTE, DESTINATION)?;
    let request = inputs.honest_request(PREDECESSOR)?;
    Ok((inputs, request))
}

fn assert_rejection(
    inputs: &VerifiedReadOnlyInputs,
    request: &TransitionRequest,
    expected: TransitionError,
) {
    let mut state = ReferenceApplicationState::new(PREDECESSOR);
    let before = state.state_digest();
    let events = state.event_count();
    assert_eq!(state.apply(inputs, request), Err(expected));
    assert_eq!(state.state_digest(), before);
    assert_eq!(state.event_count(), events);
    assert_eq!(state.application_state(), PREDECESSOR);
}

#[test]
fn exact_frozen_evidence_creates_only_a_local_candidate() -> Result<(), String> {
    let (inputs, request) = fixture()?;
    let mut state = ReferenceApplicationState::new(PREDECESSOR);
    let before = state.state_digest();
    let outcome = state
        .apply(&inputs, &request)
        .map_err(|error| format!("honest transition rejected: {error:?}"))?;
    assert_ne!(state.state_digest(), before);
    assert_eq!(state.application_state(), inputs.accepted_root);
    assert_eq!(state.event_count(), 1);
    assert_eq!(outcome.accepted_root, inputs.accepted_root);
    assert!(!outcome.secondary_finalized);
    Ok(())
}

#[test]
fn each_owned_binding_fails_closed_without_state_or_event_change() -> Result<(), String> {
    let (inputs, honest) = fixture()?;

    let mut changed = honest.clone();
    changed.anchors.product_commit[0] ^= 1;
    assert_rejection(&inputs, &changed, TransitionError::FrozenInput);

    changed = honest.clone();
    changed.route_id[0] ^= 1;
    assert_rejection(&inputs, &changed, TransitionError::RouteManifest);

    for selector in 0..4 {
        changed = honest.clone();
        match selector {
            0 => changed.program_binary_size += 1,
            1 => changed.program_binary_sha256[0] ^= 1,
            2 => changed.image_id[0] ^= 1,
            _ => changed.raw_guest_elf_sha256[0] ^= 1,
        }
        assert_rejection(&inputs, &changed, TransitionError::ProgramIdentity);
    }

    changed = honest.clone();
    changed.raw192_sha256[0] ^= 1;
    assert_rejection(&inputs, &changed, TransitionError::RawStatement);

    changed = honest.clone();
    changed.raw_statement[0] ^= 0x80;
    assert_rejection(&inputs, &changed, TransitionError::NonCanonicalStatement);

    changed = honest.clone();
    changed.statement_leaf[0] ^= 1;
    assert_rejection(&inputs, &changed, TransitionError::StatementLeaf);

    changed = honest.clone();
    changed.primary_finality_record_id[0] ^= 1;
    assert_rejection(&inputs, &changed, TransitionError::PrimaryFinality);

    changed = honest.clone();
    changed.primary_finality_committed = false;
    assert_rejection(&inputs, &changed, TransitionError::PrimaryFinality);

    changed = honest.clone();
    changed.source_network_id[0] ^= 1;
    assert_rejection(&inputs, &changed, TransitionError::SourceBinding);

    changed = honest.clone();
    changed.destination_chain_id += 1;
    assert_rejection(&inputs, &changed, TransitionError::DestinationBinding);

    changed = honest.clone();
    changed.destination_consumer[31] ^= 1;
    assert_rejection(&inputs, &changed, TransitionError::DestinationBinding);

    changed = honest.clone();
    changed.domain_id += 1;
    assert_rejection(&inputs, &changed, TransitionError::DomainBinding);

    changed = honest.clone();
    changed.aggregation_id += 1;
    assert_rejection(&inputs, &changed, TransitionError::AggregationBinding);

    changed = honest.clone();
    changed.leaf_count = 2;
    assert_rejection(&inputs, &changed, TransitionError::AggregationBinding);

    changed = honest.clone();
    changed.leaf_index = 1;
    assert_rejection(&inputs, &changed, TransitionError::ReceiptShape);

    changed = honest.clone();
    changed.merkle_path.push([0u8; 32]);
    assert_rejection(&inputs, &changed, TransitionError::ReceiptShape);

    changed = honest.clone();
    changed.authenticated_receipt_root[0] ^= 1;
    assert_rejection(&inputs, &changed, TransitionError::ReceiptRoot);

    changed = honest.clone();
    changed.lifecycle.registered_revision = 2;
    assert_rejection(&inputs, &changed, TransitionError::LifecycleRevision);

    changed = honest.clone();
    changed.settlement_key[0] ^= 1;
    assert_rejection(&inputs, &changed, TransitionError::SettlementKey);

    changed = honest.clone();
    changed.claim_id[0] ^= 1;
    assert_rejection(&inputs, &changed, TransitionError::SettlementKey);

    changed = honest.clone();
    changed.expected_predecessor[0] ^= 1;
    assert_rejection(&inputs, &changed, TransitionError::Predecessor);

    changed = honest.clone();
    changed.next_application_state[0] ^= 1;
    assert_rejection(&inputs, &changed, TransitionError::Predecessor);
    Ok(())
}

#[test]
fn lifecycle_matrix_matches_the_read_only_v2_semantics() -> Result<(), String> {
    let (inputs, honest) = fixture()?;

    let mut draining = honest.clone();
    draining.lifecycle.status = LifecycleStatus::Draining;
    draining.lifecycle.current_revision = 2;
    draining.lifecycle.registered_revision = 1;
    draining.lifecycle.draining_from_revision = 1;
    draining.lifecycle.registered_at_block = 110;
    draining.lifecycle.drain_started_at_block = 110;
    draining.lifecycle.consume_until_block = 120;
    draining.lifecycle.destination_block = 119;
    let mut state = ReferenceApplicationState::new(PREDECESSOR);
    state
        .apply(&inputs, &draining)
        .map_err(|error| format!("predrain receipt rejected: {error:?}"))?;

    let mut at_cutoff = draining.clone();
    at_cutoff.lifecycle.destination_block = 120;
    assert_rejection(&inputs, &at_cutoff, TransitionError::LifecycleCutoff);

    let mut postdrain_registration = draining.clone();
    postdrain_registration.lifecycle.registered_at_block = 111;
    assert_rejection(
        &inputs,
        &postdrain_registration,
        TransitionError::LifecycleRevision,
    );

    let mut revoked = honest.clone();
    revoked.lifecycle.status = LifecycleStatus::Revoked;
    assert_rejection(&inputs, &revoked, TransitionError::RouteRevoked);

    let mut replaced = honest.clone();
    replaced.lifecycle.status = LifecycleStatus::Replaced;
    replaced.lifecycle.replacement_route_id = [0x22; 32];
    assert_rejection(&inputs, &replaced, TransitionError::RouteReplaced);

    let mut abandoned = honest.clone();
    abandoned.lifecycle.lineage_abandoned = true;
    assert_rejection(&inputs, &abandoned, TransitionError::LineageAbandoned);

    let mut zero_revision = honest.clone();
    zero_revision.lifecycle.current_revision = 0;
    zero_revision.lifecycle.registered_revision = 0;
    assert_rejection(&inputs, &zero_revision, TransitionError::LifecycleRevision);

    let mut max_boundary = draining.clone();
    max_boundary.lifecycle.destination_block = u64::MAX - 1;
    max_boundary.lifecycle.consume_until_block = u64::MAX;
    let mut boundary_state = ReferenceApplicationState::new(PREDECESSOR);
    boundary_state
        .apply(&inputs, &max_boundary)
        .map_err(|error| format!("max half-open boundary rejected: {error:?}"))?;
    Ok(())
}

#[test]
fn replay_and_existing_coordinate_conflict_are_atomic() -> Result<(), String> {
    let (inputs, mut request) = fixture()?;
    let mut state = ReferenceApplicationState::new(PREDECESSOR);
    state
        .apply(&inputs, &request)
        .map_err(|error| format!("honest transition rejected: {error:?}"))?;
    request.expected_predecessor = inputs.accepted_root;
    let before = state.state_digest();
    let events = state.event_count();
    assert_eq!(
        state.apply(&inputs, &request),
        Err(TransitionError::ClaimReplay)
    );
    assert_eq!(state.state_digest(), before);
    assert_eq!(state.event_count(), events);

    let vector = ReceiptRootQuorumVectorV1::from_json(DESTINATION)?;
    let cases = vector.negative_cases();
    assert!(cases.iter().any(|case| {
        case.id == "same_coordinate_metadata_conflict" && case.expected_error == "RootConflict"
    }));
    assert!(cases
        .iter()
        .any(|case| case.id == "settlement_replay" && case.expected_error == "SettlementReplay"));
    vector.verify_negative_cases()?;
    Ok(())
}

#[test]
fn malformed_noncanonical_and_version_inputs_are_rejected() -> Result<(), String> {
    let (inputs, honest) = fixture()?;
    let canonical = canonical_bytes(&honest);
    let mut truncated = canonical.clone();
    truncated.pop();
    assert_eq!(
        decode_canonical_bytes(&truncated),
        Err(TransitionError::MalformedEncoding)
    );
    let mut extended = canonical.clone();
    extended.push(0);
    assert_eq!(
        decode_canonical_bytes(&extended),
        Err(TransitionError::MalformedEncoding)
    );
    let mut bad_domain = canonical.clone();
    bad_domain[0] ^= 1;
    assert_eq!(
        decode_canonical_bytes(&bad_domain),
        Err(TransitionError::MalformedEncoding)
    );
    let status_offset = canonical.len() - 218;
    let mut bad_status = canonical.clone();
    bad_status[status_offset] = 0;
    assert_eq!(
        decode_canonical_bytes(&bad_status),
        Err(TransitionError::NonCanonicalEncoding)
    );
    let abandoned_offset = canonical.len() - 161;
    let mut bad_boolean = canonical.clone();
    bad_boolean[abandoned_offset] = 2;
    assert_eq!(
        decode_canonical_bytes(&bad_boolean),
        Err(TransitionError::NonCanonicalEncoding)
    );

    let mut wrong_oip = honest.clone();
    wrong_oip.oip_semantic_version = (0, 6, 0);
    assert_rejection(&inputs, &wrong_oip, TransitionError::WrongVersion);
    let mut wrong_inner = honest.clone();
    wrong_inner.inner_proof_version = 2;
    assert_rejection(&inputs, &wrong_inner, TransitionError::WrongVersion);
    let mut wrong_codec = honest.clone();
    wrong_codec.transition_codec_version = 2;
    assert_rejection(&inputs, &wrong_codec, TransitionError::WrongVersion);

    let unknown = DESTINATION.replacen('{', "{\"unknown\":0,", 1);
    assert!(ReceiptRootQuorumVectorV1::from_json(&unknown).is_err());
    let duplicate = DESTINATION.replacen(
        "\"vector_version\": 1,",
        "\"vector_version\": 1,\"vector_version\": 1,",
        1,
    );
    assert!(ReceiptRootQuorumVectorV1::from_json(&duplicate).is_err());
    let route_unknown = ROUTE.replacen('{', "{\"unknown\":0,", 1);
    assert!(Risc0RouteBManifestVectorV1::from_json(&route_unknown).is_err());
    Ok(())
}

#[test]
fn fixed_seed_property_mutations_never_change_rejected_state() -> Result<(), String> {
    let (inputs, honest) = fixture()?;
    let mut seed = 0x0001_0203_0405_0607u64;
    for iteration in 0..512 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        let index = (seed as usize) % 32;
        let mut changed = honest.clone();
        let expected = match iteration % 8 {
            0 => {
                changed.route_id[index] ^= 1;
                TransitionError::RouteManifest
            }
            1 => {
                changed.program_binary_sha256[index] ^= 1;
                TransitionError::ProgramIdentity
            }
            2 => {
                changed.image_id[index] ^= 1;
                TransitionError::ProgramIdentity
            }
            3 => {
                changed.raw192_sha256[index] ^= 1;
                TransitionError::RawStatement
            }
            4 => {
                changed.statement_leaf[index] ^= 1;
                TransitionError::StatementLeaf
            }
            5 => {
                changed.primary_finality_record_id[index] ^= 1;
                TransitionError::PrimaryFinality
            }
            6 => {
                changed.authenticated_receipt_root[index] ^= 1;
                TransitionError::ReceiptRoot
            }
            _ => {
                changed.expected_predecessor[index] ^= 1;
                TransitionError::Predecessor
            }
        };
        assert_rejection(&inputs, &changed, expected);
    }
    Ok(())
}
