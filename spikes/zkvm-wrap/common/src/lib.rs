//! Vendor-neutral N=1 fixture for the zkVM wrap-route spike.
//!
//! This crate deliberately lives outside the production workspace and calls
//! the public `StateSyncProver::wrap_relation` seam without changing the
//! frozen core. Vendor guests consume the same relation fixture; the canonical
//! RISC Zero guest enters through the pinned prepared-material seam.

use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOpKind,
    SmtOperation, SmtParams, SmtWitness,
};
use statesync_gkr::primitives::field::{BaseField, PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{Digest, HashGadget, Poseidon2Gadget};
use statesync_gkr::{PreparedSync, StateSyncGkrConfig, StateSyncProver, SyncRequest};
use std::io::Read;

/// Canonical byte size of the six application-level BN254 scalars.
pub const APPLICATION_STATEMENT_BYTES: usize = 6 * 32;
/// Byte size of the raw selector-plus-length artifact-input header.
pub const ARTIFACT_INPUT_HEADER_BYTES: usize = 1 + 4;
/// Exact byte size of the reviewed d24/A/Membership prepared material.
pub const PINNED_PREPARED_MATERIAL_BYTES: usize =
    statesync_gkr::wrap::prepared::PINNED_D24_A_MEMBERSHIP_MATERIAL_BYTES;
/// Canonical outer framing length field.
pub const PINNED_PREPARED_MATERIAL_LENGTH_LE: [u8; 4] =
    (PINNED_PREPARED_MATERIAL_BYTES as u32).to_le_bytes();

/// Read the exact raw selector/u32-LE-length/material/EOF transport.
///
/// The five-byte header is read on stack and its length is checked before the
/// sole payload allocation. Missing, truncated or trailing input fails closed.
pub fn read_pinned_artifact_input(mut input: impl Read) -> Option<(u8, Vec<u8>)> {
    let mut header = [0u8; ARTIFACT_INPUT_HEADER_BYTES];
    input.read_exact(&mut header).ok()?;
    if header[1..] != PINNED_PREPARED_MATERIAL_LENGTH_LE {
        return None;
    }

    let mut material = vec![0u8; PINNED_PREPARED_MATERIAL_BYTES];
    input.read_exact(&mut material).ok()?;

    let mut trailing = [0u8; 1];
    if input.read(&mut trailing).ok()? != 0 {
        return None;
    }
    Some((header[0], material))
}

/// Checkpoints emitted only by the standalone RISC Zero diagnostic guest.
///
/// The canonical guest does not use this diagnostic surface. Keeping the
/// observer out of the frozen relation lets the diagnostic image attribute
/// coarse stages without instrumenting the canonical image or the frozen core.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum DiagnosticCheckpoint {
    ProverConstructed = 0,
    RelationPrepared = 1,
    FixtureCopied = 2,
    RelationEvaluated = 3,
    StatementEncoded = 4,
}

/// Number of relation checkpoints emitted by [`evaluate_diagnostic`].
pub const DIAGNOSTIC_RELATION_CHECKPOINTS: usize = 5;

/// Adversarial selector understood by both guests.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Case {
    /// Unmodified N=1 membership relation.
    Honest = 0,
    /// Flip one bit in the inner proof payload.
    InnerProofBit = 1,
    /// Replace the operation while preserving the original statement/witness.
    Operation = 2,
    /// Mutate the request public input.
    Request = 3,
    /// Mutate the Merkle witness.
    Witness = 4,
    /// Mutate the encoded circuit identity.
    Identity = 5,
    /// Mutate the encoded protocol version.
    Version = 6,
}

impl Case {
    /// Decode a guest input byte. Unknown selectors fail closed.
    pub fn from_u8(value: u8) -> Option<Self> {
        match value {
            0 => Some(Self::Honest),
            1 => Some(Self::InnerProofBit),
            2 => Some(Self::Operation),
            3 => Some(Self::Request),
            4 => Some(Self::Witness),
            5 => Some(Self::Identity),
            6 => Some(Self::Version),
            _ => None,
        }
    }
}

fn f(value: u32) -> BaseField {
    BaseField::from_u32(value)
}

fn config() -> StateSyncGkrConfig {
    StateSyncGkrConfig {
        smt: SmtParams {
            depth: 24,
            ..Default::default()
        },
        layer_strategy: LayerStrategy::A,
        batching: Default::default(),
    }
}

fn siblings() -> Vec<Digest<BaseField>> {
    (0..24)
        .map(|index| Digest([f(index * 13 + 1); 8]))
        .collect()
}

fn membership_request() -> SyncRequest {
    let hash = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: 24,
        ..Default::default()
    };
    let key = AssetId(5);
    let payload = LeafPayload {
        sync_state: vec![f(42), f(key.0 as u32)],
        identity_digest: [9; 32],
    };
    let leaf = LeafState::Occupied(payload.clone());
    let path = MerklePath {
        siblings: siblings(),
    };
    let old_root = path
        .compute_root(&hash, &params, key, &leaf)
        .expect("fixed membership fixture must be valid");
    let value_digest = hash
        .hash_leaf(&leaf.encode())
        .expect("fixed membership leaf must fit the structural bound");

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

fn mutate(case: Case, request: &mut SyncRequest, encoded: &mut [u8]) {
    match case {
        Case::Honest => {}
        Case::InnerProofBit => {
            let last = encoded.len() - 1;
            encoded[last] ^= 1;
        }
        Case::Operation => {
            request.operation = SmtOperation::NonMembership { key: AssetId(5) };
        }
        Case::Request => {
            request.public_inputs.asset_id = AssetId(6);
        }
        Case::Witness => {
            request.witness.path.siblings[0] = Digest([f(999); 8]);
        }
        Case::Identity => {
            // First circuit-identity byte after the fixed envelope prefix.
            encoded[17] ^= 1;
        }
        Case::Version => {
            // proof_encoding_version immediately follows the eight-byte magic.
            encoded[8] ^= 1;
        }
    }
}

fn evaluate_prepared(
    prover: &StateSyncProver,
    prepared: &PreparedSync,
    case: Case,
) -> Option<[u8; APPLICATION_STATEMENT_BYTES]> {
    let mut request = membership_request();
    let mut encoded =
        include_bytes!("../../../../tests/vectors/inner-proof-v1/membership-d24.bin").to_vec();
    mutate(case, &mut request, &mut encoded);

    let statement = prover.wrap_relation(prepared, &request, &encoded)?;
    let mut output = [0; APPLICATION_STATEMENT_BYTES];
    for (index, scalar) in statement.frs.iter().enumerate() {
        output[index * 32..(index + 1) * 32].copy_from_slice(&scalar.0);
    }
    Some(output)
}

/// Execute the frozen relation over the committed d=24 membership vector.
///
/// The return value is the application statement only. Vendor journal or
/// public-values framing and the final Groth16 public inputs are intentionally
/// separate layers measured by each host harness.
pub fn evaluate(case: Case) -> Option<[u8; APPLICATION_STATEMENT_BYTES]> {
    let prover = StateSyncProver::new(config());
    let prepared = prover.prepare(SmtOpKind::Membership).ok()?;
    evaluate_prepared(&prover, &prepared, case)
}

/// Execute the canonical honest relation using caller-supplied bytes that pass
/// the crate-owned pinned d24/A/Membership validator.
///
/// Non-honest selectors fail before material validation. For the honest case,
/// the caller supplies no digest, commitment, profile, wiring or expected
/// statement anchor, and this path never falls back to
/// [`StateSyncProver::prepare`].
pub fn evaluate_with_pinned_material(
    selector: u8,
    material: Vec<u8>,
) -> Option<[u8; APPLICATION_STATEMENT_BYTES]> {
    if selector != Case::Honest as u8 {
        return None;
    }
    let prover = StateSyncProver::new(config());
    let prepared = prover
        .prepare_pinned_d24_a_membership(&material)
        .ok()?;
    drop(material);
    evaluate_prepared(&prover, &prepared, Case::Honest)
}

/// Execute the same fixed N=1 relation while emitting coarse checkpoints.
///
/// This function exists solely for the separately identified diagnostic guest.
/// Its relation construction intentionally mirrors [`evaluate`] so the
/// canonical guest source and journal contract remain untouched.
pub fn evaluate_diagnostic(
    case: Case,
    mut checkpoint: impl FnMut(DiagnosticCheckpoint),
) -> Option<[u8; APPLICATION_STATEMENT_BYTES]> {
    let prover = StateSyncProver::new(config());
    checkpoint(DiagnosticCheckpoint::ProverConstructed);

    let prepared = prover.prepare(SmtOpKind::Membership).ok()?;
    checkpoint(DiagnosticCheckpoint::RelationPrepared);

    let mut request = membership_request();
    let mut encoded =
        include_bytes!("../../../../tests/vectors/inner-proof-v1/membership-d24.bin").to_vec();
    checkpoint(DiagnosticCheckpoint::FixtureCopied);

    mutate(case, &mut request, &mut encoded);
    let statement = prover.wrap_relation(&prepared, &request, &encoded)?;
    checkpoint(DiagnosticCheckpoint::RelationEvaluated);

    let mut output = [0; APPLICATION_STATEMENT_BYTES];
    for (index, scalar) in statement.frs.iter().enumerate() {
        output[index * 32..(index + 1) * 32].copy_from_slice(&scalar.0);
    }
    checkpoint(DiagnosticCheckpoint::StatementEncoded);
    Some(output)
}

#[cfg(test)]
mod tests {
    use super::{APPLICATION_STATEMENT_BYTES, Case, evaluate, evaluate_diagnostic};

    #[test]
    fn honest_relation_returns_six_scalars() {
        assert_eq!(
            evaluate(Case::Honest).unwrap().len(),
            APPLICATION_STATEMENT_BYTES
        );
    }

    #[test]
    fn diagnostic_relation_matches_canonical_output_and_checkpoint_order() {
        let mut checkpoints = Vec::new();
        let diagnostic = evaluate_diagnostic(Case::Honest, |stage| checkpoints.push(stage));
        assert_eq!(diagnostic, evaluate(Case::Honest));
        assert_eq!(checkpoints.len(), 5);
        assert!(
            checkpoints
                .windows(2)
                .all(|pair| pair[0] as usize + 1 == pair[1] as usize)
        );
    }

    #[test]
    fn adversarial_inputs_fail_closed() {
        for case in [
            Case::InnerProofBit,
            Case::Operation,
            Case::Request,
            Case::Witness,
            Case::Identity,
            Case::Version,
        ] {
            assert!(evaluate(case).is_none(), "{case:?} must be rejected");
        }
    }
}
