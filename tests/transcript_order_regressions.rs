//! Source-fact regressions on the public API: the transcript absorbs an
//! extension element in basis order, the product sumcheck prover and verifier
//! observe a round before drawing its challenge, and the object API and the
//! canonical codec accept the coefficient counts they document. These tests do
//! not establish a random-oracle distribution, adaptive-witness soundness, or
//! multi-round Fiat-Shamir security.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use statesync_gkr::compiler::{
    AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOpKind,
    SmtOperation, SmtParams, SmtWitness,
};
use statesync_gkr::primitives::{
    Transcript,
    field::{BaseField as F, ChallengeField as E, PrimeCharacteristicRing},
    hash::{Digest, HashGadget, Poseidon2Gadget},
};
use statesync_gkr::sumcheck::{
    self, ChallengeSource, RoundPoly, SumcheckInstance, SumcheckOracle, SumcheckProof,
};
use statesync_gkr::{StateSyncGkrConfig, StateSyncProver, SyncRequest};

const DEPTH: u32 = 3;

#[test]
fn production_extension_absorption_uses_basis_order() {
    let coefficients = [1, 3, 5, 7].map(F::from_u32);
    let mut ext = Transcript::new(b"basis");
    let mut base = Transcript::new(b"basis");
    let mut reversed = Transcript::new(b"basis");
    ext.observe_ext(E::new(coefficients));
    base.observe_many(&coefficients);
    for c in coefficients.into_iter().rev() {
        reversed.observe_base(c);
    }
    let expected = base.sample_challenge();
    assert_eq!(ext.sample_challenge(), expected);
    assert_ne!(reversed.sample_challenge(), expected);
}

struct Trace {
    inner: Transcript,
    events: Vec<String>,
}

impl Trace {
    fn new() -> Self {
        Self {
            inner: Transcript::new(b"trace"),
            events: vec![],
        }
    }
}

impl ChallengeSource<E> for Trace {
    fn observe_round_poly(&mut self, p: &RoundPoly<E>) {
        self.events.push(format!("observe:{:?}", p.coeffs()));
        <Transcript as ChallengeSource<E>>::observe_round_poly(&mut self.inner, p);
    }
    fn draw_challenge(&mut self) -> E {
        let value = self.inner.sample_challenge();
        self.events.push(format!("draw:{value:?}"));
        value
    }
}

// An exact fixture polynomial 1 + 2X. The product prover and verifier, not
// fixture code, own the absorb/squeeze order under test.
struct LinearFixture {
    remaining: usize,
}

impl SumcheckOracle<E> for LinearFixture {
    fn num_vars(&self) -> usize {
        self.remaining
    }
    fn degree_bound(&self) -> usize {
        4
    }
    fn round_poly(&self) -> RoundPoly<E> {
        RoundPoly::from_coeffs(vec![E::ONE, E::from_u32(2), E::ZERO, E::ZERO, E::ZERO])
    }
    fn bind(&mut self, _: E) {
        self.remaining -= 1;
    }
}

#[test]
fn actual_prover_and_verifier_absorb_then_squeeze_match() {
    let mut prover = Trace::new();
    let (proof, p) = sumcheck::prove(&mut LinearFixture { remaining: 1 }, &mut prover);
    let mut verifier = Trace::new();
    let v = sumcheck::verify(
        &SumcheckInstance {
            num_vars: 1,
            degree_bound: 4,
            claimed_sum: E::from_u32(4),
        },
        &proof,
        &mut verifier,
    )
    .unwrap();
    assert_eq!(p, v);
    assert_eq!(prover.events, verifier.events);
    assert_eq!(prover.events.len(), 2);
    assert!(prover.events[0].starts_with("observe:"));
    assert!(prover.events[1].starts_with("draw:"));
    let mut shifted = Transcript::new(b"trace");
    let premature = shifted.sample_challenge();
    assert_ne!(premature, p.point[0]);
}

fn membership_request(key: u64) -> SyncRequest {
    let hasher = Poseidon2Gadget::default();
    let params = SmtParams {
        depth: DEPTH,
        ..Default::default()
    };
    let key = AssetId(key);
    let payload = LeafPayload {
        sync_state: vec![F::from_u32(42), F::from_u32(7)],
        identity_digest: [9u8; 32],
    };
    let leaf = LeafState::Occupied(payload.clone());
    let path = MerklePath {
        siblings: (0..DEPTH)
            .map(|i| Digest([F::from_u32(i * 13 + 1); 8]))
            .collect(),
    };
    let old_root = path.compute_root(&hasher, &params, key, &leaf).unwrap();
    let value_digest = hasher.hash_leaf(&leaf.encode()).unwrap();
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

#[test]
fn actual_object_arity_and_canonical_codec_boundary() {
    let instance = SumcheckInstance {
        num_vars: 1,
        degree_bound: 4,
        claimed_sum: E::ZERO,
    };
    for count in 0..=6 {
        let proof = SumcheckProof {
            round_polys: vec![RoundPoly::from_coeffs(vec![E::ZERO; count])],
        };
        let result = sumcheck::verify(&instance, &proof, &mut Transcript::new(b"arity"));
        assert_eq!(result.is_ok(), count <= 5);
        if let Ok(subclaim) = result {
            assert_eq!(subclaim.expected_eval, E::ZERO);
        }
    }
    let prover = StateSyncProver::new(StateSyncGkrConfig {
        smt: SmtParams {
            depth: DEPTH,
            ..Default::default()
        },
        layer_strategy: LayerStrategy::A,
        batching: Default::default(),
    });
    let prepared = prover.prepare(SmtOpKind::Membership).unwrap();
    let request = membership_request(5);
    let original = prover.prove_sync_op_prepared(&prepared, &request).unwrap();
    let good = prover.encode_sync_result(&prepared, &original).unwrap();
    assert!(prover.verify_encoded_sync_op(&prepared, &request, &good));
    for count in 0..=6 {
        let mut altered = original.clone();
        altered.proof.layer_proofs[0].sumcheck.round_polys[0] =
            RoundPoly::from_coeffs(vec![E::ZERO; count]);
        assert_eq!(
            prover.encode_sync_result(&prepared, &altered).is_ok(),
            count == 5
        );
    }
    let mut trailing = good.clone();
    trailing.push(0);
    assert!(!prover.verify_encoded_sync_op(&prepared, &request, &trailing));
}
