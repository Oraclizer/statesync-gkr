//! Source-fact regressions. These tests do not establish a random-oracle
//! distribution, adaptive-witness soundness, or multi-round Fiat-Shamir security.
use p3_challenger::{CanObserve, CanSample, DuplexChallenger};
use statesync_gkr::{
    StateSyncGkrConfig, StateSyncProver,
    compiler::{SmtOpKind, SmtParams},
    primitives::{
        Transcript,
        field::{BaseField as F, ChallengeField as E, PrimeCharacteristicRing},
        hash::Poseidon2Gadget,
    },
    sumcheck::{self, ChallengeSource, RoundPoly, SumcheckInstance, SumcheckOracle, SumcheckProof},
};

#[test]
fn real_duplex_basis_order_and_observation_buffer_reset() {
    let mut raw = DuplexChallenger::<F, _, 16, 8>::new(Poseidon2Gadget::permutation());
    let mut wrapped = Transcript::new(b"serving-regression");
    for b in b"serving-regression" {
        raw.observe(F::from_u8(*b));
    }
    raw.observe(F::from_u32(123));
    wrapped.observe_base(F::from_u32(123));
    let first: E = raw.sample();
    let block = raw.sponge_state;
    assert_eq!(first, E::new([block[7], block[6], block[5], block[4]]));
    assert_eq!(wrapped.sample_challenge(), first);
    assert_eq!(raw.output_buffer.len(), 4);
    let second: E = raw.sample();
    assert_eq!(second, E::new([block[3], block[2], block[1], block[0]]));
    assert_eq!(raw.sponge_state, block);
    assert_eq!(wrapped.sample_challenge(), second);
    assert!(raw.output_buffer.is_empty());

    let _: E = raw.sample();
    assert_eq!(raw.output_buffer.len(), 4);
    let old = raw.sponge_state;
    raw.observe(F::from_u32(77));
    assert!(raw.output_buffer.is_empty());
    assert_eq!(raw.input_buffer, vec![F::from_u32(77)]);
    let _: E = raw.sample();
    assert_ne!(raw.sponge_state, old);
    assert!(raw.input_buffer.is_empty());
    assert_eq!(raw.output_buffer.len(), 4);
}

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
            depth: 3,
            ..Default::default()
        },
        ..Default::default()
    });
    let prepared = prover.prepare(SmtOpKind::Membership).unwrap();
    let request = ssgkr_serving::fixture::original(3, "membership", 0);
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

#[test]
fn serving_key_profile_remains_narrower_than_engine_depth() {
    use statesync_gkr::primitives::field::PrimeField32;
    // The network harness intentionally retains its measured min(depth,24)
    // profile. This test does not claim to close the engine's depth-31 alias.
    assert_eq!(F::from_u32(0), F::from_u32(F::ORDER_U32));
    for depth in [24, 30, 31] {
        let request = ssgkr_serving::fixture::original(depth, "nonmembership", 0);
        let mut input = ssgkr_serving::wire::Input::from_request(&request);
        input.key = 0;
        assert!(input.request(depth).is_ok());
        input.key = F::ORDER_U32 as u64;
        assert!(input.request(depth).is_err());
    }
}
