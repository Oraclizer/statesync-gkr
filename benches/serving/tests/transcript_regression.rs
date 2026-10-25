//! Source-fact regressions that need the raw duplex challenger or the serving
//! wire profile. The regressions that use only the public API live in the root
//! `tests/transcript_order_regressions.rs`. These tests do not establish a
//! random-oracle distribution, adaptive-witness soundness, or multi-round
//! Fiat-Shamir security.
use p3_challenger::{CanObserve, CanSample, DuplexChallenger};
use statesync_gkr::primitives::{
    Transcript,
    field::{BaseField as F, ChallengeField as E, PrimeCharacteristicRing},
    hash::Poseidon2Gadget,
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
