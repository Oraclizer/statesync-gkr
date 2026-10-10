//! Direct protocol-boundary witnesses for load-bearing verifier checks.

#![allow(clippy::unwrap_used)]

use statesync_gkr::gkr::wiring::TableWiring;
use statesync_gkr::gkr::{Gate, GateKind, Layer, LayeredCircuit, evaluate_circuit, prove, verify};
use statesync_gkr::primitives::Transcript;
use statesync_gkr::primitives::field::{BaseField, ChallengeField, PrimeCharacteristicRing};

const TAG: &[u8] = b"gkr-protocol-boundary-test";

fn f(value: u32) -> BaseField {
    BaseField::from_u32(value)
}

fn gate(kind: GateKind, out: u32, in1: u32, in2: u32) -> Gate<BaseField> {
    Gate {
        kind,
        out,
        in1,
        in2,
        coeff: f(1),
    }
}

fn circuit() -> LayeredCircuit<BaseField> {
    LayeredCircuit {
        layers: vec![
            Layer {
                width_bits: 1,
                gates: vec![gate(GateKind::Mul, 0, 0, 1), gate(GateKind::Lin, 1, 2, 2)],
                consts: vec![],
            },
            Layer {
                width_bits: 2,
                gates: vec![
                    gate(GateKind::Lin, 0, 0, 0),
                    gate(GateKind::Lin, 1, 1, 1),
                    gate(GateKind::Pow3, 2, 2, 2),
                    gate(GateKind::Lin, 3, 3, 3),
                ],
                consts: vec![],
            },
        ],
        input_width_bits: 2,
    }
}

#[test]
fn last_layer_reconstruction_is_load_bearing_at_protocol_boundary() {
    let circuit = circuit();
    let inputs = [f(2), f(3), f(4), f(5)];
    let witness = evaluate_circuit(&circuit, &inputs).unwrap();
    let outputs = witness.layer_values[0].clone();

    let mut prover_transcript = Transcript::new(TAG);
    prover_transcript.observe_many(&outputs);
    let mut proof = prove(&circuit, &witness, &mut prover_transcript);
    let last = proof.layer_proofs.len() - 1;
    proof.layer_proofs[last].eval_x += ChallengeField::ONE;

    let wiring = TableWiring::new(&circuit);
    let mut verifier_transcript = Transcript::new(TAG);
    verifier_transcript.observe_many(&outputs);
    assert!(
        verify(
            &circuit,
            &wiring,
            &outputs,
            &proof,
            &mut verifier_transcript,
        )
        .is_err()
    );
}
