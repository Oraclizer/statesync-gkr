//! Inserted only as a cfg(test) child of reduce.rs in an isolated source copy.
//! Oracle arithmetic, folding, prover driver and production interfaces stay intact.
use super::*;
use crate::circuit::{Gate, evaluate_circuit};
use crate::wiring::TableWiring;
use ssgkr_primitives::field::{ExtensionField, PrimeField32};
use ssgkr_memory_allocator::{Snapshot, begin_interval, snapshot};
use sha2::{Digest as ShaDigest, Sha256};
use serde_json::{Value, json};
use std::{cell::RefCell, fs::File, hint::black_box, io::{BufWriter, Write},
          mem::size_of, path::PathBuf, time::{Instant, SystemTime, UNIX_EPOCH}};

const PROBE_TAG: &[u8] = b"ssgkr-memory-common-circuit-probe/v1";
const SCHEMA: &str = "ssgkr.memory-probe.raw.v1";

fn field(value: u32) -> BaseField { BaseField::from_u32(value) }
fn splitmix64(value: u64) -> u64 {
    let mut z=value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    z=(z^(z>>30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z=(z^(z>>27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z^(z>>31)
}
fn number(name: &str, default: usize) -> usize {
    std::env::var(name).ok().map(|v| v.parse().expect("integer probe option")).unwrap_or(default)
}
fn name(name: &str, default: &str) -> String {
    std::env::var(name).unwrap_or_else(|_| default.to_owned())
}
fn unix_ns() -> u128 { SystemTime::now().duration_since(UNIX_EPOCH).expect("clock").as_nanos() }
fn hex(bytes: &[u8]) -> String { bytes.iter().map(|v| format!("{v:02x}")).collect() }

/// Each output has one Add (two coefficient-one Lin gates), a Mul, or a
/// Pow3 plus affine contribution. All public IR unary input indices agree.
fn fixture(bits: usize, depth: usize, family: &str, seed: u64)
    -> (LayeredCircuit<BaseField>, Vec<BaseField>) {
    assert!((1..=16).contains(&bits), "bounded probe width_bits=1..16");
    assert!((1..=16).contains(&depth), "bounded probe depth=1..16");
    assert!(matches!(family, "mixed" | "add" | "mul" | "cubic_affine"));
    let width = 1usize << bits;
    let inputs = (0..width).map(|j|field((splitmix64(seed.wrapping_add(j as u64))%2_130_706_433) as u32)).collect();
    let mut layers = Vec::with_capacity(depth);
    for layer_index in 0..depth {
        let mut gates = Vec::with_capacity(2 * width);
        let mut consts = Vec::with_capacity(width);
        for output in 0..width {
            let left = ((output + layer_index) % width) as u32;
            let right = ((output + layer_index + 1) % width) as u32;
            let mut push = |kind, in1, in2, coeff| gates.push(Gate {
                kind, out: output as u32, in1, in2, coeff: field(coeff),
            });
            if family != "cubic_affine" {
                if family=="add" || (family=="mixed" && (output+layer_index)%2==0) {
                    push(GateKind::Lin, left, left, 1);
                    push(GateKind::Lin, right, right, 1);
                } else { push(GateKind::Mul, left, right, 1); }
            } else {
                match output % 3 {
                    0 => { push(GateKind::Pow3, left, left, 1); push(GateKind::Lin, right, right, 2); }
                    1 => { push(GateKind::Lin, left, left, 3); push(GateKind::Lin, right, right, 5); }
                    _ => push(GateKind::Mul, left, right, 1),
                }
                consts.push((output as u32, field(1 + (output as u32 + layer_index as u32) % 7)));
            }
        }
        layers.push(Layer { width_bits: bits, gates, consts });
    }
    // The conceptual fixture sequence is input-to-output. The public IR is
    // explicitly output-first (circuit.rs), hence reverse only its storage.
    layers.reverse();
    (LayeredCircuit { layers, input_width_bits: bits }, inputs)
}

fn circuit_bytes(circuit: &LayeredCircuit<BaseField>) -> Vec<u8> {
    let mut bytes = b"ssgkr-memory-circuit-layout/v1".to_vec();
    let mut word = |v: u64| bytes.extend_from_slice(&v.to_le_bytes());
    word(circuit.input_width_bits as u64); word(circuit.layers.len() as u64);
    for layer in &circuit.layers {
        word(layer.width_bits as u64); word(layer.gates.len() as u64);
        for gate in &layer.gates {
            word(match gate.kind { GateKind::Lin => 0, GateKind::Mul => 1, GateKind::Pow3 => 2 });
            for v in [gate.out, gate.in1, gate.in2, gate.coeff.as_canonical_u32()] { word(v as u64); }
        }
        word(layer.consts.len() as u64);
        for &(wire, value) in &layer.consts { word(wire as u64); word(value.as_canonical_u32() as u64); }
    }
    bytes
}
fn transcript(digest: &[u8; 32], inputs: &[BaseField], outputs: &[BaseField]) -> Transcript {
    let mut t = Transcript::new(PROBE_TAG);
    for &byte in digest { t.observe_base(BaseField::from_u8(byte)); }
    // Fixed per-fixture vector lengths are bound by the circuit digest.
    t.observe_many(inputs); t.observe_many(outputs); t
}
fn common_fixture_json(bits:usize,depth:usize,family:&str,seed:u64,
                       inputs:&[BaseField],outputs:&[BaseField]) -> Option<Value> {
    if family=="cubic_affine" { return None; }
    let width=1usize<<bits;
    let mut gates=Vec::with_capacity(width*depth);
    for layer in 0..depth { for output in 0..width {
        let kind=if family=="add" || (family=="mixed" && (output+layer)%2==0) {"add"}else{"mul"};
        gates.push(json!({"calculation_layer":layer,"output":output,"kind":kind,
                         "a":(output+layer)%width,"b":(output+layer+1)%width}));
    }}
    Some(json!({"schema":"common-add-mul-v1","field_modulus":2_130_706_433,"extension":"X^4-3",
        "width":width,"depth":depth,"kind":family,"seed":seed,
        "input_base_u32":inputs.iter().map(|x|x.as_canonical_u32()).collect::<Vec<_>>(),
        "output_base_u32":outputs.iter().map(|x|x.as_canonical_u32()).collect::<Vec<_>>(),
        "gates_calculation_order":gates}))
}
fn challenge_limbs<EF: ExtensionField<BaseField>>(value: &EF) -> Vec<u32> {
    value.as_basis_coefficients_slice().iter().map(|x| x.as_canonical_u32()).collect()
}
fn proof_value(proof: &GkrProof) -> Value {
    json!({"layers":proof.layer_proofs.iter().map(|lp| json!({
        "round_polys":lp.sumcheck.round_polys.iter().map(|rp|
            rp.coeffs().iter().map(challenge_limbs).collect::<Vec<_>>()).collect::<Vec<_>>(),
        "eval_x":challenge_limbs(&lp.eval_x), "eval_y":challenge_limbs(&lp.eval_y)
    })).collect::<Vec<_>>()})
}
fn verify_measure(circuit: &LayeredCircuit<BaseField>, digest: &[u8; 32], inputs: &[BaseField],
            outputs: &[BaseField], proof: &GkrProof) -> (bool,u128,u128) {
    let wiring = TableWiring::new(circuit);
    let mut t = transcript(digest, inputs, outputs);
    let start=Instant::now(); let result=verify(circuit, &wiring, outputs, proof, &mut t);
    let protocol_verify_ns=start.elapsed().as_nanos();
    match result {
        Ok(claim) => {
            let start=Instant::now();
            let x=mle_eval_base(inputs, &claim.point); let y=mle_eval_base(inputs, &claim.point_y);
            let input_claim_discharge_ns=start.elapsed().as_nanos();
            (x==claim.expected_eval && y==claim.expected_eval_y,protocol_verify_ns,input_claim_discharge_ns)
        },
        Err(_) => (false,protocol_verify_ns,0),
    }
}
fn accepted(circuit: &LayeredCircuit<BaseField>, digest: &[u8; 32], inputs: &[BaseField],
            outputs: &[BaseField], proof: &GkrProof) -> bool {
    verify_measure(circuit,digest,inputs,outputs,proof).0
}

#[derive(Clone, Copy)]
struct Buffer { name: &'static str, len: usize, capacity: usize, element_bytes: usize }
const EMPTY: Buffer = Buffer { name: "", len: 0, capacity: 0, element_bytes: 0 };
fn buffer<T>(name: &'static str, values: &Vec<T>) -> Buffer {
    Buffer { name, len: values.len(), capacity: values.capacity(), element_bytes: size_of::<T>() }
}
trait Buffers { fn buffers(&self) -> [Buffer; 11]; }
impl Buffers for DenseLayerOracle {
    fn buffers(&self) -> [Buffer; 11] {
        [buffer("lin", &self.lin), buffer("pow", &self.pow), buffer("vx", &self.vx),
         buffer("vy", &self.vy), buffer("beta", &self.beta), buffer("mul", &self.mul),
         EMPTY, EMPTY, EMPTY, EMPTY, EMPTY]
    }
}
impl Buffers for SparseLayerOracle {
    fn buffers(&self) -> [Buffer; 11] {
        [buffer("lin_x", &self.lin_x), buffer("pow_x", &self.pow_x), buffer("vx", &self.vx),
         buffer("amul_x", &self.amul_x), buffer("mul_gates", &self.mul_gates),
         buffer("v_embed", &self.v_embed), buffer("xstar", &self.xstar),
         buffer("beta_y", &self.beta_y), buffer("vy", &self.vy), buffer("mulx_y", &self.mulx_y), EMPTY]
    }
}
struct Event {
    stage: &'static str, layer: usize, round: usize, remaining: usize,
    offset_ns: u128, elapsed_ns: u128, allocation: Snapshot, buffers: [Buffer; 11],
}
struct Trace { clock: Instant, events: Vec<Event>, allocation_capacity: usize }
impl Trace {
    fn record<O: SumcheckOracle<ChallengeField> + Buffers>(&mut self, stage: &'static str,
              layer: usize, round: usize, elapsed_ns: u128, oracle: &O) {
        assert!(self.events.len() < self.allocation_capacity, "event buffer must never grow while timed");
        self.events.push(Event { stage, layer, round, remaining: oracle.num_vars(),
            offset_ns: self.clock.elapsed().as_nanos(), elapsed_ns, allocation: snapshot(),
            buffers: oracle.buffers() });
    }
}
struct Observed<'a, O> { inner: O, trace: &'a RefCell<Trace>, layer: usize, round: usize }
impl<O: SumcheckOracle<ChallengeField> + Buffers> SumcheckOracle<ChallengeField> for Observed<'_, O> {
    fn num_vars(&self) -> usize { self.inner.num_vars() }
    fn degree_bound(&self) -> usize { self.inner.degree_bound() }
    fn round_poly(&self) -> RoundPoly<ChallengeField> {
        let clock = Instant::now(); let result = self.inner.round_poly();
        let elapsed = clock.elapsed().as_nanos();
        self.trace.borrow_mut().record("round_poly", self.layer, self.round, elapsed, &self.inner);
        result
    }
    fn bind(&mut self, challenge: ChallengeField) {
        let clock = Instant::now(); self.inner.bind(challenge);
        let elapsed = clock.elapsed().as_nanos();
        self.trace.borrow_mut().record("bind", self.layer, self.round, elapsed, &self.inner);
        self.round += 1;
    }
}
fn observed_proof(circuit: &LayeredCircuit<BaseField>, witness: &CircuitWitness<BaseField>,
                  t: &mut Transcript, mode: &str, trace: &RefCell<Trace>) -> GkrProof {
    let mut layer_index=0usize;
    if mode=="dense" {
        prove_impl(circuit,witness,t,|layer,s_in,incoming,below|{
            let constructor=Instant::now(); let inner=DenseLayerOracle::new(layer,s_in,incoming,below);
            let elapsed=constructor.elapsed().as_nanos();
            trace.borrow_mut().record("constructor",layer_index,0,elapsed,&inner);
            let oracle=Observed{inner,trace,layer:layer_index,round:0};layer_index+=1;oracle
        })
    } else {
        assert_eq!(mode,"sparse");
        prove_impl(circuit,witness,t,|layer,s_in,incoming,below|{
            let constructor=Instant::now(); let inner=SparseLayerOracle::new(layer,s_in,incoming,below);
            let elapsed=constructor.elapsed().as_nanos();
            trace.borrow_mut().record("constructor",layer_index,0,elapsed,&inner);
            let oracle=Observed{inner,trace,layer:layer_index,round:0};layer_index+=1;oracle
        })
    }
}
fn alloc_json(a: Snapshot) -> Value {
    json!({"live_requested_bytes":a.live_requested_bytes,"peak_requested_bytes":a.peak_requested_bytes,
           "successful_allocation_calls":a.successful_allocation_calls,
           "successful_reallocation_calls":a.successful_reallocation_calls,
           "allocated_requested_bytes":a.allocated_requested_bytes,"freed_requested_bytes":a.freed_requested_bytes})
}
fn event_json(event: &Event) -> Value {
    let buffers: Vec<_> = event.buffers.iter().filter(|b| !b.name.is_empty()).map(|b| json!({
        "name":b.name,"len":b.len,"capacity":b.capacity,"element_bytes":b.element_bytes,
        "len_payload_bytes":b.len*b.element_bytes,"capacity_payload_bytes":b.capacity*b.element_bytes})).collect();
    json!({"stage":event.stage,"layer_index":event.layer,"round_index":event.round,
           "remaining_variables":event.remaining,"offset_ns":event.offset_ns,"elapsed_ns":event.elapsed_ns,
           "allocator":alloc_json(event.allocation),"buffers":buffers})
}
fn controls(circuit: &LayeredCircuit<BaseField>, digest: &[u8;32], inputs: &[BaseField],
            witness: &CircuitWitness<BaseField>) -> Value {
    let outputs = &witness.layer_values[0];
    let mut td = transcript(digest, inputs, outputs);
    let dense = prove_dense(circuit, witness, &mut td);
    let mut ts = transcript(digest, inputs, outputs);
    let sparse = prove(circuit, witness, &mut ts);
    assert_eq!(dense, sparse, "same-driver whole proof equality");
    assert_eq!(td.sample_challenge(), ts.sample_challenge(), "post-proof transcript parity");
    for mode in ["dense","sparse"] {
        let capacity=circuit.layers.len()*(1+4*circuit.input_width_bits)+4;
        let trace=RefCell::new(Trace{clock:Instant::now(),events:Vec::with_capacity(capacity),allocation_capacity:capacity});
        let mut observed_transcript=transcript(digest,inputs,outputs);
        let observed=observed_proof(circuit,witness,&mut observed_transcript,mode,&trace);
        assert_eq!(observed,sparse,"observer changed proof");
    }
    assert!(accepted(circuit,digest,inputs,outputs,&dense));
    assert!(accepted(circuit,digest,inputs,outputs,&sparse));
    let mut bad_proof = sparse.clone(); bad_proof.layer_proofs[0].eval_x += ChallengeField::ONE;
    assert!(!accepted(circuit,digest,inputs,outputs,&bad_proof), "proof tamper accepted");
    let mut bad_outputs = outputs.clone(); bad_outputs[0] += BaseField::ONE;
    assert!(!accepted(circuit,digest,inputs,&bad_outputs,&sparse), "output tamper accepted");
    let mut bad_inputs = inputs.to_vec(); bad_inputs[0] += BaseField::ONE;
    assert!(!accepted(circuit,digest,&bad_inputs,outputs,&sparse), "input tamper accepted");
    let mut t=transcript(digest,inputs,outputs);
    let mut claim=verify(circuit,&TableWiring::new(circuit),outputs,&sparse,&mut t).expect("good residual claim");
    claim.expected_eval+=ChallengeField::ONE;
    assert_ne!(mle_eval_base(inputs,&claim.point),claim.expected_eval,"changed residual input claim accepted");
    let canonical = serde_json::to_vec(&proof_value(&sparse)).expect("canonical proof value");
    json!({"whole_proof_equal":true,"observer_proof_equal":true,"post_proof_transcript_equal":true,"dense_accepted":true,
           "sparse_accepted":true,"proof_eval_tamper_rejected":true,"output_tamper_rejected":true,
           "input_tamper_rejected":true,"input_claim_tamper_rejected":true,
           "canonical_proof_sha256":hex(&Sha256::digest(canonical))})
}

#[test]
fn memory_probe_controls() {
    for family in ["mixed", "add", "mul", "cubic_affine"] {
        let (circuit, inputs) = fixture(3, 3, family, 7);
        let digest: [u8;32] = Sha256::digest(circuit_bytes(&circuit)).into();
        let witness = evaluate_circuit(&circuit,&inputs).expect("public circuit evaluation");
        let result = controls(&circuit,&digest,&inputs,&witness);
        let common=common_fixture_json(3,3,family,7,&inputs,&witness.layer_values[0]);
        let common_hash=common.as_ref().map(|value|hex(&Sha256::digest(serde_json::to_vec(value).expect("common fixture bytes"))));
        println!("{}",json!({"schema_version":SCHEMA,"record_type":"controls","family":family,"width":8,"depth":3,"seed":7,"controls":result,
            "common_fixture":common,"common_fixture_sha256":common_hash}));
    }
    // Exercise allocated, grown, truncated and dropped ownership explicitly.
    let before = begin_interval();
    let mut allocation = Vec::<u8>::with_capacity(1024);
    allocation.resize(1024, 1); black_box(&allocation);
    let allocated = snapshot(); assert!(allocated.live_requested_bytes >= before.live_requested_bytes+1024);
    allocation.reserve_exact(2048); let grown = snapshot();
    let capacity = allocation.capacity(); allocation.truncate(1); black_box(&allocation);
    assert_eq!(allocation.capacity(),capacity); assert_eq!(snapshot().live_requested_bytes,grown.live_requested_bytes);
    drop(allocation); assert_eq!(snapshot().live_requested_bytes,before.live_requested_bytes);
    println!("{}",json!({"schema_version":SCHEMA,"record_type":"allocator_controls",
        "allocation_growth_truncate_drop":true,"before":alloc_json(before),"allocated":alloc_json(allocated),"grown":alloc_json(grown)}));
}

#[test]
#[ignore = "explicit single-mode process memory measurement"]
fn memory_probe_one() {
    let mode = name("SSGKR_MEMORY_MODE","sparse");
    assert!(matches!(mode.as_str(),"dense"|"sparse"));
    let family = name("SSGKR_MEMORY_FAMILY","mixed");
    let bits=number("SSGKR_MEMORY_WIDTH_BITS",3); let depth=number("SSGKR_MEMORY_DEPTH",3);
    let samples=number("SSGKR_MEMORY_SAMPLES",3); let warmups=number("SSGKR_MEMORY_WARMUPS",1);
    let observer=number("SSGKR_MEMORY_OBSERVER",1); assert!(observer<=1);
    let repeat=number("SSGKR_MEMORY_REPEAT",0); let seed=number("SSGKR_MEMORY_SEED",7) as u64;
    assert!((1..=1000).contains(&samples) && warmups<=100);
    let path=PathBuf::from(std::env::var("SSGKR_MEMORY_OUT").expect("unique raw JSONL path required"));
    let file=File::options().create_new(true).write(true).open(&path).expect("never overwrite raw output");
    let mut output=BufWriter::with_capacity(64*1024,file);
    let (circuit,inputs)=fixture(bits,depth,&family,seed);
    let digest:[u8;32]=Sha256::digest(circuit_bytes(&circuit)).into();
    let witness=evaluate_circuit(&circuit,&inputs).expect("circuit evaluation");
    let outputs=&witness.layer_values[0];
    let common=common_fixture_json(bits,depth,&family,seed,&inputs,outputs);
    let common_hash=common.as_ref().map(|value|hex(&Sha256::digest(serde_json::to_vec(value).expect("common fixture bytes"))));
    // Controls must run in their own process. This measurement process never
    // allocates the other oracle, so RSS high-water mark has one mode owner.
    let shape=json!({"layers":depth,"width_bits":bits,"actual_width":1usize<<bits,"padded_width":1usize<<bits,
        "layer_gates":circuit.layers.iter().map(|layer|json!({"lin":layer.gates.iter().filter(|g|g.kind==GateKind::Lin).count(),
        "mul":layer.gates.iter().filter(|g|g.kind==GateKind::Mul).count(),"pow3":layer.gates.iter().filter(|g|g.kind==GateKind::Pow3).count(),
        "constants":layer.consts.len()})).collect::<Vec<_>>(),"base_field_bytes":size_of::<BaseField>(),
        "challenge_field_bytes":size_of::<ChallengeField>(),"mul_tuple_bytes":size_of::<(u32,u32,ChallengeField)>(),
        "witness_buffers":witness.layer_values.iter().enumerate().map(|(i,v)|json!({"layer_index":i,"len":v.len(),"capacity":v.capacity(),"element_bytes":size_of::<BaseField>()})).collect::<Vec<_>>()});
    let fixture_record=json!({"schema_version":SCHEMA,"record_type":"fixture","mode":mode,"family":family,
        "width_bits":bits,"depth":depth,"seed":seed,"process_repeat":repeat,"samples":samples,"warmups":warmups,
        "observer_enabled":observer==1,
        "conceptual_layer_order":"input_to_output","ir_storage_layer_order":"output_to_input",
        "common_gate_rule":"in1=(j+l)%W; in2=(j+l+1)%W; mixed:Add when (j+l)%2==0 else Mul",
        "common_input_rule":"SplitMix64(seed+j)%2130706433; wrapping u64 standard add/mix function",
        "circuit_sha256":hex(&digest),"circuit_layout_bytes_hex":hex(&circuit_bytes(&circuit)),
        "common_fixture":common,"common_fixture_sha256":common_hash,
        "inputs":inputs.iter().map(|x|x.as_canonical_u32()).collect::<Vec<_>>(),"shape":shape,
        "outputs":outputs.iter().map(|x|x.as_canonical_u32()).collect::<Vec<_>>(),
        "source_sha":name("SSGKR_SOURCE_SHA","UNAVAILABLE"),"probe_sha":name("SSGKR_MEMORY_PROBE_SHA","UNAVAILABLE"),
        "instrumentation":"constructor/round/bind timestamps and fixed-capacity event snapshots inside prover timer; JSON/hash/verification/flush outside",
        "observer_comparison_semantics":"observer on/off both use same allocator hook; measures incremental event observation overhead only; allocator-hook total overhead not separately calibrated",
        "proof_representation":"benchmark canonical field-basis JSON; not official codec bytes",
        "peak_interval":"whole prover interval additional requested ownership; not pure oracle-only peak",
        "allocator_semantics":"successful requested bytes; excludes System metadata/slack and realloc internal transient overlap",
        "rss_semantics":"process.time.txt and external actual-cadence RSS samples; never inferred from Vec payload"});
    writeln!(output,"{fixture_record}").expect("fixture record"); output.flush().expect("fixture flush");
    for iteration in 0..warmups+samples {
        let warmup=iteration<warmups; let sample_index=if warmup{iteration}else{iteration-warmups};
        let event_capacity=depth*(1+4*bits)+4;
        let trace=RefCell::new(Trace{clock:Instant::now(),events:Vec::with_capacity(event_capacity),allocation_capacity:event_capacity});
        let mut t=transcript(&digest,&inputs,outputs);
        let start_unix_ns=unix_ns(); let allocation_start=begin_interval(); let clock=Instant::now();
        trace.borrow_mut().clock=clock;
        let proof=if observer==1 { observed_proof(&circuit,&witness,&mut t,&mode,&trace) }
            else if mode=="dense" { prove_dense(&circuit,&witness,&mut t) }
            else { prove(&circuit,&witness,&mut t) };
        black_box(&proof); let prove_elapsed_ns=clock.elapsed().as_nanos(); let allocation_end=snapshot();
        let verify_start=Instant::now(); let (ok,protocol_verify_ns,input_claim_discharge_ns)=verify_measure(&circuit,&digest,&inputs,outputs,&proof);
        let verify_elapsed_ns=verify_start.elapsed().as_nanos(); assert!(ok,"measured proof rejected");
        let proof_json=proof_value(&proof); let canonical=serde_json::to_vec(&proof_json).expect("proof bytes");
        let row=json!({"schema_version":SCHEMA,"record_type":"sample","mode":mode,"family":family,
            "width_bits":bits,"depth":depth,"seed":seed,"process_repeat":repeat,"sample_index":sample_index,
            "observer_enabled":observer==1,
            "warmup":warmup,"started_unix_ns":start_unix_ns,"prove_elapsed_ns":prove_elapsed_ns,"verify_elapsed_ns":verify_elapsed_ns,
            "protocol_verify_elapsed_ns":protocol_verify_ns,"input_claim_discharge_elapsed_ns":input_claim_discharge_ns,
            "allocator_start":alloc_json(allocation_start),"allocator_end":alloc_json(allocation_end),
            "allocator_peak_delta_requested_bytes":allocation_end.peak_requested_bytes.saturating_sub(allocation_start.live_requested_bytes),
            "allocator_live_delta_requested_bytes":allocation_end.live_requested_bytes as i128-allocation_start.live_requested_bytes as i128,
            "allocator_allocated_delta_requested_bytes":allocation_end.allocated_requested_bytes-allocation_start.allocated_requested_bytes,
            "allocator_freed_delta_requested_bytes":allocation_end.freed_requested_bytes-allocation_start.freed_requested_bytes,
            "event_count":trace.borrow().events.len(),"event_capacity":trace.borrow().events.capacity(),
            "events":trace.borrow().events.iter().map(event_json).collect::<Vec<_>>(),"accepted":ok,
            "canonical_proof_sha256":hex(&Sha256::digest(canonical)),"canonical_proof":proof_json});
        writeln!(output,"{row}").expect("raw sample"); output.flush().expect("sample flush");
    }
    writeln!(output,"{}",json!({"schema_version":SCHEMA,"record_type":"terminal","status":"PASS",
        "samples":samples,"warmups":warmups,"process_repeat":repeat})).expect("terminal");
    output.flush().expect("terminal flush");
}
