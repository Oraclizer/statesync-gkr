//! Separate supplemental measurement caller over immutable released APIs.
mod fixture;
mod variants;

use std::{fs, hint::black_box, io::{BufWriter,Write}, path::{Path,PathBuf}, time::{Instant,SystemTime,UNIX_EPOCH}};
use rayon::prelude::*;
use serde_json::{json,Value};
use sha2::{Digest as ShaDigest,Sha256};
use statesync_gkr::{PreparedSync,StateSyncGkrConfig,StateSyncProver,SyncRequest,SyncResult};
use statesync_gkr::compiler::{compile_with_hints,generate_witness,smt_valid_native,LayerStrategy,LeafState,SmtParams,SmtOperation};
use statesync_gkr::gkr::{DerivedRegularWiring,GateKind,LayeredCircuit};
use statesync_gkr::gkr::wiring::TableWiring;
use statesync_gkr::primitives::field::{BaseField,ChallengeField,PrimeCharacteristicRing,PrimeField32};
use statesync_gkr::primitives::hash::{Digest,HashGadget,Poseidon2Gadget};
use statesync_gkr::wrap::commitment::{full_circuit_commitment,gate_kind_tag};
use ssgkr_verification::{prove_on,verify_sync_op_with};

const HEADER:&str="cell_id,process_repeat,order_index,order_seed,fixture_id,kind,depth,leaf_max_fields,old_leaf_kind,new_leaf_kind,payload_fields,key_policy,chain_id,batch,workers,cpu_set,build_mode,source_sha,driver_sha,binary_sha,circuit_sha,phase,oracle_kind,output_mode,sample_index,warmup,started_unix_ns,elapsed_ns,process_user_ticks,process_system_ticks,cpu_time_resolution,process_user_time,process_system_time,peak_rss_kib,proof_count,encoded_bytes,canonical_sha256,accepted,exit_code";

fn sha(bytes:&[u8])->String { Sha256::digest(bytes).iter().map(|b|format!("{b:02x}")).collect() }
fn env(name:&str)->String { std::env::var(name).unwrap_or_else(|_|"UNAVAILABLE".into()) }
fn now()->u128 { SystemTime::now().duration_since(UNIX_EPOCH).expect("UTC clock").as_nanos() }
fn ticks()->Option<(u64,u64)> {
    let text=fs::read_to_string("/proc/self/stat").ok()?;
    let suffix=text.rsplit_once(')')?.1;
    let fields:Vec<_>=suffix.split_whitespace().collect();
    Some((fields.get(11)?.parse().ok()?,fields.get(12)?.parse().ok()?))
}
fn csv(value:&str)->String { if value.contains(',')||value.contains('"')||value.contains('\n') { format!("\"{}\"",value.replace('"',"\"\"")) } else { value.into() } }
fn leaf_name(leaf:&LeafState)->&'static str { match leaf {LeafState::Empty=>"Empty",LeafState::Tombstone=>"Tombstone",LeafState::Occupied(_)=>"Occupied"} }
fn payload_len(leaf:&LeafState)->usize { if let LeafState::Occupied(p)=leaf {p.sync_state.len()} else {0} }
fn new_leaf(request:&SyncRequest)->LeafState { match &request.operation { SmtOperation::Update{new_leaf,..}=>new_leaf.clone(), _=>request.witness.leaf.clone() } }
fn kind_name(request:&SyncRequest)->&'static str { match &request.operation {SmtOperation::Membership{..}=>"membership",SmtOperation::NonMembership{..}=>"nonmembership",SmtOperation::Update{..}=>"update"} }
fn digest(d:&Digest<BaseField>)->Vec<u32>{d.0.iter().map(|x|x.as_canonical_u32()).collect()}
fn request_json(request:&SyncRequest,index:usize)->Value {
    let new=new_leaf(request);
    json!({"fixture_id":index,"kind":kind_name(request),"key":request.public_inputs.asset_id.0,
        "old_leaf_kind":leaf_name(&request.witness.leaf),"new_leaf_kind":leaf_name(&new),
        "old_leaf_encoding":request.witness.leaf.encode().iter().map(|x|x.as_canonical_u32()).collect::<Vec<_>>(),
        "new_leaf_encoding":new.encode().iter().map(|x|x.as_canonical_u32()).collect::<Vec<_>>(),
        "old_root":digest(&request.public_inputs.old_root),"new_root":digest(&request.public_inputs.new_root),
        "value_digest":digest(&request.public_inputs.value_digest),"op_kind_tag":request.public_inputs.op_kind_tag,
        "siblings":request.witness.path.siblings.iter().map(digest).collect::<Vec<_>>()})
}
fn circuit_sha(circuit:&LayeredCircuit<BaseField>)->String {
    let mut h=Sha256::new();
    h.update(b"ssgkr-supplement/circuit-source-layout/v1");
    h.update((circuit.input_width_bits as u64).to_le_bytes());
    h.update((circuit.layers.len() as u64).to_le_bytes());
    for layer in &circuit.layers {
        h.update((layer.width_bits as u64).to_le_bytes()); h.update((layer.gates.len() as u64).to_le_bytes());
        for gate in &layer.gates {h.update([gate_kind_tag(gate.kind)]);for x in [gate.out,gate.in1,gate.in2,gate.coeff.as_canonical_u32()]{h.update(x.to_le_bytes());}}
        h.update((layer.consts.len() as u64).to_le_bytes());for (wire,value) in &layer.consts{h.update(wire.to_le_bytes());h.update(value.as_canonical_u32().to_le_bytes());}
    }
    h.finalize().iter().map(|b|format!("{b:02x}")).collect()
}

#[derive(Clone)]
struct Options {suite:String,kind:String,variant:String,cell:String,repeat:usize,order:usize,samples:usize,warmup:usize,batch:usize,workers:usize,depth:u32,out:PathBuf,baseline:PathBuf,seed:u64}
impl Options {
    fn read()->Self {
        let number=|name,default|fixture::argument(name,default).parse::<usize>().expect("integer option");
        let repeat=number("--repeat","1");let order=number("--order","0");
        Self {suite:fixture::argument("--suite","A"),kind:fixture::argument("--kind","membership"),variant:fixture::argument("--variant",""),cell:fixture::argument("--cell","probe"),repeat,order,samples:number("--samples","3"),warmup:number("--warmup","1"),batch:number("--batch","32"),workers:number("--workers","48"),depth:number("--depth","24") as u32,out:fixture::argument("--out","results").into(),baseline:fixture::argument("--baseline","OriginalControls").into(),seed:fixture::SEED ^ (repeat as u64).wrapping_mul(0x9e3779b97f4a7c15) ^ order as u64}
    }
    fn baseline_hashes(&self,kind:&str,depth:u32)->Vec<String>{fs::read_to_string(self.baseline.join(format!("native-{kind}-d{depth}.hashes"))).expect("frozen original fixture hashes").lines().map(str::to_owned).collect()}
}

struct Timing {phase:&'static str,oracle:&'static str,mode:&'static str,sample:usize,warm:bool,start:u128,elapsed:u128,user:Option<u64>,sys:Option<u64>}
fn timed<T>(phase:&'static str,oracle:&'static str,mode:&'static str,sample:usize,warm:bool,op:impl FnOnce()->T)->(T,Timing){
    let cpu0=ticks();let start=now();let instant=Instant::now();let result=black_box(op());let elapsed=instant.elapsed().as_nanos();let cpu1=ticks();
    let delta=cpu0.zip(cpu1).map(|((u0,s0),(u1,s1))|(u1.saturating_sub(u0),s1.saturating_sub(s0)));
    (result,Timing{phase,oracle,mode,sample,warm,start,elapsed,user:delta.map(|x|x.0),sys:delta.map(|x|x.1)})
}
struct Output {options:Options,circuit_sha:String,rows:Vec<String>}
impl Output {
    fn add(&mut self,t:Timing,request:Option<(&SyncRequest,usize)>,bytes:usize,canonical:&str,proofs:usize){
        let o=&self.options;
        let info=request.map(|(r,i)|{let n=new_leaf(r);(i.to_string(),kind_name(r).to_string(),leaf_name(&r.witness.leaf).to_string(),leaf_name(&n).to_string(),format!("{}/{}",payload_len(&r.witness.leaf),payload_len(&n)))}).unwrap_or_else(||("batch".into(),o.kind.clone(),"mixed_or_batch".into(),"mixed_or_batch".into(),"see_fixtures".into()));
        let policy=if o.variant=="root_chain_update"{"same_key_sequential_root_chain"}else if o.variant=="large_key_member"{"sequential_2pow23_range_within_d24"}else{"distinct_keys_within_24bits"};
        let fields=vec![o.cell.clone(),o.repeat.to_string(),o.order.to_string(),o.seed.to_string(),info.0,info.1,o.depth.to_string(),"31".into(),info.2,info.3,info.4,policy.into(),if o.variant=="root_chain_update"{o.cell.clone()}else{String::new()},o.batch.to_string(),o.workers.to_string(),env("SSGR_CPUSET"),"native".into(),env("SSGR_SOURCE_SHA"),env("SSGR_DRIVER_SHA"),env("SSGR_BINARY_SHA"),self.circuit_sha.clone(),t.phase.into(),t.oracle.into(),t.mode.into(),t.sample.to_string(),t.warm.to_string(),t.start.to_string(),t.elapsed.to_string(),t.user.map(|x|x.to_string()).unwrap_or_default(),t.sys.map(|x|x.to_string()).unwrap_or_default(),"proc_stat_clock_ticks;see_CLK_TCK;not_nanoseconds".into(),String::new(),String::new(),String::new(),proofs.to_string(),bytes.to_string(),canonical.into(),"true".into(),"0".into()];
        assert_eq!(fields.len(),HEADER.split(',').count());self.rows.push(fields.iter().map(|x|csv(x)).collect::<Vec<_>>().join(","));
    }
    fn finish(&self){let body=format!("{}\n{}\n",HEADER,self.rows.join("\n"));fs::write(self.options.out.join("metrics.csv"),body).expect("metrics");}
}
fn controls(prover:&StateSyncProver,prepared:&PreparedSync,request:&SyncRequest,result:&SyncResult)->Vec<u8>{
    assert!(prover.verify_sync_op_prepared(prepared,request,result),"honest prepared reject");
    let bytes=prover.encode_sync_result(prepared,result).expect("encode");assert!(prover.verify_encoded_sync_op(prepared,request,&bytes),"honest encoded reject");
    let mut bad=result.clone();bad.proof.layer_proofs[0].eval_x+=ChallengeField::ONE;assert!(!prover.verify_sync_op_prepared(prepared,request,&bad),"typed proof tamper accepted");
    let mut pi=request.clone();pi.public_inputs.value_digest.0[0]+=BaseField::ONE;assert!(!prover.verify_sync_op_prepared(prepared,&pi,result),"wrong PI accepted");
    let mut root=request.clone();root.public_inputs.old_root.0[0]+=BaseField::ONE;assert!(!prover.verify_sync_op_prepared(prepared,&root,result),"wrong root accepted");bytes
}
fn save_fixtures(out:&Path,requests:&[SyncRequest]){fs::write(out.join("fixtures.jsonl"),requests.iter().enumerate().map(|(i,r)|request_json(r,i).to_string()).collect::<Vec<_>>().join("\n")+"\n").expect("fixtures");}
fn save_metadata(o:&Options,circuit_hash:&str,mut metadata:Value){
    metadata["cell_id"]=json!(o.cell);metadata["suite"]=json!(o.suite);metadata["kind"]=json!(o.kind);metadata["depth"]=json!(o.depth);metadata["batch"]=json!(o.batch);metadata["workers"]=json!(o.workers);metadata["leaf_max_fields"]=json!(31);metadata["fixture_count"]=json!(if o.suite=="B"{o.batch}else{o.samples});metadata["circuit_sha"]=json!(circuit_hash);
    metadata["order_seed"]=json!(o.seed);metadata["seed_role"]=json!("execution_order_only; not independently generated corpora across repeats");metadata["fixture_base_seed"]=json!(fixture::SEED);metadata["fixture_generator"]=json!(if o.suite=="C"{"variants-v1"}else{"immutable-original-constructor-v1"});
    metadata["fixture_seed_rule"]=json!(if o.suite=="C"{"SEED XOR 0x435f56415249414e XOR (variant_index<<40); sequential SplitMix64 stream, identical corpus across repeats"}else{"SEED XOR (depth<<32) XOR (kind_tag<<56) XOR fixture_index; identical corpus across repeats"});
    if o.suite=="C"{let variant_index=variants::NAMES.iter().position(|name|*name==o.variant).expect("variant index");metadata["fixture_variant_index"]=json!(variant_index);metadata["fixture_generator_initial_seed"]=json!(fixture::SEED ^ 0x435f56415249414e ^ ((variant_index as u64)<<40));}
    metadata["source_sha"]=json!(env("SSGR_SOURCE_SHA"));metadata["driver_sha"]=json!(env("SSGR_DRIVER_SHA"));metadata["binary_sha"]=json!(env("SSGR_BINARY_SHA"));metadata["fixtures_sha256"]=json!(sha(&fs::read(o.out.join("fixtures.jsonl")).expect("fixture bytes")));
    if o.suite=="B"{metadata["encoded_bytes_log_sha256"]=json!(sha(&fs::read(o.out.join("encoded-bytes.jsonl")).expect("byte-log bytes")));}
    fs::write(o.out.join("metadata.json"),serde_json::to_string_pretty(&metadata).expect("metadata JSON")).expect("metadata");
}
fn shape(circuit:&LayeredCircuit<BaseField>,derived:&DerivedRegularWiring)->Value{
    let stats=derived.stats();json!({"input_width_bits":circuit.input_width_bits,"layers":circuit.layers.iter().map(|l|json!({"width_bits":l.width_bits,"lin_gates":l.gates.iter().filter(|g|g.kind==GateKind::Lin).count(),"mul_gates":l.gates.iter().filter(|g|g.kind==GateKind::Mul).count(),"pow3_gates":l.gates.iter().filter(|g|g.kind==GateKind::Pow3).count(),"constants":l.consts.len()})).collect::<Vec<_>>(),"derived_groups":stats.groups,"grouped_gates":stats.grouped_gates,"sparse_gates":stats.sparse_gates,"grouped_consts":stats.grouped_consts,"sparse_consts":stats.sparse_consts})
}
fn permutation(count:usize,seed:u64)->Vec<usize>{let mut p:Vec<_>=(0..count).collect();let mut s=seed;for i in (1..count).rev(){let j=(fixture::splitmix(&mut s)%(i as u64+1)) as usize;p.swap(i,j);}p}

fn run_a(o:Options){
    assert!([24,28,32].contains(&o.depth)&&o.samples>0&&o.samples<=768);
    let config=StateSyncGkrConfig{smt:SmtParams{depth:o.depth,..Default::default()},layer_strategy:LayerStrategy::A,..Default::default()};
    let prover=StateSyncProver::new(config.clone());let requests:Vec<_>=(0..o.samples).map(|i|fixture::original(o.depth,&o.kind,i)).collect();
    save_fixtures(&o.out,&requests);let kind=requests[0].operation.kind();let setup_start=Instant::now();let prepared=prover.prepare(kind).expect("public preparation");let excluded_prepare=setup_start.elapsed().as_nanos();
    let template=Poseidon2Gadget::new(config.smt.leaf_max_fields as usize).round_template();let expected=o.baseline_hashes(&o.kind,o.depth);
    let order=permutation(o.samples,o.seed);let mut output=Output{options:o.clone(),circuit_sha:String::new(),rows:Vec::new()};let mut metadata=Value::Null;
    for iteration in 0..o.warmup+o.samples {
        let warm=iteration<o.warmup;let sample=if warm{iteration}else{iteration-o.warmup};let index=if warm{iteration%requests.len()}else{order[sample]};let r=&requests[index];
        let ((circuit,hints),t_compile)=timed("compile_with_hints","none","single",sample,warm,||compile_with_hints(&config.smt,kind,config.layer_strategy,&template).expect("compile"));
        let (derived,t_derive)=timed("derive_wiring","derived","single",sample,warm,||DerivedRegularWiring::derive(&circuit,&hints));
        let (commitment,t_commit)=timed("circuit_commitment","none","single",sample,warm,||full_circuit_commitment(&circuit,kind,&config.smt,config.layer_strategy));assert_eq!(&commitment,prepared.circuit_commitment());
        let (witness,t_witness)=timed("witness","none","single",sample,warm,||generate_witness(&config.smt,config.layer_strategy,&circuit,&r.operation,&r.public_inputs,&r.witness).expect("witness"));
        let (proof,t_prove)=timed("prove_on","none","single",sample,warm,||prove_on(&config,&circuit,kind,&commitment,&r.public_inputs,&witness));
        let result=SyncResult{public_inputs:r.public_inputs.clone(),proof};
        let (bytes,t_encode)=timed("encode","none","serial",sample,warm,||prover.encode_sync_result(&prepared,&result).expect("encode"));
        let table=TableWiring::new(&circuit);let table_first=fixture::splitmix(&mut (o.seed ^ iteration as u64))&1==0;
        let mut verification=Vec::with_capacity(2);
        for oracle in if table_first{["table","derived"]}else{["derived","table"]} {
            let (accepted,t)=if oracle=="table"{timed("verify","table","single",sample,warm,||verify_sync_op_with(&config,r,&result,&circuit,&table,&commitment))}else{timed("verify","derived","single",sample,warm,||verify_sync_op_with(&config,r,&result,&circuit,&derived,&commitment))};assert!(accepted,"shared verifier reject");verification.push(t);
        }
        let (accepted,t_encoded)=timed("encoded_verify","derived","serial",sample,warm,||prover.verify_encoded_sync_op(&prepared,r,&bytes));assert!(accepted);
        let hash=sha(&bytes);assert_eq!(hash,expected[index],"direct stages differ from original canonical proof");output.circuit_sha=circuit_sha(&circuit);
        if metadata.is_null(){let s=derived.stats();metadata=json!({"input_width_bits":circuit.input_width_bits,"layers":circuit.layers.iter().map(|l|json!({"width_bits":l.width_bits,"lin_gates":l.gates.iter().filter(|g|g.kind==GateKind::Lin).count(),"mul_gates":l.gates.iter().filter(|g|g.kind==GateKind::Mul).count(),"pow3_gates":l.gates.iter().filter(|g|g.kind==GateKind::Pow3).count(),"constants":l.consts.len()})).collect::<Vec<_>>(),"sumcheck_rounds":result.proof.layer_proofs.iter().map(|l|l.sumcheck.round_polys.len()).sum::<usize>(),"derived_groups":s.groups,"grouped_gates":s.grouped_gates,"sparse_gates":s.sparse_gates,"grouped_consts":s.grouped_consts,"sparse_consts":s.sparse_consts,"excluded_public_prepare_ns":excluded_prepare,"table_setup":"reference wrapper only, O(1), outside oracle evaluation timer","circuit_sha":output.circuit_sha});}
        for t in [t_compile,t_derive,t_commit,t_witness,t_prove,t_encode,t_encoded].into_iter().chain(verification){output.add(t,Some((r,index)),bytes.len(),&hash,1);}
    }
    save_metadata(&o,&output.circuit_sha,metadata);output.finish();
}

fn run_b(o:Options){
    assert!([32,192,768].contains(&o.batch)&&[48,192].contains(&o.workers)&&o.depth==24);
    let config=StateSyncGkrConfig{smt:SmtParams{depth:24,..Default::default()},..Default::default()};let prover=StateSyncProver::new(config.clone());let requests:Vec<_>=(0..o.batch).map(|i|fixture::original(24,&o.kind,i)).collect();save_fixtures(&o.out,&requests);let prepared=prover.prepare(requests[0].operation.kind()).expect("prepare");let expected=o.baseline_hashes(&o.kind,24);
    let (circuit,hints)=compile_with_hints(&config.smt,requests[0].operation.kind(),config.layer_strategy,&Poseidon2Gadget::default().round_template()).expect("metadata compile");let derived=DerivedRegularWiring::derive(&circuit,&hints);let circuit_shape=shape(&circuit,&derived);let mut output=Output{options:o.clone(),circuit_sha:circuit_sha(&circuit),rows:Vec::new()};let pool=rayon::ThreadPoolBuilder::new().num_threads(o.workers).build().expect("pool");let mut byte_log=BufWriter::new(fs::File::create(o.out.join("encoded-bytes.jsonl")).expect("byte log"));let mut sumcheck_rounds=0;
    for iteration in 0..o.warmup+o.samples {
        let warm=iteration<o.warmup;let sample=if warm{iteration}else{iteration-o.warmup};let parallel_first=fixture::splitmix(&mut (o.seed ^ iteration as u64))&1==0;
        for mode in if parallel_first{["parallel","serial"]}else{["serial","parallel"]} {
            let ((timings,encoded,rounds),t_full)=timed("complete_pipeline","derived",mode,sample,warm,||{
                let (jobs,t_witness)=timed("witness_batch","none",mode,sample,warm,||pool.install(||requests.par_iter().map(|r|prover.make_job_prepared(&prepared,r).expect("job")).collect::<Vec<_>>()));
                let (proofs,t_prove)=timed("prove_batch","none",mode,sample,warm,||pool.install(||prover.prove_batch_parallel(&prepared,&jobs)));
                let results:Vec<_>=proofs.into_iter().zip(&requests).map(|(proof,r)|SyncResult{public_inputs:r.public_inputs.clone(),proof}).collect();
                let rounds=results[0].proof.layer_proofs.iter().map(|l|l.sumcheck.round_polys.len()).sum::<usize>();let (encoded,t_encode)=timed("encode_batch","none",mode,sample,warm,||if mode=="parallel"{pool.install(||results.par_iter().map(|r|prover.encode_sync_result(&prepared,r).expect("encode")).collect::<Vec<_>>())}else{results.iter().map(|r|prover.encode_sync_result(&prepared,r).expect("encode")).collect::<Vec<_>>()});
                let (verdicts,t_verify)=timed("encoded_verify_batch","derived",mode,sample,warm,||if mode=="parallel"{pool.install(||requests.par_iter().zip(&encoded).map(|(r,b)|prover.verify_encoded_sync_op(&prepared,r,b)).collect::<Vec<_>>())}else{requests.iter().zip(&encoded).map(|(r,b)|prover.verify_encoded_sync_op(&prepared,r,b)).collect::<Vec<_>>()});assert_eq!(verdicts.len(),requests.len());assert!(verdicts.iter().all(|x|*x));
                (vec![t_witness,t_prove,t_encode,t_verify],encoded,rounds)
            });
            sumcheck_rounds=rounds;let mut batch_hash=Sha256::new();let total_bytes:usize=encoded.iter().map(Vec::len).sum();for (i,bytes) in encoded.iter().enumerate(){let hash=sha(bytes);assert_eq!(hash,expected[i],"batch input/output order or canonical bytes differ");batch_hash.update(hash.as_bytes());writeln!(byte_log,"{}",json!({"sample_index":sample,"warmup":warm,"output_mode":mode,"fixture_id":i,"bytes":bytes.len(),"canonical_sha256":hash})).expect("byte record");}
            let hash:String=batch_hash.finalize().iter().map(|b|format!("{b:02x}")).collect();for t in timings.into_iter().chain([t_full]){output.add(t,None,total_bytes,&hash,o.batch);}
        }
    }
    byte_log.flush().expect("flush bytes");save_metadata(&o,&output.circuit_sha,json!({"circuit_shape":circuit_shape,"sumcheck_rounds":sumcheck_rounds,"output_modes":["serial","parallel"],"pipeline_interval":"actual witness creation through encoded acceptance; includes phase tick probes, result assembly and temporary jobs/proofs/verdict drops; encoded result drops and canonical hash comparison are outside","witness_stage":"parallel make_job_prepared includes public-input cloning","stage_sum":"separate direct timers; not substituted for actual complete_pipeline","cpu_ticks":"quantized process CPU observations, not nanosecond CPU timers"}));output.finish();
}

fn run_c(mut o:Options){
    o.depth=24;o.batch=1;o.workers=1;assert!(o.samples>0);let requests=variants::construct(&o.variant,o.samples);o.kind=kind_name(&requests[0]).into();save_fixtures(&o.out,&requests);
    let config=StateSyncGkrConfig{smt:SmtParams{depth:24,..Default::default()},..Default::default()};let hasher=Poseidon2Gadget::new(config.smt.leaf_max_fields as usize);let prover=StateSyncProver::new(config.clone());let prepared=prover.prepare(requests[0].operation.kind()).expect("prepare");let (circuit,hints)=compile_with_hints(&config.smt,requests[0].operation.kind(),config.layer_strategy,&hasher.round_template()).expect("metadata compile");let derived=DerivedRegularWiring::derive(&circuit,&hints);let circuit_shape=shape(&circuit,&derived);let mut output=Output{options:o.clone(),circuit_sha:circuit_sha(&circuit),rows:Vec::new()};let order=if o.variant=="root_chain_update"{(0..requests.len()).collect()}else{permutation(requests.len(),o.seed)};let mut chain_cursor=requests[0].public_inputs.old_root;let mut sumcheck_rounds=0;
    for iteration in 0..o.warmup+o.samples {
        let warm=iteration<o.warmup;let sample=if warm{iteration}else{iteration-o.warmup};let index=if warm{iteration%requests.len()}else{order[sample]};let r=&requests[index];if o.variant=="root_chain_update"&&!warm{assert_eq!(chain_cursor,r.public_inputs.old_root,"timed root chain predecessor");}
        let (valid,t_native)=timed("native_predicate","native","single",sample,warm,||smt_valid_native(&hasher,&config.smt,&r.operation,&r.public_inputs.old_root,&r.public_inputs.new_root,&r.witness).expect("native predicate"));assert!(valid);
        let ((result,bytes,t_prove,t_encode,t_verify),t_full)=timed("complete_request","derived","serial",sample,warm,||{
            let (result,t_prove)=timed("prepared_request","none","single",sample,warm,||prover.prove_sync_op_prepared(&prepared,r).expect("prepared request"));let (bytes,t_encode)=timed("encode","none","serial",sample,warm,||prover.encode_sync_result(&prepared,&result).expect("encode"));let (ok,t_verify)=timed("encoded_verify","derived","serial",sample,warm,||prover.verify_encoded_sync_op(&prepared,r,&bytes));assert!(ok);(result,bytes,t_prove,t_encode,t_verify)
        });if sumcheck_rounds==0{sumcheck_rounds=result.proof.layer_proofs.iter().map(|l|l.sumcheck.round_polys.len()).sum::<usize>();}let hash=sha(&bytes);let checked=controls(&prover,&prepared,r,&result);assert_eq!(checked,bytes);if o.variant=="root_chain_update"&&!warm{chain_cursor=r.public_inputs.new_root;}
        for t in [t_native,t_prove,t_encode,t_verify,t_full]{output.add(t,Some((r,index)),bytes.len(),&hash,1);}
    }
    save_metadata(&o,&output.circuit_sha,json!({"variant":o.variant,"circuit_shape":circuit_shape,"sumcheck_rounds":sumcheck_rounds,"root_chain":"same key/path, constructor and timed cursor verify every previous new_root equals next old_root; warmups excluded from timed chain state; no distributed commit", "input_native_validity":"all timed and warmup requests accepted", "controls":"each result accepted by prepared and encoded verifier; typed proof/valueDigest/oldRoot mutations rejected outside timing","maximum_sync_fields":21}));output.finish();
}

fn run_controls(o:&Options){
    let mut rows=Vec::new();
    for depth in [24,28,32]{for kind in ["membership","nonmembership","update"]{
        let config=StateSyncGkrConfig{smt:SmtParams{depth,..Default::default()},..Default::default()};let prover=StateSyncProver::new(config.clone());let r=fixture::original(depth,kind,0);let prepared=prover.prepare(r.operation.kind()).expect("prepare");let result=prover.prove_sync_op_prepared(&prepared,&r).expect("prove");let bytes=controls(&prover,&prepared,&r,&result);let original=fs::read(o.baseline.join(format!("native-{kind}-d{depth}.bin"))).expect("old representative bytes");assert_eq!(bytes,original,"original representative proof changed");
        let (circuit,hints)=compile_with_hints(&config.smt,r.operation.kind(),config.layer_strategy,&Poseidon2Gadget::default().round_template()).expect("compile");let commitment=full_circuit_commitment(&circuit,r.operation.kind(),&config.smt,config.layer_strategy);let derived=DerivedRegularWiring::derive(&circuit,&hints);let table=TableWiring::new(&circuit);assert!(verify_sync_op_with(&config,&r,&result,&circuit,&derived,&commitment));assert!(verify_sync_op_with(&config,&r,&result,&circuit,&table,&commitment));rows.push(json!({"class":"original_representative","kind":kind,"depth":depth,"canonical_sha256":sha(&bytes),"bytes":bytes.len(),"positive":true,"typed_negatives":3,"derived_table_agree":true}).to_string());
    }}
    if o.suite=="representative"{fs::write(o.out.join("controls.jsonl"),rows.join("\n")+"\n").expect("representative controls");return;}
    for name in variants::NAMES{let requests=variants::construct(name,128);let config=StateSyncGkrConfig::default();let prover=StateSyncProver::new(config.clone());let hasher=Poseidon2Gadget::new(config.smt.leaf_max_fields as usize);let prepared=prover.prepare(requests[0].operation.kind()).expect("prepare");for (index,r) in requests.iter().enumerate(){assert!(smt_valid_native(&hasher,&config.smt,&r.operation,&r.public_inputs.old_root,&r.public_inputs.new_root,&r.witness).expect("native"));let result=prover.prove_sync_op_prepared(&prepared,r).expect("new fixture prove");let bytes=controls(&prover,&prepared,r,&result);if index==0{fs::write(o.out.join(format!("{name}.bin")),&bytes).expect("representative");}rows.push(json!({"class":"new_fixture","variant":name,"fixture_id":index,"canonical_sha256":sha(&bytes),"bytes":bytes.len(),"native":true,"positive":true,"typed_negatives":3}).to_string());}save_fixtures(&o.out.join(name),&requests);}
    for kind in ["membership","nonmembership","update"]{let config=StateSyncGkrConfig::default();let prover=StateSyncProver::new(config);let requests:Vec<_>=(0..768).map(|i|fixture::original(24,kind,i)).collect();let prepared=prover.prepare(requests[0].operation.kind()).expect("prepare");let expected=o.baseline_hashes(kind,24);let jobs:Vec<_>=requests.iter().map(|r|prover.make_job_prepared(&prepared,r).expect("job")).collect();let sequential=prover.prove_batch_prepared(&prepared,&jobs);for workers in [48,192]{let pool=rayon::ThreadPoolBuilder::new().num_threads(workers).build().expect("pool");let parallel=pool.install(||prover.prove_batch_parallel(&prepared,&jobs));assert_eq!(sequential,parallel,"parallel proof/order mismatch");let results:Vec<_>=parallel.into_iter().zip(&requests).map(|(proof,r)|SyncResult{proof,public_inputs:r.public_inputs.clone()}).collect();let serial:Vec<_>=results.iter().map(|r|prover.encode_sync_result(&prepared,r).expect("encode")).collect();let encoded:Vec<_>=pool.install(||results.par_iter().map(|r|prover.encode_sync_result(&prepared,r).expect("encode")).collect());assert_eq!(serial,encoded);let verdicts:Vec<_>=pool.install(||requests.par_iter().zip(&encoded).map(|(r,b)|prover.verify_encoded_sync_op(&prepared,r,b)).collect());assert_eq!(verdicts.len(),768);assert!(verdicts.iter().all(|x|*x));for (i,b) in encoded.iter().enumerate(){assert_eq!(sha(b),expected[i]);}rows.push(json!({"class":"seq_parallel_output","kind":kind,"workers":workers,"fixtures":768,"bytes_order_match":true,"encoded_acceptance":true}).to_string());}}
    fs::write(o.out.join("controls.jsonl"),rows.join("\n")+"\n").expect("controls");
}

fn main(){let o=Options::read();fs::create_dir_all(&o.out).expect("output directory");if o.suite=="controls"||o.suite=="representative"{for name in variants::NAMES{fs::create_dir_all(o.out.join(name)).expect("fixture directory");}run_controls(&o);}else{match o.suite.as_str(){"A"=>run_a(o.clone()),"B"=>run_b(o.clone()),"C"=>run_c(o.clone()),_=>panic!("unknown suite")}}fs::write(o.out.join("terminal.txt"),"supplement-cell=PASS\n").expect("terminal");}
