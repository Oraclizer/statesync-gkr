use crate::{fixture, wire::Input};
use rayon::ThreadPool;
use serde_json::{Value,json};
use sha2::{Digest as ShaDigest,Sha256};
use std::{collections::HashMap, fs::{self,File,OpenOptions}, io::{BufWriter,Write}, path::{Path,PathBuf}, sync::{Arc,Mutex,atomic::{AtomicBool,AtomicU64,AtomicUsize,Ordering}}, time::{Duration,Instant,SystemTime,UNIX_EPOCH}};
use statesync_gkr::{PreparedSync,StateSyncGkrConfig,StateSyncProver,SyncRequest,SyncResult,compiler::{SmtOpKind,SmtParams}};
use statesync_gkr::primitives::field::{BaseField,ChallengeField,PrimeCharacteristicRing};

pub type Result<T> = std::result::Result<T,Box<dyn std::error::Error+Send+Sync>>;
pub const KINDS:[&str;3]=["membership","nonmembership","update"];
pub fn now()->u64 { SystemTime::now().duration_since(UNIX_EPOCH).expect("UTC clock before epoch").as_nanos().try_into().expect("timestamp overflow") }
pub fn ns(x:Duration)->u64 { x.as_nanos().min(u64::MAX as u128) as u64 }
pub fn sha(bytes:&[u8])->String { Sha256::digest(bytes).iter().map(|b|format!("{b:02x}")).collect() }
pub fn arg(name:&str,default:&str)->String {
    let xs:Vec<_>=std::env::args().collect();
    if let Some(v)=xs.windows(2).find(|x|x[0]==name) { return v[1].clone(); }
    let key=format!("SSGR_{}",name.trim_start_matches('-').replace('-',"_").to_ascii_uppercase());
    std::env::var(key).unwrap_or_else(|_|default.into())
}
pub fn usize_arg(name:&str,default:&str)->Result<usize> { Ok(arg(name,default).parse()?) }
pub fn u64_arg(name:&str,default:&str)->Result<u64> { Ok(arg(name,default).parse()?) }
pub fn out_dir()->Result<PathBuf> {
    let path=arg("--out",""); if path.is_empty() { return Err("--out or SSGR_OUT is required; use a new result directory".into()); }
    let p=PathBuf::from(path); fs::create_dir_all(&p)?; Ok(p)
}
pub fn fresh_json(path:&Path,value:&Value)->Result<()> {
    let mut file=OpenOptions::new().write(true).create_new(true).open(path)?;
    serde_json::to_writer_pretty(&mut file,value)?; file.write_all(b"\n")?; file.sync_all()?; Ok(())
}
pub fn host_id()->String { arg("--host-id",&std::env::var("HOSTNAME").unwrap_or_else(|_|"unspecified-host".into())) }
pub fn provenance(role:&str)->Value {
    let env=|key:&str|std::env::var(key).unwrap_or_else(|_|"UNAVAILABLE".into());
    json!({"schema":"statesync-gkr.load-driver.v1","role":role,"host_id":host_id(),"process_id":std::process::id(),"run_id":arg("--run-id","pilot"),"repeat":arg("--repeat","1"),"source_sha":env("SSGR_SOURCE_SHA"),"driver_sha":env("SSGR_DRIVER_SHA"),"binary_sha":env("SSGR_BINARY_SHA"),"environment_sha":env("SSGR_ENVIRONMENT_SHA"),"cpu_set":env("SSGR_CPUSET"),"hardware_profile":env("SSGR_HARDWARE_PROFILE"),"argv":std::env::args().collect::<Vec<_>>(),"utc_start_ns":now(),"clock":"SystemTime Unix ns for event coordinates; Instant ns for local durations; no cross-host clock equality assumption","scope":"independent inner proofs and actual TCP transport through frontend cryptographic acceptance; no persistent tree state, consensus or finality","fixture_seed":fixture::SEED,"fixture_generator":"immutable-original-constructor-v1","corpus":"same fixed deterministic corpus across independent process repeats; repeated fixtures are independent proof jobs, not distinct input populations"})
}

pub struct Logger {
    writer:Mutex<BufWriter<File>>, flush_every:usize, count:AtomicUsize,
    pub observation_ns:AtomicU64, pub flush_ns:AtomicU64,
}
impl Logger {
    pub fn new(path:&Path,flush_every:usize)->Result<Arc<Self>> {
        let file=OpenOptions::new().write(true).create_new(true).open(path)?;
        Ok(Arc::new(Self { writer:Mutex::new(BufWriter::with_capacity(1024*1024,file)),flush_every:flush_every.max(1),count:AtomicUsize::new(0),observation_ns:AtomicU64::new(0),flush_ns:AtomicU64::new(0) }))
    }
    pub fn write(&self,value:&Value)->Result<()> {
        let started=Instant::now(); let bytes=serde_json::to_vec(value)?;
        let mut w=self.writer.lock().map_err(|_|"raw writer mutex poisoned")?;
        w.write_all(&bytes)?; w.write_all(b"\n")?;
        let count=self.count.fetch_add(1,Ordering::Relaxed)+1;
        if count%self.flush_every==0 { let f=Instant::now(); w.flush()?; self.flush_ns.fetch_add(ns(f.elapsed()),Ordering::Relaxed); }
        self.observation_ns.fetch_add(ns(started.elapsed()),Ordering::Relaxed); Ok(())
    }
    pub fn finish(&self)->Result<Value> {
        self.writer.lock().map_err(|_|"raw writer mutex poisoned")?.flush()?;
        Ok(json!({"rows":self.count.load(Ordering::Relaxed),"serialization_lock_write_ns":self.observation_ns.load(Ordering::Relaxed),"buffer_flush_ns":self.flush_ns.load(Ordering::Relaxed),"flush_every_rows":self.flush_every,"buffer_bytes":1024*1024,"note":"Measured logging work and contention, not a counterfactual correction of throughput."}))
    }
}

pub struct State { pub prover:StateSyncProver, pub prepared:HashMap<String,PreparedSync>, pub pool:ThreadPool, pub depth:u32 }
impl State {
    pub fn new(depth:u32,workers:usize,log:&Logger)->Result<Arc<Self>> {
        if !(1..=32).contains(&depth)||workers==0 { return Err("depth must be 1..32 and workers > 0".into()); }
        let prover=StateSyncProver::new(StateSyncGkrConfig { smt:SmtParams { depth,..Default::default() },..Default::default() });
        let mut prepared=HashMap::new();
        for (name,kind) in [("membership",SmtOpKind::Membership),("nonmembership",SmtOpKind::NonMembership),("update",SmtOpKind::Update)] {
            let t=Instant::now(); let start=now(); let p=prover.prepare(kind).map_err(|e|format!("prepare {name}: {e:?}"))?;
            let identity=prover.circuit_identity(&p).map_err(|e|format!("identity: {e:?}"))?;
            log.write(&json!({"event":"prepare","kind":name,"start_unix_ns":start,"elapsed_ns":ns(t.elapsed()),"identity":format!("{identity:?}"),"included_in_load_interval":false}))?;
            prepared.insert(name.into(),p);
        }
        let pool=rayon::ThreadPoolBuilder::new().num_threads(workers).build()?;
        Ok(Arc::new(Self { prover,prepared,pool,depth }))
    }
    pub fn controls(&self,samples:usize,out:&Path,log:&Logger)->Result<HashMap<(String,usize),String>> {
        if samples==0||samples>=(1usize<<self.depth.min(24)) { return Err("control fixture count outside key range".into()); }
        fs::create_dir_all(out.join("controls"))?; let mut reference=HashMap::new();
        for kind in KINDS {
            let p=&self.prepared[kind];
            let requests:Vec<SyncRequest>=(0..samples).map(|i|fixture::original(self.depth,kind,i)).collect();
            let jobs=requests.iter().map(|r|self.prover.make_job_prepared(p,r).map_err(|e|format!("control witness: {e:?}"))).collect::<std::result::Result<Vec<_>,_>>()?;
            let sequential=self.prover.prove_batch_prepared(p,&jobs);
            let parallel=self.pool.install(||self.prover.prove_batch_parallel(p,&jobs));
            if sequential!=parallel { return Err("sequential/parallel proof or input-order mismatch".into()); }
            for (i,(proof,request)) in sequential.into_iter().zip(&requests).enumerate() {
                let result=SyncResult { public_inputs:request.public_inputs.clone(),proof };
                let bytes=self.prover.encode_sync_result(p,&result).map_err(|e|format!("control encode: {e:?}"))?;
                if !self.prover.verify_encoded_sync_op(p,request,&bytes) { return Err("honest encoded control rejected".into()); }
                let mut bad=result.clone(); bad.proof.layer_proofs[0].eval_x+=ChallengeField::ONE;
                if self.prover.verify_sync_op_prepared(p,request,&bad) { return Err("typed proof mutation accepted".into()); }
                let mut wrong=request.clone(); wrong.public_inputs.value_digest.0[0]+=BaseField::ONE;
                if self.prover.verify_encoded_sync_op(p,&wrong,&bytes) { return Err("value digest mutation accepted".into()); }
                let mut wrong_root=request.clone(); wrong_root.public_inputs.old_root.0[0]+=BaseField::ONE;
                if self.prover.verify_encoded_sync_op(p,&wrong_root,&bytes) { return Err("root mutation accepted".into()); }
                let mut trailing=bytes.clone(); trailing.push(0);
                if self.prover.verify_encoded_sync_op(p,request,&trailing) { return Err("trailing encoded byte accepted".into()); }
                let hash=sha(&bytes); reference.insert((kind.to_string(),i),hash.clone());
                let mut file=OpenOptions::new().write(true).create_new(true).open(out.join("controls").join(format!("{kind}-{i}.bin")))?; file.write_all(&bytes)?;
                log.write(&json!({"event":"control","kind":kind,"fixture_id":i,"positive":true,"typed_proof_rejected":true,"value_digest_rejected":true,"old_root_rejected":true,"trailing_bytes_rejected":true,"sequential_parallel_proof_equal":true,"encoded_bytes":bytes.len(),"canonical_sha256":hash,"input":Input::from_request(request),"included_in_load_interval":false}))?;
            }
        }
        Ok(reference)
    }
}

pub fn telemetry(log:Arc<Logger>,stop:Arc<AtomicBool>,queued:Arc<AtomicUsize>,period_ms:u64)->Option<std::thread::JoinHandle<()>> {
    if period_ms==0 { return None; }
    Some(std::thread::spawn(move|| {
        while !stop.load(Ordering::Relaxed) {
            let observed=now(); let status=fs::read_to_string("/proc/self/status").ok(); let stat=fs::read_to_string("/proc/self/stat").ok();
            let field=|label:&str|status.as_ref().and_then(|s|s.lines().find(|l|l.starts_with(label))).and_then(|l|l.split_whitespace().nth(1)).and_then(|x|x.parse::<u64>().ok());
            let values=stat.as_ref().and_then(|s|s.rsplit_once(')')).map(|(_,s)|s.split_whitespace().collect::<Vec<_>>());
            let tick=|i:usize|values.as_ref().and_then(|v|v.get(i)).and_then(|x|x.parse::<u64>().ok());
            if let Err(e)=log.write(&json!({"event":"telemetry","observed_unix_ns":observed,"requested_period_ms":period_ms,"queued_jobs":queued.load(Ordering::Relaxed),"rss_kib":field("VmRSS:"),"peak_rss_kib":field("VmHWM:"),"process_user_ticks":tick(11),"process_system_ticks":tick(12),"minor_faults":tick(7),"major_faults":tick(9),"cpu_tick_hz":std::env::var("SSGR_CLK_TCK").ok(),"missing_reason":if status.is_none(){Some("/proc unavailable")}else{None},"phase_attribution":"whole process, includes networking, logging and instrumentation"})) { eprintln!("telemetry error: {e}"); stop.store(true,Ordering::Relaxed); break; }
            std::thread::sleep(Duration::from_millis(period_ms));
        }
    }))
}
