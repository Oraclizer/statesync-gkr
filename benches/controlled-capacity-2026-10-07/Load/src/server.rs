use crate::{shared::*,wire::{self,Job,Reply}};
use rayon::prelude::*;
use serde_json::json;
use std::{collections::{HashMap,VecDeque}, net::{TcpListener,TcpStream}, sync::{Arc,Mutex,atomic::{AtomicBool,AtomicUsize,Ordering},mpsc::{self,SyncSender,TrySendError}}, time::{Duration,Instant}};
use statesync_gkr::{SyncRequest,SyncResult};

struct Pending { job:Job, request:SyncRequest, writer:Arc<Mutex<TcpStream>>, received:u64, enqueued:u64, admitted:Instant }
fn base(p:&Pending,host:&str)->Reply {
    Reply { protocol:wire::PROTOCOL,run_id:p.job.run_id.clone(),job_id:p.job.job_id,fixture_id:p.job.fixture_id,kind:p.job.input.kind.clone(),host_id:host.into(),process_id:std::process::id(),server_received_unix_ns:p.received,server_enqueued_unix_ns:p.enqueued,..Default::default() }
}
fn reject(p:Pending,host:&str,error:&str,log:&Logger)->Result<()> {
    let mut reply=base(&p,host); reply.error=Some(error.into()); reply.server_send_start_unix_ns=now();
    let result=wire::write_reply(&mut *p.writer.lock().map_err(|_|"socket writer poisoned")?,&reply,&[]);
    log.write(&json!({"event":"server_reject","reply":reply,"warmup":p.job.warmup,"send_end_unix_ns":now(),"error":error,"write_result":result.as_ref().map(|x|*x).map_err(|x|x.to_string())}))?;
    Ok(())
}

fn connection(mut reader:TcpStream,tx:SyncSender<Pending>,state:Arc<State>,log:Arc<Logger>,stop:Arc<AtomicBool>,queued:Arc<AtomicUsize>,host:String,max_queue:usize)->Result<()> {
    reader.set_nodelay(true)?; reader.set_read_timeout(Some(Duration::from_millis(100)))?;
    let writer=Arc::new(Mutex::new(reader.try_clone()?));
    while !stop.load(Ordering::Relaxed) {
        let (job,received,request_wire_bytes,json_decode_ns)=match wire::read_request(&mut reader,&stop) {
            Ok(parts)=>parts,
            Err(e) if matches!(e.kind(),std::io::ErrorKind::UnexpectedEof|std::io::ErrorKind::Interrupted)=>break,
            Err(e)=> { log.write(&json!({"event":"connection_error","observed_unix_ns":now(),"error":e.to_string()}))?; break; }
        };
        let decoded=Instant::now();
        if job.protocol!=wire::PROTOCOL || job.run_id.is_empty() {
            log.write(&json!({"event":"protocol_error","job_id":job.job_id,"observed_unix_ns":received}))?; break;
        }
        let request=match job.input.request(state.depth) {
            Ok(request)=>request,
            Err(e)=> {
                let reply=Reply { protocol:wire::PROTOCOL,run_id:job.run_id.clone(),job_id:job.job_id,fixture_id:job.fixture_id,kind:job.input.kind.clone(),host_id:host.clone(),process_id:std::process::id(),server_received_unix_ns:received,error:Some(format!("input: {e}")),..Default::default() };
                wire::write_reply(&mut *writer.lock().map_err(|_|"socket writer poisoned")?,&reply,&[])?;
                log.write(&json!({"event":"input_error","reply":reply,"observed_unix_ns":now(),"decode_ns":ns(decoded.elapsed())}))?; continue;
            }
        };
        let enqueued=now(); let p=Pending { job,request,writer:writer.clone(),received,enqueued,admitted:Instant::now() };
        log.write(&json!({"event":"server_arrival","run_id":p.job.run_id,"job_id":p.job.job_id,"fixture_id":p.job.fixture_id,"kind":p.job.input.kind,"warmup":p.job.warmup,"scheduled_frontend_unix_ns":p.job.scheduled_unix_ns,"received_unix_ns":received,"enqueued_unix_ns":enqueued,"json_decode_ns":json_decode_ns,"request_decode_ns":ns(decoded.elapsed()),"request_wire_bytes":request_wire_bytes,"input_sha256":sha(&serde_json::to_vec(&p.job.input)?)}))?;
        if queued.fetch_add(1,Ordering::Relaxed)>=max_queue {
            queued.fetch_sub(1,Ordering::Relaxed); reject(p,&host,"server_total_queue_full",&log)?; continue;
        }
        match tx.try_send(p) {
            Ok(())=>{},
            Err(TrySendError::Full(p))=> { queued.fetch_sub(1,Ordering::Relaxed); reject(p,&host,"server_ingress_queue_full",&log)?; },
            Err(TrySendError::Disconnected(p))=> { queued.fetch_sub(1,Ordering::Relaxed); reject(p,&host,"server_stopping",&log)?; break; },
        }
    }
    Ok(())
}

fn process(batch:Vec<Pending>,id:u64,state:&State,host:&str,log:&Logger)->Result<()> {
    let kind=batch[0].job.input.kind.clone(); let prepared=&state.prepared[&kind]; let size=batch.len();
    let flush=now();
    let queue_durations:Vec<_>=batch.iter().map(|p|ns(p.admitted.elapsed())).collect();
    let start=Instant::now();
    let jobs_result=state.pool.install(||batch.par_iter().map(|p|state.prover.make_job_prepared(prepared,&p.request).map_err(|e|format!("witness: {e:?}"))).collect::<std::result::Result<Vec<_>,_>>());
    let witness_ns=ns(start.elapsed()); let witness_end=now();
    let jobs=match jobs_result { Ok(jobs)=>jobs,Err(e)=> { for p in batch { reject(p,host,&e,log)?; } return Ok(()); } };
    let proving=Instant::now(); let proofs=state.pool.install(||state.prover.prove_batch_parallel(prepared,&jobs));
    let prove_ns=ns(proving.elapsed()); let prove_end=now();
    if proofs.len()!=size { return Err("proof count differs from input count".into()); }
    let results:Vec<_>=proofs.into_iter().zip(&batch).map(|(proof,p)|SyncResult { public_inputs:p.request.public_inputs.clone(),proof }).collect();
    let encoding=Instant::now();
    let encoded=state.pool.install(||results.par_iter().map(|r|state.prover.encode_sync_result(prepared,r).map_err(|e|format!("encode: {e:?}"))).collect::<std::result::Result<Vec<_>,_>>())?;
    let encode_ns=ns(encoding.elapsed()); let encode_end=now();
    let batch_compute_ns=ns(start.elapsed());
    for ((p,bytes),queue_ns) in batch.into_iter().zip(encoded).zip(queue_durations) {
        let mut reply=base(&p,host);
        reply.batch_id=id; reply.batch_size=size; reply.flush_unix_ns=flush;
        reply.witness_start_unix_ns=flush; reply.witness_end_unix_ns=witness_end; reply.prove_end_unix_ns=prove_end; reply.encode_end_unix_ns=encode_end;
        // Instant queue duration uses this host only. The shared batch phases
        // below are not labelled as independent per-proof stage latencies.
        reply.server_queue_ns=queue_ns;
        reply.batch_witness_ns=witness_ns; reply.batch_prove_ns=prove_ns; reply.batch_encode_ns=encode_ns;
        reply.encoded_bytes=bytes.len(); reply.canonical_sha256=sha(&bytes); reply.server_send_start_unix_ns=now();
        let writing=Instant::now(); let result=wire::write_reply(&mut *p.writer.lock().map_err(|_|"socket writer poisoned")?,&reply,&bytes);
        let end=now(); let write_ns=ns(writing.elapsed());
        log.write(&json!({"event":"server_return","reply":reply,"warmup":p.job.warmup,"send_end_unix_ns":end,"write_duration_ns":write_ns,"wire_bytes":result.as_ref().ok(),"write_error":result.as_ref().err().map(|x|x.to_string()),"phase_scope":"batch-shared timers; byte hashing, framing, send and logging are outside kernel stage timers"}))?;
    }
    log.write(&json!({"event":"server_batch","batch_id":id,"kind":kind,"jobs":size,"flush_unix_ns":flush,"encode_end_unix_ns":encode_end,"batch_compute_ns":batch_compute_ns,"witness_ns":witness_ns,"prove_ns":prove_ns,"encode_ns":encode_ns}))?;
    Ok(())
}

pub fn run()->Result<()> {
    let out=out_dir()?; let log=Logger::new(&out.join("server.jsonl"),usize_arg("--log-flush-every","256")?)?;
    let workers=usize_arg("--workers","48")?; let batch_max=usize_arg("--batch-max","96")?;
    let max_wait=Duration::from_micros(u64_arg("--max-wait-us","1000")?); let max_queue=usize_arg("--max-queue","8192")?;
    if batch_max==0||max_queue==0 { return Err("batch-max and max-queue must be positive".into()); }
    let run_ms=u64_arg("--run-ms","600000")?; if run_ms==0 { return Err("run-ms must be positive".into()); }
    let io_timeout=u64_arg("--io-timeout-ms","5000")?; let host=host_id();
    let state=State::new(u64_arg("--depth","24")? as u32,workers,&log)?;
    state.controls(usize_arg("--control-samples","2")?,&out,&log)?;
    let mut meta=provenance("server"); meta["workers"]=json!(workers); meta["batch_max"]=json!(batch_max); meta["max_wait_us"]=json!(max_wait.as_micros()); meta["max_queue"]=json!(max_queue); meta["run_ms"]=json!(run_ms); meta["queue_policy"]=json!("one FIFO per operation kind; oldest ready kind first; maximum batch size or elapsed oldest wait triggers flush; one compute batch at a time");
    fresh_json(&out.join("metadata.json"),&meta)?;
    let stop=Arc::new(AtomicBool::new(false)); let queued=Arc::new(AtomicUsize::new(0));
    let monitor=telemetry(log.clone(),stop.clone(),queued.clone(),u64_arg("--telemetry-ms","100")?);
    let listener=TcpListener::bind(arg("--listen","127.0.0.1:9400"))?; listener.set_nonblocking(true)?;
    let (tx,rx)=mpsc::sync_channel::<Pending>(max_queue); let mut readers=Vec::new();
    let ready=now(); log.write(&json!({"event":"ready","ready_unix_ns":ready,"listen":listener.local_addr()?.to_string()}))?;
    println!("{}",json!({"status":"SERVER_READY","ready_unix_ns":ready,"listen":listener.local_addr()?.to_string(),"process_id":std::process::id()}));
    let started=Instant::now(); let mut queues:HashMap<String,VecDeque<Pending>>=KINDS.into_iter().map(|k|(k.into(),VecDeque::new())).collect();
    let mut batches=0u64; let mut processed=0usize;
    while started.elapsed()<Duration::from_millis(run_ms) && !stop.load(Ordering::Relaxed) {
        loop { match listener.accept() {
            Ok((stream,peer))=> {
                stream.set_write_timeout(Some(Duration::from_millis(io_timeout)))?;
                log.write(&json!({"event":"connection","peer":peer.to_string(),"observed_unix_ns":now()}))?;
                let (tx,state,log,stop,queued,host)=(tx.clone(),state.clone(),log.clone(),stop.clone(),queued.clone(),host.clone());
                readers.push(std::thread::spawn(move|| { if let Err(e)=connection(stream,tx,state,log.clone(),stop,queued,host,max_queue) { let _=log.write(&json!({"event":"reader_failure","observed_unix_ns":now(),"error":e.to_string()})); } }));
            },
            Err(e) if e.kind()==std::io::ErrorKind::WouldBlock=>break,
            Err(e)=>return Err(e.into()),
        } }
        while let Ok(p)=rx.try_recv() { queues.get_mut(&p.job.input.kind).expect("validated kind").push_back(p); }
        let chosen=queues.iter().filter_map(|(kind,q)|q.front().filter(|p|q.len()>=batch_max||p.admitted.elapsed()>=max_wait).map(|p|(kind.clone(),p.admitted))).min_by_key(|x|x.1).map(|x|x.0);
        if let Some(kind)=chosen {
            let q=queues.get_mut(&kind).expect("kind queue"); let n=q.len().min(batch_max);
            let batch:Vec<_>=q.drain(..n).collect(); queued.fetch_sub(n,Ordering::Relaxed); batches+=1; processed+=n;
            log.write(&json!({"event":"flush","batch_id":batches,"kind":kind,"jobs":n,"queued_remaining":queued.load(Ordering::Relaxed),"observed_unix_ns":now()}))?;
            process(batch,batches,&state,&host,&log)?;
        } else {
            let wait=queues.values().filter_map(|q|q.front().map(|p|max_wait.saturating_sub(p.admitted.elapsed()))).min().unwrap_or(Duration::from_millis(10)).min(Duration::from_millis(10));
            if let Ok(p)=rx.recv_timeout(wait) { queues.get_mut(&p.job.input.kind).expect("validated kind").push_back(p); }
        }
    }
    stop.store(true,Ordering::Relaxed);
    for reader in readers { reader.join().map_err(|_|"server reader panic")?; }
    while let Ok(p)=rx.try_recv() { queues.get_mut(&p.job.input.kind).expect("validated kind").push_back(p); }
    let unprocessed:usize=queues.values().map(VecDeque::len).sum();
    for q in queues.values_mut() { for p in q.drain(..) { reject(p,&host,"server_run_limit_before_compute",&log)?; } }
    if let Some(m)=monitor { m.join().map_err(|_|"telemetry panic")?; }
    fresh_json(&out.join("terminal.json"),&json!({"status":"SERVER_STOPPED","processed_jobs":processed,"unprocessed_jobs":unprocessed,"batches":batches,"ready_unix_ns":ready,"finish_unix_ns":now(),"logging":log.finish()?,"note":"Run limit ends admission; unprocessed jobs are explicit failures. Read frontend acceptance rows for success counts."}))?;
    Ok(())
}
