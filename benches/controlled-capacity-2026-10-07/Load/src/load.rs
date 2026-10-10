use crate::{fixture,shared::*,wire::{self,Input,Job,Reply}};
use serde_json::json;
use std::{collections::HashMap, net::{Shutdown,TcpStream}, sync::{Arc,Mutex,atomic::{AtomicBool,AtomicUsize,Ordering},mpsc::{self,SyncSender,TrySendError}}, time::{Duration,Instant}};
use statesync_gkr::SyncRequest;

#[derive(Clone)]
struct Entry { job:Job, request:Arc<SyncRequest>, offset_ns:u64, target:String, timeout_logged:bool, verifying:bool }
struct Task { reply:Reply, bytes:Vec<u8>, receive_start:u64, receive_end:u64, wire_bytes:usize, queued:Instant }
#[derive(Default)]
struct Counts { offered:AtomicUsize, submitted:AtomicUsize, accepted:AtomicUsize, accepted_late:AtomicUsize, rejected:AtomicUsize, transport_errors:AtomicUsize, queue_full:AtomicUsize, deadline_events:AtomicUsize, duplicate_or_unknown:AtomicUsize }
fn count(x:&AtomicUsize)->usize { x.load(Ordering::Relaxed) }
fn mixture(text:&str)->Result<Vec<String>> {
    let mut out=Vec::new();
    for part in text.split(',') {
        let (kind,n)=part.split_once(':').unwrap_or((part,"1"));
        if !KINDS.contains(&kind) { return Err(format!("unknown mixture kind {kind}").into()); }
        let weight:usize=n.parse()?; if weight>10000 { return Err("mixture weight is too large".into()); }
        out.extend(std::iter::repeat_n(kind.to_string(),weight));
    }
    if out.is_empty() { return Err("mixture must contain a positive weight".into()); } Ok(out)
}
fn sender(mut socket:TcpStream,rx:mpsc::Receiver<Job>,entries:Arc<Mutex<HashMap<u64,Entry>>>,log:Arc<Logger>,counts:Arc<Counts>,critical:Arc<AtomicBool>,target:String)->Result<()> {
    let mut broken=false;
    for job in rx {
        if broken || critical.load(Ordering::Relaxed) {
            counts.transport_errors.fetch_add(1,Ordering::Relaxed);
            entries.lock().map_err(|_|"pending mutex poisoned")?.remove(&job.job_id);
            log.write(&json!({"event":"send_error","job_id":job.job_id,"warmup":job.warmup,"target":target,"observed_unix_ns":now(),"error":"target connection closed or semantic guard stopped sender","retry_count":0}))?; continue;
        }
        let start=now(); let started=Instant::now(); let result=wire::write_request(&mut socket,&job); let end=now();
        match result {
            Ok(bytes)=> {
                counts.submitted.fetch_add(1,Ordering::Relaxed);
                log.write(&json!({"event":"sent","run_id":job.run_id,"job_id":job.job_id,"target":target,"warmup":job.warmup,"send_start_unix_ns":start,"send_end_unix_ns":end,"serialize_and_write_ns":ns(started.elapsed()),"request_wire_bytes":bytes,"retry_count":0}))?;
            },
            Err(e)=> {
                broken=true; let _=socket.shutdown(Shutdown::Both);
                counts.transport_errors.fetch_add(1,Ordering::Relaxed);
                entries.lock().map_err(|_|"pending mutex poisoned")?.remove(&job.job_id);
                log.write(&json!({"event":"send_error","job_id":job.job_id,"target":target,"warmup":job.warmup,"send_start_unix_ns":start,"send_end_unix_ns":end,"error":e.to_string(),"retry_count":0,"partial_frame_possible":true}))?;
            }
        }
    }
    // Keep the read half alive until frontend verification/drain ends.
    let _=socket.shutdown(Shutdown::Write); Ok(())
}
fn receiver(mut socket:TcpStream,tx:SyncSender<Task>,log:Arc<Logger>,stop:Arc<AtomicBool>,counts:Arc<Counts>,target:String)->Result<()> {
    socket.set_read_timeout(Some(Duration::from_millis(100)))?;
    while !stop.load(Ordering::Relaxed) {
        match wire::read_reply(&mut socket,&stop) {
            Ok((reply,bytes,wire_bytes,start,end,header_decode_ns))=> {
                log.write(&json!({"event":"received","job_id":reply.job_id,"run_id":reply.run_id,"target":target,"receive_start_unix_ns":start,"receive_end_unix_ns":end,"header_decode_ns":header_decode_ns,"wire_bytes":wire_bytes,"encoded_bytes":bytes.len(),"server":reply}))?;
                let task=Task { reply,bytes,receive_start:start,receive_end:end,wire_bytes,queued:Instant::now() };
                if tx.send(task).is_err() { return Err("frontend verification channel closed".into()); }
            },
            Err(e) if stop.load(Ordering::Relaxed)||e.kind()==std::io::ErrorKind::Interrupted=>break,
            Err(e)=> {
                counts.transport_errors.fetch_add(1,Ordering::Relaxed);
                log.write(&json!({"event":"receive_error","target":target,"observed_unix_ns":now(),"error":e.to_string(),"pending_jobs_retained_for_deadline_and_drain":true}))?; break;
            }
        }
    }
    Ok(())
}
fn verifier(rx:Arc<Mutex<mpsc::Receiver<Task>>>,entries:Arc<Mutex<HashMap<u64,Entry>>>,state:Arc<State>,reference:Arc<HashMap<(String,usize),String>>,log:Arc<Logger>,counts:Arc<Counts>,critical:Arc<AtomicBool>,clock:Instant,deadline_ns:u64)->Result<()> {
    loop {
        let task=match rx.lock().map_err(|_|"verification receiver poisoned")?.recv() { Ok(t)=>t,Err(_)=>break };
        let job_id=task.reply.job_id;
        let entry={ let mut pending=entries.lock().map_err(|_|"pending mutex poisoned")?;
            match pending.get_mut(&job_id) { Some(e) if !e.verifying=>{ e.verifying=true; Some(e.clone()) },_=>None }
        };
        let Some(entry)=entry else {
            counts.duplicate_or_unknown.fetch_add(1,Ordering::Relaxed); critical.store(true,Ordering::Relaxed);
            log.write(&json!({"event":"unexpected_response","job_id":job_id,"observed_unix_ns":now(),"error":"unknown/duplicate response"}))?; continue;
        };
        let start=now(); let waiting=ns(task.queued.elapsed()); let timer=Instant::now();
        let binding=task.reply.protocol==wire::PROTOCOL && task.reply.run_id==entry.job.run_id && task.reply.fixture_id==entry.job.fixture_id && task.reply.kind==entry.job.input.kind;
        let hash=sha(&task.bytes); let hash_matches=hash==task.reply.canonical_sha256;
        let baseline=reference.get(&(entry.job.input.kind.clone(),entry.job.fixture_id));
        let baseline_matches=baseline.map(|x|*x==hash);
        let server_error=task.reply.error.clone();
        let accepted=server_error.is_none() && binding && hash_matches && baseline_matches!=Some(false) && state.prover.verify_encoded_sync_op(&state.prepared[&entry.job.input.kind],&entry.request,&task.bytes);
        let verify_ns=ns(timer.elapsed()); let completed=now(); let complete_offset=ns(clock.elapsed());
        let latency_ns=complete_offset.saturating_sub(entry.offset_ns); let timely=latency_ns<=deadline_ns;
        if accepted {
            if timely { counts.accepted.fetch_add(1,Ordering::Relaxed); } else { counts.accepted_late.fetch_add(1,Ordering::Relaxed); }
        } else {
            counts.rejected.fetch_add(1,Ordering::Relaxed);
            if server_error.is_none() { critical.store(true,Ordering::Relaxed); }
        }
        let timeout_observed=entries.lock().map_err(|_|"pending mutex poisoned")?.get(&job_id).map(|e|e.timeout_logged).unwrap_or(entry.timeout_logged);
        log.write(&json!({"event":"completed","run_id":entry.job.run_id,"repeat":entry.job.repeat,"job_id":job_id,"fixture_id":entry.job.fixture_id,"kind":entry.job.input.kind,"target":entry.target,"warmup":entry.job.warmup,"scheduled_unix_ns":entry.job.scheduled_unix_ns,"deadline_unix_ns":entry.job.deadline_unix_ns,"receive_start_unix_ns":task.receive_start,"receive_end_unix_ns":task.receive_end,"verify_start_unix_ns":start,"accepted_end_unix_ns":completed,"scheduled_to_accept_ns":latency_ns,"frontend_verify_queue_ns":waiting,"frontend_hash_binding_and_verify_ns":verify_ns,"wire_bytes":task.wire_bytes,"encoded_bytes":task.bytes.len(),"canonical_sha256":hash,"reply_binding":binding,"reply_hash_matches":hash_matches,"control_reference_hash_matches":baseline_matches,"accepted":accepted,"deadline_met":accepted&&timely,"timeout_previously_observed":timeout_observed,"server_error":server_error,"server":task.reply,"retry_count":0}))?;
        entries.lock().map_err(|_|"pending mutex poisoned")?.remove(&job_id);
    }
    Ok(())
}

pub fn run()->Result<()> {
    let out=out_dir()?; let log=Logger::new(&out.join("frontend.jsonl"),usize_arg("--log-flush-every","256")?)?;
    let depth=u64_arg("--depth","24")? as u32; let front_workers=usize_arg("--verify-workers","16")?;
    let state=State::new(depth,front_workers,&log)?;
    let corpus=usize_arg("--corpus","768")?; if corpus==0||corpus>=(1usize<<depth.min(24)) { return Err("corpus outside key range".into()); }
    let control_samples=usize_arg("--control-samples","2")?.min(corpus); let reference=Arc::new(state.controls(control_samples,&out,&log)?);
    let kinds=mixture(&arg("--mixture","membership:1,nonmembership:1,update:1"))?;
    let targets:Vec<String>=arg("--targets","127.0.0.1:9400").split(',').map(str::to_string).collect();
    if targets.is_empty()||targets.iter().any(String::is_empty) { return Err("targets must be nonempty host:port values".into()); }
    let rate:f64=arg("--rate","100").parse()?; if !rate.is_finite()||rate<=0.0||rate>1e6 { return Err("rate must be finite and in (0,1000000]".into()); }
    let jobs=if arg("--duration-sec","0")=="0" { usize_arg("--jobs","128")? } else { let s:f64=arg("--duration-sec","0").parse()?; if !s.is_finite()||s<=0.0 { return Err("duration must be positive".into()); } (rate*s).round() as usize };
    let warmup=usize_arg("--warmup-jobs","32")?; let total=jobs.checked_add(warmup).ok_or("job count overflow")?;
    if jobs==0||total>100_000_000 { return Err("jobs outside bounded driver range".into()); }
    let deadline_ns=u64_arg("--deadline-ms","1000")?.checked_mul(1_000_000).ok_or("deadline overflow")?;
    let sender_queue=usize_arg("--sender-queue","1024")?; let max_pending=usize_arg("--max-pending","8192")?;
    if sender_queue==0||max_pending==0||front_workers==0 { return Err("queue/worker capacities must be positive".into()); }
    let run_id=arg("--run-id","pilot"); let repeat=usize_arg("--repeat","1")?;
    let mut meta=provenance("frontend"); meta["targets"]=json!(targets); meta["rate_per_second"]=json!(rate); meta["timed_jobs"]=json!(jobs); meta["warmup_jobs"]=json!(warmup); meta["corpus_per_kind"]=json!(corpus); meta["mixture_cycle"]=json!(kinds); meta["verify_workers"]=json!(front_workers); meta["deadline_ns"]=json!(deadline_ns); meta["sender_queue_per_target"]=json!(sender_queue); meta["max_pending"]=json!(max_pending); meta["arrival_contract"]=json!("fixed scheduled offsets round(i*1e9/rate), emitted independently of previous responses; bounded sender/pending overflow is recorded failure, never backpressure hidden as lower offered load");
    fresh_json(&out.join("metadata.json"),&meta)?;
    let fixture_log=Logger::new(&out.join("fixtures.jsonl"),256)?; let mut requests=HashMap::new(); let mut inputs=HashMap::new();
    for kind in KINDS { for i in 0..corpus {
        let r=Arc::new(fixture::original(depth,kind,i)); let input=Input::from_request(&r);
        fixture_log.write(&json!({"kind":kind,"fixture_id":i,"input_sha256":sha(&serde_json::to_vec(&input)?),"input":input}))?;
        requests.insert((kind.to_string(),i),r); inputs.insert((kind.to_string(),i),input);
    } }
    fixture_log.finish()?;
    let entries=Arc::new(Mutex::new(HashMap::<u64,Entry>::new())); let counts=Arc::new(Counts::default());
    let stop=Arc::new(AtomicBool::new(false)); let critical=Arc::new(AtomicBool::new(false)); let queued=Arc::new(AtomicUsize::new(0));
    let monitor=telemetry(log.clone(),stop.clone(),queued.clone(),u64_arg("--telemetry-ms","100")?);
    let (task_tx,task_rx)=mpsc::sync_channel::<Task>(usize_arg("--verify-queue","256")?.max(1)); let task_rx=Arc::new(Mutex::new(task_rx));
    let mut senders=Vec::new(); let mut sender_threads=Vec::new(); let mut receiver_threads=Vec::new(); let mut shutdown_sockets=Vec::new();
    for target in &targets {
        let socket=TcpStream::connect(target)?; socket.set_nodelay(true)?; socket.set_write_timeout(Some(Duration::from_millis(u64_arg("--io-timeout-ms","5000")?)))?;
        let read=socket.try_clone()?; shutdown_sockets.push(socket.try_clone()?);
        let (send_tx,send_rx)=mpsc::sync_channel::<Job>(sender_queue); senders.push(send_tx);
        let (send_entries,send_log,send_counts,send_critical,send_target)=(entries.clone(),log.clone(),counts.clone(),critical.clone(),target.clone());
        sender_threads.push(std::thread::spawn(move||sender(socket,send_rx,send_entries,send_log,send_counts,send_critical,send_target)));
        let (receive_tx,receive_log,receive_stop,receive_counts,receive_target)=(task_tx.clone(),log.clone(),stop.clone(),counts.clone(),target.clone());
        receiver_threads.push(std::thread::spawn(move||receiver(read,receive_tx,receive_log,receive_stop,receive_counts,receive_target)));
    }
    drop(task_tx);
    let clock=Instant::now(); let start=now(); let mut verifier_threads=Vec::new();
    for _ in 0..front_workers {
        let (rx,entries,state,reference,log,counts,critical)=(task_rx.clone(),entries.clone(),state.clone(),reference.clone(),log.clone(),counts.clone(),critical.clone());
        verifier_threads.push(std::thread::spawn(move||verifier(rx,entries,state,reference,log,counts,critical,clock,deadline_ns)));
    }
    let deadline_poll_ms=u64_arg("--deadline-poll-ms","10")?.max(1);
    let (scan_entries,scan_log,scan_counts,scan_stop,scan_queued)=(entries.clone(),log.clone(),counts.clone(),stop.clone(),queued.clone());
    let deadline_thread=std::thread::spawn(move||->Result<()> {
        while !scan_stop.load(Ordering::Relaxed) {
            deadline_scan(&scan_entries,&scan_log,&scan_counts,clock,deadline_ns)?;
            scan_queued.store(scan_entries.lock().map_err(|_|"pending mutex poisoned")?.len(),Ordering::Relaxed);
            std::thread::sleep(Duration::from_millis(deadline_poll_ms));
        }
        Ok(())
    });
    log.write(&json!({"event":"load_start","start_unix_ns":start,"scheduled_jobs":total,"rate_per_second":rate}))?;
    for i in 0..total {
        if critical.load(Ordering::Relaxed) { break; }
        let offset=(i as f64*1e9/rate).round() as u64;
        let due=Duration::from_nanos(offset);
        loop { let remaining=due.saturating_sub(clock.elapsed()); if remaining.is_zero() { break; } std::thread::sleep(remaining.min(Duration::from_millis(10))); }
        let offered=now(); let routing=Instant::now(); let target_index=i%targets.len();
        let kind=kinds[i%kinds.len()].clone(); let fixture_id=(i/kinds.len())%corpus;
        let scheduled=start.checked_add(offset).ok_or("scheduled time overflow")?;
        let job=Job { protocol:wire::PROTOCOL,run_id:run_id.clone(),job_id:i as u64,fixture_id,repeat,warmup:i<warmup,scheduled_unix_ns:scheduled,deadline_unix_ns:scheduled.checked_add(deadline_ns).ok_or("deadline timestamp overflow")?,input:inputs[&(kind.clone(),fixture_id)].clone() };
        counts.offered.fetch_add(1,Ordering::Relaxed);
        log.write(&json!({"event":"offered","run_id":run_id,"repeat":repeat,"job_id":job.job_id,"fixture_id":fixture_id,"kind":kind,"target":targets[target_index],"warmup":job.warmup,"scheduled_unix_ns":scheduled,"offered_unix_ns":offered,"generator_lateness_ns":ns(clock.elapsed()).saturating_sub(offset),"routing_ns":ns(routing.elapsed()),"input_sha256":sha(&serde_json::to_vec(&job.input)?)}))?;
        let entry=Entry { job:job.clone(),request:requests[&(kind,fixture_id)].clone(),offset_ns:offset,target:targets[target_index].clone(),timeout_logged:false,verifying:false };
        let pending_count={ let mut pending=entries.lock().map_err(|_|"pending mutex poisoned")?; if pending.len()>=max_pending { None } else { pending.insert(job.job_id,entry); Some(pending.len()) } };
        if pending_count.is_none() {
            counts.queue_full.fetch_add(1,Ordering::Relaxed);
            log.write(&json!({"event":"generator_failure","job_id":job.job_id,"warmup":job.warmup,"observed_unix_ns":now(),"error":"frontend_max_pending","retry_count":0}))?; continue;
        }
        queued.store(pending_count.unwrap_or(0),Ordering::Relaxed);
        match senders[target_index].try_send(job) {
            Ok(())=>{},
            Err(TrySendError::Full(job))|Err(TrySendError::Disconnected(job))=> {
                entries.lock().map_err(|_|"pending mutex poisoned")?.remove(&job.job_id); counts.queue_full.fetch_add(1,Ordering::Relaxed);
                log.write(&json!({"event":"generator_failure","job_id":job.job_id,"warmup":job.warmup,"target":targets[target_index],"observed_unix_ns":now(),"error":"frontend_sender_queue_full_or_closed","retry_count":0}))?;
            }
        }
        // The separate deadline scanner continues while writers are blocked.
    }
    drop(senders);
    for thread in sender_threads { thread.join().map_err(|_|"sender panic")??; }
    let draining=Instant::now(); let drain=Duration::from_millis(u64_arg("--drain-ms","30000")?);
    while draining.elapsed()<drain {
        let pending=entries.lock().map_err(|_|"pending mutex poisoned")?.len(); queued.store(pending,Ordering::Relaxed);
        if pending==0 { break; } std::thread::sleep(Duration::from_millis(10));
    }
    stop.store(true,Ordering::Relaxed);
    for socket in shutdown_sockets { let _=socket.shutdown(Shutdown::Both); }
    for thread in receiver_threads { thread.join().map_err(|_|"receiver panic")??; }
    for thread in verifier_threads { thread.join().map_err(|_|"verifier panic")??; }
    deadline_thread.join().map_err(|_|"deadline monitor panic")??;
    if let Some(m)=monitor { m.join().map_err(|_|"telemetry panic")?; }
    let remaining=entries.lock().map_err(|_|"pending mutex poisoned")?.values().cloned().collect::<Vec<_>>();
    for e in &remaining { log.write(&json!({"event":"drain_failure","job_id":e.job.job_id,"warmup":e.job.warmup,"target":e.target,"scheduled_unix_ns":e.job.scheduled_unix_ns,"observed_unix_ns":now(),"error":"response_missing_at_drain_limit","retry_count":0}))?; }
    fresh_json(&out.join("terminal.json"),&json!({"status":if critical.load(Ordering::Relaxed){"FAIL_SEMANTIC_GUARD"}else{"LOAD_OBSERVATIONS_COMPLETE"},"scheduled_jobs":total,"offered":count(&counts.offered),"submitted":count(&counts.submitted),"accepted_by_deadline_including_warmup":count(&counts.accepted),"accepted_late_including_warmup":count(&counts.accepted_late),"rejected_including_warmup":count(&counts.rejected),"deadline_event_count":count(&counts.deadline_events),"generator_failures":count(&counts.queue_full),"transport_error_events":count(&counts.transport_errors),"unexpected_response_count":count(&counts.duplicate_or_unknown),"unresolved_at_drain":remaining.len(),"finish_unix_ns":now(),"logging":log.finish()?,"note":"Read per-job warmup flags for timed statistics. Deadline events and late acceptances overlap and are not additive outcome counts."}))?;
    if critical.load(Ordering::Relaxed) { return Err("semantic/binding/canonical proof guard failed; evidence retained".into()); } Ok(())
}

fn deadline_scan(entries:&Mutex<HashMap<u64,Entry>>,log:&Logger,counts:&Counts,clock:Instant,deadline_ns:u64)->Result<()> {
    let elapsed=ns(clock.elapsed()); let mut expired=Vec::new();
    { let mut pending=entries.lock().map_err(|_|"pending mutex poisoned")?;
      for entry in pending.values_mut() { if !entry.timeout_logged && elapsed>entry.offset_ns.saturating_add(deadline_ns) { entry.timeout_logged=true; expired.push(entry.clone()); } } }
    for e in expired { counts.deadline_events.fetch_add(1,Ordering::Relaxed); log.write(&json!({"event":"deadline_exceeded","job_id":e.job.job_id,"warmup":e.job.warmup,"scheduled_unix_ns":e.job.scheduled_unix_ns,"deadline_unix_ns":e.job.deadline_unix_ns,"observed_unix_ns":now(),"observed_scheduled_elapsed_ns":elapsed.saturating_sub(e.offset_ns),"response_still_may_arrive":true,"no_cancellation_or_retry":true}))?; }
    Ok(())
}

pub fn sweep_plan()->Result<()> {
    let out=out_dir()?;
    fn integers(name:&str,default:&str)->Result<Vec<usize>> { arg(name,default).split(',').map(|x|x.parse().map_err(Into::into)).collect() }
    let workers=integers("--workers-list","24,48")?; let batches=integers("--batch-list","24,48,96,192")?;
    let rates=integers("--rate-list","100,250,500,1000")?; let waits=integers("--wait-us-list","0,1000,5000")?;
    let repeats=usize_arg("--repeats","3")?; if !(3..=5).contains(&repeats) { return Err("sweep confirmation repeats must be 3..5".into()); }
    let mut cells=Vec::new();
    for w in workers { for &b in &batches { for &rate in &rates { for &wait in &waits { for repeat in 1..=repeats {
        cells.push(json!({"workers":w,"batch_max":b,"rate":rate,"max_wait_us":wait,"repeat":repeat,"mixture":arg("--mixture","membership:1,nonmembership:1,update:1"),"targets":arg("--targets","127.0.0.1:9400"),"phase":arg("--sweep-phase","coarse"),"fresh_server_and_frontend_process_required":true}));
    } } } } }
    fresh_json(&out.join("sweep-plan.json"),&json!({"schema":"statesync-gkr.load-sweep-plan.v1","status":"PLAN_ONLY_NOT_EXECUTED","cells":cells,"note":"This is an explicit candidate list, not a command launcher or approval expansion. Select pilot rows, then provide fine lists around observed transitions. Do not run the Cartesian list blindly."}))?; Ok(())
}
