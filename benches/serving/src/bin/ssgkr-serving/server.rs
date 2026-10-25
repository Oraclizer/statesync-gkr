//! Reference proof server: four serving modes over the same components.
//!
//! - `original`: the measured v1.1 loop. One compute batch at a time
//!   (parallel witness, then proofs, then encodings); the dispatcher then
//!   hashes, frames, writes and logs each result inline, and releases the
//!   typed batch afterwards.
//! - `queued-return`: the same batch phases; the dispatcher releases the typed
//!   batch and hands the bytes to per-connection writers, which hash and write
//!   while the next batch computes.
//! - `batch-fused`: the same batching policy; every job completes inside the
//!   parallel stage (witness, proof, encoding, hash and release on its
//!   worker), so the dispatcher only hands finished bytes to the writers.
//! - `continuous`: no batches. Up to `--max-in-flight` workers each start the
//!   oldest admitted request of any kind as soon as they finish the previous
//!   one, and replies leave in completion order, matched by job identifier.
//!
//! Every mode admits, rejects, frames and bounds memory the same way and
//! produces the same proof bytes.

use crate::shared::*;
use rayon::prelude::*;
use serde_json::{Value, json};
use ssgkr_serving::admission::{Admission, AdmissionTicket, RejectReason};
use ssgkr_serving::budget::{Budget, Permit};
use ssgkr_serving::completion::{self, Completed, ContinuousRunner, sha256_hex};
use ssgkr_serving::fixture::KINDS;
use ssgkr_serving::timing::{StageTimes, ns, thread_label, unix_ns};
use ssgkr_serving::wire::{self, Job, Reply};
use statesync_gkr::{SyncRequest, SyncResult};
use std::{
    collections::{HashMap, VecDeque},
    net::{Shutdown, TcpListener, TcpStream},
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, AtomicUsize, Ordering},
        mpsc::{self, Receiver, Sender, SyncSender, TrySendError},
    },
    thread::{self, JoinHandle},
    time::{Duration, Instant},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    Original,
    QueuedReturn,
    BatchFused,
    Continuous,
}

impl Mode {
    fn parse(text: &str) -> Result<Self> {
        match text {
            "original" => Ok(Self::Original),
            "queued-return" => Ok(Self::QueuedReturn),
            "batch-fused" => Ok(Self::BatchFused),
            "continuous" => Ok(Self::Continuous),
            _ => Err(
                "serving-mode must be original, queued-return, batch-fused or continuous".into(),
            ),
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Original => "original",
            Self::QueuedReturn => "queued-return",
            Self::BatchFused => "batch-fused",
            Self::Continuous => "continuous",
        }
    }

    /// Whether each connection gets one writer thread that owns its frames.
    fn per_connection_writers(self) -> bool {
        self != Self::Original
    }

    fn policy(self) -> &'static str {
        match self {
            Self::Original => {
                "one FIFO per operation kind; oldest ready kind first; maximum batch size or elapsed oldest wait triggers a flush; one compute batch at a time; the dispatcher hashes, writes and logs each result before it releases the typed batch"
            }
            Self::QueuedReturn => {
                "same batching as original; the dispatcher releases the typed batch, then per-connection writers hash and write while the next batch computes"
            }
            Self::BatchFused => {
                "same batching as original; each job's witness, proof, encoding, hash and typed release run as one task on its worker inside the parallel stage; per-connection writers only write"
            }
            Self::Continuous => {
                "one arrival-order FIFO across kinds; up to max-in-flight workers each start the oldest admitted job when they finish the previous one; replies leave in completion order; batch-max and max-wait-us are not used"
            }
        }
    }

    fn phase_scope(self) -> &'static str {
        match self {
            Self::Original | Self::QueuedReturn => {
                "batch-shared compute timers; individual hash, return wait and complete frame write are disjoint"
            }
            Self::BatchFused => {
                "batch boundaries come from the latest job per phase and the end of the parallel stage, which includes per-job hash and release; per-job stages are in job_stages"
            }
            Self::Continuous => {
                "no batch: batch fields describe the single job; per-job stages are in job_stages"
            }
        }
    }
}

/// Recorded non-fatal and fatal failures, reported in the terminal file.
#[derive(Clone, Default)]
struct Failures(Arc<Mutex<Vec<String>>>);

impl Failures {
    fn record(&self, message: impl Into<String>) {
        if let Ok(mut list) = self.0.lock() {
            list.push(message.into());
        }
    }

    fn list(&self) -> Vec<String> {
        self.0.lock().map(|list| list.clone()).unwrap_or_default()
    }
}

/// Where one connection's frames go. With no `sink` (original mode) the
/// dispatcher and reader write inline under the socket lock; otherwise the
/// connection's single writer thread owns every frame of that connection.
#[derive(Clone)]
struct Route {
    connection: u64,
    socket: Arc<Mutex<TcpStream>>,
    sink: Option<Sender<Response>>,
}

/// The request facts every reply repeats.
struct Origin {
    job: Job,
    route: Route,
    received: u64,
    enqueued: u64,
}

struct Pending {
    origin: Origin,
    request: SyncRequest,
    admitted: Instant,
    ticket: Option<AdmissionTicket>,
}

fn base(origin: &Origin, host: &str) -> Reply {
    Reply {
        protocol: wire::PROTOCOL,
        run_id: origin.job.run_id.clone(),
        job_id: origin.job.job_id,
        fixture_id: origin.job.fixture_id,
        kind: origin.job.input.kind.clone(),
        host_id: host.into(),
        process_id: std::process::id(),
        server_received_unix_ns: origin.received,
        server_enqueued_unix_ns: origin.enqueued,
        ..Default::default()
    }
}

struct Response {
    reply: Reply,
    bytes: Vec<u8>,
    warmup: bool,
    /// Present when the job completed as one fused task.
    stages: Option<StageTimes>,
    /// True when `reply.canonical_sha256` was set before the return path.
    hashed: bool,
    finished: Instant,
    handoff_wait_ns: u64,
    ready: Instant,
    permit: Option<Permit>,
}

impl Response {
    fn new(
        reply: Reply,
        bytes: Vec<u8>,
        warmup: bool,
        stages: Option<StageTimes>,
        hashed: bool,
    ) -> Self {
        let now = Instant::now();
        Self {
            reply,
            bytes,
            warmup,
            stages,
            hashed,
            finished: now,
            handoff_wait_ns: 0,
            ready: now,
            permit: None,
        }
    }
}

#[derive(Default)]
struct ReturnCounts {
    sent: AtomicUsize,
    failed: AtomicUsize,
    rejected: AtomicUsize,
}

#[derive(Clone)]
struct Output {
    mode: Mode,
    budget: Arc<Budget>,
    log: Arc<Logger>,
    counts: Arc<ReturnCounts>,
    timeout: Duration,
}

impl Output {
    /// Charge the response to the return budget (waiting while it is full),
    /// then write it inline or hand it to the connection's writer.
    fn emit(&self, route: &Route, mut r: Response) -> Result<()> {
        let started = Instant::now();
        r.permit = Some(self.budget.acquire(r.bytes.capacity())?);
        r.handoff_wait_ns = ns(started.elapsed());
        r.ready = Instant::now();
        match &route.sink {
            None => self.write(route.connection, &route.socket, r),
            Some(sink) => match sink.send(r) {
                Ok(()) => Ok(()),
                // The writer stopped after a recorded failure. Account for the
                // response as a failed write; dropping it returns its charge.
                Err(mpsc::SendError(r)) => {
                    self.unsent(route.connection, r, "connection writer stopped")
                }
            },
        }
    }

    fn reject(&self, route: &Route, mut reply: Reply, warmup: bool, reason: &str) -> Result<()> {
        reply.error = Some(reason.into());
        self.emit(route, Response::new(reply, Vec::new(), warmup, None, true))
    }

    fn write(&self, connection: u64, socket: &Mutex<TcpStream>, mut r: Response) -> Result<()> {
        let return_queue_ns = ns(r.ready.elapsed());
        let hashing = Instant::now();
        let hash_on_return_path = r.reply.error.is_none() && !r.hashed;
        if hash_on_return_path {
            r.reply.canonical_sha256 = sha256_hex(&r.bytes);
        }
        let hash_ns = if hash_on_return_path {
            ns(hashing.elapsed())
        } else {
            0
        };
        let lock_start = Instant::now();
        let mut stream = socket.lock().map_err(|_| "socket writer poisoned")?;
        let socket_lock_ns = ns(lock_start.elapsed());
        let return_enqueue_ns = ns(r.finished.elapsed());
        r.reply.server_send_start_unix_ns = unix_ns();
        let writing = Instant::now();
        let mut progress = wire::WriteProgress::default();
        let result = wire::write_reply_deadline(
            &mut stream,
            &r.reply,
            &r.bytes,
            self.timeout,
            &mut progress,
        );
        let write_ns = ns(writing.elapsed());
        let end = unix_ns();
        // A partial frame poisons the byte stream. Never append another frame.
        if result.is_err() {
            let _ = stream.shutdown(Shutdown::Both);
        }
        drop(stream);
        if result.is_ok() {
            self.counts.sent.fetch_add(1, Ordering::Relaxed);
        } else {
            self.counts.failed.fetch_add(1, Ordering::Relaxed);
        }
        if r.reply.error.is_some() {
            self.counts.rejected.fetch_add(1, Ordering::Relaxed);
        }
        let stages = r.stages.map(|s| {
            stage_row(
                &s,
                return_enqueue_ns,
                r.reply.server_send_start_unix_ns,
                end,
            )
        });
        self.log.write(&json!({
            "event": if r.reply.error.is_some() { "server_reject" } else { "server_return" },
            "reply": r.reply,
            "warmup": r.warmup,
            "send_end_unix_ns": end,
            "write_duration_ns": write_ns,
            "hash_ns": hash_ns,
            "hash_on_return_path": hash_on_return_path,
            "socket_lock_ns": socket_lock_ns,
            "write_progress": progress,
            "return_handoff_wait_ns": r.handoff_wait_ns,
            "return_queue_ns": return_queue_ns,
            "encoded_capacity_bytes": r.bytes.capacity(),
            "return_budget": self.budget.snapshot()?,
            "wire_bytes": result.as_ref().ok(),
            "write_error": result.as_ref().err().map(|e| e.to_string()),
            "write_error_kind": result.as_ref().err().map(|e| format!("{:?}", e.kind())),
            "write_error_raw_os_error": result.as_ref().err().and_then(|e| e.raw_os_error()),
            "mode": self.mode.name(),
            "connection": connection,
            "writer_tid": thread_label(),
            "job_stages": stages,
            "phase_scope": self.mode.phase_scope(),
        }))?;
        // The permit covered the frame write and this log row.
        Ok(())
    }

    fn unsent(&self, connection: u64, r: Response, error: &str) -> Result<()> {
        self.counts.failed.fetch_add(1, Ordering::Relaxed);
        if r.reply.error.is_some() {
            self.counts.rejected.fetch_add(1, Ordering::Relaxed);
        }
        self.log.write(&json!({
            "event": if r.reply.error.is_some() { "server_reject" } else { "server_return" },
            "reply": r.reply,
            "warmup": r.warmup,
            "send_end_unix_ns": unix_ns(),
            "write_duration_ns": 0,
            "wire_bytes": Value::Null,
            "write_error": error,
            "mode": self.mode.name(),
            "connection": connection,
        }))
    }
}

/// The per-job row of the stage table: compute stages from the completing
/// worker plus the return-path times of the frame.
fn stage_row(s: &StageTimes, return_enqueue_ns: u64, write_start: u64, write_end: u64) -> Value {
    json!({
        "worker_tid": s.worker_tid,
        "worker_os_tid": s.worker_os_tid,
        "dispatch_unix_ns": s.dispatch_unix_ns,
        "witness_end_unix_ns": s.witness_end_unix_ns,
        "prove_end_unix_ns": s.prove_end_unix_ns,
        "encode_end_unix_ns": s.encode_end_unix_ns,
        "done_unix_ns": s.done_unix_ns,
        "witness_ns": s.witness_ns,
        "prove_ns": s.prove_ns,
        "encode_ns": s.encode_ns,
        "hash_ns": s.hash_ns,
        "release_ns": s.release_ns,
        "release_tid": s.release_tid,
        "return_enqueue_ns": return_enqueue_ns,
        "write_start_unix_ns": write_start,
        "write_end_unix_ns": write_end,
    })
}

fn spawn_writer(
    output: Output,
    connection: u64,
    socket: Arc<Mutex<TcpStream>>,
    rx: Receiver<Response>,
    failures: Failures,
    stop: Arc<AtomicBool>,
) -> std::io::Result<JoinHandle<()>> {
    thread::Builder::new()
        .name(format!("serving-writer-{connection}"))
        .spawn(move || {
            for r in rx {
                if let Err(e) = output.write(connection, &socket, r) {
                    failures.record(format!("writer {connection}: {e}"));
                    stop.store(true, Ordering::Relaxed);
                }
            }
        })
}

struct Config {
    mode: Mode,
    listen: String,
    workers: usize,
    max_in_flight: usize,
    depth: u32,
    batch: usize,
    max_queue: usize,
    max_connections: usize,
    return_jobs: usize,
    return_bytes: usize,
    run: Duration,
    wait: Duration,
    timeout: Duration,
    controls: usize,
    telemetry_ms: u64,
    flush: usize,
}

impl Config {
    fn read() -> Result<Self> {
        let depth = u32::try_from(u64_arg("--depth", "24")?).map_err(|_| "depth overflows u32")?;
        let workers = usize_arg("--workers", "48")?;
        let max_in_flight = match arg("--max-in-flight", "").as_str() {
            "" => workers.saturating_sub(2).max(1),
            text => text.parse()?,
        };
        let c = Self {
            mode: Mode::parse(&arg("--serving-mode", "continuous"))?,
            listen: arg("--listen", "127.0.0.1:9400"),
            workers,
            max_in_flight,
            depth,
            batch: usize_arg("--batch-max", "96")?,
            max_queue: usize_arg("--max-queue", "8192")?,
            max_connections: usize_arg("--max-connections", "64")?,
            return_jobs: usize_arg("--return-jobs", "192")?,
            return_bytes: usize_arg("--return-bytes", "67108864")?,
            run: Duration::from_millis(u64_arg("--run-ms", "600000")?),
            wait: Duration::from_micros(u64_arg("--max-wait-us", "1000")?),
            timeout: Duration::from_millis(u64_arg("--io-timeout-ms", "5000")?),
            controls: usize_arg("--control-samples", "2")?,
            telemetry_ms: u64_arg("--telemetry-ms", "100")?,
            flush: usize_arg("--log-flush-every", "256")?,
        };
        if !(1..=32).contains(&c.depth)
            || c.workers == 0
            || c.max_in_flight == 0
            || c.max_in_flight > c.workers
            || c.batch == 0
            || c.max_queue == 0
            || c.return_jobs == 0
            || c.return_bytes == 0
            || c.max_connections == 0
            || c.flush == 0
            || c.run.is_zero()
            || c.timeout.is_zero()
            || c.controls == 0
            || c.controls >= (1usize << c.depth.min(24))
        {
            return Err("invalid server numeric range: capacities, workers, max-in-flight (at most workers), times, controls and flush must be positive; depth 1..32; controls below key range".into());
        }
        // Check memory accounting before allocating channels or circuits.
        c.batch
            .checked_mul(wire::MAX_PROOF)
            .ok_or("batch memory accounting overflow")?;
        c.max_in_flight
            .checked_mul(wire::MAX_PROOF)
            .ok_or("in-flight memory accounting overflow")?;
        c.max_connections
            .checked_mul(wire::MAX_JSON)
            .ok_or("connection memory accounting overflow")?;
        Ok(c)
    }
}

/// Handles shared by readers, the dispatcher and the workers.
#[derive(Clone)]
struct Shared {
    state: Arc<State>,
    output: Output,
    admission: Arc<Admission>,
    stop: Arc<AtomicBool>,
    host: String,
    failures: Failures,
    writers: Arc<Mutex<Vec<JoinHandle<()>>>>,
}

#[derive(Default)]
struct Stats {
    processed: AtomicUsize,
    unprocessed: AtomicUsize,
    batches: AtomicUsize,
}

fn connection(
    mut reader: TcpStream,
    id: u64,
    ingress: SyncSender<Pending>,
    shared: Shared,
) -> Result<()> {
    // Winsock accepted sockets can inherit the listener's nonblocking mode.
    // These dedicated reader and writer threads use blocking I/O with deadlines.
    reader.set_nonblocking(false)?;
    reader.set_nodelay(true)?;
    reader.set_read_timeout(Some(Duration::from_millis(100)))?;
    let socket = Arc::new(Mutex::new(reader.try_clone()?));
    let sink = if shared.output.mode.per_connection_writers() {
        let (tx, rx) = mpsc::channel();
        let writer = spawn_writer(
            shared.output.clone(),
            id,
            socket.clone(),
            rx,
            shared.failures.clone(),
            shared.stop.clone(),
        )?;
        shared
            .writers
            .lock()
            .map_err(|_| "writer registry poisoned")?
            .push(writer);
        Some(tx)
    } else {
        None
    };
    let route = Route {
        connection: id,
        socket,
        sink,
    };
    let output = &shared.output;
    let log = &output.log;
    while !shared.stop.load(Ordering::Relaxed) {
        let (job, received, request_wire_bytes, json_decode_ns) = match wire::read_request(
            &mut reader,
            &shared.stop,
        ) {
            Ok(parts) => parts,
            Err(e)
                if matches!(
                    e.kind(),
                    std::io::ErrorKind::UnexpectedEof | std::io::ErrorKind::Interrupted
                ) =>
            {
                break;
            }
            Err(e) => {
                log.write(&json!({"event": "connection_error", "connection": id, "observed_unix_ns": unix_ns(), "error": e.to_string()}))?;
                break;
            }
        };
        let decoded = Instant::now();
        if job.protocol != wire::PROTOCOL || job.run_id.is_empty() {
            log.write(&json!({"event": "protocol_error", "connection": id, "job_id": job.job_id, "observed_unix_ns": received}))?;
            break;
        }
        let mut origin = Origin {
            job,
            route: route.clone(),
            received,
            enqueued: 0,
        };
        if shared.stop.load(Ordering::Relaxed) {
            // Every complete request read gets exactly one reply.
            let reply = base(&origin, &shared.host);
            output.reject(
                &route,
                reply,
                origin.job.warmup,
                RejectReason::Stopping.as_str(),
            )?;
            break;
        }
        let request = match origin.job.input.request(shared.state.depth) {
            Ok(request) => request,
            Err(e) => {
                let reply = base(&origin, &shared.host);
                output.reject(&route, reply, origin.job.warmup, &format!("input: {e}"))?;
                continue;
            }
        };
        origin.enqueued = unix_ns();
        log.write(&json!({
            "event": "server_arrival",
            "run_id": origin.job.run_id,
            "job_id": origin.job.job_id,
            "fixture_id": origin.job.fixture_id,
            "kind": origin.job.input.kind,
            "warmup": origin.job.warmup,
            "connection": id,
            "scheduled_frontend_unix_ns": origin.job.scheduled_unix_ns,
            "received_unix_ns": received,
            "enqueued_unix_ns": origin.enqueued,
            "json_decode_ns": json_decode_ns,
            "request_decode_ns": ns(decoded.elapsed()),
            "request_wire_bytes": request_wire_bytes,
            "input_sha256": sha256_hex(&serde_json::to_vec(&origin.job.input)?),
        }))?;
        // The admission count covers the hand-off channel and every queue
        // until computation starts.
        let Some(ticket) = shared.admission.try_admit() else {
            let reply = base(&origin, &shared.host);
            output.reject(
                &route,
                reply,
                origin.job.warmup,
                RejectReason::QueueFull.as_str(),
            )?;
            continue;
        };
        let pending = Pending {
            origin,
            request,
            admitted: Instant::now(),
            ticket: Some(ticket),
        };
        match ingress.try_send(pending) {
            Ok(()) => {}
            Err(TrySendError::Full(p)) => {
                drop(p.ticket);
                let reply = base(&p.origin, &shared.host);
                output.reject(
                    &route,
                    reply,
                    p.origin.job.warmup,
                    RejectReason::IngressFull.as_str(),
                )?;
            }
            Err(TrySendError::Disconnected(p)) => {
                drop(p.ticket);
                let reply = base(&p.origin, &shared.host);
                output.reject(
                    &route,
                    reply,
                    p.origin.job.warmup,
                    RejectReason::Stopping.as_str(),
                )?;
                break;
            }
        }
    }
    Ok(())
}

/// Accepts connections without blocking and reaps finished readers.
struct Acceptor {
    listener: Option<TcpListener>,
    ingress: Option<SyncSender<Pending>>,
    shared: Shared,
    readers: Vec<JoinHandle<Result<()>>>,
    next_connection: u64,
    max_connections: usize,
}

impl Acceptor {
    fn poll(&mut self) -> Result<()> {
        let mut index = 0;
        while index < self.readers.len() {
            if self.readers[index].is_finished() {
                self.readers
                    .swap_remove(index)
                    .join()
                    .map_err(|_| "server reader panic")??;
            } else {
                index += 1;
            }
        }
        let (Some(listener), Some(ingress)) = (&self.listener, &self.ingress) else {
            return Ok(());
        };
        let log = &self.shared.output.log;
        // Accept floods cannot monopolize scheduling or create unlimited threads.
        for _ in 0..8 {
            match listener.accept() {
                Ok((stream, peer)) => {
                    if self.readers.len() >= self.max_connections {
                        let _ = stream.shutdown(Shutdown::Both);
                        log.write(&json!({"event": "connection_limit", "peer": peer.to_string(), "observed_unix_ns": unix_ns()}))?;
                        continue;
                    }
                    self.next_connection += 1;
                    let id = self.next_connection;
                    log.write(&json!({"event": "connection", "connection": id, "peer": peer.to_string(), "observed_unix_ns": unix_ns()}))?;
                    let (ingress, shared) = (ingress.clone(), self.shared.clone());
                    self.readers.push(
                        thread::Builder::new()
                            .name(format!("serving-reader-{id}"))
                            .spawn(move || connection(stream, id, ingress, shared))?,
                    );
                }
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => break,
                Err(e) => return Err(e.into()),
            }
        }
        Ok(())
    }

    /// Stop accepting, release the hand-off sender and join every reader.
    fn finish(mut self) {
        self.listener = None;
        self.ingress = None;
        for reader in self.readers.drain(..) {
            match reader.join() {
                Ok(Ok(())) => {}
                Ok(Err(e)) => self.shared.failures.record(e.to_string()),
                Err(_) => self.shared.failures.record("server reader panic"),
            }
        }
    }
}

/// Batch-level reply fields shared by every result of one batch.
struct BatchTimes {
    id: u64,
    size: usize,
    flush: u64,
    witness_end: u64,
    prove_end: u64,
    encode_end: u64,
    witness_ns: u64,
    prove_ns: u64,
    encode_ns: u64,
}

/// Hand one finished result to the return path with its batch fields.
fn emit_result(
    origin: Origin,
    bytes: Vec<u8>,
    hash: Option<String>,
    stages: Option<StageTimes>,
    batch: &BatchTimes,
    queue_ns: u64,
    shared: &Shared,
) -> Result<()> {
    let output = &shared.output;
    let mut reply = base(&origin, &shared.host);
    let warmup = origin.job.warmup;
    let route = origin.route;
    if bytes.len() > wire::MAX_PROOF || bytes.capacity() > output.budget.max_bytes() {
        return output.reject(
            &route,
            reply,
            warmup,
            RejectReason::ResponseExceedsBudget.as_str(),
        );
    }
    reply.batch_id = batch.id;
    reply.batch_size = batch.size;
    reply.flush_unix_ns = batch.flush;
    reply.witness_start_unix_ns = batch.flush;
    reply.witness_end_unix_ns = batch.witness_end;
    reply.prove_end_unix_ns = batch.prove_end;
    reply.encode_end_unix_ns = batch.encode_end;
    reply.server_queue_ns = queue_ns;
    reply.batch_witness_ns = batch.witness_ns;
    reply.batch_prove_ns = batch.prove_ns;
    reply.batch_encode_ns = batch.encode_ns;
    reply.encoded_bytes = bytes.len();
    let hashed = match hash {
        Some(hash) => {
            reply.canonical_sha256 = hash;
            true
        }
        None => false,
    };
    // The request's raw input is released before any wait on the budget.
    drop(origin.job);
    output.emit(&route, Response::new(reply, bytes, warmup, stages, hashed))
}

/// The measured v1.1 batch phases: parallel witness, then parallel proofs,
/// then parallel encodings. `original` writes each result inline and releases
/// the typed batch afterwards; `queued-return` releases it first and hands the
/// bytes to the writers.
fn process_phased(batch: Vec<Pending>, id: u64, shared: &Shared) -> Result<()> {
    let state = &shared.state;
    let output = &shared.output;
    let kind = batch[0].origin.job.input.kind.clone();
    let prepared = &state.prepared[&kind];
    let size = batch.len();
    let flush = unix_ns();
    let queue_durations: Vec<_> = batch.iter().map(|p| ns(p.admitted.elapsed())).collect();
    let start = Instant::now();
    let jobs_result = state.pool.install(|| {
        batch
            .par_iter()
            .map(|p| {
                state
                    .prover
                    .make_job_prepared(prepared, &p.request)
                    .map_err(|e| format!("witness: {e:?}"))
            })
            .collect::<std::result::Result<Vec<_>, _>>()
    });
    let witness_ns = ns(start.elapsed());
    let witness_end = unix_ns();
    let jobs = match jobs_result {
        Ok(jobs) => jobs,
        Err(e) => {
            for p in batch {
                let reply = base(&p.origin, &shared.host);
                output.reject(&p.origin.route, reply, p.origin.job.warmup, &e)?;
            }
            return Ok(());
        }
    };
    let proving = Instant::now();
    let proofs = state
        .pool
        .install(|| state.prover.prove_batch_parallel(prepared, &jobs));
    let prove_ns = ns(proving.elapsed());
    let prove_end = unix_ns();
    if proofs.len() != size {
        return Err("proof count differs from input count".into());
    }
    let results: Vec<_> = proofs
        .into_iter()
        .zip(&batch)
        .map(|(proof, p)| SyncResult {
            public_inputs: p.request.public_inputs.clone(),
            proof,
        })
        .collect();
    let encoding = Instant::now();
    let encoded = state.pool.install(|| {
        results
            .par_iter()
            .map(|r| {
                state
                    .prover
                    .encode_sync_result(prepared, r)
                    .map_err(|e| format!("encode: {e:?}"))
            })
            .collect::<std::result::Result<Vec<_>, _>>()
    });
    let encode_ns = ns(encoding.elapsed());
    let encode_end = unix_ns();
    let batch_compute_ns = ns(start.elapsed());
    let mut typed = Some((results, jobs));
    let mut typed_drop_ns = None;
    let mut release = |typed: &mut Option<_>| {
        let freeing = Instant::now();
        drop(typed.take());
        typed_drop_ns = Some(ns(freeing.elapsed()));
    };
    if output.mode == Mode::QueuedReturn {
        release(&mut typed);
    }
    let encoded = match encoded {
        Ok(bytes) => bytes,
        Err(e) => {
            for p in batch {
                let reply = base(&p.origin, &shared.host);
                output.reject(&p.origin.route, reply, p.origin.job.warmup, &e)?;
            }
            release(&mut typed);
            return Ok(());
        }
    };
    let encoded_capacity_bytes: usize = encoded.iter().map(Vec::capacity).sum();
    let times = BatchTimes {
        id,
        size,
        flush,
        witness_end,
        prove_end,
        encode_end,
        witness_ns,
        prove_ns,
        encode_ns,
    };
    let handoff = Instant::now();
    for ((p, bytes), queue_ns) in batch.into_iter().zip(encoded).zip(queue_durations) {
        drop(p.request);
        emit_result(p.origin, bytes, None, None, &times, queue_ns, shared)?;
    }
    let handoff_ns = ns(handoff.elapsed());
    // `original` releases the typed batch after the return loop, as measured.
    if typed.is_some() {
        release(&mut typed);
    }
    output.log.write(&json!({
        "event": "server_batch",
        "batch_id": id,
        "kind": kind,
        "jobs": size,
        "flush_unix_ns": flush,
        "encode_end_unix_ns": encode_end,
        "batch_compute_ns": batch_compute_ns,
        "witness_ns": witness_ns,
        "prove_ns": prove_ns,
        "encode_ns": encode_ns,
        "typed_drop_ns": typed_drop_ns,
        "typed_release_tid": thread_label(),
        "handoff_ns": handoff_ns,
        "encoded_batch_capacity_bytes": encoded_capacity_bytes,
        "return_budget": output.budget.snapshot()?,
        "mode": output.mode.name(),
        "phase_scope": output.mode.phase_scope(),
    }))?;
    Ok(())
}

/// The same batching policy with every job completed as one fused task
/// inside the parallel stage.
fn process_fused(batch: Vec<Pending>, id: u64, shared: &Shared) -> Result<()> {
    let state = &shared.state;
    let output = &shared.output;
    let kind = batch[0].origin.job.input.kind.clone();
    let prepared = &state.prepared[&kind];
    let size = batch.len();
    let flush = unix_ns();
    let start = Instant::now();
    let items: Vec<_> = batch
        .into_iter()
        .map(|p| ((p.origin, ns(p.admitted.elapsed())), p.request))
        .collect();
    let results = completion::complete_batch(&state.pool, &state.prover, prepared, items);
    let batch_compute_ns = ns(start.elapsed());
    let stage_end = unix_ns();
    let done: Vec<&Completed> = results
        .iter()
        .filter_map(|(_, r)| r.as_ref().ok())
        .collect();
    let witness_end = done
        .iter()
        .map(|d| d.times.witness_end_unix_ns)
        .max()
        .unwrap_or(flush);
    let prove_end = done
        .iter()
        .map(|d| d.times.prove_end_unix_ns)
        .max()
        .unwrap_or(witness_end);
    let sum = |f: fn(&StageTimes) -> u64| done.iter().map(|d| f(&d.times)).sum::<u64>();
    let job_stage_sums = json!({
        "witness_ns": sum(|t| t.witness_ns),
        "prove_ns": sum(|t| t.prove_ns),
        "encode_ns": sum(|t| t.encode_ns),
        "hash_ns": sum(|t| t.hash_ns),
        "release_ns": sum(|t| t.release_ns),
        "released_on_worker": done.iter().filter(|d| d.times.release_tid == d.times.worker_tid).count(),
    });
    let encoded_capacity_bytes: usize = done.iter().map(|d| d.bytes.capacity()).sum();
    let failed = size - done.len();
    let times = BatchTimes {
        id,
        size,
        flush,
        witness_end,
        prove_end,
        encode_end: stage_end,
        witness_ns: witness_end.saturating_sub(flush),
        prove_ns: prove_end.saturating_sub(witness_end),
        encode_ns: stage_end.saturating_sub(prove_end),
    };
    let handoff = Instant::now();
    for ((origin, queue_ns), result) in results {
        match result {
            Ok(done) => emit_result(
                origin,
                done.bytes,
                Some(done.sha256),
                Some(done.times),
                &times,
                queue_ns,
                shared,
            )?,
            Err(e) => {
                let reply = base(&origin, &shared.host);
                output.reject(&origin.route, reply, origin.job.warmup, &e.to_string())?;
            }
        }
    }
    output.log.write(&json!({
        "event": "server_batch",
        "batch_id": id,
        "kind": kind,
        "jobs": size,
        "failed_jobs": failed,
        "flush_unix_ns": flush,
        "encode_end_unix_ns": stage_end,
        "batch_compute_ns": batch_compute_ns,
        "witness_ns": times.witness_ns,
        "prove_ns": times.prove_ns,
        "encode_ns": times.encode_ns,
        "typed_drop_ns": Value::Null,
        "job_stage_sums": job_stage_sums,
        "handoff_ns": ns(handoff.elapsed()),
        "encoded_batch_capacity_bytes": encoded_capacity_bytes,
        "return_budget": output.budget.snapshot()?,
        "mode": output.mode.name(),
        "phase_scope": output.mode.phase_scope(),
    }))?;
    Ok(())
}

fn run_batched(
    c: &Config,
    shared: &Shared,
    mut acceptor: Acceptor,
    rx: Receiver<Pending>,
    telemetry_stop: &AtomicBool,
    stats: &Stats,
) -> Result<()> {
    let mut queues: HashMap<String, VecDeque<Pending>> = KINDS
        .into_iter()
        .map(|k| (k.into(), VecDeque::new()))
        .collect();
    let push = |queues: &mut HashMap<String, VecDeque<Pending>>, p: Pending| {
        queues
            .get_mut(&p.origin.job.input.kind)
            .expect("validated kind")
            .push_back(p);
    };
    let mut batch_id = 0u64;
    let work = (|| -> Result<()> {
        while !shared.stop.load(Ordering::Relaxed) && !telemetry_stop.load(Ordering::Relaxed) {
            acceptor.poll()?;
            while let Ok(p) = rx.try_recv() {
                push(&mut queues, p);
            }
            let chosen = queues
                .iter()
                .filter_map(|(kind, q)| {
                    q.front()
                        .filter(|p| q.len() >= c.batch || p.admitted.elapsed() >= c.wait)
                        .map(|p| (kind.clone(), p.admitted))
                })
                .min_by_key(|x| x.1)
                .map(|x| x.0);
            if let Some(kind) = chosen {
                let q = queues.get_mut(&kind).expect("kind queue");
                let n = q.len().min(c.batch);
                let mut batch: Vec<_> = q.drain(..n).collect();
                for p in &mut batch {
                    // Computation starts now; release the admission slot.
                    p.ticket = None;
                }
                batch_id += 1;
                stats.batches.fetch_add(1, Ordering::Relaxed);
                stats.processed.fetch_add(n, Ordering::Relaxed);
                shared.output.log.write(&json!({
                    "event": "flush",
                    "batch_id": batch_id,
                    "kind": kind,
                    "jobs": n,
                    "queued_remaining": shared.admission.admitted(),
                    "observed_unix_ns": unix_ns(),
                }))?;
                match c.mode {
                    Mode::BatchFused => process_fused(batch, batch_id, shared)?,
                    _ => process_phased(batch, batch_id, shared)?,
                }
            } else {
                let wait = queues
                    .values()
                    .filter_map(|q| {
                        q.front()
                            .map(|p| c.wait.saturating_sub(p.admitted.elapsed()))
                    })
                    .min()
                    .unwrap_or(Duration::from_millis(10))
                    .min(Duration::from_millis(10));
                if let Ok(p) = rx.recv_timeout(wait) {
                    push(&mut queues, p);
                }
            }
        }
        Ok(())
    })();
    shared.stop.store(true, Ordering::Relaxed);
    acceptor.finish();
    while let Ok(p) = rx.try_recv() {
        push(&mut queues, p);
    }
    for q in queues.values_mut() {
        for p in q.drain(..) {
            stats.unprocessed.fetch_add(1, Ordering::Relaxed);
            let reply = base(&p.origin, &shared.host);
            if let Err(e) = shared.output.reject(
                &p.origin.route,
                reply,
                p.origin.job.warmup,
                RejectReason::RunLimitBeforeCompute.as_str(),
            ) {
                shared.failures.record(e.to_string());
            }
        }
    }
    work
}

/// Complete one admitted job on the calling worker, or reject it when the
/// run limit arrived before it started.
fn serve_one(p: Pending, shared: &Shared, stats: &Stats) -> Result<()> {
    let Pending {
        origin,
        request,
        admitted,
        ticket,
    } = p;
    // Computation starts now; release the admission slot.
    drop(ticket);
    let queue_ns = ns(admitted.elapsed());
    if shared.stop.load(Ordering::Relaxed) {
        stats.unprocessed.fetch_add(1, Ordering::Relaxed);
        let reply = base(&origin, &shared.host);
        return shared.output.reject(
            &origin.route,
            reply,
            origin.job.warmup,
            RejectReason::RunLimitBeforeCompute.as_str(),
        );
    }
    stats.processed.fetch_add(1, Ordering::Relaxed);
    let prepared = &shared.state.prepared[origin.job.input.kind.as_str()];
    match completion::complete(&shared.state.prover, prepared, request) {
        Ok(done) => {
            let t = done.times;
            let job = BatchTimes {
                id: 0,
                size: 1,
                flush: t.dispatch_unix_ns,
                witness_end: t.witness_end_unix_ns,
                prove_end: t.prove_end_unix_ns,
                encode_end: t.encode_end_unix_ns,
                witness_ns: t.witness_ns,
                prove_ns: t.prove_ns,
                encode_ns: t.encode_ns,
            };
            emit_result(
                origin,
                done.bytes,
                Some(done.sha256),
                Some(t),
                &job,
                queue_ns,
                shared,
            )
        }
        Err(e) => {
            let reply = base(&origin, &shared.host);
            shared
                .output
                .reject(&origin.route, reply, origin.job.warmup, &e.to_string())
        }
    }
}

fn run_continuous(
    c: &Config,
    shared: &Shared,
    mut acceptor: Acceptor,
    rx: Receiver<Pending>,
    telemetry_stop: &AtomicBool,
    stats: &Arc<Stats>,
) -> Result<()> {
    let (worker_shared, worker_stats) = (shared.clone(), stats.clone());
    let runner = ContinuousRunner::spawn(c.max_in_flight, rx, move |p: Pending| {
        if let Err(e) = serve_one(p, &worker_shared, &worker_stats) {
            worker_shared.failures.record(e.to_string());
            worker_shared.stop.store(true, Ordering::Relaxed);
        }
    })?;
    let work = (|| -> Result<()> {
        while !shared.stop.load(Ordering::Relaxed) && !telemetry_stop.load(Ordering::Relaxed) {
            acceptor.poll()?;
            thread::sleep(Duration::from_millis(2));
        }
        Ok(())
    })();
    shared.stop.store(true, Ordering::Relaxed);
    // Joining the readers drops every hand-off sender, so the workers drain
    // the queue, rejecting what has not started, and then stop.
    acceptor.finish();
    let panicked = runner.join();
    if panicked > 0 {
        shared
            .failures
            .record(format!("{panicked} serving workers panicked"));
    }
    work
}

pub fn run() -> Result<()> {
    // Invalid values fail before output creation, circuit preparation or listen.
    let c = Config::read()?;
    let host = host_id();
    if host.len() > wire::MAX_HOST_ID_BYTES {
        return Err("host-id exceeds bounded serving profile".into());
    }
    let out = out_dir()?;
    let log = Logger::new(&out.join("server.jsonl"), c.flush)?;
    let state = State::new(c.depth, c.workers, &log)?;
    state.controls(c.controls, &out, &log)?;
    let listener = TcpListener::bind(&c.listen)?;
    listener.set_nonblocking(true)?;
    let budget = Budget::new(c.return_jobs, c.return_bytes);
    let counts = Arc::new(ReturnCounts::default());
    let output = Output {
        mode: c.mode,
        budget: budget.clone(),
        log: log.clone(),
        counts: counts.clone(),
        timeout: c.timeout,
    };
    let mut meta = provenance("server");
    meta["serving_mode"] = json!(c.mode.name());
    meta["workers"] = json!(c.workers);
    meta["max_in_flight"] = json!(if c.mode == Mode::Continuous {
        Some(c.max_in_flight)
    } else {
        None
    });
    meta["batch_max"] = json!(c.batch);
    meta["max_wait_us"] = json!(c.wait.as_micros());
    meta["max_queue"] = json!(c.max_queue);
    meta["run_ms"] = json!(c.run.as_millis());
    meta["max_connections"] = json!(c.max_connections);
    meta["return_jobs"] = json!(c.return_jobs);
    meta["return_bytes"] = json!(c.return_bytes);
    meta["queue_policy"] = json!(c.mode.policy());
    meta["memory_scope"] = json!(
        "return budget excludes computation in progress (one batch, or max-in-flight jobs), prepared state, bounded ingress and connection frames, thread stacks and OS socket buffers; compare measured whole-process RSS separately"
    );
    fresh_json(&out.join("metadata.json"), &meta)?;
    let stop = Arc::new(AtomicBool::new(false));
    let telemetry_stop = Arc::new(AtomicBool::new(false));
    let admission = Admission::new(c.max_queue);
    let queued = admission.clone();
    let monitor = telemetry(
        log.clone(),
        telemetry_stop.clone(),
        Arc::new(move || queued.admitted()),
        c.telemetry_ms,
    );
    let failures = Failures::default();
    let writers = Arc::new(Mutex::new(Vec::new()));
    let shared = Shared {
        state,
        output,
        admission,
        stop: stop.clone(),
        host,
        failures: failures.clone(),
        writers: writers.clone(),
    };
    let (ingress, rx) = mpsc::sync_channel::<Pending>(c.max_queue);
    let ready = unix_ns();
    let listen = listener.local_addr()?.to_string();
    let acceptor = Acceptor {
        listener: Some(listener),
        ingress: Some(ingress),
        shared: shared.clone(),
        readers: Vec::new(),
        next_connection: 0,
        max_connections: c.max_connections,
    };
    log.write(&json!({"event": "ready", "ready_unix_ns": ready, "listen": listen, "serving_mode": c.mode.name()}))?;
    println!(
        "{}",
        json!({"status": "SERVER_READY", "ready_unix_ns": ready, "listen": listen, "process_id": std::process::id(), "serving_mode": c.mode.name()})
    );
    let started = Instant::now();
    let (clock_stop, run_duration) = (stop.clone(), c.run);
    // Admission stops on time even when compute or the return budget is blocked.
    let admission_timer = thread::spawn(move || {
        while !clock_stop.load(Ordering::Relaxed) && started.elapsed() < run_duration {
            thread::sleep(
                run_duration
                    .saturating_sub(started.elapsed())
                    .min(Duration::from_millis(10)),
            );
        }
        clock_stop.store(true, Ordering::Relaxed);
    });
    let stats = Arc::new(Stats::default());
    let work = match c.mode {
        Mode::Continuous => run_continuous(&c, &shared, acceptor, rx, &telemetry_stop, &stats),
        _ => run_batched(&c, &shared, acceptor, rx, &telemetry_stop, &stats),
    };
    stop.store(true, Ordering::Relaxed);
    if let Err(e) = work {
        failures.record(e.to_string());
    }
    if admission_timer.join().is_err() {
        failures.record("admission timer panic");
    }
    drop(shared);
    // Each writer stops once the last sender for its connection is gone.
    let writer_handles =
        std::mem::take(&mut *writers.lock().map_err(|_| "writer registry poisoned")?);
    for writer in writer_handles {
        if writer.join().is_err() {
            failures.record("return writer panic");
        }
    }
    if telemetry_stop.load(Ordering::Relaxed) {
        failures.record("telemetry stopped after logging failure");
    }
    telemetry_stop.store(true, Ordering::Relaxed);
    if let Some(m) = monitor
        && m.join().is_err()
    {
        failures.record("telemetry panic");
    }
    let snapshot = budget.snapshot()?;
    if snapshot.resident_jobs != 0 || snapshot.resident_bytes != 0 {
        failures.record("return budget did not drain");
    }
    let failures = failures.list();
    fresh_json(
        &out.join("terminal.json"),
        &json!({
            "status": if failures.is_empty() { "SERVER_STOPPED" } else { "SERVER_FAILED" },
            "serving_mode": c.mode.name(),
            "processed_jobs": stats.processed.load(Ordering::Relaxed),
            "unprocessed_jobs": stats.unprocessed.load(Ordering::Relaxed),
            "batches": stats.batches.load(Ordering::Relaxed),
            "responses_written": counts.sent.load(Ordering::Relaxed),
            "response_write_failures": counts.failed.load(Ordering::Relaxed),
            "rejected_jobs": counts.rejected.load(Ordering::Relaxed),
            "return_budget": snapshot,
            "ready_unix_ns": ready,
            "finish_unix_ns": unix_ns(),
            "failures": failures,
            "logging": log.finish()?,
            "note": "Admission closes at the run limit. Admitted work that has not started receives explicit failures; computed returns and those failures drain before exit. Frontend strict acceptance defines success.",
        }),
    )?;
    if failures.is_empty() {
        Ok(())
    } else {
        Err("server cleanup recorded failures; evidence retained".into())
    }
}
