//! The request and reply envelope, bounded framing and deadline writes.
//!
//! A request frame is a 4-byte big-endian length and a JSON [`Job`]. A reply
//! frame is a 4-byte length, a JSON [`Reply`] header, a 4-byte length and the
//! canonical encoded proof. Every reply carries the run and job identifiers of
//! its request, so a client matches replies by identifier and accepts them in
//! any order. Readers enforce frame and metadata limits before allocating or
//! admitting work, and [`write_reply_deadline`] holds one absolute deadline
//! for the whole frame. The format is the one the controlled-capacity caller
//! speaks, so either side interoperates with that caller.

use serde::{Deserialize, Serialize};
use statesync_gkr::primitives::{
    field::{BaseField, PrimeCharacteristicRing, PrimeField32},
    hash::Digest,
};
use statesync_gkr::{
    SyncRequest,
    compiler::{
        AssetId, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOperation, SmtWitness,
    },
};
use std::io::{self, Read, Write};
use std::sync::atomic::{AtomicBool, Ordering};

pub const PROTOCOL: u32 = 1;
pub const MAX_JSON: usize = 2 * 1024 * 1024;
pub const MAX_PROOF: usize = 16 * 1024 * 1024;
pub const MAX_RUN_ID_BYTES: usize = 256;
pub const MAX_KIND_BYTES: usize = 64;
pub const MAX_HOST_ID_BYTES: usize = 256;

#[derive(Clone, Serialize, Deserialize)]
pub struct Leaf {
    pub tag: u8,
    pub payload: Vec<u32>,
    pub identity: [u8; 32],
}
impl Leaf {
    fn from_leaf(x: &LeafState) -> Self {
        match x {
            LeafState::Empty => Self {
                tag: 0,
                payload: vec![],
                identity: [0; 32],
            },
            LeafState::Tombstone => Self {
                tag: 2,
                payload: vec![],
                identity: [0; 32],
            },
            LeafState::Occupied(p) => Self {
                tag: 1,
                payload: p.sync_state.iter().map(|x| x.as_canonical_u32()).collect(),
                identity: p.identity_digest,
            },
        }
    }
    fn leaf(&self) -> Result<LeafState, String> {
        if self.payload.len() > 21 {
            return Err("payload exceeds measured profile".into());
        }
        match self.tag {
            0 | 2 if self.payload.is_empty() && self.identity == [0; 32] => Ok(if self.tag == 0 {
                LeafState::Empty
            } else {
                LeafState::Tombstone
            }),
            1 => Ok(LeafState::Occupied(LeafPayload {
                sync_state: self
                    .payload
                    .iter()
                    .map(|x| fe(*x))
                    .collect::<Result<_, _>>()?,
                identity_digest: self.identity,
            })),
            _ => Err("invalid leaf tag/fields".into()),
        }
    }
}
fn fe(x: u32) -> Result<BaseField, String> {
    if x >= BaseField::ORDER_U32 {
        Err("noncanonical input field".into())
    } else {
        Ok(BaseField::from_u32(x))
    }
}
fn digest(x: &[u32; 8]) -> Result<Digest<BaseField>, String> {
    let mut out = [BaseField::ZERO; 8];
    for (a, b) in out.iter_mut().zip(x) {
        *a = fe(*b)?;
    }
    Ok(Digest(out))
}
fn residues(x: &Digest<BaseField>) -> [u32; 8] {
    core::array::from_fn(|i| x.0[i].as_canonical_u32())
}

#[derive(Clone, Serialize, Deserialize)]
pub struct Input {
    pub kind: String,
    pub key: u64,
    pub old_leaf: Leaf,
    pub new_leaf: Leaf,
    pub siblings: Vec<[u32; 8]>,
    pub old_root: [u32; 8],
    pub new_root: [u32; 8],
    pub value_digest: [u32; 8],
}
impl Input {
    pub fn from_request(r: &SyncRequest) -> Self {
        let (kind, new) = match &r.operation {
            SmtOperation::Membership { .. } => ("membership", &r.witness.leaf),
            SmtOperation::NonMembership { .. } => ("nonmembership", &r.witness.leaf),
            SmtOperation::Update { new_leaf, .. } => ("update", new_leaf),
        };
        Self {
            kind: kind.into(),
            key: r.public_inputs.asset_id.0,
            old_leaf: Leaf::from_leaf(&r.witness.leaf),
            new_leaf: Leaf::from_leaf(new),
            siblings: r.witness.path.siblings.iter().map(residues).collect(),
            old_root: residues(&r.public_inputs.old_root),
            new_root: residues(&r.public_inputs.new_root),
            value_digest: residues(&r.public_inputs.value_digest),
        }
    }
    pub fn request(&self, depth: u32) -> Result<SyncRequest, String> {
        if self.siblings.len() != depth as usize
            || depth == 0
            || depth > 32
            || self.key >= (1u64 << depth.min(24))
        {
            return Err("input outside measured profile".into());
        }
        let old = self.old_leaf.leaf()?;
        let new = self.new_leaf.leaf()?;
        let key = AssetId(self.key);
        let (tag, operation) = match self.kind.as_str() {
            "membership" => {
                if self.old_leaf.tag != 1
                    || serde_json::to_vec(&self.old_leaf).ok()
                        != serde_json::to_vec(&self.new_leaf).ok()
                {
                    return Err("invalid membership leaves".into());
                }
                let LeafState::Occupied(p) = old.clone() else {
                    return Err("membership payload missing".into());
                };
                (0, SmtOperation::Membership { key, payload: p })
            }
            "nonmembership" => {
                if !matches!(self.old_leaf.tag, 0 | 2)
                    || serde_json::to_vec(&self.old_leaf).ok()
                        != serde_json::to_vec(&self.new_leaf).ok()
                {
                    return Err("invalid absence leaves".into());
                }
                (1, SmtOperation::NonMembership { key })
            }
            "update" => (
                2,
                SmtOperation::Update {
                    key,
                    old_leaf: old.clone(),
                    new_leaf: new,
                },
            ),
            _ => return Err("unknown operation kind".into()),
        };
        Ok(SyncRequest {
            operation,
            witness: SmtWitness {
                leaf: old,
                path: MerklePath {
                    siblings: self.siblings.iter().map(digest).collect::<Result<_, _>>()?,
                },
            },
            public_inputs: PublicInputs {
                old_root: digest(&self.old_root)?,
                new_root: digest(&self.new_root)?,
                value_digest: digest(&self.value_digest)?,
                asset_id: key,
                op_kind_tag: tag,
            },
        })
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct Job {
    pub protocol: u32,
    pub run_id: String,
    pub job_id: u64,
    pub fixture_id: usize,
    pub repeat: usize,
    pub warmup: bool,
    pub scheduled_unix_ns: u64,
    pub deadline_unix_ns: u64,
    pub input: Input,
}
#[derive(Clone, Default, Serialize, Deserialize)]
pub struct Reply {
    pub protocol: u32,
    pub run_id: String,
    pub job_id: u64,
    pub fixture_id: usize,
    pub kind: String,
    pub host_id: String,
    pub process_id: u32,
    pub batch_id: u64,
    pub batch_size: usize,
    pub server_received_unix_ns: u64,
    pub server_enqueued_unix_ns: u64,
    pub flush_unix_ns: u64,
    pub witness_start_unix_ns: u64,
    pub witness_end_unix_ns: u64,
    pub prove_end_unix_ns: u64,
    pub encode_end_unix_ns: u64,
    pub server_send_start_unix_ns: u64,
    pub server_queue_ns: u64,
    pub batch_witness_ns: u64,
    pub batch_prove_ns: u64,
    pub batch_encode_ns: u64,
    pub encoded_bytes: usize,
    pub canonical_sha256: String,
    pub error: Option<String>,
}

pub fn write_request(out: &mut impl Write, job: &Job) -> io::Result<usize> {
    let data = serde_json::to_vec(job).map_err(io::Error::other)?;
    if data.len() > MAX_JSON {
        return Err(io::Error::other("request frame too large"));
    }
    out.write_all(&(data.len() as u32).to_be_bytes())?;
    out.write_all(&data)?;
    Ok(data.len() + 4)
}
/// One absolute deadline covers every write in the frame. On error the caller
/// must close the stream, since a partially written frame cannot be retried.
#[derive(Default, Serialize)]
pub struct WriteProgress {
    pub calls: usize,
    pub bytes_written: usize,
    pub would_block: usize,
    pub timed_out: usize,
    pub interrupted: usize,
    pub would_block_after_progress: usize,
    pub bytes_written_after_would_block: usize,
    pub deadline_expired: bool,
}

// The concrete TCP path and deterministic I/O-state tests consume this same
// loop. The adapters supply transport outcomes and elapsed time, not a second
// implementation of offset, retry or deadline decisions.
trait DeadlineWrite: Write {
    fn set_remaining_timeout(&mut self, remaining: std::time::Duration) -> io::Result<()>;
}
impl DeadlineWrite for std::net::TcpStream {
    fn set_remaining_timeout(&mut self, remaining: std::time::Duration) -> io::Result<()> {
        self.set_write_timeout(Some(remaining))
    }
}
trait FrameClock {
    fn elapsed(&self) -> std::time::Duration;
    fn sleep(&mut self, duration: std::time::Duration);
}
struct ElapsedClock(std::time::Instant);
impl FrameClock for ElapsedClock {
    fn elapsed(&self) -> std::time::Duration {
        self.0.elapsed()
    }
    fn sleep(&mut self, duration: std::time::Duration) {
        std::thread::sleep(duration);
    }
}
pub fn write_reply_deadline(
    out: &mut std::net::TcpStream,
    reply: &Reply,
    proof: &[u8],
    timeout: std::time::Duration,
    progress: &mut WriteProgress,
) -> io::Result<usize> {
    let mut clock = ElapsedClock(std::time::Instant::now());
    let data = serde_json::to_vec(reply).map_err(io::Error::other)?;
    if data.len() > MAX_JSON || proof.len() > MAX_PROOF || proof.len() != reply.encoded_bytes {
        return Err(io::Error::other("reply frame bounds/length"));
    }
    let header = (data.len() as u32).to_be_bytes();
    let body = (proof.len() as u32).to_be_bytes();
    write_frame_parts(
        out,
        [&header[..], &data[..], &body[..], proof],
        timeout,
        &mut clock,
        progress,
    )
}
fn write_frame_parts<W: DeadlineWrite, C: FrameClock>(
    out: &mut W,
    parts: [&[u8]; 4],
    timeout: std::time::Duration,
    clock: &mut C,
    progress: &mut WriteProgress,
) -> io::Result<usize> {
    let total = parts.iter().map(|p| p.len()).sum();
    for mut bytes in parts {
        while !bytes.is_empty() {
            let remaining = timeout.saturating_sub(clock.elapsed());
            if remaining.is_zero() {
                progress.deadline_expired = true;
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "response frame deadline",
                ));
            }
            out.set_remaining_timeout(remaining)?;
            progress.calls += 1;
            match out.write(bytes) {
                Ok(0) => {
                    return Err(io::Error::new(
                        io::ErrorKind::WriteZero,
                        "peer stopped accepting frame",
                    ));
                }
                Ok(n) => {
                    progress.bytes_written += n;
                    if progress.would_block > 0 {
                        progress.bytes_written_after_would_block += n;
                    }
                    bytes = &bytes[n..];
                }
                Err(e) if e.kind() == io::ErrorKind::Interrupted => {
                    progress.interrupted += 1;
                }
                // Some targets report a would-block result immediately on an
                // accepted socket inherited from a nonblocking listener. It is
                // temporary backpressure, not a broken frame. Preserve offset
                // and retry within the SAME absolute frame deadline.
                Err(e)
                    if matches!(
                        e.kind(),
                        io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
                    ) =>
                {
                    if e.kind() == io::ErrorKind::WouldBlock {
                        progress.would_block += 1;
                        if progress.bytes_written > 0 {
                            progress.would_block_after_progress += 1;
                        }
                    } else {
                        progress.timed_out += 1;
                    }
                    let remaining = timeout.saturating_sub(clock.elapsed());
                    if remaining.is_zero() {
                        progress.deadline_expired = true;
                        return Err(io::Error::new(
                            io::ErrorKind::TimedOut,
                            "response frame deadline",
                        ));
                    }
                    clock.sleep(remaining.min(std::time::Duration::from_millis(1)));
                }
                Err(e) => return Err(e),
            }
        }
    }
    if clock.elapsed() >= timeout {
        progress.deadline_expired = true;
        return Err(io::Error::new(
            io::ErrorKind::TimedOut,
            "response frame deadline",
        ));
    }
    Ok(total)
}
fn exact(input: &mut impl Read, buf: &mut [u8], stop: &AtomicBool) -> io::Result<(u64, u64)> {
    let mut offset = 0;
    let mut first = None;
    while offset < buf.len() {
        if stop.load(Ordering::Relaxed) {
            return Err(io::Error::new(
                io::ErrorKind::Interrupted,
                "driver stopping",
            ));
        }
        match input.read(&mut buf[offset..]) {
            Ok(0) => {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "peer closed frame",
                ));
            }
            Ok(n) => {
                first.get_or_insert(crate::timing::unix_ns());
                offset += n;
            }
            Err(e)
                if matches!(
                    e.kind(),
                    io::ErrorKind::WouldBlock
                        | io::ErrorKind::TimedOut
                        | io::ErrorKind::Interrupted
                ) => {}
            Err(e) => return Err(e),
        }
    }
    let end = crate::timing::unix_ns();
    Ok((first.unwrap_or(end), end))
}
fn length(input: &mut impl Read, bound: usize, stop: &AtomicBool) -> io::Result<(usize, u64, u64)> {
    let mut bytes = [0; 4];
    let (first, end) = exact(input, &mut bytes, stop)?;
    let n = u32::from_be_bytes(bytes) as usize;
    if n > bound {
        Err(io::Error::other("frame exceeds bound"))
    } else {
        Ok((n, first, end))
    }
}
pub fn read_request(
    input: &mut impl Read,
    stop: &AtomicBool,
) -> io::Result<(Job, u64, usize, u64)> {
    let (n, _, _) = length(input, MAX_JSON, stop)?;
    let mut bytes = vec![0; n];
    let (_, end) = exact(input, &mut bytes, stop)?;
    let t = std::time::Instant::now();
    let job: Job = serde_json::from_slice(&bytes).map_err(io::Error::other)?;
    if job.run_id.is_empty()
        || job.run_id.len() > MAX_RUN_ID_BYTES
        || job.input.kind.len() > MAX_KIND_BYTES
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "request metadata exceeds bounded serving profile",
        ));
    }
    Ok((job, end, n + 4, crate::timing::ns(t.elapsed())))
}
/// One received reply frame: header, proof bytes, wire bytes, Unix time of the
/// first and last received byte, and header decode time in nanoseconds.
pub type ReplyFrame = (Reply, Vec<u8>, usize, u64, u64, u64);

pub fn read_reply(input: &mut impl Read, stop: &AtomicBool) -> io::Result<Option<ReplyFrame>> {
    // EOF before the first byte of a new frame is an orderly peer close. EOF
    // after any byte of a header or body remains a truncated-frame error.
    let mut header = [0u8; 4];
    let (first, _) = match exact(input, &mut header[..1], stop) {
        Ok(t) => t,
        Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(None),
        Err(e) => return Err(e),
    };
    exact(input, &mut header[1..], stop)?;
    let n = u32::from_be_bytes(header) as usize;
    if n > MAX_JSON {
        return Err(io::Error::other("frame exceeds bound"));
    }
    let mut head = vec![0; n];
    exact(input, &mut head, stop)?;
    let t = std::time::Instant::now();
    let reply: Reply = serde_json::from_slice(&head).map_err(io::Error::other)?;
    if reply.run_id.len() > MAX_RUN_ID_BYTES
        || reply.kind.len() > MAX_KIND_BYTES
        || reply.host_id.len() > MAX_HOST_ID_BYTES
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "response metadata exceeds bounded serving profile",
        ));
    }
    let decode_ns = crate::timing::ns(t.elapsed());
    let (p, _, _) = length(input, MAX_PROOF, stop)?;
    if p != reply.encoded_bytes {
        return Err(io::Error::other("reply body length mismatch"));
    }
    let mut bytes = vec![0; p];
    let (_, end) = exact(input, &mut bytes, stop)?;
    Ok(Some((reply, bytes, n + p + 8, first, end, decode_ns)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        io::Cursor,
        net::{TcpListener, TcpStream},
        time::{Duration, Instant},
    };
    #[test]
    fn clean_eof_and_partial_frame_have_different_outcomes() {
        let stop = AtomicBool::new(false);
        assert!(
            read_reply(&mut Cursor::new(Vec::<u8>::new()), &stop)
                .unwrap()
                .is_none()
        );
        assert_eq!(
            read_reply(&mut Cursor::new(vec![0, 0]), &stop)
                .err()
                .unwrap()
                .kind(),
            io::ErrorKind::UnexpectedEof
        );
        let reply = Reply {
            encoded_bytes: 3,
            ..Default::default()
        };
        let head = serde_json::to_vec(&reply).unwrap();
        let mut frame = (head.len() as u32).to_be_bytes().to_vec();
        frame.extend(head);
        frame.extend(3u32.to_be_bytes());
        frame.extend([1, 2]);
        assert_eq!(
            read_reply(&mut Cursor::new(frame), &stop)
                .err()
                .unwrap()
                .kind(),
            io::ErrorKind::UnexpectedEof
        );
    }
    #[test]
    fn request_metadata_is_bounded_before_admission() {
        let request = crate::fixture::original(3, "membership", 0);
        let mut job = Job {
            protocol: PROTOCOL,
            run_id: "x".repeat(MAX_RUN_ID_BYTES),
            job_id: 1,
            fixture_id: 0,
            repeat: 1,
            warmup: false,
            scheduled_unix_ns: 0,
            deadline_unix_ns: 0,
            input: Input::from_request(&request),
        };
        let stop = AtomicBool::new(false);
        let mut encoded = Vec::new();
        write_request(&mut encoded, &job).unwrap();
        assert!(read_request(&mut Cursor::new(encoded), &stop).is_ok());
        job.run_id.push('x');
        let mut encoded = Vec::new();
        write_request(&mut encoded, &job).unwrap();
        assert!(read_request(&mut Cursor::new(encoded), &stop).is_err());
        job.run_id = "test".into();
        job.input.kind = "x".repeat(MAX_KIND_BYTES + 1);
        let mut encoded = Vec::new();
        write_request(&mut encoded, &job).unwrap();
        assert!(read_request(&mut Cursor::new(encoded), &stop).is_err());
    }
    #[derive(Serialize)]
    struct Pressure {
        prefilled_bytes: usize,
        would_block_observations: usize,
        stable_block_ns: u64,
    }
    fn saturate_without_reader(server: &mut TcpStream) -> Pressure {
        // Buffer capacities are OS policy, not constants inferred from a frame
        // size. Establish and record a sustained real WouldBlock before testing
        // the production writer. Total prefill and preparation wall are bounded.
        const MAX_PREFILL: usize = 64 * 1024 * 1024;
        let chunk = [0xa5; 64 * 1024];
        let started = Instant::now();
        let mut report = Pressure {
            prefilled_bytes: 0,
            would_block_observations: 0,
            stable_block_ns: 0,
        };
        let mut blocked_since = None;
        loop {
            assert!(
                started.elapsed() < Duration::from_secs(2),
                "PRESSURE_FIXTURE_NOT_SATURATED: no stable WouldBlock within 2 seconds; prefilled={}",
                report.prefilled_bytes
            );
            assert!(
                report.prefilled_bytes < MAX_PREFILL,
                "PRESSURE_FIXTURE_NOT_SATURATED: OS buffered the full 64 MiB prefill cap"
            );
            let amount = chunk.len().min(MAX_PREFILL - report.prefilled_bytes);
            match server.write(&chunk[..amount]) {
                Ok(0) => panic!("pressure fixture unexpectedly closed"),
                Ok(n) => {
                    report.prefilled_bytes += n;
                    blocked_since = None;
                }
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                    report.would_block_observations += 1;
                    let since = blocked_since.get_or_insert_with(Instant::now);
                    if since.elapsed() >= Duration::from_millis(30) {
                        report.stable_block_ns = crate::timing::ns(since.elapsed());
                        return report;
                    }
                    std::thread::sleep(Duration::from_millis(1));
                }
                Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => panic!("pressure fixture transport failure: {e}"),
            }
        }
    }
    fn drain_prefix(client: &mut TcpStream, mut remaining: usize) {
        let mut scratch = [0u8; 64 * 1024];
        while remaining > 0 {
            let n = remaining.min(scratch.len());
            client.read_exact(&mut scratch[..n]).unwrap();
            assert!(scratch[..n].iter().all(|b| *b == 0xa5));
            remaining -= n;
        }
    }
    #[test]
    fn nonblocking_backpressure_recovers_when_reader_resumes() {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let mut client = TcpStream::connect(listener.local_addr().unwrap()).unwrap();
        let (mut server, _) = listener.accept().unwrap();
        server.set_nonblocking(true).unwrap();
        let pressure = saturate_without_reader(&mut server);
        let prefilled = pressure.prefilled_bytes;
        let receiving = std::thread::spawn(move || {
            std::thread::sleep(Duration::from_millis(150));
            drain_prefix(&mut client, prefilled);
            let (_, bytes, _, _, _, _) = read_reply(&mut client, &AtomicBool::new(false))
                .unwrap()
                .unwrap();
            assert_eq!(bytes.len(), MAX_PROOF);
            assert!(bytes.iter().all(|b| *b == 73));
        });
        let bytes = vec![73; MAX_PROOF];
        let response = Reply {
            encoded_bytes: bytes.len(),
            ..Default::default()
        };
        let mut progress = WriteProgress::default();
        let result = write_reply_deadline(
            &mut server,
            &response,
            &bytes,
            Duration::from_secs(5),
            &mut progress,
        );
        eprintln!(
            "{}",
            serde_json::json!({"pressure_test":"reader_resumes","prefill":pressure,"frame_write":progress,"result":result.as_ref().ok()})
        );
        let written = result.unwrap();
        assert_eq!(
            written, progress.bytes_written,
            "frame offset duplicated or omitted bytes"
        );
        assert!(
            progress.would_block > 0,
            "PRESSURE_FIXTURE_NOT_CONSUMED: writer did not observe WouldBlock"
        );
        assert!(
            progress.bytes_written_after_would_block > 0,
            "PRESSURE_FIXTURE_NOT_CONSUMED: no successful continuation after WouldBlock"
        );
        receiving.join().unwrap();
    }
    #[test]
    fn nonreading_peer_reaches_one_absolute_deadline() {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let _client = TcpStream::connect(listener.local_addr().unwrap()).unwrap();
        let (mut server, _) = listener.accept().unwrap();
        server.set_nonblocking(true).unwrap();
        let pressure = saturate_without_reader(&mut server);
        let bytes = vec![0; MAX_PROOF];
        let response = Reply {
            encoded_bytes: bytes.len(),
            ..Default::default()
        };
        let started = Instant::now();
        let mut progress = WriteProgress::default();
        let result = write_reply_deadline(
            &mut server,
            &response,
            &bytes,
            Duration::from_millis(50),
            &mut progress,
        );
        eprintln!(
            "{}",
            serde_json::json!({"pressure_test":"nonreading_peer","prefill":pressure,"frame_write":progress,"elapsed_ns":crate::timing::ns(started.elapsed()),"result":result.as_ref().ok()})
        );
        assert!(
            progress.would_block > 0,
            "PRESSURE_FIXTURE_NOT_CONSUMED: writer did not observe WouldBlock"
        );
        let error = result.expect_err("PRESSURE_FIXTURE_LOST: full frame fit after saturation; this is not a timeout counterexample");
        assert_eq!(error.kind(), io::ErrorKind::TimedOut);
        assert!(progress.deadline_expired);
        assert!(started.elapsed() >= Duration::from_millis(50));
        assert!(started.elapsed() < Duration::from_secs(2));
    }

    use std::{cell::Cell, collections::VecDeque, rc::Rc};
    struct ManualClock(Rc<Cell<Duration>>);
    impl FrameClock for ManualClock {
        fn elapsed(&self) -> Duration {
            self.0.get()
        }
        fn sleep(&mut self, d: Duration) {
            self.0.set(self.0.get() + d);
        }
    }
    enum Step {
        Write(usize, u64),
        Error(io::ErrorKind, u64),
    }
    struct ScriptedWriter {
        clock: Rc<Cell<Duration>>,
        steps: VecDeque<Step>,
        block_when_empty: bool,
        received: Vec<u8>,
        timeouts: Vec<Duration>,
    }
    impl Write for ScriptedWriter {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            let idle = if self.block_when_empty {
                Step::Error(io::ErrorKind::WouldBlock, 0)
            } else {
                Step::Write(usize::MAX, 0)
            };
            let step = self.steps.pop_front().unwrap_or(idle);
            match step {
                Step::Write(limit, ms) => {
                    self.clock.set(self.clock.get() + Duration::from_millis(ms));
                    let n = limit.min(bytes.len());
                    self.received.extend_from_slice(&bytes[..n]);
                    Ok(n)
                }
                Step::Error(kind, ms) => {
                    self.clock.set(self.clock.get() + Duration::from_millis(ms));
                    Err(io::Error::from(kind))
                }
            }
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }
    impl DeadlineWrite for ScriptedWriter {
        fn set_remaining_timeout(&mut self, d: Duration) -> io::Result<()> {
            self.timeouts.push(d);
            Ok(())
        }
    }
    fn scripted(steps: Vec<Step>, block: bool) -> (ScriptedWriter, ManualClock) {
        let state = Rc::new(Cell::new(Duration::ZERO));
        (
            ScriptedWriter {
                clock: state.clone(),
                steps: steps.into(),
                block_when_empty: block,
                received: vec![],
                timeouts: vec![],
            },
            ManualClock(state),
        )
    }
    const PARTS: [&[u8]; 4] = [b"ABCD", b"EFGH", b"IJKL", b"MNOP"];
    #[test]
    fn production_loop_preserves_partial_part_offsets_and_interruptions() {
        use io::ErrorKind::{Interrupted, WouldBlock};
        let (mut writer, mut clock) = scripted(
            vec![
                Step::Write(2, 3),
                Step::Error(WouldBlock, 0),
                Step::Error(Interrupted, 2),
                Step::Write(1, 1),
                Step::Write(usize::MAX, 1),
                Step::Write(3, 1),
                Step::Error(WouldBlock, 0),
                Step::Write(usize::MAX, 1),
                Step::Write(1, 1),
                Step::Error(Interrupted, 0),
                Step::Write(usize::MAX, 1),
                Step::Write(2, 1),
                Step::Error(WouldBlock, 0),
                Step::Write(usize::MAX, 1),
            ],
            false,
        );
        let mut progress = WriteProgress::default();
        assert_eq!(
            write_frame_parts(
                &mut writer,
                PARTS,
                Duration::from_millis(50),
                &mut clock,
                &mut progress
            )
            .unwrap(),
            16
        );
        assert_eq!(writer.received, b"ABCDEFGHIJKLMNOP");
        assert_eq!(progress.bytes_written, 16);
        assert_eq!(progress.would_block, 3);
        assert_eq!(progress.would_block_after_progress, 3);
        assert_eq!(progress.interrupted, 2);
        assert!(writer.steps.is_empty());
        assert!(writer.timeouts.windows(2).all(|w| w[1] <= w[0]));
        assert!(!progress.deadline_expired);
        eprintln!(
            "{}",
            serde_json::json!({"write_state_test":"partial_offsets_and_interruptions","scope":"scripted transport and logical time; same production loop","progress":progress,"received":"ABCDEFGHIJKLMNOP","remaining_ms":writer.timeouts.iter().map(|t|t.as_millis()).collect::<Vec<_>>()})
        );
    }
    #[test]
    fn production_loop_shares_one_deadline_across_parts_and_retries() {
        let (mut writer, mut clock) = scripted(
            vec![Step::Write(usize::MAX, 6), Step::Write(usize::MAX, 6)],
            true,
        );
        let mut progress = WriteProgress::default();
        let error = write_frame_parts(
            &mut writer,
            PARTS,
            Duration::from_millis(15),
            &mut clock,
            &mut progress,
        )
        .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::TimedOut);
        assert_eq!(writer.received, b"ABCDEFGH");
        assert_eq!(clock.elapsed(), Duration::from_millis(15));
        assert_eq!(writer.timeouts, [15, 9, 3, 2, 1].map(Duration::from_millis));
        assert_eq!(progress.would_block, 3);
        assert!(progress.deadline_expired);
        eprintln!(
            "{}",
            serde_json::json!({"write_state_test":"one_deadline","scope":"scripted transport and logical time; same production loop","progress":progress,"elapsed_ms":clock.elapsed().as_millis(),"remaining_ms":writer.timeouts.iter().map(|t|t.as_millis()).collect::<Vec<_>>()})
        );
    }
    #[test]
    fn production_loop_rejects_a_final_write_completed_after_deadline() {
        let (mut writer, mut clock) = scripted(
            vec![
                Step::Write(usize::MAX, 1),
                Step::Write(usize::MAX, 1),
                Step::Write(usize::MAX, 1),
                Step::Write(usize::MAX, 20),
            ],
            false,
        );
        let mut progress = WriteProgress::default();
        let error = write_frame_parts(
            &mut writer,
            PARTS,
            Duration::from_millis(10),
            &mut clock,
            &mut progress,
        )
        .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::TimedOut);
        assert_eq!(writer.received, b"ABCDEFGHIJKLMNOP");
        assert_eq!(clock.elapsed(), Duration::from_millis(23));
        assert_eq!(writer.timeouts, [10, 9, 8, 7].map(Duration::from_millis));
        assert!(progress.deadline_expired);
    }
}
