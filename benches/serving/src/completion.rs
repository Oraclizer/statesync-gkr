//! Fused per-job completion and the batch and continuous helpers built on it.
//!
//! [`complete`] generates the witness, proves, encodes, hashes and releases
//! the typed intermediates of one request on the calling thread. The thread
//! that allocated the typed witness and proof also frees them, so a
//! dispatcher never pays for releasing a whole batch between batches.
//!
//! Proof bytes do not depend on which helper, thread or order runs a job.
//! [`complete`] calls `make_job_prepared` and `prove_batch_prepared` with a
//! single job, the same per-job proving path as the prover's sequential and
//! parallel batch APIs, and each proof transcript starts from that job's own
//! public inputs.

use crate::timing::{StageTimes, ns, os_thread_id, thread_label, unix_ns};
use sha2::{Digest, Sha256};
use statesync_gkr::{PreparedSync, StateSyncProver, SyncRequest, SyncResult};
use std::fmt;
use std::sync::mpsc::Receiver;
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};
use std::time::Instant;

/// One completed job: the canonical encoded proof, its SHA-256 and stage times.
pub struct Completed {
    pub bytes: Vec<u8>,
    pub sha256: String,
    pub times: StageTimes,
}

/// Why a job was not completed. No partial proof is ever returned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompletionError {
    /// Witness generation refused the request.
    Witness(String),
    /// The prover returned a different number of proofs than jobs.
    ProofCount(usize),
    /// The canonical encoder refused the proved result.
    Encode(String),
}

impl fmt::Display for CompletionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Witness(e) => write!(f, "witness: {e}"),
            Self::ProofCount(n) => write!(f, "prover returned {n} proofs for one job"),
            Self::Encode(e) => write!(f, "encode: {e}"),
        }
    }
}

impl std::error::Error for CompletionError {}

/// Lowercase hexadecimal SHA-256 of `bytes`.
pub fn sha256_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        out.push(char::from(HEX[usize::from(byte >> 4)]));
        out.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    out
}

/// Complete one request on the calling thread: witness, proof, canonical
/// encoding, SHA-256 of the encoding, then release of the typed witness,
/// typed proof and request before returning the bytes.
pub fn complete(
    prover: &StateSyncProver,
    prepared: &PreparedSync,
    request: SyncRequest,
) -> Result<Completed, CompletionError> {
    let mut times = StageTimes {
        worker_tid: thread_label(),
        worker_os_tid: os_thread_id(),
        dispatch_unix_ns: unix_ns(),
        ..StageTimes::default()
    };
    let started = Instant::now();
    let job = prover
        .make_job_prepared(prepared, &request)
        .map_err(|e| CompletionError::Witness(format!("{e:?}")))?;
    times.witness_ns = ns(started.elapsed());
    times.witness_end_unix_ns = unix_ns();

    let proving = Instant::now();
    let mut proofs = prover.prove_batch_prepared(prepared, std::slice::from_ref(&job));
    times.prove_ns = ns(proving.elapsed());
    times.prove_end_unix_ns = unix_ns();
    if proofs.len() != 1 {
        return Err(CompletionError::ProofCount(proofs.len()));
    }
    let result = SyncResult {
        public_inputs: request.public_inputs.clone(),
        proof: proofs.pop().expect("exactly one proof was checked above"),
    };

    let encoding = Instant::now();
    let bytes = prover
        .encode_sync_result(prepared, &result)
        .map_err(|e| CompletionError::Encode(format!("{e:?}")))?;
    times.encode_ns = ns(encoding.elapsed());
    times.encode_end_unix_ns = unix_ns();

    let hashing = Instant::now();
    let sha256 = sha256_hex(&bytes);
    times.hash_ns = ns(hashing.elapsed());

    let releasing = Instant::now();
    drop(result);
    drop(proofs);
    drop(job);
    drop(request);
    times.release_ns = ns(releasing.elapsed());
    times.release_tid = thread_label();
    times.done_unix_ns = unix_ns();
    Ok(Completed {
        bytes,
        sha256,
        times,
    })
}

/// Complete every request of one batch inside `pool`, one fused task per
/// request, and return the results in input order with each request's tag.
///
/// A failed job affects only its own result. The call returns when the
/// slowest job of the batch finishes; [`ContinuousRunner`] avoids that wait.
pub fn complete_batch<T: Send>(
    pool: &rayon::ThreadPool,
    prover: &StateSyncProver,
    prepared: &PreparedSync,
    items: Vec<(T, SyncRequest)>,
) -> Vec<(T, Result<Completed, CompletionError>)> {
    use rayon::prelude::*;
    pool.install(|| {
        items
            .into_par_iter()
            .map(|(tag, request)| {
                let result = complete(prover, prepared, request);
                (tag, result)
            })
            .collect()
    })
}

/// A fixed set of worker threads. Each takes the oldest queued item, handles
/// it to the end, and then takes the next one, so a finished worker never
/// waits for a batch to end and items of any kind interleave in queue order.
///
/// The workers stop when every sender of the queue has been dropped and the
/// queue is empty.
pub struct ContinuousRunner {
    handles: Vec<JoinHandle<()>>,
}

impl ContinuousRunner {
    pub fn spawn<T, F>(workers: usize, queue: Receiver<T>, handle: F) -> std::io::Result<Self>
    where
        T: Send + 'static,
        F: Fn(T) + Send + Sync + 'static,
    {
        let queue = Arc::new(Mutex::new(queue));
        let handle = Arc::new(handle);
        let mut handles = Vec::with_capacity(workers);
        for index in 0..workers {
            let queue = queue.clone();
            let handle = handle.clone();
            let worker = thread::Builder::new()
                .name(format!("serving-worker-{index}"))
                .spawn(move || {
                    loop {
                        // The lock is held only while waiting for the next
                        // item, never while handling one.
                        let next = match queue.lock() {
                            Ok(receiver) => receiver.recv(),
                            Err(_) => return,
                        };
                        match next {
                            Ok(item) => handle(item),
                            Err(_) => return,
                        }
                    }
                })?;
            handles.push(worker);
        }
        Ok(Self { handles })
    }

    /// Wait for every worker and return how many of them panicked.
    pub fn join(self) -> usize {
        self.handles
            .into_iter()
            .map(JoinHandle::join)
            .filter(Result::is_err)
            .count()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fixture;
    use statesync_gkr::{StateSyncGkrConfig, compiler::SmtOpKind, compiler::SmtParams};
    use std::sync::mpsc;

    fn prover(depth: u32) -> StateSyncProver {
        StateSyncProver::new(StateSyncGkrConfig {
            smt: SmtParams {
                depth,
                ..Default::default()
            },
            ..Default::default()
        })
    }

    #[test]
    fn hex_matches_the_reference_digest() {
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn fused_completion_equals_the_batch_api_bytes_for_every_kind() {
        let depth = 3;
        let prover = prover(depth);
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(2)
            .build()
            .unwrap();
        for (label, kind) in [
            ("membership", SmtOpKind::Membership),
            ("nonmembership", SmtOpKind::NonMembership),
            ("update", SmtOpKind::Update),
        ] {
            let prepared = prover.prepare(kind).unwrap();
            let requests: Vec<_> = (0..3).map(|i| fixture::original(depth, label, i)).collect();
            let jobs: Vec<_> = requests
                .iter()
                .map(|r| prover.make_job_prepared(&prepared, r).unwrap())
                .collect();
            let parallel = pool.install(|| prover.prove_batch_parallel(&prepared, &jobs));
            let expected: Vec<Vec<u8>> = parallel
                .into_iter()
                .zip(&requests)
                .map(|(proof, r)| {
                    let result = SyncResult {
                        public_inputs: r.public_inputs.clone(),
                        proof,
                    };
                    prover.encode_sync_result(&prepared, &result).unwrap()
                })
                .collect();
            for (request, bytes) in requests.iter().zip(&expected) {
                let done = complete(&prover, &prepared, request.clone()).unwrap();
                assert_eq!(&done.bytes, bytes, "{label}");
                assert_eq!(done.sha256, sha256_hex(bytes));
                assert!(prover.verify_encoded_sync_op(&prepared, request, &done.bytes));
                assert_eq!(done.times.worker_tid, done.times.release_tid);
            }
            let tagged: Vec<_> = requests.iter().cloned().enumerate().collect();
            let batch = complete_batch(&pool, &prover, &prepared, tagged);
            assert_eq!(batch.len(), expected.len());
            for (index, (tag, result)) in batch.into_iter().enumerate() {
                assert_eq!(tag, index);
                assert_eq!(result.unwrap().bytes, expected[index], "{label}");
            }
        }
    }

    #[test]
    fn a_refused_witness_fails_only_that_job() {
        let depth = 3;
        let prover = prover(depth);
        let prepared = prover.prepare(SmtOpKind::Membership).unwrap();
        let good = fixture::original(depth, "membership", 0);
        let mut bad = good.clone();
        bad.witness.path.siblings.pop();
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(2)
            .build()
            .unwrap();
        let results = complete_batch(&pool, &prover, &prepared, vec![(0, bad), (1, good)]);
        assert!(matches!(results[0].1, Err(CompletionError::Witness(_))));
        assert!(results[1].1.is_ok());
    }

    #[test]
    fn continuous_runner_handles_every_item_and_stops_when_senders_drop() {
        let (tx, rx) = mpsc::sync_channel::<u64>(16);
        let seen = Arc::new(Mutex::new(Vec::new()));
        let record = seen.clone();
        let runner = ContinuousRunner::spawn(3, rx, move |item| {
            record.lock().unwrap().push((item, thread_label()));
        })
        .unwrap();
        for item in 0..40 {
            tx.send(item).unwrap();
        }
        drop(tx);
        assert_eq!(runner.join(), 0);
        let mut items: Vec<_> = seen.lock().unwrap().iter().map(|x| x.0).collect();
        items.sort_unstable();
        assert_eq!(items, (0..40).collect::<Vec<_>>());
    }
}
