//! Module 3 - Deadline-Aware Batching Prover Loop.
//!
//! Amortizes prover cost by proving N witnesses of the SAME circuit as
//! one batch, under a deadline: the real throughput lever of pre-trading
//! finality (single-proof latency is not the story; batched throughput
//! is).
//!
//! v0.1 scope (core freeze): the STRUCTURE below is real implementation
//! surface (not a placeholder to be discarded); only batch-size TUNING
//! values are parameters for the later measurement loop. Theorem D
//! (batching correctness: each proof in a batch verifies exactly as a
//! single proof) is FV-track work.
//!
//! Four elements (design doc, Module 3): witness queue (classified per
//! circuit kind), batch-size policy (deadline remaining + queue length +
//! amortization), batch prover loop, result distribution.

use std::collections::VecDeque;
use std::time::Duration;

use ssgkr_compiler::{PublicInputs, SmtOpKind};
use ssgkr_primitives::field::BaseField;
use ssgkr_protocol::CircuitWitness;

/// One queued proving job: a witness for a known circuit kind.
#[derive(Clone, Debug)]
pub struct ProveJob {
    /// Circuit selector (jobs batch only within the same kind).
    pub kind: SmtOpKind,
    /// Public inputs of this job.
    pub public_inputs: PublicInputs,
    /// Full wire assignment.
    pub witness: CircuitWitness<BaseField>,
}

/// Witness queue, classified per circuit kind so a batch always shares
/// one compiled circuit (Module 1 caches structure per kind).
#[derive(Debug, Default)]
pub struct WitnessQueue {
    membership: VecDeque<ProveJob>,
    non_membership: VecDeque<ProveJob>,
    update: VecDeque<ProveJob>,
}

impl WitnessQueue {
    /// Create an empty queue.
    pub fn new() -> Self {
        Self::default()
    }

    /// Enqueue a job under its circuit kind.
    pub fn push(&mut self, job: ProveJob) {
        match job.kind {
            SmtOpKind::Membership => self.membership.push_back(job),
            SmtOpKind::NonMembership => self.non_membership.push_back(job),
            SmtOpKind::Update => self.update.push_back(job),
        }
    }

    /// Queue length for one kind.
    pub fn len(&self, kind: SmtOpKind) -> usize {
        match kind {
            SmtOpKind::Membership => self.membership.len(),
            SmtOpKind::NonMembership => self.non_membership.len(),
            SmtOpKind::Update => self.update.len(),
        }
    }

    /// Whether all lanes are empty.
    pub fn is_empty(&self) -> bool {
        self.membership.is_empty() && self.non_membership.is_empty() && self.update.is_empty()
    }

    /// Drain up to `n` jobs of one kind (FIFO) for a batch.
    pub fn drain(&mut self, kind: SmtOpKind, n: usize) -> Vec<ProveJob> {
        let lane = match kind {
            SmtOpKind::Membership => &mut self.membership,
            SmtOpKind::NonMembership => &mut self.non_membership,
            SmtOpKind::Update => &mut self.update,
        };
        let take = n.min(lane.len());
        lane.drain(..take).collect()
    }
}

/// Batch-size policy knobs. VALUES here are the measured-tuning surface
/// (2c loop + v0.2 sweep); the STRUCTURE (what the decision reads) is
/// fixed: deadline remaining, queue length, amortization curve.
#[derive(Clone, Copy, Debug)]
pub struct BatchPolicy {
    /// Hard cap on batch size (amortization saturates; default from the
    /// benchmark sweep, provisional until measured).
    pub max_batch_size: usize,
    /// Proving deadline for one batch (pre-trading finality window
    /// budget share; instance parameter).
    pub deadline: Duration,
    /// Minimum queue length worth batching (below this, prove singly to
    /// keep latency flat).
    pub min_batch_size: usize,
}

impl Default for BatchPolicy {
    fn default() -> Self {
        Self {
            max_batch_size: 32,
            deadline: Duration::from_millis(200),
            min_batch_size: 2,
        }
    }
}

/// Deadline-aware batch-size decision.
///
/// FV note: scheduling is NOT part of the soundness surface (Theorem D
/// covers proof equivalence, not timing); property-based tests carry the
/// correctness weight here (design doc, Module 3 difficulty note).
#[derive(Clone, Debug, Default)]
pub struct DeadlineScheduler {
    /// Policy knobs.
    pub policy: BatchPolicy,
}

impl DeadlineScheduler {
    /// Decide the batch size for one kind given the current queue length and
    /// the remaining deadline budget.
    ///
    /// Structure (frozen): the decision reads queue length, the amortization
    /// cap (`max_batch_size`), and the remaining deadline; the VALUES are the
    /// tunable surface (2c loop + v0.2 sweep). Deterministic by design (N1):
    /// a tighter remaining budget proves proportionally fewer jobs so the
    /// batch finishes in time, but never below `min_batch_size`.
    pub fn decide_batch_size(&self, queue_len: usize, remaining: Duration) -> usize {
        let p = &self.policy;
        if queue_len == 0 {
            return 0;
        }
        if queue_len < p.min_batch_size {
            // Too few to amortize, but still make progress on what is queued.
            return queue_len;
        }
        // Amortization saturates at the cap.
        let mut size = queue_len.min(p.max_batch_size);
        // Deadline bias: scale down proportionally to the remaining fraction
        // of the deadline (integer arithmetic - no wall-clock nondeterminism
        // beyond the caller-supplied `remaining`).
        if remaining < p.deadline {
            let rn = remaining.as_nanos().max(1);
            let dn = p.deadline.as_nanos().max(1);
            let scaled = (size as u128 * rn / dn) as usize;
            let floor = p.min_batch_size.min(queue_len);
            size = scaled.clamp(floor, size);
        }
        size
    }
}

/// A proved batch: per-job proofs in queue order.
#[derive(Debug)]
pub struct BatchResult {
    /// Per-job GKR proofs, aligned with the drained jobs.
    pub proofs: Vec<ssgkr_protocol::GkrProof>,
}

/// Batch prover loop: drains the queue per policy, proves each batch on
/// one shared compiled circuit, distributes results.
///
/// FV-CONTRACT (Theorem D, stated in FV track):
///   every proof in `BatchResult` verifies exactly as if produced by the
///   single-proof path with the same witness and transcript convention.
#[derive(Debug, Default)]
pub struct BatchProver {
    /// Scheduling policy.
    pub scheduler: DeadlineScheduler,
}

impl BatchProver {
    /// Run one scheduling round: for each circuit kind, decide a batch size,
    /// drain that many jobs, and prove them as one batch over the shared
    /// compiled circuit. The actual proving is INJECTED (`prove_batch`) so
    /// this crate stays pure batching structure - the compile-once/prove-many
    /// amortization and the transcript convention live one layer up (the
    /// facade), keeping the dependency direction clean (S-1).
    ///
    /// `remaining` is the caller-supplied deadline budget for this round.
    pub fn prove_round<F>(
        &mut self,
        queue: &mut WitnessQueue,
        remaining: Duration,
        mut prove_batch: F,
    ) -> Vec<BatchResult>
    where
        F: FnMut(SmtOpKind, &[ProveJob]) -> Vec<ssgkr_protocol::GkrProof>,
    {
        let mut results = Vec::new();
        for kind in [
            SmtOpKind::Membership,
            SmtOpKind::NonMembership,
            SmtOpKind::Update,
        ] {
            let n = queue.len(kind);
            let size = self.scheduler.decide_batch_size(n, remaining);
            if size == 0 {
                continue;
            }
            let jobs = queue.drain(kind, size);
            let proofs = prove_batch(kind, &jobs);
            results.push(BatchResult { proofs });
        }
        results
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ssgkr_compiler::AssetId;
    use ssgkr_primitives::hash::Digest;
    use ssgkr_protocol::{CircuitWitness, GkrProof};

    fn policy() -> BatchPolicy {
        BatchPolicy {
            max_batch_size: 32,
            deadline: Duration::from_millis(200),
            min_batch_size: 2,
        }
    }

    fn dummy_job(kind: SmtOpKind) -> ProveJob {
        ProveJob {
            kind,
            public_inputs: PublicInputs {
                old_root: Digest::zero(),
                new_root: Digest::zero(),
                op_kind_tag: PublicInputs::kind_tag(kind),
                asset_id: AssetId(0),
                value_digest: Digest::zero(),
            },
            witness: CircuitWitness {
                layer_values: vec![],
            },
        }
    }

    #[test]
    fn decide_batch_size_logic() {
        let s = DeadlineScheduler { policy: policy() };
        let ample = Duration::from_millis(200);
        assert_eq!(s.decide_batch_size(0, ample), 0);
        assert_eq!(
            s.decide_batch_size(1, ample),
            1,
            "below min: take what's there"
        );
        assert_eq!(
            s.decide_batch_size(10, ample),
            10,
            "ample budget, under cap"
        );
        assert_eq!(s.decide_batch_size(100, ample), 32, "amortization cap");
        assert_eq!(
            s.decide_batch_size(32, Duration::from_millis(100)),
            16,
            "half the deadline proves half the batch"
        );
        assert_eq!(
            s.decide_batch_size(32, Duration::from_nanos(1)),
            2,
            "very tight budget floors at min_batch_size"
        );
    }

    #[test]
    fn prove_round_drains_and_batches_per_kind() {
        let mut q = WitnessQueue::new();
        for _ in 0..5 {
            q.push(dummy_job(SmtOpKind::Membership));
        }
        for _ in 0..3 {
            q.push(dummy_job(SmtOpKind::Update));
        }
        let mut bp = BatchProver::default();
        let results = bp.prove_round(&mut q, Duration::from_millis(200), |_kind, jobs| {
            jobs.iter()
                .map(|_| GkrProof {
                    layer_proofs: vec![],
                })
                .collect()
        });
        let total: usize = results.iter().map(|r| r.proofs.len()).sum();
        assert_eq!(total, 8, "all queued jobs proved this round");
        assert!(q.is_empty());
    }
}
