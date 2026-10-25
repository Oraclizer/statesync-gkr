//! Bounded admission with explicit rejection.
//!
//! An overloaded service should answer with a visible, countable rejection
//! instead of queueing without limit and paying later in latency and memory.
//! [`Admission`] caps the jobs that are admitted but have not yet started
//! computing, across every connection. A job holds its [`AdmissionTicket`]
//! until computation starts, and dropping the ticket releases the slot.
//! [`RejectReason`] names each explicit refusal sent back to a client.

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

/// A shared cap on admitted jobs that have not started computing.
#[derive(Debug)]
pub struct Admission {
    limit: usize,
    admitted: AtomicUsize,
}

/// One admitted job's slot. Dropping it releases the slot.
#[derive(Debug)]
pub struct AdmissionTicket {
    admission: Arc<Admission>,
}

impl Admission {
    /// A cap of `limit` admitted jobs. A zero limit rejects every job.
    pub fn new(limit: usize) -> Arc<Self> {
        Arc::new(Self {
            limit,
            admitted: AtomicUsize::new(0),
        })
    }

    /// Admit one job, or return `None` when the cap is reached. The count can
    /// never exceed the cap, even transiently, under concurrent callers.
    pub fn try_admit(self: &Arc<Self>) -> Option<AdmissionTicket> {
        self.admitted
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |n| {
                (n < self.limit).then_some(n + 1)
            })
            .ok()
            .map(|_| AdmissionTicket {
                admission: self.clone(),
            })
    }

    /// Jobs currently admitted and not yet computing.
    pub fn admitted(&self) -> usize {
        self.admitted.load(Ordering::Acquire)
    }

    pub fn limit(&self) -> usize {
        self.limit
    }
}

impl Drop for AdmissionTicket {
    fn drop(&mut self) {
        self.admission.admitted.fetch_sub(1, Ordering::AcqRel);
    }
}

/// An explicit refusal returned to the client in place of a proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RejectReason {
    /// The admission cap was reached.
    QueueFull,
    /// The bounded hand-off to the scheduler was full.
    IngressFull,
    /// The server is stopping and no longer schedules work.
    Stopping,
    /// The run limit arrived before this admitted job started computing.
    RunLimitBeforeCompute,
    /// The encoded proof does not fit the frame or return budget limits.
    ResponseExceedsBudget,
}

impl RejectReason {
    /// The stable reason string carried in the reply's `error` field.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::QueueFull => "server_total_queue_full",
            Self::IngressFull => "server_ingress_queue_full",
            Self::Stopping => "server_stopping",
            Self::RunLimitBeforeCompute => "server_run_limit_before_compute",
            Self::ResponseExceedsBudget => "encoded_response_exceeds_return_budget",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cap_is_enforced_and_dropping_a_ticket_releases_its_slot() {
        let admission = Admission::new(2);
        let first = admission.try_admit().unwrap();
        let _second = admission.try_admit().unwrap();
        assert!(admission.try_admit().is_none());
        assert_eq!(admission.admitted(), 2);
        drop(first);
        assert_eq!(admission.admitted(), 1);
        assert!(admission.try_admit().is_some());
    }

    #[test]
    fn zero_limit_rejects_everything() {
        let admission = Admission::new(0);
        assert!(admission.try_admit().is_none());
        assert_eq!(admission.admitted(), 0);
    }

    #[test]
    fn concurrent_admission_never_exceeds_the_cap() {
        let admission = Admission::new(5);
        let tickets = std::sync::Mutex::new(Vec::new());
        std::thread::scope(|scope| {
            for _ in 0..8 {
                scope.spawn(|| {
                    for _ in 0..100 {
                        if let Some(ticket) = admission.try_admit() {
                            assert!(admission.admitted() <= admission.limit());
                            tickets.lock().unwrap().push(ticket);
                        }
                    }
                });
            }
        });
        assert_eq!(tickets.lock().unwrap().len(), 5);
        tickets.lock().unwrap().clear();
        assert_eq!(admission.admitted(), 0);
    }

    #[test]
    fn reason_strings_are_the_wire_values() {
        assert_eq!(RejectReason::QueueFull.as_str(), "server_total_queue_full");
        assert_eq!(
            RejectReason::RunLimitBeforeCompute.as_str(),
            "server_run_limit_before_compute"
        );
    }
}
