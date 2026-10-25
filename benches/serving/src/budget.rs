//! Bounded return budget for finished responses.
//!
//! A finished response holds its encoded proof until the frame write and the
//! write's log row complete. The budget caps those resident responses by
//! count and by encoded-buffer capacity, so a slow or stalled peer turns into
//! backpressure on the producers instead of unbounded memory. A [`Permit`]
//! stays charged until it is dropped, which includes the active write.
//!
//! The byte figure counts encoded `Vec` capacity only. Computation in
//! progress, prepared circuits, ingress frames, thread stacks, socket buffers
//! and allocator overhead are outside it; compare whole-process RSS
//! separately.

use serde::Serialize;
use std::fmt;
use std::sync::{Arc, Condvar, Mutex};
use std::time::Instant;

#[derive(Default)]
struct Usage {
    jobs: usize,
    bytes: usize,
    peak_jobs: usize,
    peak_bytes: usize,
    waits: usize,
    wait_ns: u64,
    closed: bool,
}

/// The shared return budget.
pub struct Budget {
    max_jobs: usize,
    max_bytes: usize,
    usage: Mutex<Usage>,
    available: Condvar,
}

/// One resident response's charge. Dropping it returns the charge.
pub struct Permit {
    budget: Arc<Budget>,
    bytes: usize,
}

/// A point-in-time view of the budget, serialized into server logs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct BudgetSnapshot {
    pub resident_jobs: usize,
    pub resident_bytes: usize,
    pub peak_jobs: usize,
    pub peak_bytes: usize,
    pub max_jobs: usize,
    pub max_bytes: usize,
    pub wait_count: usize,
    pub wait_ns: u64,
    pub includes_active_writer: bool,
    pub byte_scope: &'static str,
}

/// Why a permit was not granted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BudgetError {
    /// One response is larger than the whole byte budget.
    Oversize { bytes: usize, max_bytes: usize },
    /// The budget was closed while waiting or before the call.
    Closed,
    /// A thread panicked while holding the budget lock.
    Poisoned,
}

impl fmt::Display for BudgetError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Oversize { bytes, max_bytes } => write!(
                f,
                "one response of {bytes} bytes exceeds the return byte budget {max_bytes}"
            ),
            Self::Closed => f.write_str("return budget closed"),
            Self::Poisoned => f.write_str("return budget poisoned"),
        }
    }
}

impl std::error::Error for BudgetError {}

const BYTE_SCOPE: &str = "encoded Vec capacity only; computation in progress, metadata, prepared state, sockets and allocator overhead are separate";

impl Budget {
    /// A budget of at most `max_jobs` resident responses and `max_bytes` of
    /// encoded capacity.
    pub fn new(max_jobs: usize, max_bytes: usize) -> Arc<Self> {
        Arc::new(Self {
            max_jobs,
            max_bytes,
            usage: Mutex::new(Usage::default()),
            available: Condvar::new(),
        })
    }

    pub fn max_jobs(&self) -> usize {
        self.max_jobs
    }

    pub fn max_bytes(&self) -> usize {
        self.max_bytes
    }

    /// Wait until one response of `bytes` fits, then charge it.
    pub fn acquire(self: &Arc<Self>, bytes: usize) -> Result<Permit, BudgetError> {
        if bytes > self.max_bytes {
            return Err(BudgetError::Oversize {
                bytes,
                max_bytes: self.max_bytes,
            });
        }
        let start = Instant::now();
        let mut usage = self.usage.lock().map_err(|_| BudgetError::Poisoned)?;
        let mut waited = false;
        while !usage.closed && (usage.jobs == self.max_jobs || bytes > self.max_bytes - usage.bytes)
        {
            waited = true;
            usage = self
                .available
                .wait(usage)
                .map_err(|_| BudgetError::Poisoned)?;
        }
        if usage.closed {
            return Err(BudgetError::Closed);
        }
        if waited {
            usage.waits += 1;
            usage.wait_ns = usage
                .wait_ns
                .saturating_add(crate::timing::ns(start.elapsed()));
        }
        usage.jobs += 1;
        usage.bytes += bytes;
        usage.peak_jobs = usage.peak_jobs.max(usage.jobs);
        usage.peak_bytes = usage.peak_bytes.max(usage.bytes);
        Ok(Permit {
            budget: self.clone(),
            bytes,
        })
    }

    /// Refuse every current and future waiter. Existing permits stay valid.
    pub fn close(&self) {
        if let Ok(mut usage) = self.usage.lock() {
            usage.closed = true;
        }
        self.available.notify_all();
    }

    pub fn snapshot(&self) -> Result<BudgetSnapshot, BudgetError> {
        let u = self.usage.lock().map_err(|_| BudgetError::Poisoned)?;
        Ok(BudgetSnapshot {
            resident_jobs: u.jobs,
            resident_bytes: u.bytes,
            peak_jobs: u.peak_jobs,
            peak_bytes: u.peak_bytes,
            max_jobs: self.max_jobs,
            max_bytes: self.max_bytes,
            wait_count: u.waits,
            wait_ns: u.wait_ns,
            includes_active_writer: true,
            byte_scope: BYTE_SCOPE,
        })
    }
}

impl Drop for Permit {
    fn drop(&mut self) {
        if let Ok(mut u) = self.budget.usage.lock() {
            u.jobs -= 1;
            u.bytes -= self.bytes;
        }
        self.budget.available.notify_all();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{sync::mpsc, thread, time::Duration};

    #[test]
    fn active_writer_remains_charged_until_drop() {
        let budget = Budget::new(2, 10);
        let p = budget.acquire(7).unwrap();
        let (tx, rx) = mpsc::channel();
        let b = budget.clone();
        let handle = thread::spawn(move || {
            let q = b.acquire(4).unwrap();
            tx.send(()).unwrap();
            drop(q);
        });
        assert!(rx.recv_timeout(Duration::from_millis(30)).is_err());
        drop(p);
        rx.recv_timeout(Duration::from_secs(1)).unwrap();
        handle.join().unwrap();
        assert_eq!(budget.snapshot().unwrap().resident_jobs, 0);
        assert_eq!(budget.snapshot().unwrap().peak_bytes, 7);
    }

    #[test]
    fn failure_wakes_waiters_and_oversize_fails() {
        let budget = Budget::new(1, 10);
        assert_eq!(
            budget.acquire(11).err(),
            Some(BudgetError::Oversize {
                bytes: 11,
                max_bytes: 10
            })
        );
        let _p = budget.acquire(1).unwrap();
        let b = budget.clone();
        let handle = thread::spawn(move || b.acquire(1).is_err());
        budget.close();
        assert!(handle.join().unwrap());
    }
}
