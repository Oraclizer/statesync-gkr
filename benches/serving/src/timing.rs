//! Clocks, durations, thread labels and the per-job stage record.

use serde::Serialize;
use std::cell::Cell;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

/// Wall-clock Unix time in nanoseconds. Use it for event coordinates on one
/// host only; differences across hosts assume nothing about clock agreement.
pub fn unix_ns() -> u64 {
    let elapsed = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock is set before the Unix epoch");
    u64::try_from(elapsed.as_nanos()).expect("Unix timestamp overflows u64 nanoseconds")
}

/// A duration in whole nanoseconds, saturating at `u64::MAX`.
pub fn ns(duration: Duration) -> u64 {
    u64::try_from(duration.as_nanos()).unwrap_or(u64::MAX)
}

static NEXT_THREAD_LABEL: AtomicU64 = AtomicU64::new(1);

thread_local! {
    static THREAD_LABEL: Cell<u64> = const { Cell::new(0) };
    static OS_THREAD_ID: Cell<Option<Option<u64>>> = const { Cell::new(None) };
}

/// A small process-unique label for the calling thread, assigned on first use.
///
/// Labels show which thread ran or released a job inside one process. They are
/// not operating-system thread identifiers; see [`os_thread_id`] for those.
pub fn thread_label() -> u64 {
    THREAD_LABEL.with(|label| {
        if label.get() == 0 {
            label.set(NEXT_THREAD_LABEL.fetch_add(1, Ordering::Relaxed));
        }
        label.get()
    })
}

/// The operating-system thread identifier where the platform exposes it to
/// safe code (Linux `/proc/thread-self`), cached per thread. `None` elsewhere.
pub fn os_thread_id() -> Option<u64> {
    OS_THREAD_ID.with(|cached| {
        if let Some(value) = cached.get() {
            return value;
        }
        let value = std::fs::read_link("/proc/thread-self")
            .ok()
            .and_then(|link| link.file_name()?.to_str()?.parse().ok());
        cached.set(Some(value));
        value
    })
}

/// Stage record of one fused job completion.
///
/// Durations come from one monotonic clock on the completing thread. The
/// `*_unix_ns` fields are wall-clock coordinates from the same host.
/// `worker_tid` and `release_tid` are [`thread_label`] values: equal values
/// mean the thread that built the typed witness and proof also freed them.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
pub struct StageTimes {
    pub worker_tid: u64,
    pub worker_os_tid: Option<u64>,
    pub dispatch_unix_ns: u64,
    pub witness_end_unix_ns: u64,
    pub prove_end_unix_ns: u64,
    pub encode_end_unix_ns: u64,
    pub done_unix_ns: u64,
    pub witness_ns: u64,
    pub prove_ns: u64,
    pub encode_ns: u64,
    pub hash_ns: u64,
    pub release_ns: u64,
    pub release_tid: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn thread_labels_are_stable_per_thread_and_distinct_across_threads() {
        let here = thread_label();
        assert_eq!(here, thread_label());
        let there = std::thread::spawn(thread_label).join().unwrap();
        assert_ne!(here, there);
        assert_ne!(here, 0);
        assert_ne!(there, 0);
    }

    #[test]
    fn durations_saturate_instead_of_wrapping() {
        assert_eq!(ns(Duration::from_nanos(7)), 7);
        assert_eq!(ns(Duration::MAX), u64::MAX);
    }
}
