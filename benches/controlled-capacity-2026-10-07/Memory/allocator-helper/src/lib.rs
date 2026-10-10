//! Benchmark-only requested-byte accounting over the unchanged System allocator.
//! This independent test dependency does not relax any production crate lint.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
static ALLOC_CALLS: AtomicUsize = AtomicUsize::new(0);
static ALLOCATED: AtomicUsize = AtomicUsize::new(0);
static FREED: AtomicUsize = AtomicUsize::new(0);
static REALLOC_CALLS: AtomicUsize = AtomicUsize::new(0);

struct CountingSystem;
#[global_allocator]
static ALLOCATOR: CountingSystem = CountingSystem;

fn add(bytes: usize) {
    let live = LIVE.fetch_add(bytes, Ordering::SeqCst) + bytes;
    PEAK.fetch_max(live, Ordering::SeqCst);
    ALLOCATED.fetch_add(bytes, Ordering::SeqCst);
}
fn remove(bytes: usize) {
    LIVE.fetch_sub(bytes, Ordering::SeqCst);
    FREED.fetch_add(bytes, Ordering::SeqCst);
}

// All unsafe operations delegate the caller's unchanged Layout/pointer to System.
// Counter operations allocate no memory and must not call formatting or logging.
unsafe impl GlobalAlloc for CountingSystem {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let pointer = unsafe { System.alloc(layout) };
        if !pointer.is_null() {
            ALLOC_CALLS.fetch_add(1, Ordering::SeqCst);
            add(layout.size());
        }
        pointer
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let pointer = unsafe { System.alloc_zeroed(layout) };
        if !pointer.is_null() {
            ALLOC_CALLS.fetch_add(1, Ordering::SeqCst);
            add(layout.size());
        }
        pointer
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        unsafe { System.dealloc(pointer, layout) };
        remove(layout.size());
    }
    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let replacement = unsafe { System.realloc(pointer, layout, new_size) };
        if !replacement.is_null() {
            REALLOC_CALLS.fetch_add(1, Ordering::SeqCst);
            // A successful realloc releases the previous requested block and
            // owns its replacement. Failed realloc leaves old ownership intact.
            remove(layout.size());
            add(new_size);
        }
        replacement
    }
}

/// Cumulative successful allocator requests, excluding allocator metadata/slack.
#[derive(Clone, Copy, Debug)]
pub struct Snapshot {
    pub live_requested_bytes: usize,
    pub peak_requested_bytes: usize,
    pub successful_allocation_calls: usize,
    pub successful_reallocation_calls: usize,
    pub allocated_requested_bytes: usize,
    pub freed_requested_bytes: usize,
}
pub fn snapshot() -> Snapshot {
    Snapshot {
        live_requested_bytes: LIVE.load(Ordering::SeqCst),
        peak_requested_bytes: PEAK.load(Ordering::SeqCst),
        successful_allocation_calls: ALLOC_CALLS.load(Ordering::SeqCst),
        successful_reallocation_calls: REALLOC_CALLS.load(Ordering::SeqCst),
        allocated_requested_bytes: ALLOCATED.load(Ordering::SeqCst),
        freed_requested_bytes: FREED.load(Ordering::SeqCst),
    }
}
/// Reset only the high-water mark to existing live ownership, never reset live.
/// Call at a quiescent single-test boundary; unrelated thread allocations are
/// process allocations and are not silently excluded.
pub fn begin_interval() -> Snapshot {
    PEAK.store(LIVE.load(Ordering::SeqCst), Ordering::SeqCst);
    snapshot()
}
