//! Host-system integration seam (OPEN SEAM - never frozen).
//!
//! The prover stack is developed against this minimal, explicit contract
//! and a swappable mock of the host core, so the host side can evolve
//! freely and integration later means replacing the mock only
//! (integration-seam rule: freezing applies to prover-internal math,
//! never to this boundary).

pub use ssgkr_verification::{SyncRequest, SyncResult};

/// The contract the HOST core fulfils toward the prover stack: a source
/// of requests and a sink of results. Deliberately minimal; anything
/// richer (streaming, backpressure, priorities) is added on the host
/// side of the seam.
pub trait OssCoreInterface {
    /// Pull the next pending request, if any.
    fn next_request(&mut self) -> Option<SyncRequest>;

    /// Deliver a completed proof.
    fn deliver(&mut self, result: SyncResult);
}

/// Swappable in-memory mock of the host core (test/dev harness).
/// Integration later = replacing this type, nothing else.
#[derive(Debug, Default)]
pub struct MockOssCore {
    /// Queued requests.
    pub requests: Vec<SyncRequest>,
    /// Delivered results.
    pub delivered: Vec<SyncResult>,
}

impl OssCoreInterface for MockOssCore {
    fn next_request(&mut self) -> Option<SyncRequest> {
        if self.requests.is_empty() {
            None
        } else {
            Some(self.requests.remove(0))
        }
    }

    fn deliver(&mut self, result: SyncResult) {
        self.delivered.push(result);
    }
}
