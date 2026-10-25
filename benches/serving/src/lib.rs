//! Serving components for StateSync-GKR proof services.
//!
//! The prover library produces and checks proofs; a service around it also
//! needs the parts collected here. Each module is usable on its own:
//!
//! - [`wire`]: the request and reply envelope bound to a run and job
//!   identifier, length-prefixed framing with size and metadata limits, and a
//!   reply writer that holds one absolute deadline per frame.
//! - [`admission`]: a bounded admission count shared by every connection and
//!   the explicit rejection reasons a client receives instead of unbounded
//!   queueing.
//! - [`budget`]: a bounded return budget, in responses and encoded bytes, that
//!   stays charged until the frame write and its log row finish.
//! - [`completion`]: fused per-job completion (witness, proof, encoding,
//!   hash and release of typed intermediates on one thread), a batch helper
//!   built on it, and a continuous worker runner that starts the oldest
//!   waiting job as soon as a worker is free.
//! - [`timing`]: clocks, thread labels and the per-job stage record.
//! - [`fixture`]: the deterministic request constructor used by the measured
//!   benchmark corpus.
//!
//! Every helper calls only the public prover API. A completed job is proved
//! by the same per-job calls as the prover's own batch entry points, and each
//! proof transcript starts from that job's public inputs, so scheduling and
//! thread choices cannot change proof bytes. The reference server and load
//! frontend in `src/bin/ssgkr-serving` compose these parts.

pub mod admission;
pub mod budget;
pub mod completion;
pub mod fixture;
pub mod timing;
pub mod wire;
