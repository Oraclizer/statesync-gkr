//! Top-level configuration: the single isolation point for all
//! measured/tuned values (structure frozen, values tunable).
//!
//! Everything a benchmark sweep or an instance genesis may change lives
//! here as a VALUE; nothing here changes code structure. This is the
//! "measured-value isolation" rule: tree depth, layer strategy and batch
//! sizing are re-tuned by the measurement loop without touching the
//! frozen interfaces.

use ssgkr_batching::BatchPolicy;
use ssgkr_compiler::{LayerStrategy, SmtParams};

/// Full prover-stack configuration.
///
/// R3 refinement note (mapping #27): the config is the value surface that
/// fixes the `statesync_gkr_v01` locale's instance - `smt` supplies the
/// model's `params` (depth `dd`), `layer_strategy` selects the modeled
/// compilation fragment (strategy A - the domain clause machine-checked at
/// `compile`/`verify_sync_op`), and the compiled stack these values
/// determine is the concrete instantiation of the locale's abstract
/// `stack` parameter. `batching` is Theorem D surface (mapping #32,
/// outside R1~R4).
#[derive(Clone, Debug, Default)]
pub struct StateSyncGkrConfig {
    /// SMT shape (depth d; genesis parameter, default 24).
    pub smt: SmtParams,
    /// Module 1 layer-cutting strategy (default A; candidate order
    /// A > C > B, finalized by the measurement loop).
    pub layer_strategy: LayerStrategy,
    /// Module 3 batching knobs (sizes/deadline; tuned in v0.2).
    pub batching: BatchPolicy,
}
