//! Compiler parameters - the isolation point for measured/tuned values.
//!
//! STRUCTURE here is frozen with the design; VALUES are not. Tree depth,
//! layer strategy and their defaults are instance/genesis parameters that
//! the 2c measurement loop may re-tune without touching code structure
//! (measured-value isolation principle, design doc D-29).

/// SMT shape parameters.
///
/// The tree is the RWA Registry asset-state tree: sequential AssetID
/// keys, depth `d` fixed per instance at genesis. Re-instancing with
/// d = 28/32 is a config change, not a code change (D-28).
/// (Under `--cfg creusot` the verifier's `PartialEq` derive needs a
/// `DeepModel`; plain machine data, simply derived - same for
/// [`LayerStrategy`] below.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(creusot, derive(creusot_std::prelude::DeepModel))]
pub struct SmtParams {
    /// Tree depth `d` (path length). Default 24: 2^24 ~ 16.7M slots per
    /// instance, migration trigger at 60-70% occupancy.
    pub depth: u32,
    /// Maximum leaf ENCODING length (field elements, tag included) the
    /// instance supports - the structural bound of the collision-resistant
    /// leaf hash (2d ping-pong CR fix): the leaf pre-image is a FIXED,
    /// LOSSLESS `[tag, len, verbatim, 0-pad]` layout of this bound, fully
    /// absorbed by the sponge, and longer encodings are a structural error
    /// (never hashed). A genesis parameter like `depth`: it fixes the leaf
    /// gadget's circuit width, so re-instancing (bigger asset-state schema)
    /// is a config change, not a code change. Default: generous double
    /// cover of the RWA asset-state schema envelope (spec section 3.7).
    pub leaf_max_fields: u32,
}

impl Default for SmtParams {
    fn default() -> Self {
        Self {
            depth: 24,
            leaf_max_fields: ssgkr_primitives::hash::DEFAULT_LEAF_MAX_FIELDS as u32,
        }
    }
}

/// Layer-cutting strategy for Module 1 (candidate ranking A > C > B from
/// the 1a interview; final pick confirmed by the 2c measurement loop).
///
/// The strategy is a compiler INPUT, not a compile-time constant, so
/// benchmarks can sweep it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
#[cfg_attr(creusot, derive(creusot_std::prelude::DeepModel))]
pub enum LayerStrategy {
    /// One SMT tree level = one logical GKR layer (data-parallel regular
    /// wiring; lowest FV cost; the default).
    #[default]
    A,
    /// Merge `k` adjacent tree levels into one GKR layer (only if round
    /// count is the measured bottleneck; raises predicate degree/density
    /// and FV cost).
    B {
        /// Number of merged levels.
        merge_k: u32,
    },
    /// Split each level's hash rounds into thin low-degree layers
    /// (refinement option; less pressing with the x^3 S-box).
    C,
}
