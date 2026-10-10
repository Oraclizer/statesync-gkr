//! StateSync-GKR: a GKR prover stack specialised for sparse-Merkle-tree
//! state verification, built on plonky3 primitives.
//!
//! # Workspace map (dependency direction is a frozen boundary, S-1)
//!
//! ```text
//! ssgkr-primitives   thin plonky3 =0.4.3 adapter (field/hash/transcript)
//!       ^
//! ssgkr-sumcheck     multilinear sumcheck (generic; AFP-conformant shape)
//!       ^
//! ssgkr-protocol     circuit IR + GKR assembly (generic)
//!       ^
//! ssgkr-compiler     Module 1: SMT -> circuit compiler (workload-specific)
//! ssgkr-batching     Module 3: deadline-aware batching structure
//! ssgkr-commitment   full circuit commitment + strategy identity
//!       ^                 ^
//! ssgkr-verification R3 owner
//! ssgkr-wrap         Module 4: outer wrap adapter
//!       ^
//! statesync-gkr      this facade: host seam + product API
//! ```
//!
//! The generic crates (`sumcheck`, `gkr`) carry no SMT assumptions and
//! stay extractable as standalone contributions; the compiler and the
//! host seam carry all workload specifics.
//!
//! # FV anticipation
//!
//! Formal models and historical target-theorem sketches live in
//! `formal/isabelle/`
//! (Isabelle, sketch-only). Contracts appear throughout as
//! `FV-CONTRACT` / `FV-KANI` comments; tooling runs in a later track.

pub mod config;
pub mod oss_interface;

pub use config::StateSyncGkrConfig;
pub use oss_interface::{MockOssCore, OssCoreInterface, SyncRequest, SyncResult};
pub use ssgkr_verification::{DOMAIN_TAG_V01, SyncError};

pub use ssgkr_batching as batching;
pub use ssgkr_compiler as compiler;
pub use ssgkr_primitives as primitives;
pub use ssgkr_protocol as gkr;
pub use ssgkr_sumcheck as sumcheck;
pub use ssgkr_wrap as wrap;

use ssgkr_batching::ProveJob;
use ssgkr_compiler::{PublicInputs, SmtOpKind, compile_with_hints, generate_witness};
use ssgkr_primitives::field::{BaseField, PrimeCharacteristicRing};
use ssgkr_primitives::hash::{DefaultHasher, Digest, HashGadget};
use ssgkr_protocol::LayeredCircuit;
use ssgkr_protocol::wiring::DerivedRegularWiring;
use ssgkr_verification as verification;
use ssgkr_wrap::commitment::{full_circuit_commitment, strategy_identity};
use ssgkr_wrap::encoding::{self, CircuitIdentity, EncodeError, InnerProofEnvelope};

// Named imports on purpose (the prelude glob would shadow the std derives
// and `vec!` - see the note in ssgkr-primitives::hash). `LayerStrategy` is
// named only inside contracts (the modeled-domain clauses below).
#[cfg(creusot)]
use creusot_std::prelude::trusted;

// (No facade-local extern specs: `Result::map_err` already carries a
// creusot-std spec at the pinned rev - supplying another is a duplicate-spec
// error, verified empirically.)

/// The composed prover: compiled-circuit cache + single-path prove/verify
/// (Module 3 wraps this for batching).
#[derive(Debug, Default)]
pub struct StateSyncProver {
    /// Stack configuration (measured values isolated here).
    pub config: StateSyncGkrConfig,
}

/// Per-`(kind, config)` prepared pipeline state (v0.2, ADR-0001): exactly
/// the batch-shareable work and nothing else - the compiled circuit
/// (prover and verifier side) and the derived succinct wiring oracle (the
/// verifier's amortizable `v_setup`).
///
/// Profile evidence (`cargo run --release --bin profile`, benches/REPORT):
/// every other prove stage is (challenge, witness)-dependent per job -
/// oracle construction + sumcheck folding ~86-90%, Fiat-Shamir hashing
/// ~8-12%, allocation ~0.3% - so sharing STOPS here and further
/// throughput comes from job-level parallelism
/// ([`StateSyncProver::prove_batch_parallel`]), never from cross-job
/// state (which would touch proof bytes and break the Theorem D
/// pointwise-agreement obligation).
///
/// Intended lifetime: long-lived - build once per op kind at
/// startup/genesis, reuse across every batch. Immutable after
/// construction and `Sync`, so one instance serves all worker threads.
#[derive(Clone, Debug)]
pub struct PreparedSync {
    kind: SmtOpKind,
    circuit: LayeredCircuit<BaseField>,
    wiring: DerivedRegularWiring,
    /// Full circuit commitment (v0.3 S-5 hardening) - circuit-only, so it
    /// is exactly batch-shareable setup like the two fields above.
    commitment: Digest<BaseField>,
}

impl PreparedSync {
    /// The op kind this preparation serves (jobs batch per kind, S-1 lanes).
    pub fn kind(&self) -> SmtOpKind {
        self.kind
    }

    /// The full circuit commitment this preparation binds proofs to
    /// (canonical compile or compiled pinned constant; never caller wire).
    pub fn circuit_commitment(&self) -> &Digest<BaseField> {
        &self.commitment
    }
}

impl StateSyncProver {
    /// Create a prover with the given configuration.
    pub fn new(config: StateSyncGkrConfig) -> Self {
        Self { config }
    }

    /// Prove one sync operation through the normative R3 owner.
    pub fn prove_sync_op(&self, request: &SyncRequest) -> Result<SyncResult, SyncError> {
        verification::prove_sync_op(&self.config, request)
    }

    /// Build a batching job from a request (compile + witness generation).
    /// Module 3 enqueues these and drains them per policy.
    ///
    /// (Refinement scope note: Theorem D surface, mapping #32 - OUTSIDE
    /// R1~R4; batching correctness is the separate v0.2 FV track, so no
    /// refinement contract is placed here. `trusted` is crate-survival
    /// only: the body hits the same `Unsupported(Ctor(Variant, Fn))`
    /// translation wall as [`Self::prove_sync_op`]. Zero claims.)
    #[cfg_attr(creusot, trusted)]
    pub fn make_job(&self, request: &SyncRequest) -> Result<ProveJob, SyncError> {
        let kind = request.operation.kind();
        let circuit = verification::circuit_for(&self.config, kind)?;
        let witness = generate_witness(
            &self.config.smt,
            self.config.layer_strategy,
            &circuit,
            &request.operation,
            &request.public_inputs,
            &request.witness,
        )
        .map_err(SyncError::Witness)?;
        Ok(ProveJob {
            kind,
            public_inputs: request.public_inputs.clone(),
            witness,
        })
    }

    /// Prove a batch of same-kind jobs over ONE shared compiled circuit (the
    /// amortization: compile once, prove many). Injected into
    /// [`ssgkr_batching::BatchProver::prove_round`], which owns the queue and
    /// scheduling structure. Each proof uses the identical S-5 preamble as
    /// [`Self::prove_sync_op`], so the same [`Self::verify_sync_op`] accepts it.
    ///
    /// (Refinement scope note: Theorem D surface, mapping #32 - OUTSIDE
    /// R1~R4, as [`Self::make_job`]. `trusted` is crate-survival only: a
    /// non-trusted body referencing [`DOMAIN_TAG_V01`] pulls the
    /// byte-string constant into translation, which ICEs the backend
    /// (`lower_term` not-yet-implemented, R3 finding). Zero claims.)
    #[cfg_attr(creusot, trusted)]
    pub fn prove_batch(&self, kind: SmtOpKind, jobs: &[ProveJob]) -> Vec<gkr::GkrProof> {
        let circuit = match verification::circuit_for(&self.config, kind) {
            Ok(c) => c,
            Err(_) => return Vec::new(),
        };
        let commitment =
            full_circuit_commitment(&circuit, kind, &self.config.smt, self.config.layer_strategy);
        jobs.iter()
            .map(|job| {
                verification::prove_on(
                    &self.config,
                    &circuit,
                    kind,
                    &commitment,
                    &job.public_inputs,
                    &job.witness,
                )
            })
            .collect()
    }

    // ------------------------------------------------------------------
    // v0.2 throughput surface (ADR-0001: independent-job batching).
    //
    // Every function below is (Creusot) claim-free `trusted`: this is the
    // Theorem D surface (refinement mapping #32, OUTSIDE R1~R4) plus the
    // R3-pinned translation walls (byte-string constant, foreign `==`).
    // The verification meaning is untouched - single-path semantics stay
    // machine-checked where they were, and the batch pipe's obligations
    // (length + pointwise agreement with the single path) are discharged
    // on the Isabelle side (GKR_Batching.thy, v0.2 pipe interpretation)
    // and pinned executable by tests/batch_v02.rs.
    // ------------------------------------------------------------------

    /// Compile + derive ONCE for one op kind: the amortizable setup of both
    /// the prover (compile) and the verifier (compile + wiring derivation =
    /// the `v_setup` of benches/REPORT). Build per kind at startup, reuse
    /// across every batch (see [`PreparedSync`]).
    ///
    /// (Creusot: claim-free `trusted`, v0.2 surface - see the section note.
    /// The modeled-domain iff stays machine-checked at `compile` /
    /// [`Self::verify_sync_op`]; this function adds no claims.)
    #[cfg_attr(creusot, trusted)]
    pub fn prepare(&self, kind: SmtOpKind) -> Result<PreparedSync, SyncError> {
        let template =
            DefaultHasher::new(self.config.smt.leaf_max_fields as usize).round_template();
        let (circuit, hints) = match compile_with_hints(
            &self.config.smt,
            kind,
            self.config.layer_strategy,
            &template,
        ) {
            Ok(v) => v,
            Err(e) => return Err(SyncError::Compile(e)),
        };
        let wiring = DerivedRegularWiring::derive(&circuit, &hints);
        let commitment =
            full_circuit_commitment(&circuit, kind, &self.config.smt, self.config.layer_strategy);
        Ok(PreparedSync {
            kind,
            circuit,
            wiring,
            commitment,
        })
    }

    /// Construct prepared state only from the reviewed d24, strategy-A,
    /// Membership material. The validator owns every expected anchor and does
    /// not compile or fall back to [`Self::prepare`] on failure.
    pub fn prepare_pinned_d24_a_membership(
        &self,
        bytes: &[u8],
    ) -> Result<PreparedSync, wrap::prepared::PreparedMaterialError> {
        if self.config.smt.depth != wrap::prepared::PREPARED_DEPTH
            || self.config.smt.leaf_max_fields != wrap::prepared::PREPARED_LEAF_MAX_FIELDS
            || self.config.layer_strategy != ssgkr_compiler::LayerStrategy::A
        {
            return Err(wrap::prepared::PreparedMaterialError::ConfigMismatch);
        }

        let validated = wrap::prepared::validate_pinned_d24_a_membership_material(bytes)?;
        let material = validated.material;
        let bytes = wrap::prepared::PINNED_D24_A_MEMBERSHIP_CIRCUIT_COMMITMENT;
        let commitment = Digest(std::array::from_fn(|index| {
            let word = std::array::from_fn(|byte| bytes[index * 4 + byte]);
            BaseField::from_u32(u32::from_le_bytes(word))
        }));
        Ok(PreparedSync {
            kind: material.kind,
            circuit: material.circuit,
            wiring: validated.derived_wiring,
            commitment,
        })
    }

    /// Prove one request against prepared state (no per-request compile).
    /// Proof bytes are identical to [`Self::prove_sync_op`] - both funnel
    /// through the same normative verification-owner pipeline.
    ///
    /// (Creusot: claim-free `trusted`, v0.2 surface - see the section note.)
    #[cfg_attr(creusot, trusted)]
    pub fn prove_sync_op_prepared(
        &self,
        prepared: &PreparedSync,
        request: &SyncRequest,
    ) -> Result<SyncResult, SyncError> {
        debug_assert_eq!(request.operation.kind(), prepared.kind);
        let witness = match generate_witness(
            &self.config.smt,
            self.config.layer_strategy,
            &prepared.circuit,
            &request.operation,
            &request.public_inputs,
            &request.witness,
        ) {
            Ok(w) => w,
            Err(e) => return Err(SyncError::Witness(e)),
        };
        let proof = verification::prove_on(
            &self.config,
            &prepared.circuit,
            prepared.kind,
            &prepared.commitment,
            &request.public_inputs,
            &witness,
        );
        Ok(SyncResult {
            public_inputs: request.public_inputs.clone(),
            proof,
        })
    }

    /// Build a batching job against prepared state. Unlike
    /// [`Self::make_job`] (which compiles per request - the v0.1 hidden
    /// cost), this reuses the prepared circuit, so job construction is
    /// witness generation only (~0.5-1.2 ms vs ~17-30 ms with compile).
    ///
    /// (Creusot: claim-free `trusted`, v0.2 surface - see the section note.)
    #[cfg_attr(creusot, trusted)]
    pub fn make_job_prepared(
        &self,
        prepared: &PreparedSync,
        request: &SyncRequest,
    ) -> Result<ProveJob, SyncError> {
        debug_assert_eq!(request.operation.kind(), prepared.kind);
        let witness = match generate_witness(
            &self.config.smt,
            self.config.layer_strategy,
            &prepared.circuit,
            &request.operation,
            &request.public_inputs,
            &request.witness,
        ) {
            Ok(w) => w,
            Err(e) => return Err(SyncError::Witness(e)),
        };
        Ok(ProveJob {
            kind: prepared.kind,
            public_inputs: request.public_inputs.clone(),
            witness,
        })
    }

    /// v0.2 amortized batch prover: one shared prepared circuit, one proof
    /// per job (queue order preserved). This is the `prove_batch` injection
    /// surface of [`ssgkr_batching::BatchProver::prove_round`] with the
    /// per-batch compile amortized away entirely.
    ///
    /// (Creusot: claim-free `trusted`, v0.2 surface - see the section note.)
    #[cfg_attr(creusot, trusted)]
    pub fn prove_batch_prepared(
        &self,
        prepared: &PreparedSync,
        jobs: &[ProveJob],
    ) -> Vec<gkr::GkrProof> {
        jobs.iter()
            .map(|job| {
                verification::prove_on(
                    &self.config,
                    &prepared.circuit,
                    prepared.kind,
                    &prepared.commitment,
                    &job.public_inputs,
                    &job.witness,
                )
            })
            .collect()
    }

    /// v0.2 parallel batch prover: job-level parallelism over the shared
    /// prepared circuit (rayon). Determinism gate (N1, pinned by
    /// tests/batch_v02.rs): each job's transcript is seeded from its own
    /// public inputs only and results are collected in input order, so
    /// worker count and scheduling CANNOT change any proof byte - the
    /// output equals [`Self::prove_batch_prepared`] element for element.
    ///
    /// Worker count follows the ambient rayon pool (callers wanting a
    /// fixed count run this inside `ThreadPoolBuilder::install`, as the
    /// measure harness does).
    ///
    /// (Creusot: claim-free `trusted`, v0.2 surface - see the section note.)
    #[cfg(feature = "host")]
    #[cfg_attr(creusot, trusted)]
    pub fn prove_batch_parallel(
        &self,
        prepared: &PreparedSync,
        jobs: &[ProveJob],
    ) -> Vec<gkr::GkrProof> {
        use rayon::prelude::*;
        jobs.par_iter()
            .map(|job| {
                verification::prove_on(
                    &self.config,
                    &prepared.circuit,
                    prepared.kind,
                    &prepared.commitment,
                    &job.public_inputs,
                    &job.witness,
                )
            })
            .collect()
    }

    /// Verify one sync proof against prepared state: the amortizable
    /// `v_setup` (compile + derivation) lives in [`Self::prepare`], so this
    /// call pays only the per-proof marginal cost (~6-10 ms flat in depth,
    /// benches/REPORT). Kind mismatch rejects early (the S-5 circuit digest
    /// would reject it cryptographically anyway).
    ///
    /// (Creusot: claim-free `trusted`, v0.2 surface - see the section note.
    /// The Theorem C clause-by-clause meaning lives on
    /// the verification owner's shared verifier, which this entry shares
    /// with the other two verify entries.)
    #[cfg_attr(creusot, trusted)]
    pub fn verify_sync_op_prepared(
        &self,
        prepared: &PreparedSync,
        request: &SyncRequest,
        result: &SyncResult,
    ) -> bool {
        if request.operation.kind() != prepared.kind {
            return false;
        }
        verification::verify_sync_op_with(
            &self.config,
            request,
            result,
            &prepared.circuit,
            &prepared.wiring,
            &prepared.commitment,
        )
    }

    /// Verify one sync proof through the normative R3 owner.
    pub fn verify_sync_op(&self, request: &SyncRequest, result: &SyncResult) -> bool {
        verification::verify_sync_op(&self.config, request, result)
    }

    /// Verify through the normative R3 materialized-wiring audit path.
    pub fn verify_sync_op_reference(&self, request: &SyncRequest, result: &SyncResult) -> bool {
        verification::verify_sync_op_reference(&self.config, request, result)
    }

    // ------------------------------------------------------------------
    // v0.3 external proof boundary (inner-proof-v1 + wrap pipeline).
    //
    // Responsibility split (frozen with PG-3, prose twin in
    // docs/encoding/inner-proof-v1.md): the DECODER (ssgkr-wrap) checks
    // byte shape, versions and canonicality; THIS layer checks the
    // decoded identity against the local config and the LOCALLY
    // RECOMPUTED circuit commitment (nothing identity-critical is
    // trusted from the wire); the inner verifier checks the
    // cryptography; a wrap backend proves exactly [`Self::wrap_relation`]
    // and nothing wider.
    //
    // (Creusot: claim-free `trusted` where marked - same wall classes as
    // the entries above (foreign `==` via derived PartialEq, byte-string
    // constant reachability); boundary meaning is carried by the frozen
    // encoding spec + the executable pins in tests/encoding_v03.rs.)
    // ------------------------------------------------------------------

    /// The frozen inner-proof-v1 circuit identity of one prepared kind
    /// under this config (versions from the encoding layer, instance
    /// values from the config, commitment from the canonical compile).
    ///
    /// Errs only when a config value cannot fit its frozen wire width.
    #[cfg_attr(creusot, trusted)]
    pub fn circuit_identity(
        &self,
        prepared: &PreparedSync,
    ) -> Result<CircuitIdentity, EncodeError> {
        let leaf_max_fields = u16::try_from(self.config.smt.leaf_max_fields)
            .map_err(|_| EncodeError::CountOverflow)?;
        Ok(CircuitIdentity {
            op_kind_tag: PublicInputs::kind_tag(prepared.kind),
            depth: self.config.smt.depth,
            circuit_version: encoding::CIRCUIT_VERSION,
            leaf_encoding_version: encoding::LEAF_ENCODING_VERSION,
            leaf_max_fields,
            layer_strategy_id: strategy_identity(self.config.layer_strategy).0,
            full_circuit_commitment: prepared.commitment,
        })
    }

    /// Encode one proved result into canonical inner-proof-v1 bytes (the
    /// external transport form; witness bytes never included).
    #[cfg_attr(creusot, trusted)]
    pub fn encode_sync_result(
        &self,
        prepared: &PreparedSync,
        result: &SyncResult,
    ) -> Result<Vec<u8>, EncodeError> {
        let identity = self.circuit_identity(prepared)?;
        encoding::encode_inner_proof(&InnerProofEnvelope {
            identity,
            public_inputs: result.public_inputs.clone(),
            proof: result.proof.clone(),
        })
    }

    /// Decode, validate and cryptographically verify one encoded inner
    /// proof against a request (fail closed at every stage): strict
    /// decode -> identity must equal this config's identity INCLUDING the
    /// locally recomputed full circuit commitment -> the inner verifier
    /// runs on the decoded statement + proof.
    #[cfg_attr(creusot, trusted)]
    pub fn verify_encoded_sync_op(
        &self,
        prepared: &PreparedSync,
        request: &SyncRequest,
        bytes: &[u8],
    ) -> bool {
        let Ok(env) = encoding::decode_inner_proof(bytes) else {
            return false;
        };
        let Ok(expected) = self.circuit_identity(prepared) else {
            return false;
        };
        if env.identity != expected {
            return false;
        }
        let result = SyncResult {
            public_inputs: env.public_inputs,
            proof: env.proof,
        };
        self.verify_sync_op_prepared(prepared, request, &result)
    }

    /// The WRAP RELATION - the exact predicate every outer (wrap) proof
    /// attests: "these canonical inner-proof bytes decode to this
    /// config's circuit identity and the internal verifier (seal S-4)
    /// accepts them for a witness the wrapper holds". Returns the
    /// wrap-statement (the outer proof's public inputs) exactly when the
    /// relation holds.
    ///
    /// This function is backend-independent ON PURPOSE: a zkVM guest
    /// runs this same composition over the same crates; a hand-built
    /// circuit must constrain exactly this predicate. Backends may
    /// reject, but may never widen it.
    #[cfg_attr(creusot, trusted)]
    pub fn wrap_relation(
        &self,
        prepared: &PreparedSync,
        request: &SyncRequest,
        encoded_inner: &[u8],
    ) -> Option<wrap::statement::WrapStatementV1> {
        let env = encoding::decode_inner_proof(encoded_inner).ok()?;
        let expected = self.circuit_identity(prepared).ok()?;
        if env.identity != expected {
            return None;
        }
        let statement = wrap::statement::wrap_statement_v1(&env.identity, &env.public_inputs);
        let result = SyncResult {
            public_inputs: env.public_inputs,
            proof: env.proof,
        };
        if !self.verify_sync_op_prepared(prepared, request, &result) {
            return None;
        }
        Some(statement)
    }

    /// Wrap one encoded inner proof through a backend. The native
    /// relation is checked FIRST (a backend is never asked to prove a
    /// false statement), and the backend's echoed statement is
    /// cross-checked against the locally computed one (defense in
    /// depth: a backend cannot silently rebind the statement).
    #[cfg_attr(creusot, trusted)]
    pub fn wrap_sync_op<B: wrap::WrapBackend>(
        &self,
        backend: &B,
        prepared: &PreparedSync,
        request: &SyncRequest,
        encoded_inner: &[u8],
    ) -> Result<wrap::WrappedProof, wrap::WrapError> {
        let Some(statement) = self.wrap_relation(prepared, request, encoded_inner) else {
            return Err(wrap::WrapError::Rejected {
                reason: "inner proof fails the wrap relation".into(),
            });
        };
        let input = wrap::WrapInput {
            encoded_inner,
            operation: &request.operation,
            witness: &request.witness,
        };
        let wrapped = backend.wrap(&input)?;
        if wrapped.statement != statement {
            return Err(wrap::WrapError::Rejected {
                reason: "backend echoed a different wrap statement".into(),
            });
        }
        Ok(wrapped)
    }
}
