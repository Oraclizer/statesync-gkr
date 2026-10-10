# Refinement evidence and reusable acceptance checks

StateSync-GKR provides a conditional, mechanized forward acceptance theorem,
recorded proofs for selected Rust contracts, and verifier control flow that is
available to Creusot translation around explicit foreign-field seams. Together with the
compiler and GKR models, these artifacts let developers trace which checks
turn an original request into an acceptance verdict and reuse that review
basis when integrating a frontend or maintaining the engine.

## What the refinement work establishes

The forward theorem connects an accepted trace to the GKR model's
reduction-chain event under model well-formedness and an explicit Rust/model
value relation. The former local-bridge premise is no longer assumed: it is
derived from the concrete sumcheck-round checks and the finish-evaluation part
of that value relation. The proof therefore exposes the round and termination
conditions that supply that step of the argument.

Recorded Creusot/Why3 proofs establish the contract of the exact public-input
equality helper and the contract of the acceptance classifier: the verdict is
the conjunction of seven observations, namely public-input binding, request
guards, the zero-output construction, sumcheck consistency and carry
consistency (both of which record the protocol verifier's result) and the two
final input-MLE observations. Populating those observations from the actual
checks happens in the facade body, which exists in test and Creusot
configurations and whose recorded obligation remains open; ordinary builds
retain the short-circuit rejection form.

The sumcheck and per-layer verifier bodies no longer opt out of translation
as whole functions. The opt-outs are narrowed to explicit foreign-field
equality seams that are claim-free: they compare field values without stating
any proof postcondition. Round counts, degrees, rejection branches, transcript
observation order, carry construction and final claims remain available to
translation and review. Production wiring-oracle evaluations, transcript
operations and the circuit and public-input observation helpers remain trusted
translation boundaries. Translation coverage is distinct from proof
completion: the recorded sumcheck and layer-verifier proofs cover the
translated bodies' verification conditions, their stated postconditions
remain design contracts that the tool does not check, and the layer-verifier
evidence includes an open obligation.

## How developers can reuse the evidence

For an SMT integration, inspect the request's public inputs and the checks
that consume them before relying on a verification result. The source,
contract and theorem map below gives concrete review targets for request
binding, protocol checks and final input evaluations. Reproduction reports
can name the exact contract or check whose behavior differs.

For another arithmetic frontend, reuse the sumcheck/GKR engine and this
review map, then establish that frontend's statement binding, witness
interpretation and consumption of both residual input claims. The model
event omits request/public-input guards, so it cannot replace those checks
or authorize executable acceptance by itself. Existing frontend evidence
does not automatically verify a new adapter.

This is a reusable basis for integration review and maintenance. It is not
a measured development-time saving, a count of prevented vulnerabilities,
or an independent security-audit endorsement.

## Source and evidence map

| Review target | Canonical source | Recorded evidence or result |
|---|---|---|
| SMT meanings and compiler model | [Compiler correctness](../formal/isabelle/SMT_Circuit_Compiler_Correctness/Compiler_Correctness.thy) | Model soundness and completeness, with their witness and hash assumptions |
| Forward acceptance and concrete local-bridge derivation | [Verifier acceptance refinement](../formal/isabelle/GKR_Protocol/Verifier_Acceptance_Refinement.thy) | `production_verifier_acceptance_refines_gkr_chain_bad`, `concrete_checks_supply_local_bridge`; explicit value-relation premise |
| Request's exact public-input equality | [Verification owner](../crates/verification/src/lib.rs) | [public_inputs_match proof](../verif/ssgkr_verification_rlib/public_inputs_match/proof.json) |
| Actual acceptance observations | [Verification owner](../crates/verification/src/lib.rs) | [AcceptanceTrace classifier proof](../verif/ssgkr_verification_rlib/impl_AcceptanceTrace/accepts/proof.json), test/translation configurations |
| Sumcheck control flow | [Sumcheck verifier](../crates/sumcheck/src/lib.rs) | [Recorded verify proof](../verif/ssgkr_sumcheck_rlib/verify/proof.json); foreign-field equality seam remains explicit |
| Layer sequencing and carry construction | [Layer verifier](../crates/protocol/src/reduce.rs) | [Recorded layer-verifier obligations](../verif/ssgkr_protocol_rlib/reduce/verify/proof.json), including an open `null` leaf |
| Selected compiler-domain and leaf-width contracts | [Compiler](../crates/compiler/src/compile.rs), [hash layout](../crates/primitives/src/hash.rs) | [Compile proof](../verif/ssgkr_compiler_rlib/compile/compile/proof.json) (relies on the `compile_with_hints` contract, whose record has open obligations), [leaf_pre_width proof](../verif/ssgkr_primitives_rlib/hash/leaf_pre_width/proof.json) |
| Selected open obligations | [Verification owner](../crates/verification/src/lib.rs), [protocol](../crates/protocol/src/reduce.rs), [compiler](../crates/compiler/src/compile.rs) | [Facade body](../verif/ssgkr_verification_rlib/verify_sync_op_with/proof.json), [derived body](../verif/ssgkr_verification_rlib/verify_sync_op_with_derived_body/proof.json), [leaf fold](../verif/ssgkr_primitives_rlib/hash/leaf_fold/proof.json), [compiler with hints](../verif/ssgkr_compiler_rlib/compile/compile_with_hints/proof.json), [MLE evaluation](../verif/ssgkr_protocol_rlib/mle/mle_eval_base/proof.json), [beta evaluation](../verif/ssgkr_protocol_rlib/reduce/beta_eval/proof.json), [public-input equality refinement](../verif/ssgkr_compiler_rlib/witness/impl_PartialEq_for_PublicInputs/eq__refines/proof.json) |
| Executable acceptance and rejection controls | [Refinement tests](../tests/verifier_acceptance_refinement.rs), [in-crate tests](../crates/verification/src/lib.rs) | Honest acceptance and public-input, sumcheck, carry and final-input rejection controls; separate from theorem and contract evidence |

The source map names results and selected open records rather than adding
solver leaves into a whole-program completion percentage. Other proof records
in `verif/` also contain open obligations. A `null` obligation receives no
proof credit.

## Remaining correspondence and security boundaries

The forward theorem's `rust_hol_value_trace_relation` remains a load-bearing
premise. It relates the Rust/Creusot trace, final running claim, wiring
right-hand side and off-cube polynomial representation to the model. The
equivalence of the test/translation trace form and ordinary execution is part
of that remaining correspondence. The former local bridge is derived; this
value relation is not discharged against the exact compiled program.

The result does not establish whole-program compiled-Rust refinement,
the executable transcript's independent uniform challenge sequence, a
multi-round Fiat-Shamir security reduction, or a comprehensive implementation
security audit. Field/hash dependencies and trusted interfaces retain their
documented assumptions. The separate
[challenge-generation review](challenge-generation-review.md) keeps its own
stated scope; these refinement results do not extend it.

[Formal verification](../FORMAL_VERIFICATION.md) owns the exact theorem
families, R1-R4 scopes and trusted boundaries.
[Usage](usage.md) describes frontend inputs and residual-claim responsibilities.
[Security](../SECURITY.md) describes reporting and operational review.

## Reading and replaying the recorded proofs

The Creusot/Why3 records are retained contract-proof evidence and tool inputs
for replay. They are not rebuilt by a hosted workflow on every push. Read
the named source, assumptions, successful solver leaves and open obligations
together. [Replay metadata](../verif/README.md) identifies the pinned
configuration and local tool requirements.

A source consistency check, solver record, executable test and historical
external zkVM proof answer different questions. The source distribution's
[identity record](../release/v1.1/LICENSING_DISTRIBUTION.json) distinguishes the
current source from the recorded historical program; the attached historical
proof does not establish a compiled identity for this tree.
