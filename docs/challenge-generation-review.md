# Challenge generation and the extension-field soundness bound

An independent review of the challenge-generation assumptions behind the
extension-field transfer of Theorem B. The bounded question was under which
idealization or security assumptions the executable verifier's
transcript-derived `ChallengeField` samples correspond to the uniform
challenges of the machine-checked model, and what the `p^4` denominator
therefore supports about the pinned implementation.

## Reviewed revision and sources

Repository revision `73bdd1e270fa17e262fd4454c98a18dc23eb8dad`. Relative
to the requested baseline `42a6e7f8ab855bb71a07cbb38e743c71c021bffa`, the
`crates/`, `src/`, and `tests/` trees, `Cargo.lock`, `rust-toolchain.toml`,
and every `.thy` file are byte-identical; the intervening commits change the
paper, the prose documents, and the release tooling.

The published archives of `p3-challenger`, `p3-field`, `p3-koala-bear`,
`p3-monty-31`, `p3-poseidon2`, and `p3-symmetric`, all at `0.4.3`, were
fetched and their SHA-256 values compared with the `checksum` entries in
`Cargo.lock`; all six match.

| Surface | Files read |
|---|---|
| Field and transcript adapter | `crates/primitives/src/field.rs`, `crates/primitives/src/transcript.rs`, `crates/primitives/src/hash.rs` |
| Protocol callers and codecs | `crates/verification/src/lib.rs`, `crates/protocol/src/reduce.rs`, `crates/sumcheck/src/lib.rs`, `crates/sumcheck/src/poly.rs`, `crates/commitment/src/lib.rs`, `crates/wrap/src/encoding.rs`, `crates/compiler/src/witness.rs` |
| Model | `KoalaBear_Ext4_Field.thy`, `KoalaBear_Ext4_GKR.thy`, `GKR_Assembly.thy`, `Composition.thy`, `Verifier_Acceptance_Refinement.thy`, `Layer_Representative.thy` |
| Pinned dependency sources | `p3-challenger` `src/duplex_challenger.rs`; `p3-field` `src/extension/binomial_extension.rs` and `src/integers.rs`; `p3-koala-bear` `src/koala_bear.rs`; `p3-monty-31` `src/extension.rs`, `src/monty_31.rs`, `src/utils.rs`, and the quartic multiplication routines |

Not done: no Rust build or test run, no Isabelle replay, no independent check
of the pinned AFP archive, no new security reduction, and no attempt at a
forged proof. Existing successful hosted runs were read as provenance, not
reproduced. The integer examples below were computed with plain modular
arithmetic, not with the Rust field implementation.

## Conclusion

The claim assessed is the extension-field transfer row of
`FORMAL_VERIFICATION.md` together with the two challenge-related entries of
its trusted-boundary list: "Fiat-Shamir modeling assumptions" and "the
assumption that executable challenge derivation yields four independent
uniform base-field coefficients".

1. **Supported as written, as a model result.** `gkr_assembly_soundness_ext4`
   bounds the chain bad event by `B / p^4` over the uniform product
   distribution on the whole challenge list, with
   `B = s_out + sum_i (2 s_i dbnd(s_i) + 1)`; `ext4_denominator_exact`
   fixes the denominator; `uniform_coeff_tuple_pushforward` shows that one
   jointly uniform four-coefficient tuple maps to one uniform extension
   element. The coefficient map matches the pinned representation.
2. **Supported at the source level.** The executable assembles each challenge
   from four distinct base-field outputs of the Poseidon2 duplex, in the
   basis the model uses. There is no embedding of a single base-field value
   into the extension, no byte-to-field modular reduction, and no rejection
   sampling on this path.
3. **Not established for the executable.** Nothing in the repository
   establishes the distribution of the transcript-derived challenges. The
   assumption as previously worded named one tuple's coefficients. The model
   needs three distinct things, none proved here: joint uniformity of one
   tuple; uniformity and independence across the whole multi-round sequence,
   conditional on the interaction so far; and a Fiat-Shamir argument for a
   deterministic multi-round transcript against an adversary who can query
   the permutation before choosing its messages. A fourth condition, binding
   of the statement and the witness to the transcript, sits between the
   model's fixed inputs and the executable's request handling.

The row is retained. The trusted-boundary entries are rewritten so that the
single-tuple statement, the sequence-level idealization, the Fiat-Shamir
reduction, and the input-binding condition are separate items. No
implementation defect that yields a false acceptance was found, and none is
claimed. The `p^4` denominator is not, by itself, an executable soundness
error or a bit-security level: the `~2^124` in `field.rs` is the size of the
challenge field, the theorem's bound is `B / p^4` with the numerator above,
and no executable figure follows from either.

## Source-to-model analysis

### Field and coefficient representation

`ChallengeField` is `BinomialExtensionField<KoalaBear, 4>` with
`p = 2^31 - 2^24 + 1 = 2130706433`. `p3-koala-bear` sets `W = 3` for degree
four, so the field is `F_p[X] / (X^4 - 3)`, and a value's array `[F; 4]`
holds the coefficients of `1, X, X^2, X^3` in that order. Both the generic
and the vectorized pinned multiplication routines compute the constant term
as `c0 d0 + 3 (c1 d3 + c2 d2 + c3 d1)`, which fixes that convention.

The model builds the same field as a quadratic tower: `kb_quad` with
`kb_y * kb_y = 3`, then `koala_bear_ext4` with `kb_alpha * kb_alpha = KBE kb_y 0`,
so `kb_alpha ^ 4 = kb4_embed 3`. The map `coeff4 (c0, c1, c2, c3) = KBE (KBQ c0 c2) (KBQ c1 c3)`
therefore denotes `(c0 + c2 X^2) + X (c1 + c3 X^2) = c0 + c1 X + c2 X^2 + c3 X^3`:
the pinned basis with no permutation of coefficients. `coeff4_bij` and
`uniform_coeff_tuple_pushforward` are correct for it. Because the pushforward
is through a bijection, it holds for every fixed ordering of the four
coordinates, so the order in which the duplex hands out coefficients has no
bearing on the distributional claim.

### The sampling path

`Transcript::sample_challenge` calls `CanSample<ChallengeField>::sample` on
`DuplexChallenger<KoalaBear, Poseidon2KoalaBear<16>, 16, 8>`. In
`p3-challenger` that method is `from_basis_coefficients_fn`, evaluated for
coefficient indices 0 to 3 in order; each evaluation first runs `duplexing`
if the input buffer is non-empty or the output buffer is empty, then pops one
element from the output buffer. `duplexing` overwrites state positions
`0 .. len(input_buffer)` with the buffered inputs, applies the permutation,
and refills the output buffer with state positions `0 .. 8`.

Consequences, all read from the pinned source:

- After a refill the first sample has coefficients
  `(state[7], state[6], state[5], state[4])`; a second sample with no
  observation in between takes `(state[3], state[2], state[1], state[0])`
  from the same permutation output. Every `observe` clears the output
  buffer, so the first sample after any observation is taken from a
  permutation call made after that observation.
- Absorption is overwrite mode over the buffered prefix only; rate positions
  not overwritten keep the previous permutation output. No length or padding
  is added on this path. The upstream padded, length-tagged
  `absorb_rate_padded_with_tag` exists but is not called here.
- The transcript, the circuit-commitment sponge, and the leaf sponge and node
  compression of `DefaultHasher` all use one permutation instance,
  `default_koalabear_poseidon2_16`.

Under an ideal permutation, the response to a fresh query is uniform on
`F_p^16` apart from the exclusion of outputs already returned, and any four
of its coordinates are then jointly uniform on `F_p^4` up to that
exclusion. That is the natural single-tuple idealization behind the
pushforward's hypothesis. It is an idealization about one call, not a
property proved of Poseidon2 or of the executable.

### Transcript schedule

The composed verifier (`verify_sync_op_with`) replays the following, in this
order (`verification/src/lib.rs`, `protocol/src/reduce.rs`,
`sumcheck/src/lib.rs`):

1. `Transcript::new(b"statesync-gkr/v0.1")`: the tag bytes, each as one
   base-field element.
2. Circuit shape (kind tag, depth, input width, layer count, then per layer
   the width, gate count, and constant count) and the eight-element circuit
   commitment.
3. Public inputs: `old_root`, `new_root`, `op_kind_tag`, the low and high
   32-bit halves of `asset_id`, `value_digest`.
4. The claimed output table, which the composed verifier fixes to all zeros.
5. `s_out` samples for the output evaluation point `z_0`, with no observation
   between them.
6. Per layer: for each of the `2 s_i` sumcheck rounds, the degree and sum
   checks, the round polynomial's coefficients absorbed as extension elements
   in ascending order, then one sample; then `eval_x` and `eval_y` absorbed;
   then the wiring end-check; then, for every layer but the last, one carry
   sample.
7. After the last layer, both residual input-MLE equalities are checked
   against the input vector the verifier derives itself from the request.

The running layer claim is computed, not absorbed; the source comment in
`transcript.rs` that lists an observed "layer claim" is shorthand for this
schedule and is not what the code does. The witness-derived input vector and
the Merkle siblings are never absorbed. The model reserves one carry slot per
layer, including an unused final one; appending an unused uniform value to an
ideal execution accounts for it without changing the event.

### What the theorems say

`gkr_assembly_soundness` takes its probability under
`pmf_of_set (tuples UNIV N)`, the uniform distribution on the entire flat
challenge list, with the prover strategy `A` a function of the challenges
drawn so far. The circuit, its true layer values, and the false output claim
are fixed parameters. `theorem_C_composition` fixes the witness `w`, the
roots, the value digest, and the operation outside the probability space and
derives the layer values from the honest encoding of that witness.
`gkr_assembly_soundness_deg4_ext4` specializes `dbnd` to 4 at the statement
level; the registered `Layer_Representative` instance supplies a total-degree
bound of `2 s`, so the per-variable degree-four numerator remains a
specialization without a registered instance. The acceptance refinement
carries `rust_hol_value_trace_relation` as an undischarged premise. None of
these premises is affected by the challenge question, and none is discharged
by it.

## Which properties are idealized rather than established

**One tuple.** The pushforward's hypothesis is a jointly uniform tuple in
`F_p^4`. Uniform marginals do not suffice: the tuple `(U, U, U, U)` has
uniform coordinates and only `p` possible values. Nothing in the repository
proves or tests the joint law of the four popped coordinates; under the
single-call ideal-permutation idealization above it holds.

**The whole sequence.** The theorems consume the uniform product law on the
complete challenge list. A sufficient condition on an interactive execution
is: at every sampling point, once the transcript content so far (and with it
the prover's messages) is fixed, the next four-coefficient tuple is uniform
on `F_p^4` and independent of everything earlier. With a prover whose
messages depend only on the past, this yields the product law the theorems
use. Per-challenge uniformity is not enough: if two successive challenges
were the same uniform value `R`, a polynomial `Z - R` chosen after the first
would vanish at the second with probability one. Deterministic proof digests
and statistical tests on outputs cannot establish this conditional property
against an adaptive prover. It is an idealization of the duplex, not a
property established for the executable.

**Fiat-Shamir.** The executable is deterministic: for fixed public data and
proof bytes the challenges are fixed. A prover may evaluate the permutation
on candidate messages and continuations before choosing what to submit, so
the submitted transcript is not an online execution that received fresh
challenges after irrevocable messages. Transferring the interactive bound to
the non-interactive verifier therefore needs a Fiat-Shamir reduction for this
multi-round protocol, with a loss that depends on the number of permutation
queries and on the round structure, and with a model of this exact duplex
convention: overwrite absorption of a buffered prefix, buffered output reuse,
no length tags, and one permutation shared with the hash and the commitment.
Round-by-round soundness and state-restoration soundness of the interactive
protocol are sufficient conditions for such a reduction in an idealized-hash
model; neither is proved here, and neither is required by every possible
reduction. No reduction, loss term, or instantiation argument is part of this
repository, and this review adds none.

**Statement and witness binding.** Three source facts bear on what the
transcript binds before challenges are drawn.

- The transcript absorbs the public inputs and the circuit commitment but
  not the witness. `theorem_C_composition` bounds the event for each fixed
  witness. An adversary who fixes its proof messages, and with them every
  challenge and the final `InputClaim`, can then vary the leaf and siblings
  without changing any challenge, and the verifier recomputes the input
  vector from whatever witness it receives. Each such witness is a separate
  attempt at the two final input-MLE equalities, so a transfer must either
  charge the adversary for every attempt or bind the witness-derived input
  before the challenges. The input vector is not freely selectable: every
  prover-controlled entry (the leaf pre-image and the siblings) also feeds
  the Poseidon2 accumulator chain that the verifier recomputes, so the two
  equalities are not a linear system in free variables. No false acceptance
  is constructed or claimed; the point is that the fixed-input theorem does
  not by itself cover an input chosen after the challenges.
- `observe_public_inputs` maps each 32-bit half of `asset_id` through
  `from_u32`, which reduces modulo `p`. Keys `k` and `k + p` with the same
  high half absorb the same two field elements. Both pass the key-range guard
  only when `depth >= 31`; for `depth <= 30`, including the default depth 24,
  every admitted key is below `p` and the encoding is injective. Where the
  alias exists, two distinct statements share one challenge sequence. The
  key also enters the input vector as key bits and through the left/right
  order of the accumulator chain, so the final MLE checks compare a proof
  against the input vector of the key actually submitted, which differs
  between a key and its alias. This is an encoding fact to record in any
  binding argument, not a demonstrated forgery.
- `RoundPoly::degree` is the coefficient count minus one, saturating at
  zero, so the in-memory verifier accepts coefficient vectors of length 0
  through 5 for the degree bound 4, and an empty vector absorbs nothing. The
  inner-proof codec accepts exactly five coefficients on both encode and
  decode, and the honest prover emits five. Because the duplex adds no
  length tags, an argument that treats each message as one fixed-width
  absorption applies to the codec path and to the fixed schedule above, not
  to the object API in general.

## Claim wording

`FORMAL_VERIFICATION.md` is changed in the trusted-boundary list only. The
entry that named "four independent uniform base-field coefficients" now
states the sequence-level idealization and says that it is not established
for the executable; the entry "Fiat-Shamir modeling assumptions" now says
what an implementation-facing reading would additionally need; and a new
entry records the input-binding condition. A short paragraph states that the
exact `p^4` denominator belongs to the model bound, whose numerator and other
premises still apply, and is not an executable error probability or a
security level. The extension-field row of the theorem table already
excludes the executable challenge derivation and is retained.

The paper's limitations section already states the model-only qualification
and names the challenge distribution as the residual assumption; that
wording is consistent with this review. Its sentence that security in an
idealized-hash model "requires strictly more than the plain soundness
mechanized here (round-by-round or state-restoration soundness of the
interactive protocol)" names sufficient routes rather than a necessary
condition, and the maintainers may wish to phrase it that way when carrying
this conclusion into the paper. No paper source or PDF is changed here.

## Suggested regression controls

None of these is implemented here, and none establishes the distributional
or Fiat-Shamir properties above; they pin the reviewed source facts against
drift.

- Observe a fixed prefix, draw one `ChallengeField`, and assert that its
  basis coefficients equal `sponge_state[7]`, `[6]`, `[5]`, `[4]` of the
  challenger after the call, and that a second draw equals positions 3 down
  to 0.
- Assert that an observation between two draws forces a new permutation
  call, and that two draws without an observation share one call.
- Feed a four-coefficient round polynomial to the object-API verifier and
  to the codec, recording acceptance on one side and the arity rejection on
  the other, so the gap stays documented rather than accidental.
- At depth 31, absorb the public inputs for keys `0` and `2130706433` and
  record the identical field pair, alongside the default-depth rejection of
  the second key.
- Compare prover and verifier absorb-and-squeeze traces on a fixed fixture,
  so any change to the frozen schedule is visible as a trace difference.
