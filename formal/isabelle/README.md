# StateSync-GKR Isabelle verification

This directory is the canonical home of StateSync-GKR Isabelle sources.
Repository-level ownership, refinement status, tool evidence, and claim
boundaries are recorded in [`../../FORMAL_VERIFICATION.md`](../../FORMAL_VERIFICATION.md).

## Mechanized sessions

| Session | Responsibility | Build status recorded by the pinned verification campaign |
|---|---|---|
| `GKR_Protocol` | Layered-circuit semantics, multilinear extensions, wiring MLEs, sumcheck instantiation, GKR assembly soundness, batching, and the conditional verifier-acceptance refinement | Mechanized; session sources are `sorry`/`oops`-free |
| `SMT_Circuit_Compiler_Correctness` | SMT semantics, leaf encoding/fold, compiler model and correctness, composition, KoalaBear instance, and nonvacuity instances | Mechanized; session sources are `sorry`/`oops`-free |
| `KoalaBear_Ext4_Nonsquare` | Quadratic-reciprocity nonsquare certificates for KoalaBear and the explicit square root of minus one | Mechanized; session sources are `sorry`/`oops`-free |
| `KoalaBear_Ext4_Field` | Exact quadratic tower for `X^4 = 3`, finite-field instances, cardinality `p^4`, and the base-field embedding | Mechanized; session sources are `sorry`/`oops`-free |
| `KoalaBear_Ext4_Lift` | Polynomial, multilinear-extension, layer, circuit, well-formedness, and false-output lifting along the embedding | Mechanized; session sources are `sorry`/`oops`-free |
| `KoalaBear_Ext4_GKR` | GKR soundness instance over the exact extension field and the conditional pushforward from four uniform base coefficients | Mechanized; session sources are `sorry`/`oops`-free |

`ROOTS` registers all six sessions. `SMT_Circuit_Compiler_Correctness`
depends on `GKR_Protocol`, and the four extension-field sessions form a chain
on top of it in the order listed.

## Canonical-source boundary

Only the sessions registered by `ROOTS` are authoritative formal sources
in the current product tree. Pre-mechanization drafts containing `sorry` are
retained as internal design history outside this tree and are not proof
evidence.

## Building

With Isabelle2025-2 and the AFP dependency tree containing
`Sumcheck_Protocol` available:

```bash
isabelle build \
  -d /path/to/afp/thys \
  -d formal/isabelle \
  SMT_Circuit_Compiler_Correctness
```

The parent session `GKR_Protocol` is resolved through
`formal/isabelle/ROOTS`. Building `KoalaBear_Ext4_GKR` instead builds the
whole catalog, because the extension-field chain ends there.

## Change discipline

A change to a session theory, mapped Rust symbol, Creusot contract, theorem
disposition, or trusted boundary must update the repository-level
`FORMAL_VERIFICATION.md` in the same change. Generated `verif/**/proof.json`
files are Creusot/why3find replay metadata; they are not Isabelle sources and
remain at their tool-defined repository path.
