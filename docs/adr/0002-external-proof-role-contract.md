# ADR-0002: External proof role contract

## Status

Accepted for the StateSync-GKR v1.0 component boundary.

## Context

The core prover establishes a primary-finality record. External proof systems,
receipt networks, delivery agents, and destination consumers are different
trust domains. Treating them as one verifier would hide which system owns each
claim and which authority can mutate external state.

## Decision

StateSync-GKR separates four roles:

1. the core compiler and GKR prover produce and verify the primary record;
2. a selected zkVM profile binds that record to a fixed program identity;
3. an external verifier and receipt path attest to the submitted statement;
4. a destination consumer may accept the authenticated receipt under its own
   immutable policy and replay/conflict rules.

The component repository owns source, proof identity, public vectors, the
receipt-gated reference transition, and the EVM-compatible integration seam.
It does not own a production destination deployment, native rollup execution
proof, parent-chain settlement, or secondary-finality claim.

Route identity and settlement identity are separate. A route describes the
proof and receipt profile. A settlement key binds the intended state
transition and destination and is not made route-dependent merely by changing
the proof carrier.

## Fail-closed behavior

- Wrong program identity, statement, receipt root, path, domain, destination,
  authorization, nonce, or predecessor is rejected.
- A duplicate or conflicting claim does not mutate the reference state.
- An unavailable or unsupported external dependency does not become an
  implicit success.
- The local example creates a candidate only; it does not submit a transaction
  and leaves secondary finality false.

## Consequences

External receipt evidence can be published without claiming that the
destination is deployed or production-ready. A future deployment must bind
exact addresses, code hashes, roles, custody, recovery, monitoring, and
finality policy independently of this component release.
