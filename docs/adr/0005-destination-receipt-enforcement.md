# ADR-0005: Destination receipt-root enforcement reference

## Status

Accepted for component reference semantics. No deployment is selected.

## Context

The selected external proof profile has public proof, aggregation, receipt,
and observed delivery evidence. A destination still needs its own policy for
source identity, authorization, nonce, replay, conflict, path, lifecycle, and
settlement handling.

## Decision

The reference policy fixes:

- source network and runtime identity;
- a domain-separated direct signing digest;
- signer-set epoch, sorted unique recovered signers, and threshold;
- strict-next authorization nonce;
- immutable receipt coordinates;
- explicit replay and conflict errors;
- native one-leaf statement hashing;
- route-independent settlement identity; and
- atomic claim/settlement replay behavior.

Rust performs direct-digest secp256k1 recovery and explicitly rejects zero
values, high-`s`, invalid recovery identifiers, failed recovery, and the zero
address. An EVM implementation must enforce equivalent checks around the
precompile; the precompile alone does not provide this policy.

The public vector uses fixed test-only signers and signatures. It does not
identify production principals or authorize a live system.

## Consequences

- Authorization replay and same-coordinate metadata conflicts reject without
  state mutation.
- A new coordinate uses the exact next nonce; skipped or reused nonces reject.
- The version-one native profile accepts one-leaf receipts only.
- Delivery claim identity and route-independent settlement identity remain
  separate replay keys.
- Negative rows compare exact errors and the complete reference-state digest.
- The accepted statement's action and root are parser-derived rather than
  caller assertions.
- A primary-record signer is not automatically receipt-root authority.
- Overflow rejects before insertion.
- A future direct-consensus or alternate quorum adapter requires a new policy
  version.

## Non-claims

This Rust reference is not deployed bytecode, live signer use, source-consensus
proof, production activation, human audit, or operational readiness. An
EVM-compatible integration check can show execution-environment compatibility
without creating a deployment or secondary-finality claim.

See
[`risc0-route-b-destination-policy-v1.md`](../encoding/risc0-route-b-destination-policy-v1.md)
and the protected vector under `tests/vectors/`.
