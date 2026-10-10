# ADR-0003: Native RISC Zero route manifest identity

## Status

Accepted for the selected component evidence profile.

## Scope

Native RISC Zero v3 proof statement, zkVerify Volta coordinates, destination
trust ceiling, and the canonical content address. Not in scope: live receiver
enforcement, production readiness, public deployment, or any change to the
frozen GKR core.

## Decision

The native RISC Zero path uses `Risc0RouteBManifestV1` and the domain
`ssgkr/risc0-route-b-manifest/v1`. It does not reuse or revise the Groth16
`RouteManifestV1` defined by ADR-0002. The two profiles expose different proof
statements and VK meanings and therefore require disjoint type and hash
domains.

The native manifest uses a strict versioned JSON input, a typed canonical
binary encoding, and `SHA-256(domain || canonical_bytes)`. The Rust codec and a
standard-library Python codec share only the input JSON and must agree on the
complete bytes and transcript.

The static profile pins:

- zkVerify Volta genesis and live runtime source/spec coordinates;
- RISC Zero release, source, toolchain, guest artifact, verification context,
  verifier-version hash, image ID, and image-ID/VK semantics;
- the exact raw192 application-statement and four-field Keccak statement
  contracts;
- aggregation domain `2`, Base Sepolia, and the observed gateway proxy,
  implementation, and both runtime code hashes;
- the observed publisher plus capability-only `OPERATOR`, `UPGRADER`, and
  `DEFAULT_ADMIN` trust model without inventing admin or upgrader principals;
- the operator-authenticated transport and its lack of destination-side Volta
  GRANDPA verification;
- observed same-coordinate overwrite capability, absent conflict rejection,
  and required-but-not-enforced receipt-tuple canonicality; and
- the existing route-independent settlement-key profile.

Aggregation IDs, receipt roots, source/destination transaction coordinates,
proof bytes, block coordinates, and individual raw192 values are dynamic
delivery evidence and are excluded from the route content address.

## Consequences

Changing any static leaf changes the route ID or fails parsing. JSON key order
and whitespace do not. Missing, duplicate, unknown, noncanonical hex, bad
width, wrong numeric type, and out-of-range values fail closed.

The manifest describes the trust ceiling but does not make it smaller. A
destination receiver still has to authenticate the approved source policy,
pin current code and roles, reject stale or conflicting roots, enforce the
count/path/index relation, reject unauthorized publishers and changed
implementations, and prevent replay before any stronger finality claim.

The profile is selected for component evidence. Production activation and
publication remain separate decisions.

## References

- [Canonical encoding](../encoding/risc0-route-b-manifest-v1.md)
- [Input schema](../encoding/risc0-route-b-manifest-v1.schema.json)
- [External proof role contract](0002-external-proof-role-contract.md)
