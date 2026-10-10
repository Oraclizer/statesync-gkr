# ADR-0004: Selected external proof profile

## Status

Accepted for the v1.0 component evidence boundary.

## Context

The selected profile has a fixed RISC Zero v3.0.4 program identity, an exact
saved proof, local verification against the image ID and public statement, a
public verifier receipt, observed delivery, strict route and destination-policy
vectors, and a host-only receipt-gated candidate transition.

The program binary-to-image-ID link is owned by the recorded controlled build.
The saved proof verifier independently checks the proof bytes, image ID, and
public journal.

## Decision

Route B is the selected evidence profile for this component. Selection fixes
the proof identity and its interpretation. It does not grant standing authority
to regenerate or submit proofs, sign or fund an account, deploy a contract,
move assets, publish a release, or activate a production route.

The current runtime profile preserves the proof contract while changing the
content-addressed route manifest to:

```text
0x27b40b99a41976f061e94124b84cc8c43ee4e5ed6bad2e94267057e1d375f2ef
```

The proof, program binary, image ID, raw statement, and statement leaf remain
unchanged. The earlier manifest identity remains a protected historical vector
and is not overwritten.

## Evidence boundary

The component may publish the fixed identity, proof hash, public inputs,
receipt observation, route manifest, and local reference-transition evidence.

It does not claim:

- confidentiality for arbitrary dynamic user secrets;
- human security or custody audit;
- production signer or administrator custody;
- live contract activation;
- source-consensus verification inside the destination;
- native rollup proving or parent settlement; or
- secondary finality.

Any future deployment requires fresh principals and addresses, exact code and
role binding, numeric operating policy, recovery objectives, monitoring, an
operational drill, and independent review.

## Consequences

A different program identity is a different candidate and cannot reuse this
proof. A static route-leaf change rotates the route identity. Dynamic receipt
coordinates remain delivery evidence and do not change the static route
content address.
