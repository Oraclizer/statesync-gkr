# Security policy

StateSync-GKR is unaudited research software. There is no
production-supported release.

## Reporting a vulnerability

Report suspected vulnerabilities privately by email to
[jay@oraclizer.io](mailto:jay@oraclizer.io).

GitHub private vulnerability reporting on the Security tab is a second
private channel for the public repository.

Include the affected revision, environment, reproduction steps, expected and
observed behavior, and potential impact. Arrange a protected transfer before
sending sensitive supporting material.

Do not open a public issue for an undisclosed vulnerability. Do not include
credentials, private keys, personal information, or private infrastructure
locations. Do not test systems or accounts you do not own or lack explicit
permission to assess.

Reports are evaluated as capacity permits. This policy does not promise a
response time, remediation deadline, bounty, safe-harbor agreement,
compensation, or production support.

## Scope

Security-sensitive surfaces include:

- sparse-Merkle semantics and circuit compilation;
- sumcheck, GKR verification, transcript binding, and circuit commitment;
- proof encoding and the fixed zkVM program identity;
- canonical vector and receipt encodings;
- prepared material and deterministic artifact identity;
- resource exhaustion, side channels, and dependency integrity; and
- external proof and destination integrations where this repository directly
  owns code.

Formal proofs and passing tests are scoped evidence, not a guarantee that these
surfaces are free from vulnerabilities.
