# Security policy

This policy describes how to report vulnerabilities in StateSync-GKR. The
verified results and their assumptions are described in
[FORMAL_VERIFICATION.md](FORMAL_VERIFICATION.md) and the
[refinement guide](docs/refinement.md).

## Supported versions

| Version | Security fixes |
| --- | --- |
| `main` and the current release, v1.1.1 | Yes |
| v1.1.0 and earlier | No |

Fixes are published in a new release. Published releases and their tags are
immutable.

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

Reports are triaged by severity. Bounty, safe-harbor and compensation terms
are not part of this public policy. Production support is arranged under a
commercial license; see [SUPPORT.md](SUPPORT.md).

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
