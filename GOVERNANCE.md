# Governance

## Who decides

StateSync-GKR has one maintainer, Jinwook Kim
([@jay-oraclizer](https://github.com/jay-oraclizer)), who holds final say on
scope, review, merge, release, security coordination, and compatibility.

This is stated plainly so you can judge it for yourself. There is no
committee, no vote, and no second approver, which makes decisions fast and
consistent but leaves the project with a single point of failure. Weigh that
before you depend on it.

What this does commit to: every decision is made against the published
criteria below, and a decision that turns down a contribution will say which
criterion it failed. If you believe a criterion was misapplied, say so on the
issue; the reasoning is revisited on the record rather than by private
decision. Being turned down is not a judgement of the work. The most common
reason is scope, not quality.

## Decision principles

Changes are evaluated for:

- semantic correctness and explicit non-claims;
- preservation of trust and ownership boundaries;
- reproducibility and deterministic encodings;
- security impact and fail-closed behavior;
- compatibility with the frozen proof-bound source;
- adequate positive, negative, and mutation evidence; and
- maintainable public documentation.

Large changes should begin with an issue describing the problem, alternatives,
claim impact, migration, and verification plan.

## Merge policy

Changes enter the maintained branch through pull requests and required
checks. Force pushes and reuse of immutable release tags are not part of the
normal workflow. A clean status check is evidence for the exact reviewed
revision only.

The frozen protected source of the current release line cannot be changed as
incidental hygiene. A protected
byte change is a different candidate identity and requires separately
authorized identity and proof work.

## Release policy

A release requires:

- a clean public-history subject;
- exact source, proof, input, and attachment manifests;
- passing source, Rust, formal, and integration checks appropriate to scope;
- dependency, license, and advisory scan results and a provenance statement,
  with the underlying process records retained privately;
- an independent public-surface audit with no unresolved critical, high,
  medium, or low finding; and
- an explicit publication decision.

Repository visibility alone does not create a release. A tag is immutable and
is never moved or reused.

## Security decisions

Vulnerability reports follow [SECURITY.md](SECURITY.md). The maintainer may
temporarily restrict details while coordinating a fix. This repository does
not promise a bounty, safe harbor, response time, support term, or remediation
deadline.

## Amendments

Governance changes use the same reviewed process as code changes. A governance
document cannot expand a technical proof, license, security guarantee, or
deployment claim beyond its underlying evidence.
