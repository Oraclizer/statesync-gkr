# StateSync-GKR v1.1 release evidence

The current v1.1.1 distribution aligns licensing metadata with BUSL-1.1.
The historical v1.1 program/proof records below retain their original scope.
The current root Cargo license field differs, and an exact compiled identity
comparison for this metadata revision has not completed. See
[LICENSING_DISTRIBUTION.json](LICENSING_DISTRIBUTION.json).

This index connects the exact component release to its verification material.
The repository remains unaudited research software and this index does not
claim production readiness, cryptographic security, or external endorsement.

- [Release verifier](verify.py)
- [Attachment inventory](ATTACHMENTS.json)
- [Checksums](SHA256SUMS)
- [Software bill of materials](SBOM.spdx.json)
- [Local provenance statement](PROVENANCE.intoto.jsonl)
- [Protected-source manifest](PROTECTED_SOURCE_MANIFEST.json)
- [Frozen-source allowlist](FROZEN_SOURCE_ALLOWLIST.json)
- [Proof manifest](PROOF_MANIFEST.json)
- [Public inputs](PUBLIC_INPUTS.json)
- [Dependency update policy](DEPENDENCY_UPDATE_POLICY.json)
- [Reproduction report template](REPRODUCTION_REPORT_TEMPLATE.json)
- [Release notes](RELEASE_NOTES.md)
- [Source reproduction recipe](SOURCE_RECIPE.md)
- [Reproduce v1.1](../../REPRODUCING.md)

The historical v1.1.0 version was published on 2026-10-04;
attachment filenames retain the documented `v1.1` prefix. The
historical release retained with the separately preserved source history
is the publication record. The complete tracked source at that tag is archived
at [DOI 10.5281/zenodo.23136385](https://doi.org/10.5281/zenodo.23136385).
The Release assets remain pinned to the tag. Manifests on the maintained branch
describe the current branch source tree; use the current BSL release package for current source reproduction, and keep historical proof observations separately scoped.
Unpublished manuscript drafts are excluded from the current source package;
this release does not submit or publish a paper.

## Relation to the previous baseline

`release/v1.0` is the baseline of the previous identity cycle. It is kept byte
frozen and is not regenerated: it records what the earlier release claimed, at
the commit named in [RELEASE_NOTES.md](RELEASE_NOTES.md). The live gate is this
directory. The verifier here additionally compares the whole superseded
directory against one recorded digest, so the earlier record cannot be edited
without failing a check.

Three point-in-time receipts belong to the previous cycle and are published
with it, in
[`../v1.0/AWS_CUSTODY_RECEIPT.json`](../v1.0/AWS_CUSTODY_RECEIPT.json),
[`../v1.0/DEPENDENCY_RECEIPT.json`](../v1.0/DEPENDENCY_RECEIPT.json), and
[`../v1.0/ADVISORY_RECEIPT.json`](../v1.0/ADVISORY_RECEIPT.json). They are
redacted records of project-operated checks, they state what was true for the
v1.0 artifacts, and they are not reissued for this line. The underlying process
logs stay in the maintainer's private records. What each receipt establishes,
and what it does not, is summarized in [RELEASE_NOTES.md](RELEASE_NOTES.md).
