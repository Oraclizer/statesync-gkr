# StateSync-GKR v1.1 release evidence

This index connects the v1.1 release line to its verification material. The
attached proof is historical evidence for the recorded v1.1 program; an exact
compiled identity has not been reproduced for the current package metadata.
See [LICENSING_DISTRIBUTION.json](LICENSING_DISTRIBUTION.json). This index is
not a security audit, a cryptographic security claim or an external
endorsement.

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

v1.1.0 was published on 2026-10-04; its complete tracked source is archived at
[DOI 10.5281/zenodo.23136385](https://doi.org/10.5281/zenodo.23136385). The
current release is v1.1.1, archived at
[DOI 10.5281/zenodo.23280552](https://doi.org/10.5281/zenodo.23280552); its
assets are attached to the signed `v1.1.1` release and retain the documented
`v1.1` filename prefix. Manifests on the main branch describe the current
branch source tree. Keep historical proof observations separately scoped.
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
