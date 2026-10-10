## Scope

Describe the problem, affected public behavior, and why this is the smallest
complete change.

## Claim and trust-boundary impact

- [ ] I identified every affected claim, assumption, external dependency, and
      non-claim.
- [ ] I updated architecture, verification, encoding, or release documentation
      where the public meaning changes.
- [ ] This change does not edit the frozen proof-bound source, or it is part of
      a separately authorized new-identity lifecycle.

## Verification

- [ ] `cargo fmt --all --check`
- [ ] `cargo clippy --workspace --all-targets --locked -- -D warnings`
- [ ] `cargo test --workspace --release --locked`
- [ ] `python3 release/v1.1/verify.py --mode pull-request`
- [ ] Relevant positive, negative, mutation, formal, or archive checks

## Security and provenance

- [ ] No credentials, personal data, private paths, private repository
      coordinates, work attribution, raw logs, caches, or restricted material.
- [ ] Generated files and evidence identify their source and deterministic
      regeneration path.
- [ ] I have the right to submit this contribution under the repository
      license.
