# Frozen RISC Zero guest identity

Every recorded program identity is bound to an exact source selection, and
this directory preserves the expected record of each identity line. The
current source is the v1.2 line: two controlled clean builds of its identity
selection produced the same eight identity outputs, recorded in
`risc0-route-b-guest-expected-v1.2.json`. The attached external proof is a
proof of the v1.2 identity, recorded in
[PROOF_MANIFEST.json](../../../release/v1.2/PROOF_MANIFEST.json); the
boundaries are stated in
[IDENTITY_DISTRIBUTION.json](../../../release/v1.2/IDENTITY_DISTRIBUTION.json).
This directory holds one expected record per identity line. A record is never
rewritten when a new line opens: the new line gets its own file, and the
earlier files stay as they were.

## Authority

- `risc0-route-b-guest-expected-v1.2.json` is the current v1.2 program line.
  It fixes the expected program binary, image ID, guest ELF, generated methods
  source, host binary, diagnostic artifacts, and controlled-build inputs, and
  it names the previous line's program binary and image ID under
  `superseded_references` with `covers_current_identity` set to false.
- `risc0-route-b-guest-expected-v1.1.json` is the v1.1 program line, whose
  program the v1.1 proof is bound to.
- `risc0-route-b-guest-expected-v1.json` is the v1.0 line, held byte frozen as
  part of the protected source. It fixes the same fields for the identity the
  v1.0 proof is bound to.
- `risc0-route-b-guest-change-v1.json` is a frozen historical record of a
  rebind inside the v1.0 line. Its development-coordinate field names remain
  only because they are part of the protected source and are classified by
  the public legacy allowlist.
- `release/v1.2/PROTECTED_SOURCE_MANIFEST.json` fixes the complete 79-path
  protected surface.
- `release/v1.2/FROZEN_SOURCE_ALLOWLIST.json` fixes every permitted
  historical annotation occurrence.

## Change policy

Any protected path, mode, byte, canonical JSON key order, field name, test
vector, diagnostic string, comment, or package description change is a hard
failure.

Do not update expected hashes to make a changed build pass. A changed
protected source is a different candidate identity and requires separately
authorized identity and proof work. A proof is never carried across lines: the
v1.0 proof belongs to its recorded v1.0 identity, the v1.1 proof to its
recorded v1.1 identity, and the v1.2 proof to the recorded v1.2 identity.

## Public policy check

```sh
python3 release/v1.2/verify.py --mode clean-history
```

The release verifier is the check. It compares the protected surface byte for
byte, holds the superseded baselines to their recorded digests, and classifies
every permitted historical annotation. It does not fetch private history,
regenerate an identity, build a guest, or inspect a machine-local cache.

## Exact build

The controlled exact build is documented in
[`../reproducible/risc0-route-b/README.md`](../reproducible/risc0-route-b/README.md).
That recipe carries one payload profile per release line and selects the
profile together with the expected record above, so a build is always compared
against the line it belongs to. A claim of reproduced program identity requires
a matching verified receipt. Hosted source checks enforce source consistency;
they do not claim to rerun the controlled build.

## Legacy annotation boundary

Protected development labels are historical, non-sensitive, non-endorsing,
non-authorizing, and forbidden in new source. See
[`../../../docs/frozen-source-identifiers.md`](../../../docs/frozen-source-identifiers.md).
Credentials, personal information, private paths, work attribution, and
operational secrets have no exception.
