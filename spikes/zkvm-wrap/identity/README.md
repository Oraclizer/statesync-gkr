# Frozen RISC Zero guest identity

Every recorded proof is bound to an exact RISC Zero program identity, and
this directory preserves the expected records for those historical lines.
The current source differs from the recorded v1.1 program source in one root
Cargo package-metadata field and does not claim a newly reproduced compiled
identity. Its source checks and the historical program boundary are recorded in
[LICENSING_DISTRIBUTION.json](../../../release/v1.1/LICENSING_DISTRIBUTION.json).
This directory holds one expected record per historical identity line. A record is never
rewritten when a new line opens: the new line gets its own file, and the
earlier files stay as they were.

## Authority

- `risc0-route-b-guest-expected-v1.1.json` is the historical v1.1 program line. It fixes the
  expected program binary, image ID, guest ELF, generated methods source, host
  binary, diagnostic artifacts, and controlled-build inputs, and it names the
  previous line's program binary and image ID under `superseded_references`
  with `covers_current_identity` set to false.
- `risc0-route-b-guest-expected-v1.json` is the previous line, held byte
  frozen as part of the protected source. It fixes the same fields for the
  identity the v1.0 proof is bound to.
- `risc0-route-b-guest-change-v1.json` is a frozen historical record of a
  rebind inside the previous line. Its development-coordinate field names
  remain only because they are part of the protected source and are classified
  by the public legacy allowlist.
- `release/v1.1/PROTECTED_SOURCE_MANIFEST.json` fixes the complete 79-path
  protected surface.
- `release/v1.1/FROZEN_SOURCE_ALLOWLIST.json` fixes every permitted
  historical annotation occurrence.

## Change policy

Any protected path, mode, byte, canonical JSON key order, field name, test
vector, diagnostic string, comment, or package description change is a hard
failure.

Do not update expected hashes to make a changed build pass. A changed
protected source is a different candidate identity and requires separately
authorized identity and proof work. A proof is never carried across lines: the
v1.0 proof belongs to its recorded v1.0 identity, and the recorded v1.1 proof
belongs to its historical v1.1 identity. Neither establishes a compiled
identity for the current source.

## Public policy check

```sh
python3 release/v1.1/verify.py --mode clean-history
```

The release verifier is the check. It compares the protected surface byte for
byte, holds the superseded baseline to one recorded digest, and classifies
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
