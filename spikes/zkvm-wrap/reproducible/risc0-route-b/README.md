# Controlled RISC Zero identity build

This directory specifies the controlled build used to compare the exact
StateSync-GKR RISC Zero program identity.

## Files

- `Dockerfile` defines the pinned guest build environment.
- `build-guest.sh` builds the selected guest and host artifacts.
- `toolchain-checksums.txt` records fixed toolchain material checksums.
- `toolchain-payload-profile-v1.json` and `toolchain-payload-profile-v1.1.json`
  describe the exact OCI payload, compiler, dependency cache, locks, and
  expected outputs, one file per release line. The runtime payload, the
  dependency cache, and both lock files are shared; the two files differ only in
  the digest of the allowlisted source selection and the eight outputs that
  selection produces.
- `validate-toolchain-payload-v1.py` checks the payload and mutation controls.
- `verify-two-clean-builds.sh` runs the locked, offline, network-disabled
  build and compares all expected outputs. It selects the profile and the
  expected identity record by release line, taking the line from the identity
  guard when one is given, from `--release-line` otherwise, and defaulting to
  the current line. A request that contradicts the guard is refused.

## Exact output boundary

A valid run compares:

- program binary and byte length;
- image ID;
- raw guest ELF;
- generated methods source;
- host binary;
- diagnostic program binary;
- diagnostic guest ELF; and
- identity-regression count.

All values must match the protected expected record. The script must not update
that record.

## Material boundary

The original controlled run used a content-addressed dependency cache and OCI
payload held in private durable custody. A normal public networked build is not
the same experiment. A user without the exact controlled materials can build
and test the source but cannot claim the recorded exact identity build.

Public release metadata may disclose logical artifact names, sizes, hashes,
retention class, and restore results. It must not disclose private object
locations, credentials, machine paths, or operator access details.

## Execution requirements

The controlled run requires:

- Linux x86-64;
- the pinned OCI runtime payload;
- the exact dependency cache archive and manifest;
- locked and offline package resolution;
- a read-only source root;
- network-disabled build containers; and
- a new, empty evidence output directory.

The final release receipt is valid only after independent restoration of the
custody objects and a fresh run that matches every expected identity layer.

## Anonymous source reproduction

See
[`release/v1.1/SOURCE_RECIPE.md`](../../../../release/v1.1/SOURCE_RECIPE.md)
for public build, test, surface verification, and deterministic source archive
commands.

## Non-claims

This recipe does not establish dependency safety, license compliance,
vulnerability absence, kernel or firmware identity, operator confidentiality,
production readiness, deployment authorization, or a new proof identity.
