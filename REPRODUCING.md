# Reproducing the current StateSync-GKR distribution

This guide separates the short source-level reproduction from the exact
release-asset verification.

The current release is v1.2.0. Its
[identity record](release/v1.2/IDENTITY_DISTRIBUTION.json) records the program
identity that two controlled clean builds of the release source produced, and
states that the attached external proof belongs to the historical v1.1
program, not to the v1.2.0 program identity.

The measurements and the historical proof refer to v1.1.0, archived as
[DOI 10.5281/zenodo.23136385](https://doi.org/10.5281/zenodo.23136385).
Research and other non-production reproduction are permitted under
[LICENSE](LICENSE).

## Profile 1: source quick start

```sh
git clone --depth 1 https://github.com/Oraclizer/statesync-gkr.git
cd statesync-gkr
rustup show
cargo run --release --locked --example state_sync_prove_verify
```

Pin a specific commit instead of the branch tip when you want a fixed subject
to report against. Record the selected commit in every reproduction report.
[Installation](https://oraclizer.io/ss-gkr/docs/get-started/installation/)
covers toolchain setup and platform notes.

Expected output:

```text
honest-proof=PASS
tampered-proof=REJECTED
secondary-finalized=false
```

[`release/v1.0/RELEASE_NOTES.md`](release/v1.0/RELEASE_NOTES.md) records a
measured environment, wall time, peak memory, and disk use for this profile on
the previous line. That measurement has not been reissued for this line, so
treat it as an order-of-magnitude reference rather than a baseline. Report the
values you observe; a materially different result should be reported with the
report template below.

## Profile 2: exact release package

Download **every** asset of the v1.2.0 release from the
[Releases page](https://github.com/Oraclizer/statesync-gkr/releases) into one empty directory. `statesync-gkr-v1.2-sha256sums.txt` covers all of them and
`sha256sum -c` fails on any that is missing, so a partial download cannot pass
this step. The four the rest of this profile uses directly are:

- `statesync-gkr-v1.2-source.tar.gz`;
- `statesync-gkr-v1.1-proof.cbor`;
- `statesync-gkr-v1.2-attachments.json`;
- `statesync-gkr-v1.2-sha256sums.txt`.

Verify the attachment list before extracting the source:

```sh
sha256sum -c statesync-gkr-v1.2-sha256sums.txt
mkdir statesync-gkr-v1.2-source
tar -xzf statesync-gkr-v1.2-source.tar.gz -C statesync-gkr-v1.2-source
cd statesync-gkr-v1.2-source
python3 release/v1.2/verify.py \
  --mode source-archive \
  --require-proof \
  --proof ../statesync-gkr-v1.1-proof.cbor
```

This command checks package integrity and the recorded size and hash of the
proof attachment. The proof belongs to the historical v1.1 program; the v1.2.0
program identity is recorded in the identity record named above.

Expected final lines include:

```text
external-proof=PASS
public-surface=PASS
```

## Tamper rejection

Create a disposable copy and flip one proof byte:

```sh
python3 -c "from pathlib import Path; p=Path('../statesync-gkr-v1.1-proof.cbor'); b=bytearray(p.read_bytes()); b[-1] ^= 1; Path('../tampered-proof.cbor').write_bytes(b)"
python3 release/v1.2/verify.py \
  --mode source-archive \
  --require-proof \
  --proof ../tampered-proof.cbor
```

The second command must exit nonzero with an external-proof size/hash mismatch.

## Advanced formal build

The Isabelle sessions are a separate advanced profile. Follow
[FORMAL_VERIFICATION.md](FORMAL_VERIFICATION.md). This build is not required
for the short source quick start or proof-attachment hash verification.

## Report a result

Copy `release/v1.2/REPRODUCTION_REPORT_TEMPLATE.json`, fill only observed
values, and attach it to a reproduction issue created from the repository's
issue form. Use `PASS`, `PARTIAL`, or `FAIL`; record every deviation instead of
normalizing it away. Use [SECURITY.md](SECURITY.md) instead when the deviation
may expose a vulnerability.
