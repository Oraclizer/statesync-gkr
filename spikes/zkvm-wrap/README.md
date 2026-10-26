# Selected zkVM integration

This subtree contains the selected StateSync-GKR RISC Zero integration source,
fixed program identity, saved-proof verifier, and controlled identity-build
recipe.

The `spikes/` path is historical. It remains because moving the protected
guest, host, common, or methods source can change the program identity. The
selected code is a release input, not an unreviewed experiment.

## Public map

- `common/` - shared public statement and guest/host data types;
- `risc0-methods/` - guest method source and generated method identity;
- `risc0-host/` - host build and verification entry;
- `risc0-proof-verify/` - standalone saved-proof verifier;
- `identity/` - expected program identity per release line and the frozen
  change record;
- `reproducible/risc0-route-b/` - pinned controlled-build recipe;
- `logs/` - one curated run record per identity cycle, holding the measured
  facts and the non-claims of that run.

A curated run record is a structured summary, not a raw log. Unselected vendor
trials, raw logs, internal evidence indexes, cloud runbooks, private provenance
scripts, and machine paths are not public release interfaces.

## Fixed identity

The current program identity belongs to the v1.2 line. Two controlled clean
builds of the current source produced it, and its expected record is
[`identity/risc0-route-b-guest-expected-v1.2.json`](identity/risc0-route-b-guest-expected-v1.2.json).

| Layer | Content address |
|---|---|
| Program binary | `e552917c28f7030a46171d33fb90661edb0d1be149efabb1b70bde5b63cc4a28` |
| Image ID | `1a8b55f4e1a5f703386dcfc07e5e8b2e42b5adade6be3d0057f2d565f75eb131` |
| Raw guest ELF | `d8dbb98fcde9cd56089db24af8a7f9a7a28220c526a1a3405b60ec6d751995ee` |
| Generated methods source | `04c2d2af369acc302e22252fe6a2018a73343276a97ae48b844169ebd5620edb` |
| Host binary | `3344d9335fcdddfdd4b491ae9d8a8f5139191a136dec57a3d9a154c0288ff90d` |
| External proof CBOR | `1785b88baeb7dbc49aa2dee0913bf86bc1a3bc22075e217881e257a8a6c9f39b` |

The external proof, `statesync-gkr-v1.2-proof.cbor`, is a secure succinct
proof of this identity. Its production run is recorded in
[`logs/risc0-v3.0.4-v1.2-identity-cuda-secure-proof-2026-10-25.json`](logs/risc0-v3.0.4-v1.2-identity-cuda-secure-proof-2026-10-25.json)
and its public verifier receipt in
[`release/v1.2/PROOF_MANIFEST.json`](../../release/v1.2/PROOF_MANIFEST.json).
The proof applies only to this identity and public statement. Expected values
are immutable comparison targets. A mismatch does not authorize an update,
new identity, or proof regeneration.

The v1.1 program identity is kept as history in
[`identity/risc0-route-b-guest-expected-v1.1.json`](identity/risc0-route-b-guest-expected-v1.1.json)
and in `release/v1.1`, with the proof that release carries:

| Layer | Content address |
|---|---|
| Program binary | `9bb3740d9c0e35f55a42adafa5bfd5cc89fe2520e1c391632807c4e33931cb04` |
| Image ID | `dc9a5f0da608178bbe56e98604cb895060c555c18329846b453f71d562d16530` |
| Raw guest ELF | `38b337c16334226f9dcd2ea319b5e6924aa583ba637126c9d7a8cfacb5cb9a5d` |
| Generated methods source | `3b8c0c23d5f0ceb84e1224b472428772c1f53bcd5c97b5ff1502acc1a6878e03` |
| Host binary | `cad5e07c07465c9f8baddbf6364ad52ae8f35529954d742f5a1449c0ee77aab9` |
| External proof CBOR | `b1a9c3dc86802da706af32eb8ea17eb1ae0ed9c52954a4829cc5e3e9fdee1822` |

The v1.0 program identity is kept as history in
[`identity/risc0-route-b-guest-expected-v1.json`](identity/risc0-route-b-guest-expected-v1.json)
and in `release/v1.0`. Its program binary was
`7dcb6d1d...a9ba`, its image ID `dd947fec...8643`, and its proof
`2ed10736...582a`. Those values describe what the earlier releases claimed and
are not the current identity.

## Build and verification boundary

The controlled identity recipe uses pinned container payloads and a
content-addressed dependency cache, then builds locked, offline, with network
access disabled. Anonymous users can build and test public source with pinned
public dependencies, but that is distinct from reproducing the recorded exact
identity with the original controlled materials.

See:

- [identity policy](identity/README.md)
- [controlled-build recipe](reproducible/risc0-route-b/README.md)
- [public source recipe](../../release/v1.2/SOURCE_RECIPE.md)
- [frozen source identifiers](../../docs/frozen-source-identifiers.md)

## External receipt boundary

The selected proof has a public-verifiable receipt profile and a
receipt-gated local candidate transition. These establish component integration
evidence only.

They do not grant proof-submission authority, identify production signers,
activate a destination, prove source consensus inside the destination, deploy
contracts, establish native rollup proving, confirm parent settlement, or
create secondary finality.

## Privacy boundary

The fixed fixture contains no dynamic user secret. Saved-proof verification
shows that the exact proof matches the fixed image ID and public journal. It
does not establish confidentiality for arbitrary applications, operator
confidentiality, side-channel resistance, or a general zero-knowledge claim.

## Verification

The proof is a release attachment, not a member of the source tree, and
`release/v1.2/artifacts/` is the path the verifier expects it at. Put the
downloaded file there first; the directory is deliberately untracked.

```sh
cargo run --release --locked \
  --manifest-path spikes/zkvm-wrap/risc0-proof-verify/Cargo.toml -- \
  release/v1.2/artifacts/statesync-gkr-v1.2-proof.cbor

python3 release/v1.2/verify.py --mode clean-history --require-proof
```

The release verifier checks exact protected bytes and the finite historical
annotation allowlist. The meaning of every retained legacy label is public and
non-authorizing; new use is forbidden.
