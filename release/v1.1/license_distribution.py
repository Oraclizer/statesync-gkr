"""Strict source checks for the licensing-only distribution.

The historical executable identity remains a separate, immutable claim.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import tomllib

BASE_CARGO_SHA256 = "283797b91cb1b839f1b1571e83f2aff03629023400afd637a221bdbcef0a4bcf"
CURRENT_CARGO_SHA256 = "3156d7423eaab5c4b7efc826618bfe18fa653ee5c2c7bcc06de898fab58b5a1d"
BASE_SOURCE_SHA256 = "13eacaa5bf18f26c8089ec6ddf27a7410bb436f28330e12f1135abf5684cf31c"
CURRENT_SOURCE_SHA256 = "7f1ff6b352b8d93cf839273a086ae4db3d62eabae34c1f9fb1ef018dbc1d6dae"
BASE_MANIFEST_SHA256 = "23c5ce2c21a9d8658e6c983cd63928f6e87b184af6027df0f831b2285294aca0"
BASE_ALLOWLIST_SHA256 = "3a68db09cabe247e860a88ff4dd3241890c1b2c7ef1d41ebbf9dacaeebe14450"
CURRENT_DOI = "10.5281/zenodo.23280552"
LICENSE_SHA256 = "9a44129ee88d76331756f1ca1b5a487b7f8c6f81eeee2e1b04472f90c72251a5"
BASE_LICENSE = b'license = "MIT OR Apache-2.0"'
CURRENT_LICENSE = b'license = "BUSL-1.1"'
OWN_PACKAGES = {"statesync-gkr", "ssgkr-primitives", "ssgkr-sumcheck", "ssgkr-protocol", "ssgkr-compiler", "ssgkr-batching", "ssgkr-commitment", "ssgkr-verification", "ssgkr-wrap"}
IDENTITY_EXACT = {"Cargo.toml", "Cargo.lock", "rust-toolchain.toml", "tests/vectors/inner-proof-v1/membership-d24.bin"}
IDENTITY_PREFIXES = ("src/", "crates/", "spikes/zkvm-wrap/common/", "spikes/zkvm-wrap/risc0-host/", "spikes/zkvm-wrap/risc0-methods/")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob_oid(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


def unique_object(pairs: list[tuple[str, object]]) -> dict:
    result: dict = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_record(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)
    if not isinstance(value, dict):
        raise ValueError("expected a JSON object")
    return value


def check_current_cargo(data: bytes) -> None:
    if len(data) != 5081 or digest(data) != CURRENT_CARGO_SHA256:
        raise ValueError("current Cargo bytes are outside the approved license-only delta")
    if data.count(CURRENT_LICENSE) != 1:
        raise ValueError("current Cargo license declaration is absent or ambiguous")
    if tomllib.loads(data.decode("utf-8"))["workspace"]["package"]["license"] != "BUSL-1.1":
        raise ValueError("current workspace license differs")


def historical_cargo_projection(data: bytes) -> bytes:
    """Return comparison bytes in memory; never write an old-license source copy."""
    check_current_cargo(data)
    projected = data.replace(CURRENT_LICENSE, BASE_LICENSE, 1)
    if len(projected) != 5090 or digest(projected) != BASE_CARGO_SHA256:
        raise ValueError("Cargo contains a change beyond the one license field")
    return projected


def protected_data(root: Path, name: str) -> bytes:
    data = (root / name).read_bytes()
    return historical_cargo_projection(data) if name == "Cargo.toml" else data


def identity_source_digests(root: Path, manifest: dict) -> tuple[int, str, str]:
    entries = [e for e in manifest["entries"] if e["path"] in IDENTITY_EXACT or e["path"].startswith(IDENTITY_PREFIXES)]
    if len(entries) != 64 or len({e["path"] for e in entries}) != 64:
        raise ValueError("identity selection must contain the exact 64 paths")
    raw_lines: list[str] = []
    projected_lines: list[str] = []
    for entry in sorted(entries, key=lambda e: e["path"].encode("utf-8")):
        name = entry["path"]
        data = (root / name).read_bytes()
        projected = historical_cargo_projection(data) if name == "Cargo.toml" else data
        raw_lines.append(f"{entry['mode']}\t{digest(data)}\t{name}\n")
        projected_lines.append(f"{entry['mode']}\t{digest(projected)}\t{name}\n")
    current = digest("".join(raw_lines).encode("utf-8"))
    historical = digest("".join(projected_lines).encode("utf-8"))
    if current != CURRENT_SOURCE_SHA256 or historical != BASE_SOURCE_SHA256:
        raise ValueError("current or projected identity source digest differs")
    return len(entries), current, historical


def cff_scalar(raw: str) -> str:
    """Accept the repository's plain, single-quoted or JSON-quoted YAML scalars."""
    raw = raw.strip()
    if raw.startswith('"'):
        value, end = json.JSONDecoder().raw_decode(raw)
        tail = raw[end:].strip()
        if not isinstance(value, str) or (tail and not tail.startswith("#")):
            raise ValueError("invalid quoted CFF scalar")
        return value
    if raw.startswith("'"):
        match = re.fullmatch(r"'((?:[^']|'')*)'\s*(?:#.*)?", raw)
        if not match:
            raise ValueError("invalid single-quoted CFF scalar")
        return match.group(1).replace("''", "'")
    value = re.split(r"\s+#", raw, maxsplit=1)[0].strip()
    if not re.fullmatch(r"[A-Za-z0-9._:/+-]+", value):
        raise ValueError("unsupported CFF scalar syntax")
    return value


def verify_cff(text: str) -> None:
    fields: dict[str, str] = {}
    for line in text.splitlines():
        if "\t" in line:
            raise ValueError("CFF must use spaces for indentation")
        if not line.strip() or line.lstrip().startswith("#") or line[0].isspace():
            continue
        match = re.fullmatch(r"([A-Za-z][A-Za-z0-9-]*)\s*:\s*(.*)", line)
        if not match:
            raise ValueError("unsupported CFF top-level syntax")
        key, raw = match.groups()
        if key in fields:
            raise ValueError(f"duplicate CFF key: {key}")
        fields[key] = raw
    if cff_scalar(fields.get("license", "")) != "BUSL-1.1":
        raise ValueError("current citation license differs")
    if cff_scalar(fields.get("version", "")) != "1.1.1":
        raise ValueError("current citation version differs")
    doi = cff_scalar(fields.get("doi", "")).lower().removeprefix("https://doi.org/")
    if doi != CURRENT_DOI:
        raise ValueError("current citation DOI differs from the assigned distribution DOI")


def verify_distribution(root: Path, *, require_sbom: bool = True) -> dict:
    record = load_record(root / "release/v1.1/LICENSING_DISTRIBUTION.json")
    expected_keys = {"schema", "distribution_version", "license", "source_binding", "historical_protected_manifest_sha256", "historical_allowlist_sha256", "current_compiled_identity_reproduced", "proof_scope", "bounded_build_observation", "interpretation"}
    if set(record) != expected_keys or record.get("schema") != "statesync-gkr.licensing-distribution.v1":
        raise ValueError("unsupported licensing distribution record")
    if record.get("distribution_version") != "1.1.1" or record.get("license") != "BUSL-1.1":
        raise ValueError("distribution version or license differs")
    if digest((root / "LICENSE").read_bytes()) != LICENSE_SHA256:
        raise ValueError("approved root BSL text changed")
    manifest_path = root / "release/v1.1/PROTECTED_SOURCE_MANIFEST.json"
    allowlist_path = root / "release/v1.1/FROZEN_SOURCE_ALLOWLIST.json"
    if record["historical_protected_manifest_sha256"] != BASE_MANIFEST_SHA256 or digest(manifest_path.read_bytes()) != BASE_MANIFEST_SHA256:
        raise ValueError("historical protected authority changed")
    if record["historical_allowlist_sha256"] != BASE_ALLOWLIST_SHA256 or digest(allowlist_path.read_bytes()) != BASE_ALLOWLIST_SHA256:
        raise ValueError("historical annotation authority changed")
    binding = {"historical_identity_source_sha256": BASE_SOURCE_SHA256, "current_distribution_source_sha256": CURRENT_SOURCE_SHA256,
               "changed_protected_path": "Cargo.toml", "changed_field": "workspace.package.license",
               "historical_cargo_sha256": BASE_CARGO_SHA256, "current_cargo_sha256": CURRENT_CARGO_SHA256}
    if record["source_binding"] != binding:
        raise ValueError("licensing source binding differs")
    identity_source_digests(root, load_record(manifest_path))
    if record["current_compiled_identity_reproduced"] is not False or record["proof_scope"] != "historical-v1.1-program-only":
        raise ValueError("unmeasured current compiled identity was promoted")
    observation = record["bounded_build_observation"]
    if not isinstance(observation, dict) or set(observation) != {"status", "program_comparison_completed", "new_proof_generated"}:
        raise ValueError("invalid bounded-build observation")
    if observation["status"] != "STOPPED_AT_HOST_MEMORY_RESERVE" or observation["program_comparison_completed"] is not False or observation["new_proof_generated"] is not False:
        raise ValueError("stopped bounded build was promoted")
    verify_cff((root / "CITATION.cff").read_text(encoding="utf-8"))
    crates = sorted((root / "crates").glob("*/Cargo.toml"))
    if len(crates) != 8:
        raise ValueError("workspace crate count differs")
    names = {"statesync-gkr"}
    for path in crates:
        package = tomllib.loads(path.read_text(encoding="utf-8"))["package"]
        if package["license"] != {"workspace": True}:
            raise ValueError("workspace license inheritance changed")
        names.add(package["name"])
    if names != OWN_PACKAGES:
        raise ValueError("own package set differs")
    caller = root / "benches/controlled-capacity-2026-10-07/Load"
    if tomllib.loads((caller / "Cargo.toml").read_text(encoding="utf-8"))["package"]["license"] != "BUSL-1.1":
        raise ValueError("caller license differs")
    if (caller / "LICENSE").read_bytes() != (root / "LICENSE").read_bytes():
        raise ValueError("caller BSL text differs")
    if (caller / "LICENSE-MIT").exists() or (caller / "LICENSE-APACHE").exists():
        raise ValueError("current caller retains superseded license files")
    if not require_sbom:
        # The source archive self-excludes package seals to avoid digest cycles.
        # Its accompanying SBOM is checked by the full-tree package verifier.
        return record
    sbom = load_record(root / "release/v1.1/SBOM.spdx.json")
    own_rows = [p for p in sbom["packages"] if p.get("name") in OWN_PACKAGES or p.get("SPDXID") == "SPDXRef-Package-SourceArchive"]
    if len(own_rows) != 10 or {p["name"] for p in own_rows if p.get("SPDXID") != "SPDXRef-Package-SourceArchive"} != OWN_PACKAGES:
        raise ValueError("own SBOM package inventory differs")
    if any(p.get("licenseDeclared") != "BUSL-1.1" or p.get("licenseConcluded") != "BUSL-1.1" for p in own_rows):
        raise ValueError("own SBOM license differs")
    return record
