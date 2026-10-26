"""Strict source, identity and distribution checks for the v1.2 line.

The v1.2 source is its own program identity: the 64-path identity selection
of the protected surface was measured by two controlled clean builds whose
eight outputs agree. The newest external proof stays a separate claim whose
scope this record states and these checks hold.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import tomllib

IDENTITY_RECORD = "release/v1.2/IDENTITY_DISTRIBUTION.json"
PROTECTED_MANIFEST = "release/v1.2/PROTECTED_SOURCE_MANIFEST.json"
SBOM = "release/v1.2/SBOM.spdx.json"
IDENTITY_SOURCE_SHA256 = "6cd794e7ef393e758f3e04b04b95b6949e7f9a05e46f5483b47151f2d5175ace"
PREVIOUS_IDENTITY_SOURCE_SHA256 = "13eacaa5bf18f26c8089ec6ddf27a7410bb436f28330e12f1135abf5684cf31c"
HISTORICAL_MANIFEST_SHA256 = "23c5ce2c21a9d8658e6c983cd63928f6e87b184af6027df0f831b2285294aca0"
HISTORICAL_ALLOWLIST_SHA256 = "3a68db09cabe247e860a88ff4dd3241890c1b2c7ef1d41ebbf9dacaeebe14450"
EXPECTED_IDENTITY_RECORD = "spikes/zkvm-wrap/identity/risc0-route-b-guest-expected-v1.2.json"
HISTORICAL_PROOF_MANIFEST = "release/v1.1/PROOF_MANIFEST.json"
# The distributions this line may record: its release and the following patch
# release. The citation and the SBOM must name the version the identity record
# states, so a patch distribution cannot pass with another version's metadata.
DISTRIBUTION_VERSIONS = ("1.2.0", "1.2.1")
# The latest published software release before this line is released. Its
# citation pair stays valid until a published v1.2 release replaces it.
PUBLISHED_PREDECESSOR = ("1.1.1", "10.5281/zenodo.23280552")
LICENSE_SHA256 = "9a44129ee88d76331756f1ca1b5a487b7f8c6f81eeee2e1b04472f90c72251a5"
OWN_PACKAGES = {"statesync-gkr", "ssgkr-primitives", "ssgkr-sumcheck", "ssgkr-protocol", "ssgkr-compiler", "ssgkr-batching", "ssgkr-commitment", "ssgkr-verification", "ssgkr-wrap"}
IDENTITY_EXACT = {"Cargo.toml", "Cargo.lock", "rust-toolchain.toml", "tests/vectors/inner-proof-v1/membership-d24.bin"}
IDENTITY_PREFIXES = ("src/", "crates/", "spikes/zkvm-wrap/common/", "spikes/zkvm-wrap/risc0-host/", "spikes/zkvm-wrap/risc0-methods/")
CALLERS = ("benches/controlled-capacity-2026-10-07/Load", "benches/serving")
PROOF_SCOPES = ("historical-v1.1-program-only", "current-v1.2-program")
EXPECTED_KEYS = {
    "schema", "release_line", "distribution_version", "license", "identity_source",
    "compiled_identity", "proof", "citation", "historical_baseline", "interpretation",
}


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


def identity_source_digest(root: Path, manifest: dict) -> tuple[int, str]:
    """Digest of the identity selection, in the controlled build's row format."""
    entries = [e for e in manifest["entries"] if e["path"] in IDENTITY_EXACT or e["path"].startswith(IDENTITY_PREFIXES)]
    if len(entries) != 64 or len({e["path"] for e in entries}) != 64:
        raise ValueError("identity selection must contain the exact 64 paths")
    rows = []
    for entry in sorted(entries, key=lambda e: e["path"].encode("utf-8")):
        data = (root / entry["path"]).read_bytes()
        rows.append(f"{entry['mode']}\t{digest(data)}\t{entry['path']}\n")
    value = digest("".join(rows).encode("utf-8"))
    if value != IDENTITY_SOURCE_SHA256:
        raise ValueError("identity source digest differs from the recorded selection")
    return len(entries), value


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


def cff_fields(text: str) -> dict[str, str]:
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
    return fields


def verify_citation_pair(version: str, doi: str, distribution_version: str) -> None:
    """A citation names the published predecessor or the recorded v1.2 distribution."""
    if (version, doi) == PUBLISHED_PREDECESSOR:
        return
    if (version == distribution_version and version in DISTRIBUTION_VERSIONS
            and re.fullmatch(r"10\.5281/zenodo\.\d+", doi) and doi != PUBLISHED_PREDECESSOR[1]):
        return
    raise ValueError("citation names neither the published predecessor nor a published v1.2 release")


def verify_cff(text: str, citation: dict, distribution_version: str) -> None:
    fields = cff_fields(text)
    if cff_scalar(fields.get("license", "")) != "BUSL-1.1":
        raise ValueError("current citation license differs")
    version = cff_scalar(fields.get("version", ""))
    doi = cff_scalar(fields.get("doi", "")).lower().removeprefix("https://doi.org/")
    if version != citation["version"] or doi != citation["doi"]:
        raise ValueError("citation differs from the identity record")
    verify_citation_pair(version, doi, distribution_version)


def verify_compiled_identity(root: Path, record: dict) -> None:
    compiled = record["compiled_identity"]
    if set(compiled) != {"reproduced", "clean_build_count", "expected_record", "expected_record_sha256", "image_id", "program_binary_sha256"}:
        raise ValueError("invalid compiled identity section")
    if compiled["reproduced"] is not True or compiled["clean_build_count"] != 2:
        raise ValueError("compiled identity requires two agreeing clean builds")
    if compiled["expected_record"] != EXPECTED_IDENTITY_RECORD:
        raise ValueError("compiled identity names another expected record")
    raw = (root / EXPECTED_IDENTITY_RECORD).read_bytes()
    if digest(raw) != compiled["expected_record_sha256"]:
        raise ValueError("expected identity record changed")
    expected = json.loads(raw, object_pairs_hook=unique_object)
    if expected.get("release_line") != record["release_line"]:
        raise ValueError("expected identity record belongs to another line")
    if expected["recipe"]["source_manifest_sha256"] != IDENTITY_SOURCE_SHA256:
        raise ValueError("expected identity record binds another source selection")
    if expected["recipe"]["clean_build_count"] != compiled["clean_build_count"]:
        raise ValueError("expected identity record states another build count")
    artifacts = expected["artifacts"]
    if artifacts["image_id"] != compiled["image_id"] or artifacts["program_binary"]["sha256"] != compiled["program_binary_sha256"]:
        raise ValueError("compiled identity differs from the expected record")


def verify_proof_scope(root: Path, record: dict) -> None:
    proof = record["proof"]
    if set(proof) != {"scope", "release_line", "asset_name", "bytes", "sha256", "bound_image_id", "record", "covers_current_identity"}:
        raise ValueError("invalid proof section")
    if proof["scope"] not in PROOF_SCOPES:
        raise ValueError("unknown proof scope")
    manifest = load_record(root / proof["record"])
    recorded = manifest["proof"]
    if (proof["asset_name"], proof["bytes"], proof["sha256"]) != (recorded["asset_name"], recorded["bytes"], recorded["sha256"]):
        raise ValueError("proof section differs from its proof manifest")
    if proof["bound_image_id"] != manifest["program_identity"]["image_id"]:
        raise ValueError("proof section names another bound program")
    current = record["compiled_identity"]["image_id"]
    if proof["scope"] == "historical-v1.1-program-only":
        if proof["record"] != HISTORICAL_PROOF_MANIFEST or proof["release_line"] != "v1.1":
            raise ValueError("historical proof scope must name the v1.1 proof manifest")
        if proof["covers_current_identity"] is not False or proof["bound_image_id"] == current:
            raise ValueError("a historical proof was promoted to the current identity")
    else:
        if proof["record"] != "release/v1.2/PROOF_MANIFEST.json" or proof["release_line"] != "v1.2":
            raise ValueError("a current-line proof must name the v1.2 proof manifest")
        if proof["covers_current_identity"] is not True or proof["bound_image_id"] != current:
            raise ValueError("a current-line proof must be bound to the current identity")


def verify_distribution(root: Path, *, require_sbom: bool = True) -> dict:
    record = load_record(root / IDENTITY_RECORD)
    if set(record) != EXPECTED_KEYS or record.get("schema") != "statesync-gkr.identity-distribution.v1":
        raise ValueError("unsupported identity distribution record")
    distribution_version = record["distribution_version"]
    if record["release_line"] != "v1.2" or distribution_version not in DISTRIBUTION_VERSIONS or record["license"] != "BUSL-1.1":
        raise ValueError("release line, distribution version or license differs")
    if digest((root / "LICENSE").read_bytes()) != LICENSE_SHA256:
        raise ValueError("approved root BSL text changed")

    source = record["identity_source"]
    if source != {"path_count": 64, "sha256": IDENTITY_SOURCE_SHA256, "previous_line_sha256": PREVIOUS_IDENTITY_SOURCE_SHA256}:
        raise ValueError("identity source section differs")
    identity_source_digest(root, load_record(root / PROTECTED_MANIFEST))
    verify_compiled_identity(root, record)
    verify_proof_scope(root, record)

    baseline = record["historical_baseline"]
    if baseline != {"release_line": "v1.1", "protected_manifest_sha256": HISTORICAL_MANIFEST_SHA256, "allowlist_sha256": HISTORICAL_ALLOWLIST_SHA256}:
        raise ValueError("historical baseline section differs")
    if digest((root / "release/v1.1/PROTECTED_SOURCE_MANIFEST.json").read_bytes()) != HISTORICAL_MANIFEST_SHA256:
        raise ValueError("historical protected authority changed")
    if digest((root / "release/v1.1/FROZEN_SOURCE_ALLOWLIST.json").read_bytes()) != HISTORICAL_ALLOWLIST_SHA256:
        raise ValueError("historical annotation authority changed")

    citation = record["citation"]
    if set(citation) != {"version", "doi", "status"} or citation["status"] != "LATEST_PUBLISHED_RELEASE":
        raise ValueError("invalid citation section")
    verify_cff((root / "CITATION.cff").read_text(encoding="utf-8"), citation, distribution_version)

    crates = sorted((root / "crates").glob("*/Cargo.toml"))
    if len(crates) != 8:
        raise ValueError("workspace crate count differs")
    workspace = tomllib.loads((root / "Cargo.toml").read_text(encoding="utf-8"))
    if workspace["workspace"]["package"]["license"] != "BUSL-1.1":
        raise ValueError("workspace license differs")
    names = {"statesync-gkr"}
    for path in crates:
        package = tomllib.loads(path.read_text(encoding="utf-8"))["package"]
        if package["license"] != {"workspace": True}:
            raise ValueError("workspace license inheritance changed")
        names.add(package["name"])
    if names != OWN_PACKAGES:
        raise ValueError("own package set differs")
    for relative in CALLERS:
        caller = root / relative
        if tomllib.loads((caller / "Cargo.toml").read_text(encoding="utf-8"))["package"]["license"] != "BUSL-1.1":
            raise ValueError(f"caller license differs: {relative}")
        if (caller / "LICENSE").read_bytes() != (root / "LICENSE").read_bytes():
            raise ValueError(f"caller BSL text differs: {relative}")
        if (caller / "LICENSE-MIT").exists() or (caller / "LICENSE-APACHE").exists():
            raise ValueError(f"caller retains superseded license files: {relative}")
    if not require_sbom:
        # The source archive self-excludes package seals to avoid digest cycles.
        # Its accompanying SBOM is checked by the full-tree package verifier.
        return record
    sbom = load_record(root / SBOM)
    own_rows = [p for p in sbom["packages"] if p.get("name") in OWN_PACKAGES or p.get("SPDXID") == "SPDXRef-Package-SourceArchive"]
    if len(own_rows) != 10 or {p["name"] for p in own_rows if p.get("SPDXID") != "SPDXRef-Package-SourceArchive"} != OWN_PACKAGES:
        raise ValueError("own SBOM package inventory differs")
    if any(p.get("licenseDeclared") != "BUSL-1.1" or p.get("licenseConcluded") != "BUSL-1.1" for p in own_rows):
        raise ValueError("own SBOM license differs")
    archive = [p for p in own_rows if p.get("SPDXID") == "SPDXRef-Package-SourceArchive"]
    if archive[0].get("versionInfo") != distribution_version:
        raise ValueError("SBOM source archive version differs from the distribution version")
    return record
