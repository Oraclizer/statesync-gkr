#!/usr/bin/env python3
"""Fail-closed verifier for the StateSync-GKR frozen public surface.

This is the v1.1 baseline. The v1.0 baseline in release/v1.0 stays frozen:
it is a historical record of the v1.0 identity cycle and it is checked here
only for byte stability, never regenerated.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys
from typing import Any

import license_distribution


MANIFEST_SHA256 = "23c5ce2c21a9d8658e6c983cd63928f6e87b184af6027df0f831b2285294aca0"
ALLOWLIST_SHA256 = "3a68db09cabe247e860a88ff4dd3241890c1b2c7ef1d41ebbf9dacaeebe14450"
# The v1.0 baseline bound its protected manifest to a development commit that
# the published, clean-history repository does not contain. This line binds the
# manifest to content instead: the digest of the exact source selection that
# produces the accepted program identity, which any clone can recompute.
AUTHORITY_BINDING = "BOUND_BY_CONTENT"
IDENTITY_SOURCE_MANIFEST_SHA256 = "13eacaa5bf18f26c8089ec6ddf27a7410bb436f28330e12f1135abf5684cf31c"
PROTECTED_PATH_SET_SHA256 = "e91cf1768632c12f812a345b605dbc86002fa9a8e55dc94eb6a0a4f35f085636"
LEGACY_OCCURRENCES = 123
# The superseded baseline is evidence, not a live gate. It must not change.
FROZEN_BASELINE_PREFIX = "release/v1.0/"
FROZEN_BASELINE_FILE_COUNT = 23
FROZEN_BASELINE_SHA256 = "53c9dd80c2672b045c4fa1916648dc7c82360dfbebff35fd63ad178b67f04197"
FROZEN_BASELINE_LAST_VALID_COMMIT = "a456846f98df6e0b60c9e6d33d67592a82ef9500"
GLOSSARY = "docs/frozen-source-identifiers.md"
MANIFEST_PATH = "release/v1.1/PROTECTED_SOURCE_MANIFEST.json"
ALLOWLIST_PATH = "release/v1.1/FROZEN_SOURCE_ALLOWLIST.json"
PROOF_PATH = "release/v1.1/artifacts/statesync-gkr-v1.1-proof.cbor"
TREE_MANIFEST_PATH = "release/v1.1/TREE_MANIFEST.json"
SOURCE_MANIFEST_PATH = "release/v1.1/SOURCE_MANIFEST.json"
ATTACHMENTS_PATH = "release/v1.1/ATTACHMENTS.json"
SHA256SUMS_PATH = "release/v1.1/SHA256SUMS"
SEAL_PATHS = {
    TREE_MANIFEST_PATH,
    "release/v1.1/PROOF_MANIFEST.json",
    "release/v1.1/PUBLIC_INPUTS.json",
    "release/v1.1/SBOM.spdx.json",
    "release/v1.1/PROVENANCE.intoto.jsonl",
    ATTACHMENTS_PATH,
    SHA256SUMS_PATH,
}
SCANNER_DEFINITION_PATHS = frozenset({
    "release/v1.0/verify.py",
    "release/v1.1/verify.py",
})
PAPER_BIBLIOGRAPHY_PATH = "paper/TEX/references.bib"
SCHOLAR_NAME_COLLISION = "March{\\'e}, " + "Clau" + "de"


class VerificationError(RuntimeError):
    pass


def fail(message: str) -> None:
    raise VerificationError(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def strict_json(path: Path) -> dict[str, Any]:
    def pairs(items: list[tuple[str, Any]]) -> dict[str, Any]:
        out: dict[str, Any] = {}
        for key, value in items:
            if key in out:
                fail(f"duplicate JSON key in {path}: {key}")
            out[key] = value
        return out

    try:
        result = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=pairs)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        fail(f"strict JSON parse failed for {path}: {exc}")
    if not isinstance(result, dict):
        fail(f"expected JSON object: {path}")
    return result


def repository_root() -> Path:
    return Path(__file__).resolve().parents[2]


def safe_path(root: Path, name: str) -> Path:
    logical = PurePosixPath(name)
    if logical.is_absolute() or not logical.parts or any(part in ("", ".", "..") for part in logical.parts):
        fail(f"unsafe manifest path: {name!r}")
    if "\\" in name:
        fail(f"non-POSIX manifest path: {name!r}")
    path = (root / Path(*logical.parts)).resolve()
    if root != path and root not in path.parents:
        fail(f"path escapes repository: {name}")
    return path


def git(root: Path, *args: str) -> str:
    process = subprocess.run(
        ["git", "-C", str(root), *args],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        check=False,
    )
    if process.returncode != 0:
        fail(f"git {' '.join(args)} failed: {process.stderr.strip()}")
    return process.stdout


def selected_paths(root: Path, manifest: dict[str, Any]) -> set[str]:
    rule = manifest["selection_rule"]
    result: set[str] = set()
    for prefix in rule["recursive_prefixes"]:
        directory = safe_path(root, prefix)
        if not directory.is_dir():
            fail(f"missing protected directory: {prefix}")
        for path in directory.rglob("*"):
            if path.is_symlink():
                fail(f"symlink inside protected surface: {path}")
            if path.is_file():
                result.add(path.relative_to(root).as_posix())
    for name in rule["exact_paths"]:
        path = safe_path(root, name)
        if not path.is_file() or path.is_symlink():
            fail(f"missing protected file: {name}")
        result.add(name)
    return result


def entry_modes_from_git(root: Path, paths: list[str]) -> dict[str, tuple[str, str]]:
    output = git(root, "ls-files", "-s", "--", *paths)
    result: dict[str, tuple[str, str]] = {}
    for line in output.splitlines():
        metadata, name = line.split("\t", 1)
        mode, blob, _stage = metadata.split(" ")
        result[name] = (mode, blob)
    return result


def verify_protected(root: Path, manifest: dict[str, Any], allowlist: dict[str, Any], has_git: bool) -> set[str]:
    subject = manifest.get("subject", {})
    if subject.get("commit") != AUTHORITY_BINDING or subject.get("tree") != AUTHORITY_BINDING:
        fail("protected manifest authority binding mismatch")
    if subject.get("identity_source_manifest_sha256") != IDENTITY_SOURCE_MANIFEST_SHA256:
        fail("protected manifest identity-source binding mismatch")
    if manifest.get("tracked_path_count") != 79:
        fail("protected path count mismatch")
    if manifest.get("tracked_path_set_sha256") != PROTECTED_PATH_SET_SHA256:
        fail("protected path-set identity mismatch")
    if allowlist.get("subject", {}).get("protected_surface_manifest_sha256") != MANIFEST_SHA256:
        fail("allowlist does not bind the protected manifest")
    if allowlist.get("legacy_occurrence_count") != LEGACY_OCCURRENCES:
        fail("legacy occurrence authority mismatch")

    entries = manifest.get("entries")
    if not isinstance(entries, list) or len(entries) != 79:
        fail("protected entries array mismatch")
    expected_paths = [str(entry["path"]) for entry in entries]
    if expected_paths != sorted(expected_paths, key=lambda value: value.encode("utf-8")):
        fail("protected entries are not bytewise path-sorted")
    if selected_paths(root, manifest) != set(expected_paths):
        fail("protected path set drift")

    git_modes = entry_modes_from_git(root, expected_paths) if has_git else {}
    entry_by_path: dict[str, dict[str, Any]] = {}
    for entry in entries:
        name = str(entry["path"])
        path = safe_path(root, name)
        if not path.is_file() or path.is_symlink():
            fail(f"protected file type drift: {name}")
        actual_data = path.read_bytes()
        if name == "Cargo.toml":
            # Check the current file and current index before projecting the
            # single approved metadata field to the historical comparison.
            try:
                license_distribution.check_current_cargo(actual_data)
            except ValueError as exc:
                fail(str(exc))
            current_blob = license_distribution.git_blob_oid(actual_data)
            if has_git and git_modes.get(name) != (entry["mode"], current_blob):
                fail(f"current Cargo Git mode/blob drift: {name}")
            if not has_git and os.name != "nt" and stat.S_IMODE(path.stat().st_mode) != 0o644:
                fail(f"current Cargo filesystem mode drift: {name}")
            data = license_distribution.historical_cargo_projection(actual_data)
        else:
            data = actual_data
            if has_git and git_modes.get(name) != (entry["mode"], entry["git_blob_oid"]):
                fail(f"protected Git mode/blob drift: {name}")
            if not has_git:
                expected_mode = 0o755 if entry["mode"] == "100755" else 0o644
                if os.name != "nt" and stat.S_IMODE(path.stat().st_mode) != expected_mode:
                    fail(f"protected filesystem mode drift: {name}")
        if len(data) != int(entry["bytes"]) or sha256_bytes(data) != entry["sha256"]:
            fail(f"historical protected comparison drift: {name}")
        entry_by_path[name] = entry

    verify_json_order(root, manifest)
    verify_legacy_occurrences(root, allowlist, entry_by_path)
    return set(expected_paths)


def pointer_get(value: Any, pointer: str) -> Any:
    if pointer == "/":
        return value
    current = value
    for raw in pointer.lstrip("/").split("/"):
        token = raw.replace("~1", "/").replace("~0", "~")
        if isinstance(current, list):
            current = current[int(token)]
        elif isinstance(current, dict):
            current = current[token]
        else:
            fail(f"JSON pointer crosses scalar: {pointer}")
    return current


def verify_json_order(root: Path, manifest: dict[str, Any]) -> None:
    for owner in manifest.get("canonical_json_object_key_order", []):
        name = owner["path"]
        path = safe_path(root, name)
        document = strict_json(path)
        if sha256_file(path) != owner["containing_blob_sha256"]:
            fail(f"JSON order owner hash drift: {name}")
        for record in owner["object_key_orders"]:
            target = pointer_get(document, record["json_pointer"])
            if not isinstance(target, dict) or list(target.keys()) != record["keys_in_order"]:
                fail(f"canonical JSON key order drift: {name}{record['json_pointer']}")


def verify_legacy_occurrences(root: Path, allowlist: dict[str, Any], entry_by_path: dict[str, dict[str, Any]]) -> None:
    occurrences = allowlist.get("occurrences")
    if not isinstance(occurrences, list) or len(occurrences) != LEGACY_OCCURRENCES:
        fail("legacy occurrence list mismatch")
    pattern = re.compile(allowlist["policy"]["legacy_scan_regex"])
    expected: Counter[tuple[str, int, str, bytes]] = Counter()
    by_path: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for occurrence in occurrences:
        name = occurrence["path"]
        if name not in entry_by_path:
            fail(f"legacy occurrence outside protected surface: {name}")
        data = license_distribution.protected_data(root, name)
        token = bytes.fromhex(occurrence["match_bytes_hex"])
        offset = int(occurrence["blob_byte_offset_zero_based"])
        if data[offset : offset + len(token)] != token:
            fail(f"legacy anchor bytes drift: {occurrence['occurrence_id']}")
        if sha256_bytes(data) != occurrence["containing_blob_sha256"]:
            fail(f"legacy containing blob drift: {name}")
        lines = data.splitlines()
        line_index = int(occurrence["line_number_advisory"]) - 1
        if line_index < 0 or line_index >= len(lines) or sha256_bytes(lines[line_index]) != occurrence["line_sha256"]:
            fail(f"legacy line anchor drift: {occurrence['occurrence_id']}")
        expected[(name, offset, occurrence["family"], token)] += 1
        by_path[name].append(occurrence)

    actual: Counter[tuple[str, int, str, bytes]] = Counter()
    for name in by_path:
        data = license_distribution.protected_data(root, name)
        text = data.decode("utf-8")
        for match in pattern.finditer(text):
            offset = len(text[: match.start()].encode("utf-8"))
            actual[(name, offset, str(match.lastgroup), match.group(0).encode("utf-8"))] += 1
    if actual != expected or sum(actual.values()) != LEGACY_OCCURRENCES:
        fail("legacy occurrence multiset drift")


def readable_text(path: Path) -> str | None:
    binary_suffixes = {".bin", ".cbor", ".gz", ".pdf", ".png", ".jpg", ".jpeg", ".wasm", ".elf"}
    if path.suffix.lower() in binary_suffixes:
        return None
    try:
        return path.read_text(encoding="utf-8")
    except (UnicodeDecodeError, OSError):
        return None


def ai_attribution_scan_text(name: str, text: str) -> str:
    """Remove one exact scholar-name collision without weakening other scans."""
    if name == PAPER_BIBLIOGRAPHY_PATH:
        return text.replace(SCHOLAR_NAME_COLLISION, "")
    return text


def isabelle_prose(text: str) -> str:
    selected: list[str] = []
    active = False
    for line in text.splitlines():
        if re.search(r"(?:text|chapter|section|subsection|subsubsection)\s+\\<open>", line):
            active = True
        if active:
            selected.append(line)
        if active and "\\<close>" in line:
            active = False
    return "\n".join(selected)


def public_files(root: Path, has_git: bool) -> list[tuple[str, Path]]:
    result: list[tuple[str, Path]] = []
    if has_git:
        names = {
            name
            for name in git(
                root,
                "ls-files",
                "--cached",
                "--others",
                "--exclude-standard",
                "-z",
            ).split("\0")
            if name
        }
        paths = [safe_path(root, name) for name in names]
    else:
        paths = list(root.rglob("*"))
    for path in paths:
        relative = path.relative_to(root).as_posix()
        if not path.exists():
            # An unstaged deletion can still be present in the private index;
            # it is not a member of the candidate public tree.
            continue
        if path.is_symlink():
            fail(f"public tree contains symlink: {relative}")
        if path.is_file():
            result.append((relative, path))
        elif not path.is_dir():
            fail(f"public tree contains non-regular object: {relative}")
    return sorted(result, key=lambda item: item[0].encode("utf-8"))


def verify_sensitive_and_new_identifiers(root: Path, protected: set[str], manifest: dict[str, Any], allowlist: dict[str, Any], has_git: bool) -> None:
    files = public_files(root, has_git)
    email_pattern = re.compile(r"[A-Za-z0-9.!#$%&'*+/=?^_`{|}~-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}")
    credential_patterns = [
        re.compile(r"-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----"),
        re.compile(r"AKIA[0-9A-Z]{16}"),
        re.compile(r"gh" + r"[pousr]_[A-Za-z0-9_]{20,}"),
        re.compile(r"xox" + r"[baprs]-[A-Za-z0-9-]{10,}"),
    ]
    private_path_patterns = [
        re.compile(r"[A-Za-z]:[\\/](?:Users|Documents)[\\/]", re.IGNORECASE),
        re.compile(r"/(?:home|Users)/[^/\s]+/"),
        re.compile(r"/mnt/[a-z]/Users/", re.IGNORECASE),
    ]
    tool_names = ["Clau" + "de", "Co" + "dex", "Chat" + "GPT", "Open" + "AI", "Anth" + "ropic"]
    tool_pattern = re.compile("|".join(map(re.escape, tool_names)), re.IGNORECASE)
    private_coordinate = re.compile(r"(?:cod" + r"ex/|wt/|PR\s*#\d+|release/v1\.0-public-readiness)", re.IGNORECASE)
    legacy_pattern = re.compile(allowlist["policy"]["legacy_scan_regex"])

    expected_contact_counts = Counter(owner["path"] for owner in manifest["declared_public_professional_contact"]["owners"])
    declared_contact = manifest["declared_public_professional_contact"]["contact"]
    actual_contact_counts: Counter[str] = Counter()
    definition_files = {GLOSSARY, ALLOWLIST_PATH, "release/v1.0/FROZEN_SOURCE_ALLOWLIST.json"}
    exact_census_files = {
        MANIFEST_PATH,
        ALLOWLIST_PATH,
        "release/v1.0/PROTECTED_SOURCE_MANIFEST.json",
        "release/v1.0/FROZEN_SOURCE_ALLOWLIST.json",
    }
    census_hashes = (
        MANIFEST_SHA256,
        ALLOWLIST_SHA256,
        "75370592a45938c77f7c637dd9110af600926b67bf80ae51be2edb5cc86adc88",
        "9ab8b541261a3b088cf93e5044c429a8440bdc252cc9de1f828f44fb1c9e2bd4",
    )

    for name, path in files:
        if name in exact_census_files and sha256_file(path) in census_hashes:
            # These two copied census artifacts were independently scanned
            # before publication. Their exact hashes make this a finite
            # evidence exception rather than a pattern exception.
            continue
        text = readable_text(path)
        if text is None:
            continue
        for pattern in credential_patterns + private_path_patterns:
            if pattern.search(text):
                fail(f"sensitive pattern in public file: {name}")
        if tool_pattern.search(ai_attribution_scan_text(name, text)):
            fail(f"artificial-intelligence attribution in public file: {name}")
        for email in email_pattern.findall(text):
            if email != declared_contact or name not in expected_contact_counts:
                fail(f"undeclared email in public file: {name}")
            actual_contact_counts[name] += 1

        if name in protected or name in definition_files:
            continue
        scan_text = isabelle_prose(text) if path.suffix == ".thy" else text
        scan_text = scan_text.replace("http://www.w3.org/2000/svg", "")
        if legacy_pattern.search(scan_text) or legacy_pattern.search(name):
            fail(f"new legacy identifier outside frozen definitions: {name}")
        # The scanner source necessarily spells out the private-coordinate
        # signatures that it rejects. This is an exact, single-file
        # definition exclusion for that one check only: credentials, private
        # paths, AI attribution, email ownership, protected bytes, and every
        # other verification above still apply to this file.
        if name not in SCANNER_DEFINITION_PATHS and (
            private_coordinate.search(scan_text) or private_coordinate.search(name)
        ):
            fail(f"private repository coordinate in public file: {name}")

    if actual_contact_counts != expected_contact_counts:
        fail(f"declared public contact tuple drift: {dict(actual_contact_counts)}")


def verify_frozen_baseline(root: Path, has_git: bool) -> None:
    """The superseded baseline is a historical record and must not change.

    Every file it contains is compared as one digest, so an edit or a removal
    fails here instead of silently rewriting what the earlier release claimed.
    """
    names = sorted(
        name
        for name, _path in public_files(root, has_git)
        if name.startswith(FROZEN_BASELINE_PREFIX)
    )
    if len(names) != FROZEN_BASELINE_FILE_COUNT:
        fail(f"frozen baseline file count drift: {len(names)}")
    joined = "\0".join(f"{name}:{sha256_file(safe_path(root, name))}" for name in names)
    if sha256_bytes(joined.encode("utf-8")) != FROZEN_BASELINE_SHA256:
        fail("frozen baseline content drift")


def verify_glossary(root: Path, allowlist: dict[str, Any]) -> None:
    path = safe_path(root, GLOSSARY)
    text = path.read_text(encoding="utf-8")
    required = [
        "Compatibility seals",
        "Refinement scopes and theorem families",
        "Prepared material profile",
        "Public proof-bound legacy annotations",
        "not a current public workflow or approval procedure",
        "not an external endorsement",
        "not runtime authorization or a security role",
        "reuse in new source is forbidden",
    ]
    for phrase in required:
        if phrase not in text:
            fail(f"frozen-source glossary missing policy phrase: {phrase}")
    for token in ("S-1", "S-2", "S-3", "S-4", "S-5", "S-6", "R1", "R2", "R3", "R4", "R2-1", "Theorem A", "Theorem B", "Theorem C", "Theorem D", "A0"):
        if token not in text:
            fail(f"frozen-source glossary missing stable identifier: {token}")
    if allowlist["policy"]["public_glossary_owner"].split("#", 1)[0] != GLOSSARY:
        fail("allowlist glossary owner mismatch")


def verify_proof(root: Path, manifest: dict[str, Any], required: bool, supplied: Path | None) -> None:
    authority = manifest["external_proof_artifact"]
    path = supplied.resolve() if supplied else safe_path(root, PROOF_PATH)
    if not path.exists():
        if required:
            fail(f"required external proof is absent: {path}")
        print("external-proof=DEFERRED")
        return
    if not path.is_file() or path.is_symlink():
        fail("external proof is not a regular file")
    if path.stat().st_size != authority["bytes"] or sha256_file(path) != authority["sha256"]:
        fail("external proof size/hash mismatch")
    print("external-proof=PASS")


def candidate_modes(root: Path, has_git: bool) -> dict[str, str]:
    result: dict[str, str] = {}
    if has_git:
        for record in git(root, "ls-files", "-s", "-z").split("\0"):
            if not record:
                continue
            metadata, name = record.split("\t", 1)
            result[name] = metadata.split(" ", 1)[0]
    return result


def resolve_candidate_mode(
    indexed_mode: str | None,
    has_git: bool,
    filesystem_mode: int,
) -> str:
    if indexed_mode is not None:
        return indexed_mode
    if has_git:
        # Git will add ordinary new files as 100644 unless the executable bit
        # is explicitly recorded. DrvFS can project execute bits onto every
        # Windows file, so POSIX stat is not an intended-index authority for
        # untracked files in the canonical Windows worktree.
        return "100644"
    return "100755" if filesystem_mode & 0o111 else "100644"


def candidate_mode(
    root: Path,
    name: str,
    tracked_modes: dict[str, str],
    has_git: bool,
) -> str:
    path = safe_path(root, name)
    return resolve_candidate_mode(
        tracked_modes.get(name),
        has_git,
        stat.S_IMODE(path.stat().st_mode),
    )


def verify_entry_manifest(
    root: Path,
    manifest_path: str,
    expected_names: set[str],
    has_git: bool,
    tracked_modes: dict[str, str],
) -> dict[str, Any]:
    path = safe_path(root, manifest_path)
    manifest = strict_json(path)
    entries = manifest.get("entries")
    if not isinstance(entries, list):
        fail(f"entries array missing: {manifest_path}")
    names = [str(entry.get("path", "")) for entry in entries]
    if names != sorted(names, key=lambda item: item.encode("utf-8")):
        fail(f"manifest paths are not bytewise sorted: {manifest_path}")
    if len(names) != len(set(names)) or set(names) != expected_names:
        fail(f"manifest path-set mismatch: {manifest_path}")
    for entry in entries:
        name = str(entry["path"])
        file_path = safe_path(root, name)
        if not file_path.is_file() or file_path.is_symlink():
            fail(f"manifest member is not a regular file: {name}")
        if file_path.stat().st_size != int(entry["bytes"]):
            fail(f"manifest size mismatch: {name}")
        if sha256_file(file_path) != entry["sha256"]:
            fail(f"manifest hash mismatch: {name}")
        if candidate_mode(root, name, tracked_modes, has_git) != entry["mode"]:
            fail(f"manifest mode mismatch: {name}")
    if manifest.get("path_count") != len(entries):
        fail(f"manifest path_count mismatch: {manifest_path}")
    return manifest


def verify_content_manifests(root: Path, has_git: bool, mode: str) -> None:
    names = {name for name, _path in public_files(root, has_git)}
    tracked_modes = candidate_modes(root, has_git)
    if SOURCE_MANIFEST_PATH not in names:
        fail("SOURCE_MANIFEST.json is absent")
    if mode == "source-archive":
        source_expected = names - {SOURCE_MANIFEST_PATH}
        verify_entry_manifest(
            root,
            SOURCE_MANIFEST_PATH,
            source_expected,
            has_git,
            tracked_modes,
        )
        return

    if TREE_MANIFEST_PATH not in names:
        fail("TREE_MANIFEST.json is absent")
    source_expected = names - {SOURCE_MANIFEST_PATH, TREE_MANIFEST_PATH} - SEAL_PATHS
    verify_entry_manifest(
        root,
        SOURCE_MANIFEST_PATH,
        source_expected,
        has_git,
        tracked_modes,
    )
    verify_entry_manifest(
        root,
        TREE_MANIFEST_PATH,
        names - {TREE_MANIFEST_PATH},
        has_git,
        tracked_modes,
    )


def parse_sha256sums(path: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line:
            continue
        parts = line.split("  ", 1)
        if len(parts) != 2 or not re.fullmatch(r"[0-9a-f]{64}", parts[0]):
            fail(f"invalid SHA256SUMS line: {line!r}")
        if parts[1] in result:
            fail(f"duplicate SHA256SUMS name: {parts[1]}")
        result[parts[1]] = parts[0]
    return result


def verify_provenance_bindings(
    root: Path, statement: Any, attachment_sums: dict[str, str]
) -> None:
    """Check every digest the provenance statement asserts.

    A subject names a release attachment, so the inventory decides its bytes. A
    dependency either names a tracked path, in which case that file decides its
    bytes, or it carries the logical-evidence scheme for a record held outside
    the tree, which this gate cannot resolve and does not guess at.
    """
    subjects = statement.get("subject")
    if not isinstance(subjects, list) or not subjects:
        fail("provenance carries no subject")
    for subject in subjects:
        name = str(subject["name"])
        if name not in attachment_sums:
            fail(f"provenance subject is not an inventoried attachment: {name}")
        if str(subject["digest"]["sha256"]) != attachment_sums[name]:
            fail(f"provenance subject digest differs from the inventory: {name}")

    dependencies = statement["predicate"]["buildDefinition"]["resolvedDependencies"]
    if not isinstance(dependencies, list) or not dependencies:
        fail("provenance carries no resolved dependency")
    for dependency in dependencies:
        uri = str(dependency.get("uri", ""))
        if uri.startswith("logical-evidence:"):
            continue
        tracked = safe_path(root, uri)
        if not tracked.is_file():
            fail(f"provenance dependency names no tracked file: {uri}")
        if sha256_file(tracked) != str(dependency["digest"]["sha256"]):
            fail(f"provenance dependency digest differs from the file: {uri}")


def verify_release_package(
    root: Path,
    mode: str,
    proof: Path | None,
    source_archive: Path | None,
) -> None:
    if mode == "source-archive":
        return
    required_json = [
        "release/v1.1/PROOF_MANIFEST.json",
        "release/v1.1/PUBLIC_INPUTS.json",
        "release/v1.1/SBOM.spdx.json",
        ATTACHMENTS_PATH,
    ]
    for name in required_json:
        strict_json(safe_path(root, name))
    provenance = safe_path(root, "release/v1.1/PROVENANCE.intoto.jsonl")
    lines = [line for line in provenance.read_text(encoding="utf-8").splitlines() if line]
    if len(lines) != 1:
        fail("provenance must contain exactly one JSONL statement")
    try:
        statement = json.loads(lines[0])
    except json.JSONDecodeError as exc:
        fail(f"provenance JSONL parse failed: {exc}")

    attachments = strict_json(safe_path(root, ATTACHMENTS_PATH))
    entries = attachments.get("attachments")
    if not isinstance(entries, list) or not entries:
        fail("attachment inventory is empty")
    expected_sums: dict[str, str] = {}
    for entry in entries:
        name = str(entry["asset_name"])
        expected_sums[name] = str(entry["sha256"])
        source_path = entry.get("tracked_source_path")
        if source_path:
            tracked = safe_path(root, str(source_path))
            if tracked.stat().st_size != int(entry["bytes"]):
                fail(f"tracked attachment size mismatch: {name}")
            if sha256_file(tracked) != entry["sha256"]:
                fail(f"tracked attachment hash mismatch: {name}")
    expected_sums["statesync-gkr-v1.1-attachments.json"] = sha256_file(
        safe_path(root, ATTACHMENTS_PATH)
    )
    verify_provenance_bindings(root, statement, expected_sums)

    actual_sums = parse_sha256sums(safe_path(root, SHA256SUMS_PATH))
    if actual_sums != expected_sums:
        fail("SHA256SUMS and attachment inventory disagree")

    external = {str(entry["role"]): entry for entry in entries if not entry.get("tracked_source_path")}
    if proof is not None:
        record = external.get("public-proof")
        if record is None or proof.stat().st_size != int(record["bytes"]) or sha256_file(proof) != record["sha256"]:
            fail("proof attachment inventory mismatch")
    if source_archive is not None:
        archive = source_archive.resolve(strict=True)
        record = external.get("deterministic-source-archive")
        if record is None or archive.stat().st_size != int(record["bytes"]) or sha256_file(archive) != record["sha256"]:
            fail("source archive inventory mismatch")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--mode",
        choices=("auto", "worktree", "clean-history", "source-archive", "pull-request"),
        default="auto",
    )
    parser.add_argument("--require-proof", action="store_true")
    parser.add_argument("--proof", type=Path)
    parser.add_argument("--source-archive", type=Path)
    parser.add_argument("--require-no-remotes", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = repository_root()
    has_git = (root / ".git").exists()
    mode = args.mode
    if mode == "auto":
        mode = "clean-history" if has_git and not git(root, "status", "--porcelain") else ("worktree" if has_git else "source-archive")
    if mode in ("worktree", "clean-history", "pull-request") and not has_git:
        fail(f"{mode} mode requires .git")
    if mode == "source-archive" and has_git:
        fail("source-archive mode requires an archive without .git")
    if mode == "clean-history" and git(root, "status", "--porcelain"):
        fail("clean-history mode requires a clean tree")
    if args.require_no_remotes and has_git and git(root, "remote").strip():
        fail("clean-history candidate must have no remotes")

    manifest_path = safe_path(root, MANIFEST_PATH)
    allowlist_path = safe_path(root, ALLOWLIST_PATH)
    if sha256_file(manifest_path) != MANIFEST_SHA256:
        fail("protected manifest file hash mismatch")
    if sha256_file(allowlist_path) != ALLOWLIST_SHA256:
        fail("frozen allowlist file hash mismatch")
    manifest = strict_json(manifest_path)
    allowlist = strict_json(allowlist_path)

    protected = verify_protected(root, manifest, allowlist, has_git)
    try:
        license_distribution.verify_distribution(root, require_sbom=mode != "source-archive")
    except (ValueError, KeyError, TypeError) as exc:
        fail(f"licensing distribution mismatch: {exc}")
    print("source-consistency=78-unchanged-protected-files-plus-exact-Cargo-license-field")
    print("current-identity-source-manifest=" + license_distribution.CURRENT_SOURCE_SHA256)
    print("historical-identity-source-manifest=" + license_distribution.BASE_SOURCE_SHA256)
    print("current-compiled-identity=NOT_REPRODUCED")
    print("proof-scope=historical-v1.1-program-only")
    verify_frozen_baseline(root, has_git)
    verify_glossary(root, allowlist)
    verify_sensitive_and_new_identifiers(root, protected, manifest, allowlist, has_git)
    if mode == "pull-request":
        # A contributor change legitimately alters ordinary file hashes, so the
        # full-tree content manifests and the release-package inventory are
        # checked when the change lands on the release line, not per pull
        # request. The frozen protected surface, the glossary, and every
        # sensitive-content check above still gate each pull request. Path
        # membership is still compared against the tree manifest so additions
        # and removals are visible, and a new file under .github/ that the
        # manifest does not list is refused outright.
        tree_names = {
            str(entry["path"])
            for entry in strict_json(safe_path(root, TREE_MANIFEST_PATH)).get("entries", [])
        }
        current_names = {name for name, _path in public_files(root, has_git)}
        added = sorted(current_names - tree_names - {TREE_MANIFEST_PATH})
        removed = sorted(tree_names - current_names)
        for name in added:
            if name.startswith(".github/"):
                fail(f"pull request adds an unmanifested automation file: {name}")
        if added:
            print(f"paths-added={len(added)}: " + ", ".join(added[:20]))
        if removed:
            print(f"paths-removed={len(removed)}: " + ", ".join(removed[:20]))
        print(f"mode={mode}")
        print(f"protected-paths={len(protected)}")
        print("public-surface=PASS")
        return 0
    verify_content_manifests(root, has_git, mode)
    verify_proof(root, manifest, args.require_proof, args.proof)
    verify_release_package(root, mode, args.proof, args.source_archive)

    print(f"mode={mode}")
    print(f"protected-paths={len(protected)}")
    print(f"protected-path-set-sha256={PROTECTED_PATH_SET_SHA256}")
    print(f"legacy-occurrences={LEGACY_OCCURRENCES}")
    print(f"protected-surface-manifest-sha256={MANIFEST_SHA256}")
    print(f"frozen-source-allowlist-sha256={ALLOWLIST_SHA256}")
    print(f"superseded-baseline-sha256={FROZEN_BASELINE_SHA256}")
    print(f"superseded-baseline-last-valid-commit={FROZEN_BASELINE_LAST_VALID_COMMIT}")
    print("public-surface=PASS")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except VerificationError as exc:
        print(f"public-surface=FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
