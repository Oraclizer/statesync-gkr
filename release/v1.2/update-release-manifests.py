#!/usr/bin/env python3
"""Regenerate deterministic v1.2 source, SBOM, attachment, and tree metadata."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
SOURCE_MANIFEST = "release/v1.2/SOURCE_MANIFEST.json"
TREE_MANIFEST = "release/v1.2/TREE_MANIFEST.json"
SBOM = "release/v1.2/SBOM.spdx.json"
PROVENANCE = "release/v1.2/PROVENANCE.intoto.jsonl"
ATTACHMENTS = "release/v1.2/ATTACHMENTS.json"
SHA256SUMS = "release/v1.2/SHA256SUMS"
PROTECTED_MANIFEST = "release/v1.2/PROTECTED_SOURCE_MANIFEST.json"
IDENTITY_RECORD = "release/v1.2/IDENTITY_DISTRIBUTION.json"
ATTACHMENT_INVENTORY_ASSET = "statesync-gkr-v1.2-attachments.json"
EXTERNAL_FIELDS = ("distribution_version", "license", "citation_version", "citation_doi")
SEAL_PATHS = {
    TREE_MANIFEST,
    SBOM,
    PROVENANCE,
    ATTACHMENTS,
    SHA256SUMS,
}


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def write_json(path: Path, value: dict[str, Any]) -> None:
    path.write_text(
        json.dumps(value, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )


def git(*args: str) -> str:
    process = subprocess.run(
        ["git", "-C", str(ROOT), *args],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        encoding="utf-8",
    )
    if process.returncode != 0:
        raise RuntimeError(process.stderr.strip())
    return process.stdout


def candidate_names() -> set[str]:
    names = {
        name
        for name in git("ls-files", "--cached", "--others", "--exclude-standard", "-z").split("\0")
        if name
    }
    return {name for name in names if (ROOT / name).is_file()}


def tracked_modes() -> dict[str, str]:
    result: dict[str, str] = {}
    for record in git("ls-files", "-s", "-z").split("\0"):
        if not record:
            continue
        metadata, name = record.split("\t", 1)
        result[name] = metadata.split(" ", 1)[0]
    return result


def role(name: str) -> str:
    if name.startswith(".github/"):
        return "repository-automation-or-community"
    if name.startswith(("release/v1.0/", "release/v1.1/")):
        return "superseded-release-evidence-or-tooling"
    if name.startswith("release/v1.2/"):
        return "release-evidence-or-tooling"
    if name.startswith("formal/") or name.startswith("verif/"):
        return "formal-source-or-replay-metadata"
    if name.startswith("tests/") or name.startswith("examples/"):
        return "test-vector-or-example"
    if name.startswith("docs/") or name.endswith(".md"):
        return "documentation"
    return "repository-source-or-metadata"


def entries(names: set[str]) -> list[dict[str, Any]]:
    modes = tracked_modes()
    result: list[dict[str, Any]] = []
    for name in sorted(names, key=lambda value: value.encode("utf-8")):
        path = ROOT / name
        result.append(
            {
                "path": name,
                "mode": modes.get(name, "100644"),
                "bytes": path.stat().st_size,
                "sha256": digest(path),
                "role": role(name),
            }
        )
    return result


def identity_fields(record: dict[str, Any]) -> dict[str, Any]:
    """Distribution and identity facts that the source manifest and provenance repeat."""
    return {
        "distribution_version": record["distribution_version"],
        "license": record["license"],
        "citation_version": record["citation"]["version"],
        "citation_doi": record["citation"]["doi"],
        "identity_source_sha256": record["identity_source"]["sha256"],
        "previous_line_identity_source_sha256": record["identity_source"]["previous_line_sha256"],
        "compiled_identity_reproduced": record["compiled_identity"]["reproduced"],
        "compiled_image_id": record["compiled_identity"]["image_id"],
        "proof_scope": record["proof"]["scope"],
    }


def update_source_manifest() -> str:
    names = candidate_names()
    expected = names - {SOURCE_MANIFEST, TREE_MANIFEST} - SEAL_PATHS
    manifest = load_json(ROOT / SOURCE_MANIFEST)
    # The manifest cannot embed the commit that will contain it, so the commit
    # binding is delegated to Git itself: the release tag resolves the exact
    # commit and tree for this content.
    manifest["status"] = "RELEASE_EVIDENCE"
    protected = load_json(ROOT / PROTECTED_MANIFEST)
    manifest["subject"].update({
        "protected_authority_commit": protected["subject"]["commit"],
        "protected_authority_tree": protected["subject"]["tree"],
        "protected_manifest_sha256": digest(ROOT / PROTECTED_MANIFEST),
        "protected_path_set_sha256": protected["tracked_path_set_sha256"],
    })
    record = load_json(ROOT / IDENTITY_RECORD)
    manifest["subject"].update(identity_fields(record))
    manifest["subject"]["current_git_commit"] = "BOUND_BY_GIT_TAG"
    manifest["subject"]["current_git_tree"] = "BOUND_BY_GIT_TAG"
    manifest["path_count"] = len(expected)
    manifest["entries"] = entries(expected)
    write_json(ROOT / SOURCE_MANIFEST, manifest)
    return digest(ROOT / SOURCE_MANIFEST)


def update_provenance(archive: Path, source_manifest_sha256: str) -> None:
    """Refresh every digest the statement carries.

    Each subject and each resolved dependency is bound to a source of truth:
    the built archive, the proof manifest, a tracked file named by the
    attachment inventory, or a tracked path used as the dependency uri. An
    entry with no such source is left alone and reported, so a stale digest
    cannot survive silently the way it does when only a few names are
    refreshed by hand.
    """
    path = ROOT / PROVENANCE
    statement = json.loads(path.read_text(encoding="utf-8").strip())

    record = load_json(ROOT / IDENTITY_RECORD)
    fields = identity_fields(record)
    statement["predicate"]["buildDefinition"]["externalParameters"].update({
        key: fields[key] for key in EXTERNAL_FIELDS
    })
    statement["predicate"]["buildDefinition"]["internalParameters"].update({
        key: value for key, value in fields.items()
        if key not in EXTERNAL_FIELDS
    })
    tracked_by_asset: dict[str, str] = {}
    for item in load_json(ROOT / ATTACHMENTS)["attachments"]:
        tracked = item.get("tracked_source_path")
        if tracked:
            tracked_by_asset[str(item["asset_name"])] = str(tracked)

    proof = record["proof"]
    known_by_asset = {str(proof["asset_name"]): str(proof["sha256"])}

    unresolved: list[str] = []
    for subject in statement["subject"]:
        name = str(subject["name"])
        if name.endswith("-source.tar.gz"):
            subject["digest"]["sha256"] = digest(archive)
        elif name in known_by_asset:
            subject["digest"]["sha256"] = known_by_asset[name]
        elif name in tracked_by_asset:
            subject["digest"]["sha256"] = digest(ROOT / tracked_by_asset[name])
        else:
            unresolved.append(f"subject {name}")

    for dependency in statement["predicate"]["buildDefinition"]["resolvedDependencies"]:
        uri = str(dependency.get("uri", ""))
        candidate = ROOT / uri
        if uri == SOURCE_MANIFEST:
            dependency["digest"]["sha256"] = source_manifest_sha256
        elif not uri.startswith("logical-evidence:") and candidate.is_file():
            dependency["digest"]["sha256"] = digest(candidate)
        elif not uri.startswith("logical-evidence:"):
            unresolved.append(f"dependency {uri}")

    # Optional timestamps from an earlier package must not describe this one.
    metadata = statement["predicate"]["runDetails"]["metadata"]
    metadata.pop("startedOn", None)
    metadata.pop("finishedOn", None)
    if unresolved:
        raise ValueError("provenance entries without a source of truth: " + ", ".join(unresolved))
    path.write_text(
        json.dumps(statement, separators=(",", ":"), ensure_ascii=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )


def update_sbom(archive: Path, source_entries: list[dict[str, Any]]) -> None:
    path = ROOT / SBOM
    value = load_json(path)
    archive_sha = digest(archive)
    version = load_json(ROOT / IDENTITY_RECORD)["distribution_version"]
    value["name"] = f"StateSync-GKR v{version} BSL source distribution SBOM"
    value["creationInfo"]["created"] = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    value["documentNamespace"] = f"https://oraclizer.io/spdx/statesync-gkr-v1.2/{archive_sha}"
    own_packages = {
        "statesync-gkr", "ssgkr-primitives", "ssgkr-sumcheck", "ssgkr-protocol",
        "ssgkr-compiler", "ssgkr-batching", "ssgkr-commitment",
        "ssgkr-verification", "ssgkr-wrap",
    }
    for package in value["packages"]:
        if package.get("name") in own_packages or package["SPDXID"] == "SPDXRef-Package-SourceArchive":
            package["licenseDeclared"] = "BUSL-1.1"
            package["licenseConcluded"] = "BUSL-1.1"
        if package["SPDXID"] == "SPDXRef-Package-SourceArchive":
            package["versionInfo"] = version
            package["checksums"] = [{"algorithm": "SHA256", "checksumValue": archive_sha}]
    all_entries = list(source_entries)
    source_path = ROOT / SOURCE_MANIFEST
    all_entries.append(
        {
            "path": SOURCE_MANIFEST,
            "mode": "100644",
            "bytes": source_path.stat().st_size,
            "sha256": digest(source_path),
            "role": "release-source-manifest",
        }
    )
    all_entries.sort(key=lambda item: str(item["path"]).encode("utf-8"))
    files: list[dict[str, Any]] = []
    relationships = [
        item
        for item in value.get("relationships", [])
        if not str(item.get("spdxElementId", "")).startswith("SPDXRef-File-")
        and not str(item.get("relatedSpdxElement", "")).startswith("SPDXRef-File-")
    ]
    for item in all_entries:
        name = str(item["path"])
        spdx_id = "SPDXRef-File-" + hashlib.sha256(name.encode("utf-8")).hexdigest()[:20]
        files.append(
            {
                "fileName": "./" + name,
                "SPDXID": spdx_id,
                "checksums": [{"algorithm": "SHA256", "checksumValue": item["sha256"]}],
                "licenseConcluded": "NOASSERTION",
                "licenseInfoInFiles": ["NOASSERTION"],
                "copyrightText": "NOASSERTION",
                "comment": item["role"],
            }
        )
        relationships.append(
            {
                "spdxElementId": "SPDXRef-Package-SourceArchive",
                "relationshipType": "CONTAINS",
                "relatedSpdxElement": spdx_id,
            }
        )
    value["files"] = files
    value["relationships"] = relationships
    write_json(path, value)


def update_attachments(archive: Path) -> None:
    path = ROOT / ATTACHMENTS
    value = load_json(path)
    value["status"] = "PREPARED_RELEASE_ASSETS"
    for item in value["attachments"]:
        item["status"] = "PREPARED_RELEASE_ASSET"
        if item["role"] == "deterministic-source-archive":
            item["bytes"] = archive.stat().st_size
            item["sha256"] = digest(archive)
        tracked = item.get("tracked_source_path")
        if tracked:
            tracked_path = ROOT / str(tracked)
            item["bytes"] = tracked_path.stat().st_size
            item["sha256"] = digest(tracked_path)
    value["attachment_count"] = len(value["attachments"])
    write_json(path, value)

    sums = {str(item["asset_name"]): str(item["sha256"]) for item in value["attachments"]}
    sums[ATTACHMENT_INVENTORY_ASSET] = digest(path)
    (ROOT / SHA256SUMS).write_text(
        "".join(f"{checksum}  {name}\n" for name, checksum in sorted(sums.items())),
        encoding="utf-8",
        newline="\n",
    )


def update_tree_manifest(source_manifest_sha256: str) -> None:
    names = candidate_names()
    expected = names - {TREE_MANIFEST}
    manifest = load_json(ROOT / TREE_MANIFEST)
    manifest["status"] = "RELEASE_EVIDENCE"
    manifest["subject"]["git_commit"] = "BOUND_BY_GIT_TAG"
    manifest["subject"]["git_tree"] = "BOUND_BY_GIT_TAG"
    manifest["subject"]["history_mode"] = "CLEAN_SOURCE_ARCHIVE_WITH_FULL_TREE_MANIFEST"
    manifest["subject"]["source_manifest_sha256"] = source_manifest_sha256
    manifest["subject"]["protected_manifest_sha256"] = digest(ROOT / PROTECTED_MANIFEST)
    manifest["path_count"] = len(expected)
    manifest["candidate_path_count_including_self"] = len(expected) + 1
    manifest["entries"] = entries(expected)
    write_json(ROOT / TREE_MANIFEST, manifest)


def finalize(archive: Path) -> None:
    archive = archive.resolve(strict=True)
    source_manifest_sha256 = digest(ROOT / SOURCE_MANIFEST)
    source = load_json(ROOT / SOURCE_MANIFEST)
    update_provenance(archive, source_manifest_sha256)
    update_sbom(archive, list(source["entries"]))
    update_attachments(archive)
    update_tree_manifest(source_manifest_sha256)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("source", "finalize"))
    parser.add_argument("--archive", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.command == "source":
        print(f"source-manifest-sha256={update_source_manifest()}")
        return 0
    if args.archive is None:
        raise ValueError("--archive is required for finalize")
    finalize(args.archive)
    print(f"source-manifest-sha256={digest(ROOT / SOURCE_MANIFEST)}")
    print(f"tree-manifest-sha256={digest(ROOT / TREE_MANIFEST)}")
    print(f"attachments-sha256={digest(ROOT / ATTACHMENTS)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
