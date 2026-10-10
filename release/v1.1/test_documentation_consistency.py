#!/usr/bin/env python3
"""Hold the prose to the machine-readable authorities it describes.

Counts and asset names written into prose drift silently: nothing rebuilds
them, and the release verifier checks the bytes of a document rather than
whether its sentences are still true. Every check here compares a statement a
document makes against the file that decides it.

Frozen directories are excluded. A previous line's record is expected to name
that line's values, and rewriting it would fail the superseded-baseline digest.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


REPO = Path(__file__).resolve().parents[2]
RELEASE = "release/v1.1"
FROZEN_PREFIXES = ("release/v1.0/",)

NUMBER_WORDS = {
    "one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
    "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10,
}

# A statement is a total claim only when one of these stands near it. Without
# one, a number before "sessions" is a subset claim, such as naming the four
# sessions that carry one result, and this file does not police those.
TOTAL_MARKERS = ("registers", "registered", "all ", "build to completion")


def tracked(pattern: str) -> list[str]:
    out = subprocess.run(
        ["git", "-C", str(REPO), "ls-files", "-z", pattern],
        check=True,
        stdout=subprocess.PIPE,
        encoding="utf-8",
    ).stdout
    return [name for name in out.split("\0") if name]


def live_documents() -> list[tuple[str, str]]:
    names = tracked("*.md") + tracked("*.cff")
    result = []
    for name in sorted(names):
        if name.startswith(FROZEN_PREFIXES):
            continue
        result.append((name, (REPO / name).read_text(encoding="utf-8")))
    return result


def load_json(relative: str) -> dict:
    return json.loads((REPO / relative).read_text(encoding="utf-8"))


def verifier_constant(name: str) -> int:
    source = (REPO / RELEASE / "verify.py").read_text(encoding="utf-8")
    match = re.search(rf"^{name} = (\d+)$", source, re.M)
    assert match, f"{name} is not a plain integer constant in the verifier"
    return int(match.group(1))


def check_session_total() -> int:
    roots = (REPO / "formal/isabelle/ROOTS").read_text(encoding="utf-8").split()
    expected = len(roots)
    assert expected > 0, "ROOTS registers no session"

    pattern = re.compile(
        r"\b(" + "|".join(NUMBER_WORDS) + r"|\d+)\s+(?:[A-Za-z/.-]+\s+){0,3}?sessions?\b",
        re.I,
    )
    checked = 0
    for name, text in live_documents():
        for match in pattern.finditer(text):
            window = text[max(0, match.start() - 60) : match.end() + 60].lower()
            if not any(marker in window for marker in TOTAL_MARKERS):
                continue
            token = match.group(1).lower()
            stated = NUMBER_WORDS.get(token, None)
            if stated is None:
                stated = int(token)
            assert stated == expected, (
                f"{name} states {match.group(0)!r} while ROOTS registers {expected}"
            )
            checked += 1
    assert checked >= 3, "session-total statements are no longer being found"
    return checked


def check_every_theory_is_registered() -> int:
    theories = tracked("formal/isabelle/*/*.thy")
    assert theories, "no theory files are tracked"
    for name in theories:
        path = Path(name)
        root = REPO / path.parent / "ROOT"
        assert root.is_file(), f"{path.parent} has no ROOT"
        # A whole-word match. A substring match would accept a ROOT entry that
        # merely starts with this name, so a renamed or mistyped entry would
        # still look registered.
        registered = re.search(
            rf"(?<![A-Za-z0-9_]){re.escape(path.stem)}(?![A-Za-z0-9_])",
            root.read_text(encoding="utf-8"),
        )
        assert registered, (
            f"{name} is not registered in {path.parent}/ROOT, so it is never built"
        )
    return len(theories)


def check_legacy_occurrence_count() -> int:
    expected = verifier_constant("LEGACY_OCCURRENCES")
    allowlist = load_json(f"{RELEASE}/FROZEN_SOURCE_ALLOWLIST.json")
    assert allowlist["legacy_occurrence_count"] == expected
    assert len(allowlist["occurrences"]) == expected

    pattern = re.compile(r"\b(\d+)\s+(?:[A-Za-z-]+\s+){0,2}?occurrences?\b")
    checked = 0
    for name, text in live_documents():
        for match in pattern.finditer(text):
            assert int(match.group(1)) == expected, (
                f"{name} states {match.group(0)!r} while the verifier enforces {expected}"
            )
            checked += 1
    assert checked >= 1, "occurrence-count statements are no longer being found"
    return checked


def check_protected_path_count() -> int:
    manifest = load_json(f"{RELEASE}/PROTECTED_SOURCE_MANIFEST.json")
    expected = len(manifest["entries"])
    assert manifest["tracked_path_count"] == expected

    # Only statements about the protected surface. A bare "path" is an
    # ordinary word and appears throughout the design records.
    markers = ("protected", "bound to", "fixes the complete")
    pattern = re.compile(r"\b(\d+)[ -](?:tracked[ -]|complete[ -])?paths?\b")
    checked = 0
    for name, text in live_documents():
        for match in pattern.finditer(text):
            window = text[max(0, match.start() - 80) : match.end() + 80].lower()
            if not any(marker in window for marker in markers):
                continue
            assert int(match.group(1)) == expected, (
                f"{name} states {match.group(0)!r} while the manifest fixes {expected}"
            )
            checked += 1
    assert checked >= 1, "protected-path statements are no longer being found"
    return checked


def check_current_proof_asset() -> int:
    current = load_json(f"{RELEASE}/PROOF_MANIFEST.json")["proof"]["asset_name"]
    pattern = re.compile(r"statesync-gkr-v[0-9.]+-proof\.cbor")
    checked = 0
    for name, text in live_documents():
        for match in pattern.finditer(text):
            assert match.group(0) == current, (
                f"{name} names {match.group(0)} while the current attachment is {current}"
            )
            checked += 1
    assert checked >= 1, "proof-asset references are no longer being found"
    return checked


def check_release_metadata() -> None:
    protected_path = REPO / RELEASE / "PROTECTED_SOURCE_MANIFEST.json"
    protected = load_json(f"{RELEASE}/PROTECTED_SOURCE_MANIFEST.json")
    subject = load_json(f"{RELEASE}/SOURCE_MANIFEST.json")["subject"]
    expected = {
        "protected_authority_commit": protected["subject"]["commit"],
        "protected_authority_tree": protected["subject"]["tree"],
        "protected_manifest_sha256": hashlib.sha256(protected_path.read_bytes()).hexdigest(),
        "protected_path_set_sha256": protected["tracked_path_set_sha256"],
    }
    for key, value in expected.items():
        assert subject[key] == value, f"source manifest has a stale {key}"
    citation = (REPO / "CITATION.cff").read_text(encoding="utf-8")
    version = re.search(r'^version: "([^"]+)"$', citation, re.M)
    assert version, "citation has no component version"
    sbom = load_json(f"{RELEASE}/SBOM.spdx.json")
    source = [p for p in sbom["packages"] if p["SPDXID"] == "SPDXRef-Package-SourceArchive"]
    assert len(source) == 1, "SBOM must describe one source archive"
    assert source[0]["versionInfo"] == version.group(1), "SBOM and citation versions differ"


def main() -> int:
    check_release_metadata()
    sessions = check_session_total()
    theories = check_every_theory_is_registered()
    occurrences = check_legacy_occurrence_count()
    paths = check_protected_path_count()
    assets = check_current_proof_asset()
    print(
        "documentation-consistency=PASS "
        f"session-statements={sessions} theories={theories} "
        f"occurrence-statements={occurrences} path-statements={paths} "
        f"proof-asset-references={assets}"
    )
    return 0


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    raise SystemExit(main())
