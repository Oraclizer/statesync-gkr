#!/usr/bin/env python3
"""Fail closed if dependency update visibility or merge separation drifts."""

from __future__ import annotations

import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
DEPENDABOT = ROOT / ".github" / "dependabot.yml"
POLICY = ROOT / "release" / "v1.1" / "DEPENDENCY_UPDATE_POLICY.json"
WORKFLOWS = ROOT / ".github" / "workflows"


def fail(message: str) -> None:
    raise SystemExit(f"dependency-update-policy=FAIL: {message}")


def block(text: str, name: str) -> str:
    pattern = re.compile(
        rf"(?ms)^      {re.escape(name)}:\n(?P<body>.*?)(?=^      [a-z0-9-]+:\n|^  - package-ecosystem:|\Z)"
    )
    match = pattern.search(text)
    if match is None:
        fail(f"missing Dependabot group {name}")
    return match.group("body")


def main() -> int:
    dependabot = DEPENDABOT.read_text(encoding="utf-8").replace("\r\n", "\n")
    policy = json.loads(POLICY.read_text(encoding="utf-8"))

    if re.search(r"(?m)^\s*ignore\s*:", dependabot):
        fail("Dependabot ignore rules suppress update visibility")
    if policy["visibility"]["ignore_rule_count"] != 0:
        fail("policy receipt declares a nonzero ignore-rule count")

    proof = block(dependabot, "proof-crypto")
    routine_cargo = block(dependabot, "routine-cargo")
    routine_actions = block(dependabot, "routine-actions")
    patterns = policy["groups"]["proof-crypto"]["patterns"]
    for dependency in patterns:
        quoted = f'- "{dependency}"'
        if quoted not in proof:
            fail(f"proof-crypto group misses {dependency}")
        if quoted not in routine_cargo.split("update-types:", 1)[0]:
            fail(f"routine-cargo exclusions miss {dependency}")

    for update_type in ("minor", "patch"):
        marker = f"- {update_type}"
        if marker not in routine_cargo or marker not in routine_actions:
            fail(f"routine groups miss {update_type} updates")

    for workflow in WORKFLOWS.glob("*.yml"):
        content = workflow.read_text(encoding="utf-8").lower()
        if "dependabot" in content and any(
            marker in content
            for marker in ("--auto", "enablepullrequestautomerge", "automerge")
        ):
            fail(f"automatic Dependabot merge surface exists: {workflow.name}")

    for group in policy["groups"].values():
        if group["automatic_merge"] is not False:
            fail("the dependency policy must disable automatic merge for every group")

    print(f"proof-crypto-patterns={len(patterns)}")
    print("dependabot-ignore-rules=0")
    print("automatic-merge-surfaces=0")
    print("dependency-update-policy=PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
