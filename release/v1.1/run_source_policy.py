"""Run the base verifier, helper and wrapper as one pull-request authority.

Release lines live in release/vMAJOR.MINOR/. The newest line whose directory
holds the complete policy set (verify.py, license_distribution.py and this
wrapper) is the live gate. A pull request is judged by the base branch's
newest policy set. The one exception opens the next identity line: when a pull
request adds the immediate successor line and leaves every existing release
directory byte-identical to the base, the successor's own verifier judges it.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Iterable

BOOTSTRAP_COMMIT = "16754254c52a42f2444f1ff2ed7115a23a6c84f1"
POLICY_FILES = ("verify.py", "license_distribution.py", "run_source_policy.py")
LINE_DIRECTORY = re.compile(r"v(\d+)\.(\d+)")
Line = tuple[int, int]


def git(root: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "-C", str(root), *args], capture_output=True, check=check)


def line_paths(line: Line) -> tuple[str, ...]:
    return tuple(f"release/v{line[0]}.{line[1]}/{name}" for name in POLICY_FILES)


def complete_lines(names: Iterable[str]) -> list[Line]:
    """Release lines whose directory holds every policy file, oldest first."""
    found: dict[Line, set[str]] = {}
    for name in names:
        parts = name.split("/")
        if len(parts) != 3 or parts[0] != "release" or parts[2] not in POLICY_FILES:
            continue
        match = LINE_DIRECTORY.fullmatch(parts[1])
        if match:
            found.setdefault((int(match[1]), int(match[2])), set()).add(parts[2])
    return sorted(line for line, files in found.items() if files == set(POLICY_FILES))


def is_successor(newer: Line, older: Line) -> bool:
    return newer in ((older[0], older[1] + 1), (older[0] + 1, 0))


def tree_names(root: Path) -> list[str]:
    release = root / "release"
    if not release.is_dir():
        return []
    return [path.relative_to(root).as_posix() for path in release.glob("*/*") if path.is_file()]


def release_directories(names: Iterable[str]) -> list[str]:
    return sorted({"/".join(name.split("/")[:2]) for name in names if name.count("/") >= 2})


def require_frozen(root: Path, base: str, directories: list[str]) -> None:
    """Every existing release directory must equal the base, file for file."""
    changed = git(root, "diff", "--name-only", base, "--", *directories).stdout.strip()
    added = git(root, "ls-files", "--others", "--exclude-standard", "--", *directories).stdout.strip()
    if changed or added:
        raise ValueError("a successor line must leave every existing release directory byte-identical to the base")


def run_verifier(root: Path, line: Line, mode: str, env: dict[str, str]) -> int:
    verifier = root / line_paths(line)[0]
    return subprocess.run([sys.executable, "-B", str(verifier), "--mode", mode], cwd=root, env=env).returncode


def run_policy(root: Path, event: str, base_ref: str, repository: str, head_repository: str, head_ref: str) -> int:
    with tempfile.TemporaryDirectory(prefix="ssgkr-source-authority-") as scratch:
        env = dict(os.environ)
        env["PYTHONPYCACHEPREFIX"] = str(Path(scratch) / "bytecode")
        head_lines = complete_lines(tree_names(root))
        if not head_lines:
            raise ValueError("the tree carries no complete release policy line")
        if event != "pull_request":
            return run_verifier(root, head_lines[-1], "clean-history", env)

        git(root, "fetch", "--depth=1", "origin", base_ref)
        base = git(root, "rev-parse", "FETCH_HEAD").stdout.decode().strip()
        base_names = git(root, "ls-tree", "-r", "--name-only", base, "--", "release").stdout.decode().splitlines()
        base_lines = complete_lines(base_names)
        if not base_lines:
            # The only self-policy bootstrap is the reviewed first
            # distribution from this exact signed, parentless empty root.
            empty = not git(root, "ls-tree", "-r", "--name-only", base).stdout.strip()
            parent_line = git(root, "rev-list", "--parents", "-n", "1", base).stdout.decode().split()
            if base != BOOTSTRAP_COMMIT or not empty or parent_line != [base] or repository != head_repository or head_ref != "release/bsl-distribution":
                raise ValueError("base verifier/helper/wrapper set is incomplete outside the exact initial bootstrap")
            print("source-policy-authority=reviewed-first-distribution-on-exact-empty-bootstrap", flush=True)
            return run_verifier(root, head_lines[-1], "pull-request", env)

        newest_base, newest_head = base_lines[-1], head_lines[-1]
        if newest_head == newest_base:
            paths = line_paths(newest_base)
            saved = {name: (root / name).read_bytes() for name in paths}
            try:
                for name in paths:
                    (root / name).write_bytes(git(root, "show", f"{base}:{name}").stdout)
                print("source-policy-authority=base-verifier-helper-and-wrapper", flush=True)
                return run_verifier(root, newest_base, "pull-request", env)
            finally:
                for name, data in saved.items():
                    (root / name).write_bytes(data)
        if is_successor(newest_head, newest_base):
            require_frozen(root, base, release_directories(base_names))
            print("source-policy-authority=successor-line-with-existing-release-directories-frozen", flush=True)
            return run_verifier(root, newest_head, "pull-request", env)
        raise ValueError("the pull request removes, skips or rewinds a release policy line")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path)
    parser.add_argument("--event", required=True)
    parser.add_argument("--base-ref", default="main")
    parser.add_argument("--repository", default="")
    parser.add_argument("--head-repository", default="")
    parser.add_argument("--head-ref", default="")
    args = parser.parse_args()
    root = args.root.resolve(strict=True) if args.root else Path(__file__).resolve().parents[2]
    return run_policy(root, args.event, args.base_ref, args.repository, args.head_repository, args.head_ref)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        print(f"source policy failed: {exc}", file=sys.stderr)
        raise SystemExit(1)
