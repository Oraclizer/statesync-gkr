"""Run the base verifier, helper and wrapper as one pull-request authority."""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import sys
import tempfile

BOOTSTRAP_COMMIT = "16754254c52a42f2444f1ff2ed7115a23a6c84f1"
POLICY_PATHS = ("release/v1.1/verify.py", "release/v1.1/license_distribution.py", "release/v1.1/run_source_policy.py")


def git(root: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "-C", str(root), *args], capture_output=True, check=check)


def run_policy(root: Path, event: str, base_ref: str, repository: str, head_repository: str, head_ref: str) -> int:
    saved = {name: (root / name).read_bytes() for name in POLICY_PATHS}
    with tempfile.TemporaryDirectory(prefix="ssgkr-source-authority-") as scratch:
        env = dict(os.environ)
        env["PYTHONPYCACHEPREFIX"] = str(Path(scratch) / "bytecode")
        mode = "clean-history"
        try:
            if event == "pull_request":
                mode = "pull-request"
                git(root, "fetch", "--depth=1", "origin", base_ref)
                base = git(root, "rev-parse", "FETCH_HEAD").stdout.decode().strip()
                candidates = {name: git(root, "show", f"{base}:{name}", check=False) for name in POLICY_PATHS}
                present = [p.returncode == 0 for p in candidates.values()]
                if all(present):
                    for name, process in candidates.items():
                        (root / name).write_bytes(process.stdout)
                    print("source-policy-authority=base-verifier-helper-and-wrapper", flush=True)
                else:
                    # The only self-policy bootstrap is the reviewed first
                    # distribution from this exact signed, parentless empty root.
                    empty = not git(root, "ls-tree", "-r", "--name-only", base).stdout.strip()
                    parent_line = git(root, "rev-list", "--parents", "-n", "1", base).stdout.decode().split()
                    if any(present) or base != BOOTSTRAP_COMMIT or not empty or parent_line != [base] or repository != head_repository or head_ref != "release/bsl-distribution":
                        raise ValueError("base verifier/helper/wrapper set is incomplete outside the exact initial bootstrap")
                    print("source-policy-authority=reviewed-first-distribution-on-exact-empty-bootstrap", flush=True)
            process = subprocess.run([sys.executable, "-B", str(root / POLICY_PATHS[0]), "--mode", mode], cwd=root, env=env)
            return process.returncode
        finally:
            for name, data in saved.items():
                (root / name).write_bytes(data)


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
