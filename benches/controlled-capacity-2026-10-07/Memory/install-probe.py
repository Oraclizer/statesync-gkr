#!/usr/bin/env python3
"""Append a cfg(test) observer to an explicit isolated copy, never canonical source."""
import argparse
import hashlib
import json
from pathlib import Path

BASE_REDUCE_SHA256 = "0055b781aff0e0da98b9721bf34e93a9dae000f8ce9c1f469fb45cde822ecefb"
MARKER = b'\n// Benchmark-only observer; production reduction above remains byte-exact.\n#[cfg(test)]\n#[path = "memory_probe.rs"]\nmod memory_probe;\n'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args()
    source = args.source.resolve(strict=True)
    owner = Path(__file__).resolve().parent
    # An explicit isolated target and exact baseline are mandatory. The known
    # canonical name is forbidden on Windows and Linux alike, without exceptions.
    if "statesync-gkr-public" in str(source).lower():
        raise SystemExit("canonical source target refused")
    if source == owner or owner in source.parents:
        raise SystemExit("source must be a separate isolated source copy")
    receipt = args.receipt.resolve()
    if owner != receipt.parent and owner not in receipt.parents:
        raise SystemExit("receipt must stay inside the Memory owner root")
    reduce = source / "crates/protocol/src/reduce.rs"
    manifest = source / "crates/protocol/Cargo.toml"
    target_probe = reduce.with_name("memory_probe.rs")
    original_reduce = reduce.read_bytes()
    original_manifest = manifest.read_bytes()
    if sha(original_reduce) != BASE_REDUCE_SHA256:
        raise SystemExit("exact reduce.rs baseline mismatch; no writes performed")
    if target_probe.exists() or receipt.exists():
        raise SystemExit("probe or receipt already exists; refuse silent replacement")
    if b"[dev-dependencies]" in original_manifest:
        raise SystemExit("baseline protocol manifest gained dev-dependencies; inspect before adapting")
    helper = (owner / "allocator-helper").as_posix()
    dependency_patch = ("\n# Isolated benchmark-only dependencies; normal production graph unchanged.\n"
                        "[dev-dependencies]\n"
                        f'ssgkr-memory-allocator = {{ path = {json.dumps(helper)} }}\n'
                        "sha2.workspace = true\nserde_json.workspace = true\n").encode()
    probe_bytes = (owner / "memory_probe.rs").read_bytes()
    expected_reduce = original_reduce + MARKER
    expected_manifest = original_manifest + dependency_patch
    target_probe.write_bytes(probe_bytes)
    manifest.write_bytes(expected_manifest)
    reduce.write_bytes(expected_reduce)
    assert reduce.read_bytes()[:len(original_reduce)] == original_reduce
    assert manifest.read_bytes()[:len(original_manifest)] == original_manifest
    result = {
        "schema_version": "ssgkr.memory-probe.install.v1",
        "status": "INSTALLED_NOT_COMPILED",
        "source": str(source),
        "baseline_reduce_sha256": sha(original_reduce),
        "patched_reduce_sha256": sha(reduce.read_bytes()),
        "baseline_manifest_sha256": sha(original_manifest),
        "patched_manifest_sha256": sha(manifest.read_bytes()),
        "probe_sha256": sha(probe_bytes),
        "allocator_helper_sha256": sha((owner / "allocator-helper/src/lib.rs").read_bytes()),
        "original_reduce_prefix_byte_exact": True,
        "production_kernel_arithmetic_mutations": 0,
        "changed_paths": ["crates/protocol/src/reduce.rs", "crates/protocol/Cargo.toml"],
        "added_paths": ["crates/protocol/src/memory_probe.rs"],
        "patch_kind": "cfg(test) child plus dev-dependencies only",
        "compile_and_runtime_verified": False,
    }
    receipt.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
