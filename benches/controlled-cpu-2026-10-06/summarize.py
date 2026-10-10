#!/usr/bin/env python3
"""Validate and summarize the fixed CPU study without running GKR.

Python 3.11+, standard library only. Published replay and ordinary smoke
results have separate profiles. The three repeats are processes on one host,
not independent hardware replicas.
"""

from __future__ import annotations

import argparse
from collections import Counter
import csv
import hashlib
import io
import json
import math
import os
from pathlib import Path
import platform
import re
import statistics
import subprocess
import sys
import tomllib


SOURCE_SHA256 = "d22e2200378e21a40c254eab8df4d44dfea81f2806f02f0c9030636300d489e9"
DRIVER_SHA256 = "b2d5a631e8527bca90d22065ca3692da48863f236f306d5217e8e4528fa1c75c"
KINDS = ("membership", "nonmembership", "update")
DEPTHS = (24, 28, 32)
BATCH_PHASES = {"seq-prove", "parallel", "stream", "stream-parallel-witness"}
CURVE_WORKERS = (1, 2, 4, 8, 16, 32, 48, 96, 192)
CSV_FIELDS = (
    "record", "mode", "run", "kind", "depth", "phase", "workers",
    "batch", "sample", "elapsed_ns", "proof_bytes", "proof_sha256",
)
HASH_RE = re.compile(r"[0-9a-f]{64}")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def cell_key(cell: dict) -> tuple:
    return tuple(cell[name] for name in (
        "build_mode", "run", "kind", "depth", "phase", "workers", "batch"
    ))


def expected_cells(profile: str) -> dict[tuple, int]:
    expected = {}
    if profile == "smoke":
        for depth in DEPTHS:
            for kind in KINDS:
                expected[("native", 0, kind, depth, "prepared", 1, 1)] = 3
        return expected
    if profile != "full":
        raise ValueError("unknown measurement profile")
    for run in (1, 2, 3):
        for kind in KINDS:
            for phase in ("fresh", "prepared", "verify"):
                expected[("native", run, kind, 24, phase, 1, 1)] = 1000
            expected[("native", run, kind, 24, "seq-prove", 1, 768)] = 3
            for workers in CURVE_WORKERS:
                expected[("native", run, kind, 24, "parallel", workers, 768)] = 3
            for workers in (96, 192):
                for phase in ("stream", "stream-parallel-witness"):
                    expected[("native", run, kind, 24, phase, workers, 768)] = 3
        for depth in (28, 32):
            for kind in KINDS:
                for phase in ("prepared", "verify"):
                    expected[("native", run, kind, depth, phase, 1, 1)] = 1000
                for phase in ("parallel", "stream", "stream-parallel-witness"):
                    expected[("native", run, kind, depth, phase, 192, 768)] = 3
    return expected


def csv_rows(text: str) -> list[dict[str, str]]:
    reader = csv.DictReader(io.StringIO(text, newline=""))
    if tuple(reader.fieldnames or ()) != CSV_FIELDS:
        raise ValueError("driver CSV header differs from the fixed schema")
    rows = list(reader)
    for row in rows:
        if None in row or any(value is None for value in row.values()):
            raise ValueError("incomplete or extra CSV fields")
        for name, value in row.items():
            row[name] = value.strip()
    return rows


def positive_integer(value: str, name: str) -> int:
    if not re.fullmatch(r"[0-9]+", value):
        raise ValueError(f"non-integer {name}")
    number = int(value)
    if number <= 0:
        raise ValueError(f"non-positive {name}")
    return number


def parse_timing_text(text: str, source_label: str) -> dict:
    """Read one process CSV; suitable for in-memory archive subset checks."""
    rows = csv_rows(text)
    if any(row["record"] not in {"setup", "timing"} for row in rows):
        raise ValueError("unexpected record in a timing cell")
    timing = [row for row in rows if row["record"] == "timing"]
    setup = [row for row in rows if row["record"] == "setup"]
    if not timing or len(setup) != 1:
        raise ValueError("a cell requires timing rows and exactly one prepare row")
    first = timing[0]
    metadata_names = ("mode", "run", "kind", "depth", "phase", "workers", "batch")
    metadata = tuple(first[name] for name in metadata_names)
    if any(tuple(row[name] for name in metadata_names) != metadata for row in timing):
        raise ValueError("row metadata changes inside one process")
    phase = first["phase"]
    if phase not in BATCH_PHASES | {"fresh", "prepared", "verify"}:
        raise ValueError("unknown timing phase")
    if first["kind"] not in KINDS or int(first["depth"]) not in DEPTHS:
        raise ValueError("unknown kind or depth")
    if any(row["proof_bytes"] != "0" or row["proof_sha256"] for row in timing):
        raise ValueError("timing row carries unexpected proof metadata")
    sample_ids = [int(row["sample"]) for row in timing]
    if sample_ids != list(range(len(timing))):
        raise ValueError("sample IDs are missing, duplicated or out of order")
    durations = [positive_integer(row["elapsed_ns"], "elapsed_ns") for row in timing]
    setup_row = setup[0]
    same_setup_names = ("mode", "run", "kind", "depth", "workers")
    if any(setup_row[name] != first[name] for name in same_setup_names):
        raise ValueError("prepare metadata differs from its timing cell")
    if setup_row["phase"] != "prepare" or setup_row["sample"] != "0" or setup_row["batch"] != "1":
        raise ValueError("invalid prepare row")
    if setup_row["proof_bytes"] != "0" or setup_row["proof_sha256"]:
        raise ValueError("unexpected prepare proof metadata")
    mean = statistics.mean(durations)
    result = {
        "build_mode": first["mode"], "run": int(first["run"]),
        "kind": first["kind"], "depth": int(first["depth"]), "phase": phase,
        "workers": positive_integer(first["workers"], "workers"),
        "batch": positive_integer(first["batch"], "batch"),
        "sample_count": len(timing),
        "sample_unit": "batch" if phase in BATCH_PHASES else "request",
        "reusable_prepare_excluded_ns": positive_integer(setup_row["elapsed_ns"], "prepare_ns"),
        "median_ns": statistics.median(durations), "mean_ns": mean,
        "min_ns": min(durations), "max_ns": max(durations),
        "cv_percent": 100 * statistics.pstdev(durations) / mean,
        "raw_csv": source_label, "raw_csv_sha256": sha256_bytes(text.encode("utf-8")),
        "sample_ids": sample_ids, "durations_ns": durations,
    }
    if result["sample_unit"] == "request" and len(durations) >= 1000:
        ordered = sorted(durations)
        for name, fraction in (("p50_ns", .50), ("p95_ns", .95), ("p99_ns", .99)):
            result[name] = ordered[int((len(ordered) - 1) * fraction)]
    elif result["sample_unit"] == "batch":
        result["proofs_per_second_at_median_batch"] = result["batch"] * 1_000_000_000 / result["median_ns"]
        result["measured_proofs"] = result["batch"] * result["sample_count"]
    return result


def parse_time_text(text: str) -> tuple[int, int]:
    rss = re.findall(r"Maximum resident set size \(kbytes\):\s*([0-9]+)", text)
    exits = re.findall(r"Exit status:\s*([0-9]+)", text)
    if len(rss) != 1 or len(exits) != 1:
        raise ValueError("missing or ambiguous process RSS/exit record")
    rss_value, exit_value = int(rss[0]), int(exits[0])
    if rss_value <= 0 or exit_value != 0:
        raise ValueError("non-positive RSS or unsuccessful process")
    return rss_value, exit_value


def lock_packages(path: Path) -> dict[tuple[str, str], tuple]:
    parsed = tomllib.loads(path.read_text(encoding="utf-8"))
    return {
        (item["name"], item["version"]): (item.get("source"), item.get("checksum"))
        for item in parsed.get("package", [])
    }


def check_lock(baseline_path: Path, current_path: Path) -> dict:
    baseline, current = lock_packages(baseline_path), lock_packages(current_path)
    if not baseline or not current:
        raise ValueError("empty dependency package graph")
    checked = 0
    for key, value in current.items():
        if key[0] == "ssgkr-benchmark-driver":
            continue
        if baseline.get(key) != value:
            raise ValueError("released dependency identity differs: " + repr(key))
        checked += 1
    return {"status": "PASS", "checked_packages": checked}


def control_corpus(root: Path, count: int) -> dict:
    records = []
    for depth in DEPTHS:
        for kind in KINDS:
            prefix = f"{kind}-d{depth}"
            pairs = []
            for mode in ("native", "portable"):
                path = root / f"{mode}-{prefix}.hashes"
                values = path.read_text(encoding="utf-8").splitlines()
                if len(values) != count or any(not HASH_RE.fullmatch(value) for value in values):
                    raise ValueError("invalid control corpus: " + path.name)
                if len(set(values)) != count:
                    raise ValueError("duplicate control envelope hash: " + path.name)
                pairs.append(values)
            if pairs[0] != pairs[1]:
                raise ValueError("native/portable control hashes differ: " + prefix)
            native = root / f"native-{prefix}.bin"
            portable = root / f"portable-{prefix}.bin"
            if native.read_bytes() != portable.read_bytes():
                raise ValueError("native/portable representative bytes differ: " + prefix)
            if file_sha256(native) != pairs[0][0]:
                raise ValueError("representative proof differs from first control hash: " + prefix)
            records.append({"kind": kind, "depth": depth, "fixture_count": count,
                            "all_hashes_sha256": sha256_bytes(("\n".join(pairs[0]) + "\n").encode())})
    return {"status": "PASS", "case_count": len(records), "fixture_count_per_case": count,
            "native_portable_hashes_equal": True, "representative_bytes_equal": True,
            "cases": records}


def inspect_environment() -> dict:
    topology = subprocess.run(
        ["lscpu", "-p=CPU,CORE,SOCKET,NODE"], check=True,
        capture_output=True, text=True,
    ).stdout
    available = os.sched_getaffinity(0)
    cores, socket_cpus, logical, nodes = {}, {}, [], set()
    for line in topology.splitlines():
        if line.startswith("#") or not line.strip():
            continue
        cpu, core, socket, node = map(int, line.split(","))
        logical.append(cpu)
        if cpu in available:
            cores.setdefault((socket, core), cpu)
            socket_cpus.setdefault(socket, {})[core] = cpu
            if node >= 0:
                nodes.add(node)
    cpuinfo = Path("/proc/cpuinfo").read_text()
    model = re.search(r"^model name\s*:\s*(.+)$", cpuinfo, re.M)
    flags = re.search(r"^flags\s*:\s*(.+)$", cpuinfo, re.M)
    meminfo = Path("/proc/meminfo").read_text()
    memtotal = re.search(r"^MemTotal:\s*([0-9]+) kB$", meminfo, re.M)
    if not cores or not model or not flags or not memtotal:
        raise ValueError("incomplete CPU/memory topology")
    selected = sorted(cores.values())
    first_socket = min(socket_cpus)
    clock_policy = {}
    for name in ("scaling_driver", "scaling_governor", "scaling_min_freq", "scaling_max_freq"):
        path = Path("/sys/devices/system/cpu/cpu0/cpufreq") / name
        clock_policy[name] = path.read_text().strip() if path.is_file() else None
    boost = Path("/sys/devices/system/cpu/cpufreq/boost")
    clock_policy["boost"] = boost.read_text().strip() if boost.is_file() else None
    result = {
        "architecture": platform.machine(), "cpu_model": model.group(1).strip(),
        "logical_cpus": len(logical), "allowed_logical_cpus": len(available),
        "physical_cores_available": len(cores),
        "memory_gib": int(memtotal.group(1)) / 1024 / 1024,
        "avx512f": "avx512f" in flags.group(1).split(),
        "sockets_available": len(socket_cpus),
        "numa_nodes_available": len(nodes), "clock_policy": clock_policy,
        "physical_cpu_list": selected,
        "first_socket_cpu_list": sorted(socket_cpus[first_socket].values()),
        "kernel": platform.release(), "python": platform.python_version(),
        "policy": "allowed CPU set only; no per-thread placement or fixed-frequency claim",
    }
    return result


def same_environment(environment: dict, reference: dict | None) -> tuple[bool, list[str]]:
    differences = []
    for name, expected in (("physical_cores_available", 192), ("logical_cpus", 192),
                           ("allowed_logical_cpus", 192), ("architecture", "x86_64"),
                           ("avx512f", True)):
        if environment.get(name) != expected:
            differences.append(name)
    if not isinstance(environment.get("memory_gib"), (int, float)) or environment["memory_gib"] < 360:
        differences.append("memory_gib")
    if reference is None:
        differences.append("published hardware reference unavailable")
    else:
        if environment.get("cpu_model") != reference.get("cpu_model"):
            differences.append("cpu_model")
        reference_memory = reference.get("memory_gib")
        if not isinstance(reference_memory, (int, float)) or not math.isclose(
            environment.get("memory_gib", 0), reference_memory, rel_tol=.02
        ):
            differences.append("published memory profile")
        for name in ("kernel", "sockets_available", "numa_nodes_available", "clock_policy"):
            if name not in reference or environment.get(name) != reference[name]:
                differences.append(name)
    return not differences, differences


def phase_notes() -> list[str]:
    return [
        "The full replay memory check represents the recorded 384 GiB host profile, not an engine minimum-RAM requirement. Actual process RSS is reported separately.",
        "Repeated processes use one physical server; run-specific latency quantiles are not pooled.",
        "Matching listed source/workload/environment metadata is not a claim of identical physical hardware, fixed clocks or identical background load.",
        "Fixtures have independent random sibling paths and separately computed roots, not one global tree or a committed update log.",
        "Timed proving/caller intervals exclude proof encoding, SHA hashing, correctness controls and delivery. They are not sustained output-stream or service capacity.",
        "Prepared latency includes witness generation. Pure parallel proving excludes it. The parallel-witness caller completes witness collection before proving; there is no overlap.",
        "Batch time divided by batch size is an amortized cost, not an individual parallel job's latency.",
        "RSS is a whole-process peak including fixtures, prepared state, pools, jobs, proofs and correctness initialization.",
        "The shipped SMT verifier retains the private leaf and full path and recomputes native Merkle hashes.",
        "The recorded external vendor program is a fixed depth-24 membership example with one preserved inner proof, not an arbitrary-request proof service.",
        "No wrapper, queue, network, state-store lookup, sequential commit, production SPS, deadline or competitor-superiority claim is included.",
    ]


def summarize(root: Path, profile: str, controls_root: Path | None = None) -> dict:
    expected = expected_cells(profile)
    findings, cells, probe_cells = [], [], []
    paths = sorted(root.glob("native-r*-*.csv"))
    for path in paths:
        try:
            cell = parse_timing_text(path.read_text(encoding="utf-8"), path.name)
            cell["raw_csv_sha256"] = file_sha256(path)
            rss, exit_code = parse_time_text(path.with_suffix(".time.txt").read_text(encoding="utf-8"))
            cell.update({"process_peak_rss_kib": rss, "process_exit": exit_code})
            if profile == "full" and cell["run"] == 0:
                findings.append("pilot run excluded from final matrix: " + path.name)
                continue
            cells.append(cell)
        except (ValueError, OSError, KeyError, TypeError) as error:
            findings.append("invalid process cell " + path.name + ": " + type(error).__name__)
    counts = Counter(cell_key(cell) for cell in cells)
    duplicates = [key for key, count in counts.items() if count != 1]
    missing, extra = sorted(set(expected) - set(counts)), sorted(set(counts) - set(expected))
    if duplicates:
        findings.append("duplicate cell keys")
    if missing:
        findings.append(f"missing expected cells: {len(missing)}")
    if extra:
        findings.append(f"unexpected cell keys: {len(extra)}")
    for cell in cells:
        wanted = expected.get(cell_key(cell))
        if wanted is not None and cell["sample_count"] != wanted:
            findings.append("wrong sample count: " + cell["raw_csv"])
        if cell["workers"] <= 0 or (cell["sample_unit"] == "batch" and cell["batch"] < cell["workers"]):
            findings.append("invalid worker/batch relation: " + cell["raw_csv"])
    for path in sorted(root.glob("first-socket-*.csv")):
        try:
            probe = parse_timing_text(path.read_text(encoding="utf-8"), path.name)
            rss, exit_code = parse_time_text(path.with_suffix(".time.txt").read_text(encoding="utf-8"))
            if not (probe["run"] == 0 and probe["depth"] == 24 and probe["batch"] == 768
                    and probe["workers"] == 96 and probe["sample_count"] == 3
                    and probe["phase"] in {"parallel", "stream-parallel-witness"}):
                raise ValueError("unexpected first-socket probe configuration")
            probe.update({"process_peak_rss_kib": rss, "process_exit": exit_code})
            probe_cells.append(probe)
        except (ValueError, OSError, KeyError, TypeError) as error:
            findings.append("invalid topology probe: " + path.name + ": " + str(error).splitlines()[0])
    if probe_cells and (len(probe_cells) != 6 or len({cell_key(cell) for cell in probe_cells}) != 6):
        findings.append("incomplete or duplicate optional first-socket probe set")
    baseline = {cell_key(cell)[1:4]: cell for cell in cells if cell["phase"] == "seq-prove"}
    serial_witness = {(cell["run"], cell["kind"], cell["depth"], cell["workers"]): cell
                      for cell in cells if cell["phase"] == "stream"}
    for cell in cells:
        if cell["phase"] == "parallel":
            same = baseline.get((cell["run"], cell["kind"], cell["depth"]))
            if same and same["batch"] == cell["batch"]:
                cell["speedup_vs_same_run_sequential_prove_only"] = same["median_ns"] / cell["median_ns"]
        if cell["phase"] == "stream-parallel-witness":
            same = serial_witness.get((cell["run"], cell["kind"], cell["depth"], cell["workers"]))
            if same and same["batch"] == cell["batch"]:
                cell["caller_parallel_witness_speedup"] = same["median_ns"] / cell["median_ns"]
    terminal = (root / "terminal.txt").read_text(encoding="utf-8").strip() if (root / "terminal.txt").exists() else ""
    allowed_terminal = {"high-final-measurement=PASS", "cpu-replay-full=PASS"} if profile == "full" else {"cpu-replay-smoke=PASS"}
    if terminal not in allowed_terminal:
        findings.append("missing or incorrect exact terminal status")
    controls = None
    if controls_root is not None:
        try:
            controls = control_corpus(controls_root, 768 if profile == "full" else 4)
        except (ValueError, OSError) as error:
            findings.append("invalid controls: " + type(error).__name__)
    else:
        findings.append("control corpus not supplied")
    environment = None
    reference = None
    for name, destination in (("environment.json", "environment"), ("reference-environment.json", "reference")):
        path = root / name
        if path.exists():
            try:
                loaded = json.loads(path.read_text(encoding="utf-8"))
                if not isinstance(loaded, dict):
                    raise ValueError("environment metadata must be an object")
                if destination == "environment":
                    environment = loaded
                else:
                    reference = loaded
            except (ValueError, OSError):
                findings.append("invalid public environment metadata: " + name)
    integrity = None
    integrity_path = root / "integrity.json"
    if integrity_path.exists():
        try:
            integrity = json.loads(integrity_path.read_text(encoding="utf-8"))
            if not (integrity.get("source_archive_sha256") == SOURCE_SHA256
                    and integrity.get("driver_sha256") == DRIVER_SHA256
                    and integrity.get("source_bytes_unchanged") is True
                    and integrity.get("released_dependencies_match") is True
                    and integrity.get("driver_inputs_unchanged") is True
                    and integrity.get("native_binary_unchanged") is True
                    and integrity.get("controls_passed") is True
                    and integrity.get("stock_proof_digest_equal") is True):
                findings.append("input/control integrity record does not match the fixed study")
        except (ValueError, OSError, AttributeError):
            findings.append("invalid input/control integrity record")
    else:
        findings.append("input/control integrity record unavailable")
    environment_matches, environment_differences = same_environment(environment or {}, reference)
    if findings:
        status = "PARTIAL_MEASUREMENTS"
    elif profile == "smoke":
        status = "SMOKE_ONLY"
    elif not environment_matches:
        status = "OTHER_ENVIRONMENT"
    else:
        status = "COMPLETE_PROFILE_REPLAY"
    return {
        "schema": "statesync-gkr.cpu-measurement-summary.v1", "profile": profile,
        "status": status, "cell_count": len(cells), "expected_cell_count": len(expected),
        "findings": findings, "missing_cell_keys": missing, "extra_cell_keys": extra,
        "duplicate_cell_keys": duplicates,
        "environment_matches_published_profile": environment_matches,
        "environment_differences": environment_differences,
        "environment": environment, "controls": controls, "integrity": integrity,
        "notes": phase_notes(), "cells": cells, "topology_probe_cells": probe_cells,
    }


def write_summary(result: dict, output: Path, compact: Path | None) -> None:
    if compact is not None:
        with compact.open("w", encoding="utf-8", newline="") as handle:
            writer = csv.writer(handle, lineterminator="\n")
            writer.writerow(("cell_id", "sample_index", "elapsed_ns"))
            for index, cell in enumerate(result["cells"]):
                cell["cell_id"] = index
                for sample, duration in zip(cell["sample_ids"], cell["durations_ns"]):
                    writer.writerow((index, sample, duration))
        result["compact_samples"] = {"file": compact.name, "sha256": file_sha256(compact)}
    for cell in result["cells"] + result["topology_probe_cells"]:
        cell.pop("sample_ids", None)
        cell.pop("durations_ns", None)
    output.write_text(json.dumps(result, indent=2, ensure_ascii=True) + "\n", encoding="utf-8", newline="\n")


def check_published(root: Path) -> dict:
    """Recompute packaged numerical data; this is not a host attestation."""
    counts = []
    for name in ("measurements.json", "native-measurements.json"):
        summary = json.loads((root / name).read_text(encoding="utf-8"))
        cells = summary["cells"]
        native = name.startswith("native-")
        if native:
            expected = {(run, kind, depth): 1000 for run in (1, 2, 3)
                        for kind in KINDS for depth in DEPTHS}
            keys = [(c["run"], c["kind"], c["depth"]) for c in cells]
        else:
            expected = expected_cells("full")
            keys = [cell_key(c) for c in cells]
        if len(cells) != len(expected) or len(set(keys)) != len(expected) or set(keys) != set(expected):
            raise ValueError("published cell-key set differs from the fixed study")
        if [c["cell_id"] for c in cells] != list(range(len(cells))):
            raise ValueError("published cell IDs differ from summary order")
        compact = summary["compact_samples"]
        if Path(compact["file"]).name != compact["file"]:
            raise ValueError("compact sample name must be local to the package")
        sample_path = root / compact["file"]
        if file_sha256(sample_path) != compact["sha256"]:
            raise ValueError("compact sample SHA-256 mismatch")
        reader = csv.DictReader(io.StringIO(sample_path.read_text(encoding="utf-8")))
        if reader.fieldnames != ["cell_id", "sample_index", "elapsed_ns"]:
            raise ValueError("invalid compact sample schema")
        rows = list(reader)
        cursor = 0
        for cell, key in zip(cells, keys):
            count = expected[key]
            if cell.get("sample_count") != count or cell.get("process_exit") != 0 or cell.get("process_peak_rss_kib", 0) <= 0:
                raise ValueError("published sample/process denominator mismatch")
            part = rows[cursor:cursor + count]
            if len(part) != count or any((int(r["cell_id"]), int(r["sample_index"])) != (cell["cell_id"], i)
                                        for i, r in enumerate(part)):
                raise ValueError("compact samples missing, duplicated or out of order")
            ns = [positive_integer(r["elapsed_ns"], "elapsed_ns") for r in part]
            ordered = sorted(ns)
            calculated = {"median_ns": statistics.median(ns)}
            for label, q in (("p50_ns", .50), ("p95_ns", .95), ("p99_ns", .99)):
                if label in cell:
                    calculated[label] = ordered[int((count - 1) * q)]
            if not native:
                calculated.update(mean_ns=statistics.mean(ns), min_ns=min(ns), max_ns=max(ns),
                                  cv_percent=100 * statistics.pstdev(ns) / statistics.mean(ns))
                if cell["phase"] in BATCH_PHASES:
                    calculated["proofs_per_second_at_median_batch"] = cell["batch"] * 1e9 / statistics.median(ns)
                    calculated["measured_proofs"] = cell["batch"] * count
            if any(not math.isclose(cell[label], value, rel_tol=1e-12) for label, value in calculated.items()):
                raise ValueError("published statistics differ from compact raw samples")
            cursor += count
        if cursor != len(rows):
            raise ValueError("unexpected trailing compact samples")
        counts.append({"summary": name, "cells": len(cells), "samples": cursor})
    provenance = json.loads((root / "provenance.json").read_text(encoding="utf-8"))
    if provenance["source_archive_sha256"] != SOURCE_SHA256 or file_sha256(root / "driver/src/main.rs") != DRIVER_SHA256:
        raise ValueError("immutable source/driver pin mismatch")
    for name in ("driver/src/main.rs", "driver/Cargo.toml", "driver/Cargo.lock"):
        if file_sha256(root / name) != provenance["frozen_measured_inputs"][name]:
            raise ValueError("measured caller input mismatch")
    record = provenance["control_hashes"]
    if record["file"] != "control-hashes.csv" or file_sha256(root / record["file"]) != record["sha256"]:
        raise ValueError("published control hash corpus mismatch")
    return {"status": "PUBLISHED_NUMERICAL_DATA_PASS", "datasets": counts,
            "scope": "Numerical recomputation and packaged input checks; no independent host attestation."}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    published = commands.add_parser("check-published")
    published.add_argument("root", type=Path)
    summary = commands.add_parser("summarize")
    summary.add_argument("root", type=Path)
    summary.add_argument("--profile", choices=("full", "smoke"), required=True)
    summary.add_argument("--controls", type=Path)
    summary.add_argument("--output", type=Path, required=True)
    summary.add_argument("--compact-samples", type=Path)
    lock = commands.add_parser("check-lock")
    lock.add_argument("baseline", type=Path)
    lock.add_argument("current", type=Path)
    controls = commands.add_parser("check-controls")
    controls.add_argument("root", type=Path)
    controls.add_argument("--fixtures", type=int, choices=(4, 768), required=True)
    environment = commands.add_parser("environment")
    environment.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.command == "check-published":
            print(json.dumps(check_published(args.root.resolve())))
            return 0
        if args.command == "summarize":
            result = summarize(args.root.resolve(), args.profile, args.controls)
            write_summary(result, args.output, args.compact_samples)
            print(json.dumps({"status": result["status"], "cell_count": result["cell_count"], "findings": result["findings"]}))
            return 0 if result["status"] in {"SMOKE_ONLY", "COMPLETE_PROFILE_REPLAY", "OTHER_ENVIRONMENT"} else 2
        if args.command == "check-lock":
            print(json.dumps(check_lock(args.baseline, args.current)))
        elif args.command == "check-controls":
            print(json.dumps(control_corpus(args.root, args.fixtures)))
        elif args.command == "environment":
            args.output.write_text(json.dumps(inspect_environment(), indent=2) + "\n", encoding="utf-8")
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print("validation failed: " + str(error), file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
