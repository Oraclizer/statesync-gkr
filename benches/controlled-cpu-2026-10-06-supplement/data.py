#!/usr/bin/env python3
"""Package verified supplemental CPU data, without building or running GKR.

Standard library only. A schema smoke stays SMOKE_ONLY. The final profile
requires the frozen 35-configuration, five-process matrix and final terminals.
Input files are read-only. Public labels expand worker counts; every timing,
fixture, hash, seed, warmup and CPU-tick observation is retained.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import csv
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import runpy
import shutil
import statistics
import sys

SOURCE_SHA = "d22e2200378e21a40c254eab8df4d44dfea81f2806f02f0c9030636300d489e9"
SOURCE_COMMIT = "1b8d2f829792172b347dedbfde969016c2c05789"
SEED = 0x5353474B52202026
KINDS = ("membership", "nonmembership", "update")
VARIANTS = ("tombstone_nonmembership", "empty_to_occupied", "occupied_to_tombstone",
            "tombstone_to_occupied", "zero_payload_member", "max_payload_member",
            "root_chain_update", "large_key_member")
PHASES = {
    "A": (("compile_with_hints", "none", "single"), ("derive_wiring", "derived", "single"),
          ("circuit_commitment", "none", "single"), ("witness", "none", "single"),
          ("prove_on", "none", "single"), ("encode", "none", "serial"),
          ("verify", "derived", "single"), ("verify", "table", "single"),
          ("encoded_verify", "derived", "serial")),
    "B": tuple((p, o, mode) for mode in ("serial", "parallel") for p, o in
               (("witness_batch", "none"), ("prove_batch", "none"),
                ("encode_batch", "none"), ("encoded_verify_batch", "derived"),
                ("complete_pipeline", "derived"))),
    "C": (("native_predicate", "native", "single"), ("prepared_request", "none", "single"),
          ("encode", "none", "serial"), ("encoded_verify", "derived", "serial"),
          ("complete_request", "derived", "serial")),
}
HEADER = tuple("cell_id,process_repeat,order_index,order_seed,fixture_id,kind,depth,leaf_max_fields,old_leaf_kind,new_leaf_kind,payload_fields,key_policy,chain_id,batch,workers,cpu_set,build_mode,source_sha,driver_sha,binary_sha,circuit_sha,phase,oracle_kind,output_mode,sample_index,warmup,started_unix_ns,elapsed_ns,process_user_ticks,process_system_ticks,cpu_time_resolution,process_user_time,process_system_time,peak_rss_kib,proof_count,encoded_bytes,canonical_sha256,accepted,exit_code".split(","))
HASH = re.compile(r"[0-9a-f]{64}")
QUANTILE_METHOD = "type7: linear interpolation at (n-1)*q"
PRIVATE = re.compile(r"(?:[A-Za-z]:[\\/](?:Users|Documents)[\\/]|/(?:home|Users)/[^/\s]+/|\barn:aws:|\bAKIA[0-9A-Z]{16}|-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----|\b(?:\d{1,3}\.){3}\d{1,3}\b)")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_json(path: Path):
    def unique(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError("duplicate JSON key")
            result[key] = value
        return result
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique)


def public_label(value: str) -> str:
    return re.sub(r"-w([0-9]+)(?=$|[.-])", r"-workers\1", value)


def safe_text(data: bytes) -> str:
    text = data.decode("utf-8")
    if PRIVATE.search(text):
        raise ValueError("private path, address, account or credential in selected public material")
    return text


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=True) + "\n", encoding="utf-8", newline="\n")


def gzip_bytes(data: bytes) -> bytes:
    return gzip.compress(data, compresslevel=9, mtime=0)


def config_key(c: dict) -> tuple:
    return tuple(c[k] for k in ("suite", "kind", "depth", "batch", "workers", "variant"))


def expected_configs() -> set[tuple]:
    configs = {("A", k, d, 1, 1, "") for k in KINDS for d in (24, 28, 32)}
    configs |= {("B", k, 24, b, w, "") for k in KINDS for b in (32, 192, 768) for w in (48, 192)}
    configs |= {("C", "nonmembership" if v == "tombstone_nonmembership" else "membership" if v.endswith("member") else "update", 24, 1, 1, v) for v in VARIANTS}
    return configs


def check_plan(plan: dict, profile: str) -> None:
    if plan.get("source_archive_sha256") != SOURCE_SHA:
        raise ValueError("source archive pin mismatch")
    cells = plan["cells"]
    if len({c["cell_id"] for c in cells}) != len(cells):
        raise ValueError("duplicate process cells")
    for cell in cells:
        if config_key(cell) not in expected_configs() or cell["samples"] <= 0 or cell["warmup"] < 0:
            raise ValueError("unsupported configuration or sample denominator")
    for field in ("driver_manifest_sha256", "binary_sha256"):
        if not HASH.fullmatch(plan.get(field, "")):
            raise ValueError("missing adopted caller identity")
    if profile == "final":
        if plan.get("status") != "FROZEN_AFTER_ACTUAL_COST_PILOT" or len(cells) != 175:
            raise ValueError("final plan is not the frozen 175-process matrix")
        grouped = defaultdict(list)
        for cell in cells:
            grouped[config_key(cell)].append(cell["repeat"])
        if set(grouped) != expected_configs() or any(sorted(values) != list(range(1, 6)) for values in grouped.values()):
            raise ValueError("35 configurations x five process repetitions mismatch")
        if [c["order_index"] for c in cells] != list(range(175)):
            raise ValueError("frozen process execution order mismatch")
        if plan.get("source_commit") != SOURCE_COMMIT or plan.get("source_release") != "v1.1.0":
            raise ValueError("release source/tag mismatch")


def process_time(path: Path) -> dict:
    result = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line.startswith("Command being timed:"):
            continue
        label, value = line.rsplit(": ", 1)
        safe_text(value.encode())
        result[label] = value
    if len(result) != 22 or result.get("Exit status") != "0" or int(result.get("Maximum resident set size (kbytes)", "0")) <= 0:
        raise ValueError("incomplete or unsuccessful GNU time record")
    parts = result["Elapsed (wall clock) time (h:mm:ss or m:ss)"].split(":")
    wall = sum(float(v) * 60 ** i for i, v in enumerate(reversed(parts)))
    return {"gnu_time_metrics": result, "elapsed_wall_seconds": wall,
            "process_peak_rss_kib": int(result["Maximum resident set size (kbytes)"]),
            "process_user_seconds": float(result["User time (seconds)"]),
            "process_system_seconds": float(result["System time (seconds)"]),
            "process_exit": 0, "original_time_sha256": sha(path.read_bytes()),
            "rss_scope": "Whole process; B serial and parallel output modes share this peak."}


def validate_rows(raw: bytes, cell: dict, plan: dict, metadata: dict) -> list[dict]:
    reader = csv.DictReader(io.StringIO(safe_text(raw), newline=""))
    if tuple(reader.fieldnames or ()) != HEADER:
        raise ValueError("adopted CSV schema mismatch")
    rows = list(reader)
    expected = {(p, o, mode, warm, index) for p, o, mode in PHASES[cell["suite"]]
                for warm, count in (("true", cell["warmup"]), ("false", cell["samples"])) for index in range(count)}
    keys = [(r["phase"], r["oracle_kind"], r["output_mode"], r["warmup"], int(r["sample_index"])) for r in rows]
    if set(keys) != expected or len(keys) != len(expected):
        raise ValueError("missing, duplicate or unexpected phase/warmup/sample keys")
    seed = SEED ^ ((cell["repeat"] * 0x9E3779B97F4A7C15) & ((1 << 64) - 1)) ^ cell["order_index"]
    for r in rows:
        if None in r or any(value is None for value in r.values()):
            raise ValueError("incomplete or extra CSV fields")
        if (r["cell_id"] != cell["cell_id"] or int(r["process_repeat"]) != cell["repeat"]
                or int(r["order_index"]) != cell["order_index"] or int(r["order_seed"]) != seed
                or int(r["elapsed_ns"]) <= 0 or int(r["started_unix_ns"]) <= 0
                or r["source_sha"] != SOURCE_SHA or r["driver_sha"] != plan["driver_manifest_sha256"]
                or r["binary_sha"] != plan["binary_sha256"] or r["circuit_sha"] != metadata["circuit_sha"]
                or r["accepted"] != "true" or r["exit_code"] != "0" or r["build_mode"] != "native"):
            raise ValueError("timing/source/seed/process identity mismatch")
        if any(r[field] for field in ("process_user_time", "process_system_time", "peak_rss_kib")):
            raise ValueError("unexpected per-phase whole-process time/RSS attribution")
        if r["cpu_time_resolution"] != "proc_stat_clock_ticks;see_CLK_TCK;not_nanoseconds":
            raise ValueError("CPU tick resolution label mismatch")
        if any(not re.fullmatch(r"[0-9]*", r[k]) for k in ("process_user_ticks", "process_system_ticks")):
            raise ValueError("invalid quantized CPU ticks")
        if not HASH.fullmatch(r["canonical_sha256"]) or int(r["encoded_bytes"]) <= 0 or int(r["proof_count"]) != cell["batch"]:
            raise ValueError("associated proof/byte denominator mismatch")
    grouped = defaultdict(list)
    for row in rows:
        grouped[(row["phase"], row["oracle_kind"], row["output_mode"], row["warmup"])].append(int(row["sample_index"]))
    if any(indices != list(range(cell["warmup"] if key[-1] == "true" else cell["samples"])) for key, indices in grouped.items()):
        raise ValueError("sample indices out of order in a subcase")
    return rows


def statistics_for(rows: list[dict], cell: dict) -> list[dict]:
    groups = defaultdict(list)
    for row in rows:
        if row["warmup"] == "false":
            groups[(row["phase"], row["oracle_kind"], row["output_mode"])].append(row)
    result = []
    for (phase, oracle, mode), group in groups.items():
        durations = [int(row["elapsed_ns"]) for row in group]
        ordered = sorted(durations)
        stats = {"phase": phase, "oracle_kind": oracle, "output_mode": mode,
                 "sample_count": len(group), "sample_unit": "batch" if cell["suite"] == "B" else "request",
                 "median_ns": statistics.median(durations), "mean_ns": statistics.mean(durations),
                 "min_ns": min(durations), "max_ns": max(durations),
                 "cv_percent": 100 * statistics.pstdev(durations) / statistics.mean(durations),
                 "quantile_method": QUANTILE_METHOD}
        for name, q in (("p50_ns", .5), ("p95_ns", .95), ("p99_ns", .99)):
            position = (len(ordered) - 1) * q
            lower = int(position)
            upper = min(lower + 1, len(ordered) - 1)
            stats[name] = ordered[lower] + (ordered[upper] - ordered[lower]) * (position - lower)
        if cell["suite"] == "B":
            stats["associated_proofs_per_second_at_median_interval"] = cell["batch"] * 1e9 / stats["median_ns"]
        result.append(stats)
    return result


def check_artifact_links(rows: list[dict], fixture_bytes: bytes, encoded_bytes: bytes | None, cell: dict, metadata: dict) -> None:
    fixtures = [json.loads(line) for line in fixture_bytes.decode().splitlines()]
    count = cell["batch"] if cell["suite"] == "B" else cell["samples"]
    if len(fixtures) != count or [f["fixture_id"] for f in fixtures] != list(range(count)):
        raise ValueError("fixture sequence/count mismatch")
    seed = SEED ^ ((cell["repeat"] * 0x9E3779B97F4A7C15) & ((1 << 64) - 1)) ^ cell["order_index"]
    if metadata.get("fixture_base_seed") != SEED or metadata.get("order_seed") != seed or not metadata.get("seed_role", "").startswith("execution_order_only"):
        raise ValueError("fixture versus ordering seed role mismatch")
    if cell["suite"] == "C":
        index = VARIANTS.index(cell["variant"])
        if metadata.get("fixture_variant_index") != index or metadata.get("fixture_generator_initial_seed") != SEED ^ 0x435F56415249414E ^ (index << 40):
            raise ValueError("variant fixture generator seed mismatch")
    shape = metadata if cell["suite"] == "A" else metadata.get("circuit_shape", {})
    if not shape.get("layers") or any(k not in shape for k in ("input_width_bits", "derived_groups", "grouped_gates", "sparse_gates", "grouped_consts", "sparse_consts")):
        raise ValueError("missing circuit shape/grouping metadata")
    blocks = defaultdict(list)
    for row in rows:
        blocks[(row["warmup"], row["sample_index"])].append(row)
        if cell["suite"] != "B":
            f = fixtures[int(row["fixture_id"])]
            if any(f[k] != row[k] for k in ("kind", "old_leaf_kind", "new_leaf_kind")):
                raise ValueError("raw row/fixture leaf-kind mapping mismatch")
    if any(len({(r["fixture_id"], r["canonical_sha256"], r["circuit_sha"], r["encoded_bytes"]) for r in block}) != 1 for block in blocks.values()):
        raise ValueError("paired input/proof/byte association mismatch")
    if cell["variant"] == "root_chain_update":
        for previous, current in zip(fixtures, fixtures[1:]):
            if any(previous[a] != current[b] for a, b in (("new_root", "old_root"), ("new_leaf_encoding", "old_leaf_encoding"), ("key", "key"), ("siblings", "siblings"))):
                raise ValueError("root-chain fixture predecessor mismatch")
        chain = [int(r["fixture_id"]) for r in rows if r["phase"] == "complete_request" and r["warmup"] == "false"]
        if chain != list(range(count)):
            raise ValueError("root-chain timed sample order mismatch")
    if cell["suite"] == "B":
        records = [json.loads(line) for line in encoded_bytes.decode().splitlines()]
        expected = {(warm, sample, mode, f) for warm, n in ((True, cell["warmup"]), (False, cell["samples"]))
                    for sample in range(n) for mode in ("serial", "parallel") for f in range(count)}
        keys = [(r["warmup"], r["sample_index"], r["output_mode"], r["fixture_id"]) for r in records]
        if len(keys) != len(expected) or set(keys) != expected:
            raise ValueError("encoded-byte key count/uniqueness mismatch")
        batches = defaultdict(list)
        for record in records:
            if record["bytes"] <= 0 or not HASH.fullmatch(record["canonical_sha256"]):
                raise ValueError("encoded fixture byte/hash invalid")
            batches[(record["warmup"], record["sample_index"], record["output_mode"])].append(record)
        for row in rows:
            group = sorted(batches[(row["warmup"] == "true", int(row["sample_index"]), row["output_mode"])], key=lambda x: x["fixture_id"])
            aggregate = sha("".join(r["canonical_sha256"] for r in group).encode())
            if aggregate != row["canonical_sha256"] or sum(r["bytes"] for r in group) != int(row["encoded_bytes"]):
                raise ValueError("encoded bytes/hash aggregate differs from associated raw row")


def preserve_gzip(output: Path, name: str, data: bytes) -> dict:
    target = output / name
    target.parent.mkdir(parents=True, exist_ok=True)
    compressed = gzip_bytes(data)
    if target.exists() and target.read_bytes() != compressed:
        raise ValueError("content-addressed artifact collision")
    target.write_bytes(compressed)
    return {"file": name, "sha256": sha(compressed), "decoded_sha256": sha(data), "decoded_bytes": len(data)}


def sanitized_plan(plan: dict) -> dict:
    selected = ("schema", "status", "source_release", "source_commit", "source_archive_sha256",
                "driver_package_version", "distinct_configs", "process_repeats", "process_cells",
                "candidate_samples", "output_modes", "paired_design", "seed_role", "A_compile",
                "A_encode_preparation", "B_complete_interval", "cpu", "rss", "C_root_chain", "units",
                "frozen_utc", "driver_manifest_sha256", "binary_sha256", "driver_input_sha256",
                "adopted_guard_sha256", "source_before_manifest_sha256", "original_controls_manifest_sha256")
    result = {key: plan[key] for key in selected if key in plan}
    result["cells"] = [dict(c, cell_id=public_label(c["cell_id"])) for c in plan["cells"]]
    safe_text(json.dumps(result).encode())
    return result


def snapshot_provenance(snapshot: Path | None, bootstrap: Path | None, plan: dict, output: Path, figures: Path | None) -> dict:
    result = {"source_release": "v1.1.0", "source_commit": SOURCE_COMMIT,
              "source_archive_sha256": SOURCE_SHA, "recorded_helper_sha256": {}, "driver_inputs": [], "figures": []}
    if snapshot:
        manifest = snapshot / "adopted/driver-input.sha256"
        if sha(manifest.read_bytes()) != plan["driver_manifest_sha256"]:
            raise ValueError("adopted driver input manifest mismatch")
        for line in manifest.read_text(encoding="utf-8").splitlines():
            digest, name = line.split(maxsplit=1)
            relative = Path(name)
            if relative.is_absolute() or ".." in relative.parts or relative.parts[0] != "driver":
                raise ValueError("unsafe or unexpected driver member")
            source = snapshot / relative
            data = source.read_bytes()
            if sha(data) != digest or not HASH.fullmatch(digest):
                raise ValueError("adopted driver member differs from manifest")
            safe_text(data)
            target = output / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            result["driver_inputs"].append({"path": relative.as_posix(), "bytes": len(data), "sha256": digest})
        for name in ("final.sh", "run-cells.py", "validate-cells.py", "validate-plan.py", "freeze-plan.py", "check-common-lock.py"):
            path = snapshot / name
            if path.exists():
                result["recorded_helper_sha256"][name] = sha(path.read_bytes())
        result["helper_distribution"] = "Recorded provider/operator scripts are not copied; their hashes are preserved. Generic replay is a separate reviewed interface."
    if bootstrap:
        cpu = load_json(bootstrap / "lscpu.json")
        result["lscpu"] = cpu
        result["clock_tick_hz"] = int((bootstrap / "clock-tick-hz.txt").read_text().strip())
        result["physical_cpu_set"] = (bootstrap / "physical-cpus.txt").read_text().strip()
        result["topology_csv"] = (bootstrap / "topology.csv").read_text().splitlines()
        result["kernel"] = (bootstrap / "uname.txt").read_text().split()[2]
        result["visible_memory_kib"] = int(re.search(r"MemTotal:\s*(\d+)", (bootstrap / "meminfo.txt").read_text()).group(1))
        result["clock_policy"] = {}
        for line in (bootstrap / "clock-policy.txt").read_text().splitlines():
            if "=" in line and line.startswith("/sys/"):
                key, value = line.rsplit("=", 1)
                result["clock_policy"][key.rsplit("/", 1)[-1]] = value
            elif line.startswith("proc_cpu_mhz_count="):
                result["observed_cpu_mhz_summary"] = line
        result["rustc"] = (bootstrap / "rustc.txt").read_text().splitlines()
        result["placement_scope"] = "Allowed CPU set; no per-thread placement, fixed-frequency or identical physical-machine claim."
    if figures:
        for source in sorted(figures.glob("*.png")):
            target = output / "figures" / source.name
            target.parent.mkdir(parents=True, exist_ok=True)
            data = source.read_bytes()
            if any(token in data for token in (b"C:" + b"/" + b"Users/", b"C:" + bytes([92]) + b"Users" + bytes([92]), b"/" + b"home/", b"ip-172-", b"Co" + b"dex", b"GP" + b"T-")):
                raise ValueError("private or tool-attribution PNG metadata")
            shutil.copyfile(source, target)
            result["figures"].append({"file": "figures/" + source.name, "sha256": sha(data), "bytes": len(data), "copy": "original inspected PNG bytes; no rerender"})
    safe_text(json.dumps(result).encode())
    write_json(output / "provenance.json", result)
    return result


def convert(args) -> dict:
    plan = load_json(args.plan)
    check_plan(plan, args.profile)
    root = args.cells.resolve()
    if {p.name for p in root.iterdir() if p.is_dir()} != {c["cell_id"] for c in plan["cells"]}:
        raise ValueError("raw process directory set differs from plan")
    terminal = "supplement-schema-smoke=PASS" if args.profile == "smoke" else "supplement175-processes=PASS"
    if (root / "measurement-terminal.txt").read_text(encoding="utf-8").strip() != terminal:
        raise ValueError("exact measurement terminal missing")
    if args.profile == "final" and (root / "terminal.txt").read_text(encoding="utf-8").strip() != "supplement-full-campaign=PASS":
        raise ValueError("exact completed campaign terminal missing")
    if args.output.exists():
        raise ValueError("use a new output directory")
    args.output.mkdir(parents=True)
    # Reuse the original recorder's fixture/byte/chain checks on read-only input.
    recorder = runpy.run_path(str(args.validator))
    report = args.output / "original-validator-result.json"
    if not recorder["validate"](args.plan, root, report, args.profile == "smoke"):
        raise ValueError("original raw validator rejected input")
    report.unlink()
    cells, artifacts = [], {}
    total = Counter()
    for c in plan["cells"]:
        folder = root / c["cell_id"]
        meta = load_json(folder / "metadata.json")
        raw = (folder / "metrics.csv").read_bytes()
        rows = validate_rows(raw, c, plan, meta)
        label = public_label(c["cell_id"])
        public_rows = io.StringIO(newline="")
        writer = csv.DictWriter(public_rows, fieldnames=HEADER, lineterminator="\n")
        writer.writeheader()
        for r in rows:
            r = dict(r, cell_id=label, chain_id=public_label(r["chain_id"]))
            writer.writerow(r)
        metrics_artifact = preserve_gzip(args.output, f"rows/{label}.csv.gz", public_rows.getvalue().encode())
        fixture_data = (folder / "fixtures.jsonl").read_bytes()
        safe_text(fixture_data)
        fixture_hash = sha(fixture_data)
        encoded_data = (folder / "encoded-bytes.jsonl").read_bytes() if c["suite"] == "B" else None
        check_artifact_links(rows, fixture_data, encoded_data, c, meta)
        fixtures = preserve_gzip(args.output, f"fixtures/{fixture_hash}.jsonl.gz", fixture_data)
        public_meta = dict(meta, cell_id=label)
        safe_text(json.dumps(public_meta).encode())
        entry = dict(c, cell_id=label, original_csv_sha256=sha(raw),
                     original_metadata_sha256=sha((folder / "metadata.json").read_bytes()),
                     metadata=public_meta, rows=metrics_artifact, fixtures=fixtures,
                     process=process_time(folder / "process.time.txt"), statistics=statistics_for(rows, c))
        execution = folder / "execution.json"
        if execution.exists():
            entry["started_utc"] = load_json(execution)["start_utc"]
        finish = load_json(folder / "exit.json")
        if finish["exit_code"] != 0:
            raise ValueError("process exit differs from recorder")
        if "finish_utc" in finish:
            entry["finished_utc"] = finish["finish_utc"]
        if c["suite"] == "B":
            data = (folder / "encoded-bytes.jsonl").read_bytes()
            safe_text(data)
            entry["encoded_bytes_records"] = preserve_gzip(args.output, f"encoded-bytes/{label}.jsonl.gz", data)
            entry["encoded_bytes_record_count"] = len(data.splitlines())
            total["encoded_byte_records"] += entry["encoded_bytes_record_count"]
        for row in rows:
            total["warmup_rows" if row["warmup"] == "true" else "timed_rows"] += 1
        cells.append(entry)
        artifacts[label] = metrics_artifact["sha256"]
    public_plan = sanitized_plan(plan)
    write_json(args.output / "plan.json", public_plan)
    clock_path = args.bootstrap / "clock-tick-hz.txt" if args.bootstrap else None
    hz = int(clock_path.read_text(encoding="utf-8").strip()) if clock_path and clock_path.exists() else None
    if hz is not None and hz <= 0:
        raise ValueError("invalid CPU-tick frequency")
    if args.profile == "final" and (hz is None or args.snapshot is None):
        raise ValueError("final package requires adopted caller snapshot and CPU-tick frequency")
    snapshot_provenance(args.snapshot, args.bootstrap, plan, args.output, args.figures)
    summary = {
        "schema": "statesync-gkr.supplement-public-summary.v1",
        "status": "SMOKE_ONLY" if args.profile == "smoke" else "RECORDED_SUPPLEMENT_VALIDATED",
        "profile": args.profile, "cell_count": len(cells), "row_counts": dict(total),
        "original_plan_sha256": sha(args.plan.read_bytes()), "cpu_clock_ticks_per_second": hz,
        "source_archive_sha256": SOURCE_SHA, "source_commit": SOURCE_COMMIT,
        "driver_manifest_sha256": plan["driver_manifest_sha256"], "binary_sha256": plan["binary_sha256"],
        "quantile_method": QUANTILE_METHOD,
        "notes": [
            "Process repeats share one host and fixture corpus; order_seed changes execution order, not fixture generation.",
            "Warmup rows and raw row order are preserved. CSV output order is not timestamp order when intervals are nested.",
            "Direct stage timers and nested complete intervals are distinct; do not sum overlapping process CPU ticks.",
            "CPU ticks are quantized process observations, not nanosecond CPU timers; blank row RSS/time fields join whole-process GNU time.",
            "B serial/parallel refers to encoding and encoded verification only; witness creation and proving are parallel in both modes.",
            "B modes share process peak RSS; the peak is not attributed to one mode.",
            "proof_count and encoded_bytes associate the eventual proof with a phase; compilation and verification do not generate extra proofs.",
            "Root-chain inputs use the same key/path and preserve predecessor root/leaf relationships; no persistent or distributed state commit is measured.",
            "Worker-count identifiers are expanded in public labels; tuple/sample/fixture/timestamp/tick/hash values are preserved, and original artifact digests are recorded.",
            "This is numerical packaging over unchanged release source, not new formal verification or a complete synchronization service.",
            "All supplemental quantiles use type7 linear interpolation at (n-1)*q. Preserved p99 values are descriptive sample statistics, not stable tail inference from 300/128 requests or small batch samples.",
        ], "cells": cells}
    if args.profile == "final":
        repeats = defaultdict(set)
        for cell in cells:
            repeats[config_key(cell)].add(cell["fixtures"]["decoded_sha256"])
        if any(len(hashes) != 1 for hashes in repeats.values()):
            raise ValueError("claimed same fixture corpus differs between process repeats")
        summary["same_fixture_corpus_across_repeats"] = True
    write_json(args.output / "measurements.json", summary)
    return {"status": summary["status"], "cells": len(cells), "rows": dict(total)}


def check_package(root: Path) -> dict:
    summary = load_json(root / "measurements.json")
    if summary.get("quantile_method") != QUANTILE_METHOD:
        raise ValueError("supplement quantile method mismatch")
    plan = load_json(root / "plan.json")
    check_plan(plan, summary["profile"])
    if len(summary["cells"]) != len(plan["cells"]):
        raise ValueError("packaged cell count mismatch")
    counts = Counter()
    for cell, expected in zip(summary["cells"], plan["cells"]):
        if config_key(cell) != config_key(expected) or cell["cell_id"] != expected["cell_id"]:
            raise ValueError("packaged cell ordering/configuration mismatch")
        def decoded(record):
            path = root / record["file"]
            if path.resolve().is_relative_to(root.resolve()) is False:
                raise ValueError("artifact path outside package")
            compressed = path.read_bytes()
            data = gzip.decompress(compressed)
            if sha(compressed) != record["sha256"] or sha(data) != record["decoded_sha256"] or len(data) != record["decoded_bytes"]:
                raise ValueError("packaged compressed data mismatch")
            safe_text(data)
            return data
        raw = decoded(cell["rows"])
        rows = validate_rows(raw, cell, plan, cell["metadata"])
        if statistics_for(rows, cell) != cell["statistics"]:
            raise ValueError("packaged phase statistics differ from raw rows")
        fixtures = decoded(cell["fixtures"])
        if sha(fixtures) != cell["metadata"]["fixtures_sha256"]:
            raise ValueError("packaged fixture identity mismatch")
        data = None
        if cell["suite"] == "B":
            data = decoded(cell["encoded_bytes_records"])
            if sha(data) != cell["metadata"]["encoded_bytes_log_sha256"] or len(data.splitlines()) != cell["encoded_bytes_record_count"]:
                raise ValueError("packaged encoded-byte identity mismatch")
            counts["encoded_byte_records"] += len(data.splitlines())
        check_artifact_links(rows, fixtures, data, cell, cell["metadata"])
        for row in rows:
            counts["warmup_rows" if row["warmup"] == "true" else "timed_rows"] += 1
    if dict(counts) != summary["row_counts"]:
        raise ValueError("packaged aggregate row denominator mismatch")
    return {"status": "SUPPLEMENT_NUMERICAL_PACKAGE_PASS", "profile": summary["profile"], "cells": len(summary["cells"]), "rows": dict(counts)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    package = commands.add_parser("convert")
    package.add_argument("--plan", type=Path, required=True)
    package.add_argument("--cells", type=Path, required=True)
    package.add_argument("--validator", type=Path, required=True)
    package.add_argument("--bootstrap", type=Path)
    package.add_argument("--snapshot", type=Path)
    package.add_argument("--figures", type=Path)
    package.add_argument("--profile", choices=("smoke", "final"), default="smoke")
    package.add_argument("--output", type=Path, required=True)
    check = commands.add_parser("check-package")
    check.add_argument("root", type=Path)
    args = parser.parse_args()
    try:
        result = convert(args) if args.command == "convert" else check_package(args.root)
        print(json.dumps(result))
        return 0
    except (ValueError, OSError, KeyError, TypeError) as error:
        print("supplement packaging rejected: " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
