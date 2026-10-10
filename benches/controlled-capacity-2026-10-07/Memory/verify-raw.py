#!/usr/bin/env python3
"""Read-only checks of actual probe rows, controls and paired proof identity."""
import argparse
import hashlib
import json
from pathlib import Path

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(value):
    data = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
    return hashlib.sha256(data).hexdigest()

def inspect(path):
    rows = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]
    require(all(row.get("schema_version") == "ssgkr.memory-probe.raw.v1" for row in rows), "schema mismatch")
    require(rows[0]["record_type"] == "fixture", "fixture must be first")
    require(rows[-1]["record_type"] == "terminal" and rows[-1]["status"] == "PASS", "terminal PASS absent")
    require(sum(row["record_type"] == "fixture" for row in rows) == 1, "fixture cardinality")
    require(sum(row["record_type"] == "terminal" for row in rows) == 1, "terminal cardinality")
    fixture = rows[0]
    require(fixture["source_sha"] != "UNAVAILABLE" and fixture["probe_sha"] != "UNAVAILABLE", "provenance unavailable")
    require(hashlib.sha256(bytes.fromhex(fixture["circuit_layout_bytes_hex"])).hexdigest() == fixture["circuit_sha256"], "circuit bytes mismatch")
    if fixture["common_fixture"] is not None:
        common = fixture["common_fixture"]
        require(digest(common) == fixture["common_fixture_sha256"], "common fixture SHA mismatch")
        require(common["kind"] == fixture["family"] and common["seed"] == fixture["seed"], "common family/seed mismatch")
        require(common["width"] == 1 << fixture["width_bits"] and common["depth"] == fixture["depth"], "common shape mismatch")
        require(common["input_base_u32"] == fixture["inputs"] and common["output_base_u32"] == fixture["outputs"], "common input/output mismatch")
    samples = [row for row in rows if row["record_type"] == "sample"]
    require(len(samples) == fixture["samples"] + fixture["warmups"], "sample cardinality")
    keys = set()
    for row in samples:
        for key in ["mode", "family", "width_bits", "depth", "seed", "process_repeat", "observer_enabled"]:
            require(row[key] == fixture[key], f"sample fixture drift: {key}")
        key = (row["warmup"], row["sample_index"])
        limit = fixture["warmups"] if row["warmup"] else fixture["samples"]
        require(0 <= row["sample_index"] < limit, "sample index outside declared count")
        require(key not in keys, "duplicate sample identity")
        keys.add(key)
        require(row["accepted"] is True, "proof rejected")
        require(digest(row["canonical_proof"]) == row["canonical_proof_sha256"], "proof SHA mismatch")
        start, end = row["allocator_start"], row["allocator_end"]
        require(end["peak_requested_bytes"] >= start["live_requested_bytes"], "allocator peak below interval baseline")
        require(row["allocator_peak_delta_requested_bytes"] == end["peak_requested_bytes"] - start["live_requested_bytes"], "peak delta mismatch")
        require(row["allocator_live_delta_requested_bytes"] == end["live_requested_bytes"] - start["live_requested_bytes"], "live delta mismatch")
        events = row["events"]
        expected = fixture["depth"] * (1 + 4 * fixture["width_bits"]) if fixture["observer_enabled"] else 0
        require(len(events) == row["event_count"] == expected, "observer event cardinality")
        require(row["event_capacity"] >= len(events), "event buffer capacity")
        offsets = [event["offset_ns"] for event in events]
        require(offsets == sorted(offsets), "nonmonotone observation offsets")
        for event in events:
            for buf in event["buffers"]:
                require(0 <= buf["len"] <= buf["capacity"], "invalid Vec size")
                require(buf["len_payload_bytes"] == buf["len"] * buf["element_bytes"], "len byte accounting")
                require(buf["capacity_payload_bytes"] == buf["capacity"] * buf["element_bytes"], "capacity byte accounting")
        for layer in range(fixture["depth"]):
            local = [event for event in events if event["layer_index"] == layer]
            if not fixture["observer_enabled"]:
                continue
            require(local[0]["stage"] == "constructor", "constructor snapshot absent")
            binds = [event for event in local if event["stage"] == "bind"]
            require(len(binds) == 2 * fixture["width_bits"] and binds[-1]["remaining_variables"] == 0, "binding sequence incomplete")
            # truncate must preserve each oracle-owned table's capacity. Phase2
            # moves v_embed ownership to vy and allocates beta_y/mulx_y.
            first = {buf["name"]: buf for buf in local[0]["buffers"]}
            final = {buf["name"]: buf for buf in binds[-1]["buffers"]}
            stable = ["lin", "pow", "vx", "vy", "beta", "mul"] if fixture["mode"] == "dense" else ["lin_x", "pow_x", "vx", "amul_x", "mul_gates", "xstar"]
            require(all(first[name]["capacity"] == final[name]["capacity"] for name in stable), "retained capacity changed unexpectedly")
    require(sum(not row["warmup"] for row in samples) == fixture["samples"], "timed sample count")
    require(sum(row["warmup"] for row in samples) == fixture["warmups"], "warmup sample count")
    return fixture, samples

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw", type=Path, nargs="+", required=True)
    parser.add_argument("--controls-log", type=Path)
    args = parser.parse_args()
    checked = [inspect(path) for path in args.raw]
    controls = None
    if args.controls_log:
        controls = []
        decoder = json.JSONDecoder()
        for line in args.controls_log.read_text(encoding="utf-8").splitlines():
            # libtest --test-threads=1 writes its test-name prefix before the
            # first println on the same line. Parse the actual JSON object,
            # not the harness prefix or its trailing status text.
            offset = line.find('{"')
            if offset < 0:
                continue
            row, _ = decoder.raw_decode(line[offset:])
            if row.get("schema_version") == "ssgkr.memory-probe.raw.v1":
                controls.append(row)
        families = {row["family"] for row in controls if row.get("record_type") == "controls"}
        require(families == {"mixed", "add", "mul", "cubic_affine"}, "control families incomplete")
        require(sum(row.get("record_type") == "controls" for row in controls) == 4, "control family cardinality")
        require(sum(row.get("record_type") == "allocator_controls" for row in controls) == 1, "allocator control cardinality")
        required = ["whole_proof_equal", "observer_proof_equal", "post_proof_transcript_equal", "dense_accepted", "sparse_accepted", "proof_eval_tamper_rejected", "output_tamper_rejected", "input_tamper_rejected", "input_claim_tamper_rejected"]
        for row in controls:
            if row.get("record_type") == "controls":
                require(row["width"] == 8 and row["depth"] == 3 and row["seed"] == 7, "tiny controls shape/seed drift")
                require(all(row["controls"].get(key) is True for key in required), "control failure")
        require(any(row.get("record_type") == "allocator_controls" and row.get("allocation_growth_truncate_drop") is True for row in controls), "allocator control absent")
    groups = {}
    for fixture, samples in checked:
        key = tuple(fixture[name] for name in ["family", "width_bits", "depth", "seed", "process_repeat", "observer_enabled"])
        modes = groups.setdefault(key, {})
        require(fixture["mode"] not in modes, "duplicate mode/config raw file")
        modes[fixture["mode"]] = (fixture, samples)
    pairs = 0
    for key, modes in groups.items():
        if len(modes) == 2:
            dense, sparse = modes["dense"], modes["sparse"]
            require(dense[0]["circuit_sha256"] == sparse[0]["circuit_sha256"], "paired circuit mismatch")
            require(dense[0]["common_fixture_sha256"] == sparse[0]["common_fixture_sha256"], "paired common fixture mismatch")
            proof_d = {(row["warmup"], row["sample_index"]): row["canonical_proof_sha256"] for row in dense[1]}
            proof_s = {(row["warmup"], row["sample_index"]): row["canonical_proof_sha256"] for row in sparse[1]}
            require(proof_d == proof_s, "paired whole proof bytes mismatch")
            pairs += 1
    print(json.dumps({"schema_version": "ssgkr.memory-probe.validation.v1", "status": "PASS",
        "raw_files": len(checked), "dense_sparse_pairs": pairs,
        "actual_sample_rows": sum(len(samples) for _, samples in checked),
        "controls_checked": controls is not None}, indent=2))

if __name__ == "__main__":
    main()
