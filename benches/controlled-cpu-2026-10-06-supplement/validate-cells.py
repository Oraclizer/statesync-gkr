"""Validate exact cells, paired subcases, samples, source identities and GNU time."""
import csv
import hashlib
import json
import pathlib
import re
import sys

PHASES = {
    "A": [("compile_with_hints","none","single"),("derive_wiring","derived","single"),
          ("circuit_commitment","none","single"),("witness","none","single"),("prove_on","none","single"),
          ("encode","none","serial"),("verify","derived","single"),("verify","table","single"),
          ("encoded_verify","derived","serial")],
    "B": [(phase,oracle,mode) for mode in ("serial","parallel") for phase,oracle in
          (("witness_batch","none"),("prove_batch","none"),("encode_batch","none"),
           ("encoded_verify_batch","derived"),("complete_pipeline","derived"))],
    "C": [("native_predicate","native","single"),("prepared_request","none","single"),
          ("encode","none","serial"),("encoded_verify","derived","serial"),("complete_request","derived","serial")],
}

def validate(plan_path, root, output, smoke=False):
    plan = json.loads(plan_path.read_text())
    expected = {cell["cell_id"]: cell for cell in plan["cells"]}
    config_keys = [(c["suite"],c["kind"],c["depth"],c["batch"],c["workers"],c["variant"]) for c in plan["cells"]]
    wanted_configs = {(s,k,d,b,w,v) for s,k,d,b,w,v in
                      [("A",k,d,1,1,"") for k in ("membership","nonmembership","update") for d in (24,28,32)]
                      +[("B",k,24,b,w,"") for k in ("membership","nonmembership","update") for b in (32,192,768) for w in (48,192)]
                      +[("C","nonmembership" if v=="tombstone_nonmembership" else "membership" if v.endswith("member") else "update",24,1,1,v) for v in
                        ("tombstone_nonmembership","empty_to_occupied","occupied_to_tombstone","tombstone_to_occupied","zero_payload_member","max_payload_member","root_chain_update","large_key_member")]}
    found = {p.name for p in root.iterdir() if p.is_dir()}
    findings = []
    if not smoke and (set(config_keys) != wanted_configs or len(expected) != len(plan["cells"])
            or any(c["samples"]<=0 or c["warmup"]<0 for c in plan["cells"])
            or any({c["repeat"] for c,k in zip(plan["cells"],config_keys) if k==config} != set(range(1,6)) for config in wanted_configs)
            or any(sum(k==config for k in config_keys)!=5 for config in wanted_configs)):
        findings.append("plan35configs/repeats1to5/positive-samples mismatch")
    if (not smoke and len(expected) != 175) or found != set(expected):
        findings.append("exact175 cell set mismatch")
    cells = []
    for identity, cell in expected.items():
        out = root/identity
        if not (out/"metrics.csv").exists():
            findings.append("missing raw metrics: "+identity)
            continue
        rows = list(csv.DictReader((out/"metrics.csv").open(encoding="utf-8", newline="")))
        fixture_path=out/"fixtures.jsonl"
        metadata_path=out/"metadata.json"
        if not fixture_path.exists() or not metadata_path.exists():
            findings.append("required fixture or metadata absent: "+identity)
            continue
        fixtures=[json.loads(line) for line in fixture_path.read_text().splitlines()]
        metadata=json.loads(metadata_path.read_text())
        fixture_count=cell["batch"] if cell["suite"]=="B" else cell["samples"]
        if len(fixtures)!=fixture_count or {f["fixture_id"] for f in fixtures}!=set(range(fixture_count)):
            findings.append("fixture count/unique IDs mismatch: "+identity)
        fixture_map={f["fixture_id"]:f for f in fixtures}
        order_seed=0x5353474B52202026 ^ ((cell["repeat"]*0x9e3779b97f4a7c15)&((1<<64)-1)) ^ cell["order_index"]
        if (metadata.get("fixtures_sha256")!=hashlib.sha256(fixture_path.read_bytes()).hexdigest()
                or metadata.get("fixture_count")!=fixture_count or metadata.get("order_seed")!=order_seed
                or metadata.get("fixture_base_seed")!=0x5353474B52202026
                or not metadata.get("seed_role","").startswith("execution_order_only")
                or any(metadata.get(k)!=cell[k] for k in ("cell_id","suite","kind","depth","batch","workers"))
                or metadata.get("leaf_max_fields")!=31):
            findings.append("metadata/fixture identity/hash mismatch: "+identity)
        circuit_shape=metadata if cell["suite"]=="A" else metadata.get("circuit_shape",{})
        if (not circuit_shape.get("layers") or "input_width_bits" not in circuit_shape
                or any(k not in circuit_shape for k in ("derived_groups","grouped_gates","sparse_gates","grouped_consts","sparse_consts"))
                or not re.fullmatch(r"[0-9a-f]{64}",metadata.get("circuit_sha",""))):
            findings.append("circuit shape/wiring metadata missing: "+identity)
        if cell["suite"]=="C" and cell["variant"]=="root_chain_update":
            for previous,next_fixture in zip(fixtures,fixtures[1:]):
                if (previous["new_root"]!=next_fixture["old_root"] or previous["key"]!=next_fixture["key"]
                        or previous["siblings"]!=next_fixture["siblings"] or previous["new_leaf_encoding"]!=next_fixture["old_leaf_encoding"]):
                    findings.append("root chain fixture continuity mismatch: "+identity)
                    break
        expected_keys = {(phase,oracle,mode,str(warm).lower(),str(index))
                         for phase,oracle,mode in PHASES[cell["suite"]]
                         for warm,count in ((True,cell["warmup"]),(False,cell["samples"]))
                         for index in range(count)}
        actual_keys = [(row["phase"],row["oracle_kind"],row["output_mode"],row["warmup"],row["sample_index"]) for row in rows]
        if set(actual_keys) != expected_keys or len(actual_keys) != len(set(actual_keys)):
            findings.append("phase/warmup/sample keys mismatch: "+identity)
        if any(row["cell_id"] != identity or int(row["process_repeat"]) != cell["repeat"]
               or int(row["order_index"]) != cell["order_index"] or int(row["elapsed_ns"]) <= 0
               or row["accepted"] != "true" or row["exit_code"] != "0"
               or row["source_sha"] != plan["source_archive_sha256"]
               or row["driver_sha"] != plan["driver_manifest_sha256"]
               or row["binary_sha"] != plan["binary_sha256"]
               or int(row["order_seed"])!=order_seed or row["circuit_sha"]!=metadata["circuit_sha"]
               or int(row["depth"])!=cell["depth"] or int(row["batch"])!=cell["batch"]
               or int(row["workers"])!=cell["workers"] or row["kind"]!=cell["kind"] for row in rows):
            findings.append("invalid raw metadata or timing: "+identity)
        artifact_hashes={name:hashlib.sha256((out/name).read_bytes()).hexdigest() for name in ("fixtures.jsonl","metadata.json")}
        if cell["suite"]!="B":
            for row in rows:
                fixture=fixture_map.get(int(row["fixture_id"]))
                if (fixture is None or fixture["kind"]!=row["kind"] or fixture["old_leaf_kind"]!=row["old_leaf_kind"]
                        or fixture["new_leaf_kind"]!=row["new_leaf_kind"]):
                    findings.append("CSV fixture mapping mismatch: "+identity)
                    break
            if cell["suite"]=="C" and cell["variant"]=="root_chain_update":
                chain=[r for r in rows if r["phase"]=="complete_request" and r["warmup"]=="false"]
                if [int(r["fixture_id"]) for r in chain]!=list(range(fixture_count)):
                    findings.append("timed chain sequence mismatch: "+identity)
        else:
            byte_path=out/"encoded-bytes.jsonl"
            if not byte_path.exists():
                findings.append("required encoded-byte raw absent: "+identity)
            else:
                artifact_hashes[byte_path.name]=hashlib.sha256(byte_path.read_bytes()).hexdigest()
                encoded=[json.loads(line) for line in byte_path.read_text().splitlines()]
                expected_byte_keys={(warm,index,mode,fixture) for warm,count in ((True,cell["warmup"]),(False,cell["samples"])) for index in range(count) for mode in ("serial","parallel") for fixture in range(fixture_count)}
                actual_byte_keys=[(e["warmup"],e["sample_index"],e["output_mode"],e["fixture_id"]) for e in encoded]
                if (len(actual_byte_keys)!=len(set(actual_byte_keys)) or set(actual_byte_keys)!=expected_byte_keys
                        or metadata.get("encoded_bytes_log_sha256")!=artifact_hashes[byte_path.name]
                        or metadata.get("output_modes")!=["serial","parallel"]):
                    findings.append("encoded-byte count/unique keys/hash/mode mismatch: "+identity)
                by_batch={}
                for record in encoded:
                    by_batch.setdefault((str(record["warmup"]).lower(),str(record["sample_index"]),record["output_mode"]),[]).append(record)
                for row in rows:
                    data=sorted(by_batch.get((row["warmup"],row["sample_index"],row["output_mode"]),[]),key=lambda e:e["fixture_id"])
                    digest=hashlib.sha256("".join(e["canonical_sha256"] for e in data).encode()).hexdigest()
                    if (len(data)!=fixture_count or sum(e["bytes"] for e in data)!=int(row["encoded_bytes"])
                            or digest!=row["canonical_sha256"] or any(e["bytes"]<=0 or not re.fullmatch(r"[0-9a-f]{64}",e["canonical_sha256"]) for e in data)):
                        findings.append("encoded-byte/CSV fixture-order-byte-hash mismatch: "+identity)
                        break
        temporal = {}
        for row in rows:
            temporal.setdefault((row["warmup"],row["sample_index"]), []).append(row)
        for paired_rows in temporal.values():
            if cell["suite"] == "A":
                if len({(r["fixture_id"],r["canonical_sha256"],r["circuit_sha"]) for r in paired_rows}) != 1:
                    findings.append("paired oracle input/proof mismatch: "+identity)
            elif cell["suite"] == "B":
                if len({r["canonical_sha256"] for r in paired_rows}) != 1:
                    findings.append("paired output canonical mismatch: "+identity)
        text = (out/"process.time.txt").read_text(encoding="utf-8") if (out/"process.time.txt").exists() else ""
        metrics = {}
        for name,pattern in (("rss_kib",r"Maximum resident set size \(kbytes\):\s*(\d+)"),
                             ("user_seconds",r"User time \(seconds\):\s*([\d.]+)"),
                             ("system_seconds",r"System time \(seconds\):\s*([\d.]+)"),
                             ("exit_code",r"Exit status:\s*(\d+)")):
            match = re.search(pattern,text)
            metrics[name] = float(match.group(1)) if match else None
        terminal = out/"terminal.txt"
        exit_path = out/"exit.json"
        if (not terminal.exists() or terminal.read_text().strip() != "supplement-cell=PASS"
                or not exit_path.exists() or json.loads(exit_path.read_text())["exit_code"] != 0
                or any(x is None for x in metrics.values()) or metrics["exit_code"] != 0):
            findings.append("missing exact process/RSS/exit evidence: "+identity)
        cells.append(dict(cell, rows=len(rows), raw_sha256=hashlib.sha256((out/"metrics.csv").read_bytes()).hexdigest(),artifact_sha256=artifact_hashes,process_metrics=metrics))
    terminal = root/"measurement-terminal.txt"
    expected_terminal="supplement-schema-smoke=PASS" if smoke else "supplement175-processes=PASS"
    if not terminal.exists() or terminal.read_text().strip() != expected_terminal:
        findings.append("exact campaign terminal absent")
    result = {"schema":"statesync-gkr.supplement-validation.v1", "status":"PASS" if not findings else "FAIL",
              "cell_count":len(cells),"findings":findings,"cells":cells,
              "notes":["Per-row process user/system seconds and peak RSS fields are intentionally blank; GNU time sidecars supply actual whole-process values.",
                       "Process CPU ticks are quantized observations, distinct from monotonic nanosecond wall intervals.",
                       "Both B output modes share one process peak RSS; no per-output-mode peak is claimed."]}
    output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"status":result["status"],"cells":len(cells),"findings":findings}))
    return not findings

if __name__ == "__main__":
    ok = validate(pathlib.Path(sys.argv[1]),pathlib.Path(sys.argv[2]),pathlib.Path(sys.argv[3]),"--smoke" in sys.argv[4:])
    raise SystemExit(0 if ok else 1)
