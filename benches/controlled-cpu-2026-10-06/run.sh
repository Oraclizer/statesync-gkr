#!/usr/bin/env bash
# Generic Linux replay of the immutable source and B2D5 caller driver.
# Default: a small functional smoke, not the published measurement profile.
# Full: dedicated x86-64 Linux, 192 available physical/logical CPUs, no SMT,
# AVX-512 capability and at least 360 GiB observed memory.
# That memory check matches the recorded 384 GiB host profile; it is not
# a minimum-memory requirement of the engine. Read measured RSS separately.
# No provider resource creation, privilege changes or implicit tool installs.
set -euo pipefail

SOURCE_URL='https://github.com/Oraclizer/statesync-gkr/releases/download/v1.1.0/statesync-gkr-v1.1-source.tar.gz'
SOURCE_SHA='d22e2200378e21a40c254eab8df4d44dfea81f2806f02f0c9030636300d489e9'
DRIVER_SHA='b2d5a631e8527bca90d22065ca3692da48863f236f306d5217e8e4528fa1c75c'
mode=smoke
output=''

usage() {
  cat <<'TEXT'
Usage: bash run.sh --output NEW_DIRECTORY [--mode smoke|full]

smoke runs four accepted/negative fixtures per kind/depth on both builds,
then three prepared timing calls per case. It is not a capacity result.
full runs the fixed 243-cell, batch-768, three-process study. It does not
reproduce a service, delivery pipeline, global state tree or committed log.
Its 360+ GiB check represents the recorded 384 GiB host, not engine minimum
RAM. Other listed hardware/kernel/NUMA/clock profiles remain other-environment
results rather than being promoted to the original machine's measurements.

Install Rust 1.96.1, Python 3.11+, normal Rust build tools, curl, GNU time,
sha256sum, tar, taskset and lscpu beforehand. Output must not exist.
Timed intervals exclude encoding, SHA/control work and proof delivery.
The recorded external program is a separate fixed single-proof example.
TEXT
}

while (($#)); do
  case "$1" in
    --mode) (($# >= 2)) || { usage >&2; exit 2; }; mode=$2; shift 2 ;;
    --output) (($# >= 2)) || { usage >&2; exit 2; }; output=$2; shift 2 ;;
    --help|-h) usage; exit 0 ;;
    *) usage >&2; exit 2 ;;
  esac
done
[[ "$mode" == smoke || "$mode" == full ]] || { usage >&2; exit 2; }
[[ -n "$output" && ! -e "$output" ]] || { printf 'Use a new output directory.\n' >&2; exit 2; }
for tool in cargo rustc python3 curl sha256sum tar taskset lscpu cmp diff; do
  command -v "$tool" >/dev/null || { printf 'Missing tool: %s\n' "$tool" >&2; exit 2; }
done
for variable in CARGO_ENCODED_RUSTFLAGS CARGO_BUILD_TARGET RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER; do
  if [[ -n "${!variable-}" ]]; then
    printf 'Unset %s before replaying the fixed build profile.\n' "$variable" >&2
    exit 2
  fi
done
test -x /usr/bin/time || { printf 'GNU /usr/bin/time is required.\n' >&2; exit 2; }
python3 -c 'import sys; assert sys.version_info >= (3, 11), "Python 3.11+ required"'
cargo +1.96.1 --version >/dev/null

artifact_root=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
summary_tool="$artifact_root/summarize.py"
test -f "$summary_tool"
test -f "$artifact_root/driver/Cargo.toml"
test -f "$artifact_root/driver/Cargo.lock"
printf '%s  %s\n' "$DRIVER_SHA" "$artifact_root/driver/src/main.rs" | sha256sum -c - >/dev/null
python3 - "$artifact_root/driver/Cargo.toml" <<'PY'
import sys, tomllib
with open(sys.argv[1], "rb") as handle:
    config = tomllib.load(handle)
if config.get("dependencies", {}).get("statesync-gkr", {}).get("path") != "../source":
    raise SystemExit("use the measured driver's ../source dependency for the sibling immutable-archive layout")
PY

mkdir -p -- "$output"
work=$(CDPATH= cd -- "$output" && pwd)
results="$work/results"
mkdir -p "$results/controls" "$work/source" "$work/driver/src"
trap 'printf "replay exited with status %s\n" "$?" >&2' EXIT
python3 "$summary_tool" environment --output "$results/environment.json"
python3 - "$results/environment.json" "$mode" <<'PY'
import json, sys
meta = json.load(open(sys.argv[1], encoding="utf-8"))
if sys.argv[2] == "full":
    expected = {"architecture": "x86_64", "physical_cores_available": 192,
                "logical_cpus": 192, "allowed_logical_cpus": 192, "avx512f": True}
    if any(meta.get(key) != value for key, value in expected.items()) or meta["memory_gib"] < 360:
        raise SystemExit("full profile requires 192 available physical/logical CPUs, no SMT, AVX-512 capability and 360+ GiB observed memory; use smoke")
PY
cpus=$(python3 - "$results/environment.json" <<'PY'
import json, sys
meta = json.load(open(sys.argv[1], encoding="utf-8"))
print(",".join(map(str, meta["physical_cpu_list"])))
PY
)
if test -f "$artifact_root/reference-environment.json"; then
  cp "$artifact_root/reference-environment.json" "$results/reference-environment.json"
fi
curl --proto '=https' --tlsv1.2 -fL --retry 2 --max-time 180 -o "$work/source.tar.gz" "$SOURCE_URL"
printf '%s  %s\n' "$SOURCE_SHA" "$work/source.tar.gz" | sha256sum -c - >/dev/null
tar -xzf "$work/source.tar.gz" -C "$work/source"
cp "$artifact_root/driver/Cargo.toml" "$work/driver/Cargo.toml"
cp "$artifact_root/driver/Cargo.lock" "$work/driver/Cargo.lock"
cp "$artifact_root/driver/src/main.rs" "$work/driver/src/main.rs"
printf '%s  %s\n' "$DRIVER_SHA" "$work/driver/src/main.rs" | sha256sum -c - >/dev/null
sha256sum "$work/driver/Cargo.toml" "$work/driver/Cargo.lock" "$work/driver/src/main.rs" > "$work/driver-before.sha256"
python3 "$summary_tool" check-lock "$work/source/Cargo.lock" "$work/driver/Cargo.lock" > "$results/dependency-check.json"
find "$work/source/src" "$work/source/crates" "$work/source/formal" -type f -print0 |
  sort -z | xargs -0 sha256sum > "$work/source-before.sha256"
sha256sum "$work/source/Cargo.toml" "$work/source/Cargo.lock" "$work/source/rust-toolchain.toml" >> "$work/source-before.sha256"
fixtures=4
if [[ "$mode" == full ]]; then fixtures=768; fi
export CARGO_BUILD_JOBS=16
for build_mode in portable native; do
  export CARGO_TARGET_DIR="$work/build-$build_mode"
  if [[ "$build_mode" == native ]]; then export RUSTFLAGS='-Ctarget-cpu=native'; else unset RUSTFLAGS; fi
  cargo +1.96.1 build --release --locked --bins --manifest-path "$work/source/Cargo.toml" > "$work/build-$build_mode.log" 2>&1
  cargo +1.96.1 build --release --locked --manifest-path "$work/driver/Cargo.toml" >> "$work/build-$build_mode.log" 2>&1
  sha256sum "$CARGO_TARGET_DIR/release/ssgkr-benchmark-driver" >> "$work/driver-before.sha256"
  "$CARGO_TARGET_DIR/release/proof_digest" > "$results/proof-digest-$build_mode.txt"
  driver="$CARGO_TARGET_DIR/release/ssgkr-benchmark-driver"
  for depth in 24 28 32; do
    for kind in membership nonmembership update; do
      /usr/bin/time -v -o "$work/control-$build_mode-$kind-d$depth.time.txt" \
        taskset -c "$cpus" "$driver" --kind "$kind" --depth "$depth" --phase controls \
        --mode "$build_mode" --run 0 --workers 1 --batch "$fixtures" --samples 1 \
        --proof-dir "$results/controls" > "$work/control-$build_mode-$kind-d$depth.csv"
    done
  done
done
diff -u "$results/proof-digest-portable.txt" "$results/proof-digest-native.txt" > "$results/proof-digest-comparison.txt"
python3 "$summary_tool" check-controls "$results/controls" --fixtures "$fixtures" > "$results/control-check.json"
driver="$work/build-native/release/ssgkr-benchmark-driver"
run_cell() {
  local run=$1 kind=$2 depth=$3 phase=$4 workers=$5 samples=$6 batch=$7
  local name="native-r$run-$kind-d$depth-$phase-w$workers"
  /usr/bin/time -v -o "$results/$name.time.txt" taskset -c "$cpus" "$driver" \
    --kind "$kind" --depth "$depth" --phase "$phase" --mode native --run "$run" \
    --workers "$workers" --samples "$samples" --batch "$batch" \
    --expected "$results/controls/native-$kind-d$depth.hashes" > "$results/$name.csv"
}
if [[ "$mode" == smoke ]]; then
  for depth in 24 28 32; do
    for kind in membership nonmembership update; do
      run_cell 0 "$kind" "$depth" prepared 1 3 4
    done
  done
else
  for run in 1 2 3; do
    case "$run" in
      1) kinds='membership nonmembership update'; depths='28 32' ;;
      2) kinds='nonmembership update membership'; depths='32 28' ;;
      3) kinds='update membership nonmembership'; depths='28 32' ;;
    esac
    for kind in $kinds; do
      for phase in fresh prepared verify; do run_cell "$run" "$kind" 24 "$phase" 1 1000 768; done
      run_cell "$run" "$kind" 24 seq-prove 1 3 768
      for workers in 1 2 4 8 16 32 48 96 192; do run_cell "$run" "$kind" 24 parallel "$workers" 3 768; done
      for workers in 96 192; do
        run_cell "$run" "$kind" 24 stream "$workers" 3 768
        run_cell "$run" "$kind" 24 stream-parallel-witness "$workers" 3 768
      done
    done
    for depth in $depths; do
      for kind in $kinds; do
        run_cell "$run" "$kind" "$depth" prepared 1 1000 768
        run_cell "$run" "$kind" "$depth" verify 1 1000 768
        for phase in parallel stream stream-parallel-witness; do run_cell "$run" "$kind" "$depth" "$phase" 192 3 768; done
      done
    done
  done
fi
sha256sum -c "$work/source-before.sha256" > "$work/source-after-check.txt"
sha256sum -c "$work/driver-before.sha256" > "$work/driver-after-check.txt"
python3 - "$results/integrity.json" "$SOURCE_SHA" "$DRIVER_SHA" <<'PY'
import json, sys
result = {"source_archive_sha256": sys.argv[2], "driver_sha256": sys.argv[3],
          "source_bytes_unchanged": True, "released_dependencies_match": True,
          "driver_inputs_unchanged": True, "native_binary_unchanged": True,
          "controls_passed": True, "stock_proof_digest_equal": True}
with open(sys.argv[1], "w", encoding="utf-8") as handle:
    json.dump(result, handle, indent=2)
    handle.write("\n")
PY
printf 'cpu-replay-%s=PASS\n' "$mode" > "$results/terminal.txt"
python3 "$summary_tool" summarize "$results" --profile "$mode" \
  --controls "$results/controls" --output "$results/summary.json" \
  --compact-samples "$results/samples.csv"
printf 'Output retained. Smoke is functional validation only; read the summary status and profile.\n'
