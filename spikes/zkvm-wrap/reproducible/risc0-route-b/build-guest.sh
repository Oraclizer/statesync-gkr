#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'

die() { printf 'error: %s\n' "$*" >&2; exit 1; }
need_env() { [[ -n "${!1:-}" ]] || die "required environment variable $1 is missing"; }

decode_guest_id_declaration() {
  local declaration=$1 normalized regex word value hex image_id= i
  local -a parsed
  normalized=$(printf '%s' "$declaration" | tr -d '[:space:]')
  regex='^pubconstSSGKR_RISC0_WRAP_SPIKE_GUEST_ID:\[u32;8\]=\[([0-9]+),([0-9]+),([0-9]+),([0-9]+),([0-9]+),([0-9]+),([0-9]+),([0-9]+)\];$'
  [[ "$normalized" =~ $regex ]] || die "guest ID declaration is structurally invalid"
  parsed=("${BASH_REMATCH[@]:1}")
  (( ${#parsed[@]} == 8 )) || die "guest ID must contain exactly eight decimal u32 words"
  for i in "${!parsed[@]}"; do
    word=${parsed[$i]}
    [[ "$word" =~ ^[0-9]+$ ]] || die "guest ID contains a non-decimal word"
    [[ "$word" == 0 || "$word" != 0* ]] || die "guest ID word is not canonical decimal"
    (( ${#word} <= 10 )) || die "guest ID word exceeds u32 width"
    if (( ${#word} == 10 )); then
      [[ "$word" < 4294967296 ]] || die "guest ID word exceeds u32"
    fi
    value=$((10#$word))
    printf -v hex '%08x' "$value"
    image_id+="${hex:6:2}${hex:4:2}${hex:2:2}${hex:0:2}"
  done
  [[ "$image_id" =~ ^[0-9a-f]{64}$ ]] || die "guest ID conversion failed"
  printf '%s\n' "$image_id"
}

validate_generated_absolute_path() {
  local value=$1 label=$2 component
  local -a components
  [[ "$value" =~ ^/[A-Za-z0-9._/-]+$ ]] \
    || die "$label path is not an unescaped ASCII absolute path"
  [[ "$value" != *"//"* ]] || die "$label path contains a double slash"
  IFS='/' read -r -a components <<<"${value#/}"
  for component in "${components[@]}"; do
    [[ -n "$component" && "$component" != . && "$component" != .. ]] \
      || die "$label path contains an empty or dot component"
  done
}

extract_generated_path_const() {
  local file=$1 symbol=$2 token needle prefix suffix count line value
  token="${symbol}_PATH"
  needle="pub const ${symbol}_PATH: &str ="
  count=$( { grep -Fo "$token" "$file" || true; } | wc -l)
  (( count == 1 )) || die "$symbol PATH declaration is absent or ambiguous"
  line=$(grep -F "$needle" "$file")
  prefix="pub const ${symbol}_PATH: &str = \""
  suffix='";'
  [[ "$line" == "$prefix"*"$suffix" ]] || die "$symbol PATH declaration format mismatch"
  value=${line#"$prefix"}; value=${value%"$suffix"}
  validate_generated_absolute_path "$value" "$symbol PATH"
  printf '%s\n' "$value"
}

extract_generated_upstream_elf_const_path() {
  local file=$1 symbol=$2 token needle prefix suffix count line value
  token="${symbol}_ELF"
  needle="pub const ${symbol}_ELF: &[u8] ="
  count=$( { grep -Fo "$token" "$file" || true; } | wc -l)
  (( count == 1 )) \
    || die "$symbol upstream *_ELF const for the combined program binary is absent or ambiguous"
  line=$(grep -F "$needle" "$file")
  prefix="pub const ${symbol}_ELF: &[u8] = include_bytes!(\""
  suffix='");'
  [[ "$line" == "$prefix"*"$suffix" ]] \
    || die "$symbol upstream *_ELF const for the combined program binary has a format mismatch"
  value=${line#"$prefix"}; value=${value%"$suffix"}
  validate_generated_absolute_path "$value" "$symbol upstream *_ELF const program-binary"
  printf '%s\n' "$value"
}

HOST_TOOLCHAIN_BIN=/root/.rustup/toolchains/1.96.1-x86_64-unknown-linux-gnu/bin
RZUP_BIN=/root/.risc0/bin/rzup
[[ -d "$HOST_TOOLCHAIN_BIN" && -x "$HOST_TOOLCHAIN_BIN/cargo" \
   && -x "$HOST_TOOLCHAIN_BIN/rustc" ]] || die "direct host Rust 1.96.1 toolchain is absent"
[[ -x "$RZUP_BIN" ]] || die "direct rzup binary is absent"
export PATH="$HOST_TOOLCHAIN_BIN:${PATH:-/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin}"
[[ "$(command -v cargo)" == "$HOST_TOOLCHAIN_BIN/cargo" \
   && "$(command -v rustc)" == "$HOST_TOOLCHAIN_BIN/rustc" ]] \
  || die "host Cargo/rustc did not resolve to the direct pinned toolchain"

for cmd in cargo rustc dpkg-query sha256sum grep find sort xargs sed readelf od awk tr realpath cp stat; do
  command -v "$cmd" >/dev/null || die "required container command is unavailable: $cmd"
done
for name in EXPECTED_SOURCE_COMMIT EXPECTED_SOURCE_MANIFEST_SHA256 \
  EXPECTED_GUEST_RUSTC_SHA256 BUILD_LABEL EVIDENCE_ROOT HOST_CARGO_HOME NESTED_HOME; do
  need_env "$name"
done

historical_image_id=2631baa8be7595712cc7275a0133dd78c19448e3cc7d04b7b6d093bfb688e1e2
synthetic_declaration='pub const SSGKR_RISC0_WRAP_SPIKE_GUEST_ID: [u32; 8] = [2830774566, 1905620414, 1512556332, 2027762433, 3813184705, 3070524876, 3214135478, 3806431414];'
[[ "$(decode_guest_id_declaration "$synthetic_declaration")" == "$historical_image_id" ]] \
  || die "guest ID parser/byte-order self-test failed"

[[ "$EVIDENCE_ROOT" = /* && "$HOST_CARGO_HOME" = /* && "$NESTED_HOME" = /* ]] \
  || die "container paths must be absolute"
[[ -d "$EVIDENCE_ROOT" && -d "$HOST_CARGO_HOME" && -d "$NESTED_HOME/.cargo" ]] \
  || die "evidence and both separately seeded Cargo homes must exist"
[[ "$(cat /opt/ssgkr/source-commit.txt)" == "$EXPECTED_SOURCE_COMMIT" ]] \
  || die "source commit identity mismatch"
printf '%s  %s\n' "$EXPECTED_SOURCE_MANIFEST_SHA256" /opt/ssgkr/source-manifest.txt | sha256sum -c -
(cd /workspace/source && sha256sum -c /opt/ssgkr/source-content.sha256) \
  >"$EVIDENCE_ROOT/source-prebuild-check.txt"

host_rustc="$(rustc --version --verbose)"
host_cargo_before="$(cargo --version --verbose)"
grep -Fxq 'release: 1.96.1' <<<"$host_rustc" || die "host rustc release mismatch"
grep -Fxq 'commit-hash: 31fca3adb283cc9dfd56b49cdee9a96eb9c96ffd' <<<"$host_rustc" \
  || die "host rustc commit mismatch"
grep -Fxq 'release: 1.96.1' <<<"$host_cargo_before" || die "host cargo release mismatch"
grep -Fxq 'commit-hash: 356927216a2d746168cf76e5e88cc3f4b58e029d' <<<"$host_cargo_before" \
  || die "host cargo commit mismatch"

guest_rustc=/root/.risc0/toolchains/v1.88.0-rust-x86_64-unknown-linux-gnu/bin/rustc
[[ -x "$guest_rustc" ]] || die "pinned guest rustc is absent"
printf '%s  %s\n' "$EXPECTED_GUEST_RUSTC_SHA256" "$guest_rustc" | sha256sum -c -
guest_version="$($guest_rustc --version --verbose)"
grep -Fxq 'release: 1.88.0-dev' <<<"$guest_version" || die "guest rustc release mismatch"
grep -Fxq 'commit-hash: de85b1d3d7f48a865174798819d943994ed23a37' <<<"$guest_version" \
  || die "guest rustc commit mismatch"

export CARGO_HOME="$HOST_CARGO_HOME"
export HOME="$NESTED_HOME"
export RUSTUP_HOME=/root/.rustup
export RUSTUP_TOOLCHAIN=1.96.1
export RISC0_HOME=/root/.risc0
export RISC0_EXECUTOR=ipc
export RISC0_BUILD_LOCKED=1
export CARGO_NET_OFFLINE=true
unset RISC0_DEV_MODE CARGO_TARGET_DIR RUSTFLAGS RUSTC_WRAPPER

host_cargo_after="$(cargo --version --verbose)"
[[ "$host_cargo_after" == "$host_cargo_before" ]] \
  || die "cargo identity changed after HOME/CARGO_HOME/RUSTUP_HOME isolation"

LC_ALL=C dpkg-query -W -f='${binary:Package}\t${Version}\t${Architecture}\n' \
  | LC_ALL=C sort >"$EVIDENCE_ROOT/dpkg-packages.tsv"
find /root/.rustup/toolchains -mindepth 1 -maxdepth 1 -type d -printf '%f\n' \
  | LC_ALL=C sort >"$EVIDENCE_ROOT/rustup-toolchain-directories.txt"
"$RZUP_BIN" --version >"$EVIDENCE_ROOT/rzup-version.txt"
sha256sum "$HOST_TOOLCHAIN_BIN/rustc" "$HOST_TOOLCHAIN_BIN/cargo" \
  >"$EVIDENCE_ROOT/host-toolchain-binaries.sha256"
printf '%s\n' "$host_rustc" >"$EVIDENCE_ROOT/host-rustc-version.txt"
printf '%s\n' "$host_cargo_after" >"$EVIDENCE_ROOT/host-cargo-version.txt"
printf '%s\n' "$guest_version" >"$EVIDENCE_ROOT/guest-rustc-version.txt"

{
  printf 'source_commit=%s\nsource_manifest_sha256=%s\nbuild_label=%s\n' \
    "$EXPECTED_SOURCE_COMMIT" "$EXPECTED_SOURCE_MANIFEST_SHA256" "$BUILD_LABEL"
  printf 'HOME=%s\nCARGO_HOME=%s\nRUSTUP_HOME=%s\nRUSTUP_TOOLCHAIN=%s\nRISC0_HOME=%s\nPATH=%s\n' \
    "$HOME" "$CARGO_HOME" "$RUSTUP_HOME" "$RUSTUP_TOOLCHAIN" "$RISC0_HOME" \
    "$PATH"
  printf 'HOST_TOOLCHAIN_SELECTION=direct-path\nHOST_TOOLCHAIN_BIN=%s\n' "$HOST_TOOLCHAIN_BIN"
  printf 'NESTED_GUEST_PATH_BOUNDARY=inherits-direct-host-toolchain-prefix\n'
  printf 'RISC0_EXECUTOR=ipc\nRISC0_BUILD_LOCKED=1\nCARGO_NET_OFFLINE=true\n'
  printf 'UNSET=RISC0_DEV_MODE,CARGO_TARGET_DIR,RUSTFLAGS,RUSTC_WRAPPER\n'
  printf '%s\n%s\n%s\n' "$host_rustc" "$host_cargo_after" "$guest_version"
} >"$EVIDENCE_ROOT/toolchain-source-and-env.txt"
printf '%s\n' \
  'RISC0_EXECUTOR=ipc RISC0_BUILD_LOCKED=1 cargo build --release --locked --offline --features prove' \
  >"$EVIDENCE_ROOT/build-command.txt"

cargo metadata --locked --offline --format-version 1 \
  --manifest-path /workspace/source/spikes/zkvm-wrap/risc0-host/Cargo.toml \
  >"$EVIDENCE_ROOT/host-metadata.json" 2>"$EVIDENCE_ROOT/host-metadata.stderr.txt"
cargo metadata --locked --offline --format-version 1 \
  --manifest-path /workspace/source/spikes/zkvm-wrap/risc0-methods/guest/Cargo.toml \
  >"$EVIDENCE_ROOT/guest-metadata.json" 2>"$EVIDENCE_ROOT/guest-metadata.stderr.txt"

cd /workspace/source/spikes/zkvm-wrap/risc0-host
set +e
cargo build --release --locked --offline --features prove \
  >"$EVIDENCE_ROOT/build.stdout.txt" 2>"$EVIDENCE_ROOT/build.stderr.txt"
build_exit=$?
set -e
printf '%s\n' "$build_exit" >"$EVIDENCE_ROOT/build-exit.txt"
(( build_exit == 0 )) || die "locked offline build failed with exit $build_exit"

(cd /workspace/source && sha256sum -c /opt/ssgkr/source-content.sha256) \
  >"$EVIDENCE_ROOT/source-postbuild-check.txt"

target=/workspace/source/spikes/zkvm-wrap/risc0-host/target
target_real=$(realpath -e "$target")
[[ "$target_real" == "$target" ]] || die "target path is not canonical"
find "$target" -type f -printf '%P\n' | LC_ALL=C sort >"$EVIDENCE_ROOT/target-file-list.txt"

host_bin="$target/release/ssgkr-risc0-wrap-spike-host"
[[ -e "$host_bin" ]] || die "release host binary is absent"
[[ -f "$host_bin" ]] || die "release host binary is not a regular file"
[[ ! -L "$host_bin" ]] || die "release host binary must not be a symlink"
host_real=$(realpath -e "$host_bin")
[[ "$host_real" == "$host_bin" ]] || die "release host binary path is not canonical"

mapfile -d '' methods_files < <(find "$target/release/build" -mindepth 3 -maxdepth 3 \
  -path "$target/release/build/ssgkr-risc0-wrap-spike-methods-*/out/methods.rs" \
  -type f -print0)
(( ${#methods_files[@]} == 1 )) || die "expected exactly one generated methods.rs"
methods_rs=${methods_files[0]}
[[ ! -L "$methods_rs" && -f "$methods_rs" ]] || die "generated methods.rs is not a regular non-symlink file"
methods_real=$(realpath -e "$methods_rs")
[[ "$methods_real" == "$methods_rs" \
   && "$methods_real" == "$target_real/release/build/ssgkr-risc0-wrap-spike-methods-"*/out/methods.rs ]] \
  || die "generated methods.rs is outside its strict target descendant scope"
cp -- "$methods_rs" "$EVIDENCE_ROOT/generated-methods.rs"
sha256sum "$EVIDENCE_ROOT/generated-methods.rs" >"$EVIDENCE_ROOT/generated-methods.sha256"

guest_symbol=SSGKR_RISC0_WRAP_SPIKE_GUEST
diagnostic_symbol=SSGKR_RISC0_WRAP_SPIKE_DIAGNOSTIC_GUEST
guest_program=$(extract_generated_path_const "$methods_rs" "$guest_symbol")
diagnostic_program=$(extract_generated_path_const "$methods_rs" "$diagnostic_symbol")
guest_upstream_elf_const=$(extract_generated_upstream_elf_const_path "$methods_rs" "$guest_symbol")
diagnostic_upstream_elf_const=$(extract_generated_upstream_elf_const_path "$methods_rs" "$diagnostic_symbol")
[[ "$guest_program" == "$guest_upstream_elf_const" ]] \
  || die "canonical guest PATH/upstream-ELF-const coupling mismatch"
[[ "$diagnostic_program" == "$diagnostic_upstream_elf_const" ]] \
  || die "diagnostic guest PATH/upstream-ELF-const coupling mismatch"
[[ "$guest_program" != "$diagnostic_program" ]] \
  || die "canonical and diagnostic guest program paths must be distinct"

for tuple in "main:$guest_program:ssgkr-risc0-wrap-spike-guest.bin" \
  "diagnostic:$diagnostic_program:ssgkr-risc0-wrap-spike-diagnostic-guest.bin"; do
  label=${tuple%%:*}; remainder=${tuple#*:}; program=${remainder%%:*}; expected_basename=${remainder#*:}
  [[ "$program" == "$target_real/riscv-guest/"* ]] \
    || die "$label program binary is outside the strict riscv-guest target descendant"
  [[ "${program##*/}" == "$expected_basename" ]] || die "$label program binary basename mismatch"
  [[ -e "$program" ]] || die "$label program binary is absent"
  [[ -f "$program" ]] || die "$label program binary is not a regular file"
  [[ ! -L "$program" ]] || die "$label program binary must not be a symlink"
  program_real=$(realpath -e "$program")
  [[ "$program_real" == "$program" ]] || die "$label program binary textual and resolved paths differ"
  od -An -tx1 -N16 "$program" | tr -d ' \n' >"$EVIDENCE_ROOT/$label-program-binary-first16.hex"
  stat -c '%s' "$program" >"$EVIDENCE_ROOT/$label-program-binary-size.txt"
done

guest_user_elf=${guest_program%.bin}
diagnostic_user_elf=${diagnostic_program%.bin}
[[ "$guest_user_elf" != "$guest_program" && "$diagnostic_user_elf" != "$diagnostic_program" ]] \
  || die "generated program binary paths must end in .bin"
[[ "${guest_user_elf##*/}" == ssgkr-risc0-wrap-spike-guest \
   && "${diagnostic_user_elf##*/}" == ssgkr-risc0-wrap-spike-diagnostic-guest ]] \
  || die "raw user ELF basename mismatch"
[[ "${guest_user_elf%/*}" == "${guest_program%/*}" \
   && "${diagnostic_user_elf%/*}" == "${diagnostic_program%/*}" ]] \
  || die "raw user ELF must share its program binary parent"
[[ "$guest_user_elf" != "$diagnostic_user_elf" ]] || die "raw user ELF paths must be distinct"

for tuple in "main:$guest_user_elf" "diagnostic:$diagnostic_user_elf"; do
  label=${tuple%%:*}; user_elf=${tuple#*:}
  [[ "$user_elf" == "$target_real/riscv-guest/"* ]] \
    || die "$label raw user ELF is outside the strict riscv-guest target descendant"
  [[ -e "$user_elf" ]] || die "$label raw user ELF is absent"
  [[ -f "$user_elf" ]] || die "$label raw user ELF is not a regular file"
  [[ ! -L "$user_elf" ]] || die "$label raw user ELF must not be a symlink"
  user_elf_real=$(realpath -e "$user_elf")
  [[ "$user_elf_real" == "$user_elf" ]] || die "$label raw user ELF textual and resolved paths differ"
  [[ "$(od -An -tx1 -N4 "$user_elf" | tr -d ' \n')" == 7f454c46 ]] \
    || die "$label raw user ELF lacks ELF magic"
  readelf -h "$user_elf" >"$EVIDENCE_ROOT/$label-raw-user-elf-header.txt"
  grep -Eq '^  Class:[[:space:]]+ELF32$' "$EVIDENCE_ROOT/$label-raw-user-elf-header.txt" \
    || die "$label raw user ELF is not ELF32"
  grep -Eq '^  Machine:[[:space:]]+RISC-V$' "$EVIDENCE_ROOT/$label-raw-user-elf-header.txt" \
    || die "$label raw user ELF is not RISC-V"
done

{
  printf 'host=%s\n' "$(realpath --relative-to="$target_real" "$host_bin")"
  printf 'methods=%s\n' "$(realpath --relative-to="$target_real" "$methods_rs")"
  printf 'main_program_binary=%s\n' "$(realpath --relative-to="$target_real" "$guest_program")"
  printf 'diagnostic_program_binary=%s\n' "$(realpath --relative-to="$target_real" "$diagnostic_program")"
  printf 'main_raw_user_elf=%s\n' "$(realpath --relative-to="$target_real" "$guest_user_elf")"
  printf 'diagnostic_raw_user_elf=%s\n' "$(realpath --relative-to="$target_real" "$diagnostic_user_elf")"
} >"$EVIDENCE_ROOT/artifact-paths.txt"

id_decl_count=$(grep -o 'SSGKR_RISC0_WRAP_SPIKE_GUEST_ID' "$methods_rs" | wc -l)
(( id_decl_count == 1 )) || die "canonical guest ID declaration is absent or ambiguous"
id_block=$(sed -n '/pub const SSGKR_RISC0_WRAP_SPIKE_GUEST_ID:/,/];/p' "$methods_rs")
image_id=$(decode_guest_id_declaration "$id_block")
printf '%s\n' "$image_id" >"$EVIDENCE_ROOT/main-guest-image-id.txt"
sha256sum "$guest_program" | awk '{print $1}' >"$EVIDENCE_ROOT/main-guest-program-binary.sha256"

{
  sha256sum "$host_bin" "$guest_program" "$diagnostic_program" \
    "$guest_user_elf" "$diagnostic_user_elf" "$methods_rs"
} | sed "s#  $target/#  #" >"$EVIDENCE_ROOT/artifacts.sha256"
printf 'PASS\n' >"$EVIDENCE_ROOT/build-result.txt"
