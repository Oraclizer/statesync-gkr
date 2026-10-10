#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'
export GIT_NO_REPLACE_OBJECTS=1

die() { printf 'error: %s\n' "$*" >&2; exit 1; }
usage() {
  cat >&2 <<'EOF'
Usage: verify-two-clean-builds.sh \
  --source-repo ABS_PATH --expected-source-commit 40_HEX \
  --cargo-cache-archive ABS_PATH --cargo-cache-manifest ABS_PATH \
  --evidence-root ABS_PRIVATE_PATH \
  [--identity-guard ABS_EXPECTED_IDENTITY_JSON] [--release-line v1|v1.1]

The release line selects the payload profile and the expected identity
record. It defaults to the current line and is derived from the identity
guard when one is given.
EOF
  exit 2
}

SOURCE_REPO= EXPECTED_SOURCE_COMMIT= CACHE_ARCHIVE= CACHE_MANIFEST= EVIDENCE_ROOT=
IDENTITY_GUARD=
REQUESTED_RELEASE_LINE=
CURRENT_RELEASE_LINE=v1.1
SUPPORTED_RELEASE_LINES=(v1 v1.1)
while (( $# )); do
  case "$1" in
    --source-repo) SOURCE_REPO=${2:-}; shift 2 ;;
    --expected-source-commit) EXPECTED_SOURCE_COMMIT=${2:-}; shift 2 ;;
    --cargo-cache-archive) CACHE_ARCHIVE=${2:-}; shift 2 ;;
    --cargo-cache-manifest) CACHE_MANIFEST=${2:-}; shift 2 ;;
    --evidence-root) EVIDENCE_ROOT=${2:-}; shift 2 ;;
    --identity-guard) IDENTITY_GUARD=${2:-}; shift 2 ;;
    --release-line) REQUESTED_RELEASE_LINE=${2:-}; shift 2 ;;
    *) usage ;;
  esac
done

for cmd in git docker ctr python3 sha256sum tar find sort xargs diff cmp awk sed realpath mktemp \
  cp mkdir rm flock df grep stat wc tr head tail uniq; do
  command -v "$cmd" >/dev/null || die "required command is unavailable: $cmd"
done
[[ "$SOURCE_REPO" = /* && "$CACHE_ARCHIVE" = /* && "$CACHE_MANIFEST" = /* \
   && "$EVIDENCE_ROOT" = /* ]] || usage
[[ "$EXPECTED_SOURCE_COMMIT" =~ ^[0-9a-f]{40}$ ]] || usage
[[ -d "$SOURCE_REPO/.git" || -f "$SOURCE_REPO/.git" ]] || die "source Git repository is absent"
[[ -f "$CACHE_ARCHIVE" && -f "$CACHE_MANIFEST" ]] || die "canonical cache inputs are absent"
if [[ -n "$IDENTITY_GUARD" ]]; then
  [[ "$IDENTITY_GUARD" = /* && -f "$IDENTITY_GUARD" ]] || usage
fi
RELEASE_LINE=$CURRENT_RELEASE_LINE
if [[ -n "$REQUESTED_RELEASE_LINE" ]]; then
  release_line_known=0
  for line in "${SUPPORTED_RELEASE_LINES[@]}"; do
    [[ "$REQUESTED_RELEASE_LINE" == "$line" ]] && release_line_known=1
  done
  (( release_line_known == 1 )) || usage
  RELEASE_LINE=$REQUESTED_RELEASE_LINE
fi

mem_available_kib=$(awk '/^MemAvailable:/ {print $2}' /proc/meminfo)
(( mem_available_kib >= 8388608 )) || die "at least 8 GiB available RAM is required"
tmp_parent=${TMPDIR:-/tmp}
disk_available_kib=$(df -Pk "$tmp_parent" | awk 'NR == 2 {print $4}')
(( disk_available_kib >= 31457280 )) || die "at least 30 GiB free workspace disk is required"

source_real=$(realpath "$SOURCE_REPO")
evidence_real=$(realpath -m "$EVIDENCE_ROOT")
[[ "$evidence_real" != "$source_real" && "$evidence_real" != "$source_real"/* ]] \
  || die "evidence root must be outside the source repository"
if [[ -e "$EVIDENCE_ROOT" ]]; then
  [[ -d "$EVIDENCE_ROOT" && -z "$(find "$EVIDENCE_ROOT" -mindepth 1 -print -quit)" ]] \
    || die "evidence root already exists and is not empty"
else
  mkdir -p "$EVIDENCE_ROOT"
fi
printf 'mem_available_kib=%s\ndisk_available_kib=%s\n' \
  "$mem_available_kib" "$disk_available_kib" >"$EVIDENCE_ROOT/resource-preflight.txt"

exec 9>"$tmp_parent/ssgkr-route-b-reproducible-build.lock"
flock -n 9 || die "another reproducible build orchestrator holds the global lock"

work=$(mktemp -d "$tmp_parent/ssgkr-route-b-repro.XXXXXXXX")
container_names=()
cleanup() {
  for name in "${container_names[@]:-}"; do docker rm -f "$name" >/dev/null 2>&1 || true; done
  rm -rf -- "$work"
}
trap cleanup EXIT

if [[ -n "$IDENTITY_GUARD" ]]; then
  expected_identity_real=$(realpath "$IDENTITY_GUARD")
  identity_dir=spikes/zkvm-wrap/identity
  guard_relative=
  guard_line=
  for line in "${SUPPORTED_RELEASE_LINES[@]}"; do
    candidate=risc0-route-b-guest-expected-$line.json
    if [[ "$expected_identity_real" == "$source_real/$identity_dir/$candidate" ]]; then
      guard_relative=$identity_dir/$candidate
      guard_line=$line
      break
    fi
  done
  [[ -n "$guard_relative" ]] \
    || die "identity guard must use a canonical source-controlled expected file"
  if [[ -n "$REQUESTED_RELEASE_LINE" && "$REQUESTED_RELEASE_LINE" != "$guard_line" ]]; then
    die "requested release line contradicts the identity guard"
  fi
  RELEASE_LINE=$guard_line
  git -C "$SOURCE_REPO" show "$EXPECTED_SOURCE_COMMIT:$guard_relative" \
    >"$work/expected-identity.tracked.json"
  cmp -- "$expected_identity_real" "$work/expected-identity.tracked.json" \
    || die "working expected identity differs from the exact subject commit"
  if ! python3 - "$expected_identity_real" >"$work/expected-identity.values" <<'PY'
import json
import re
import sys

with open(sys.argv[1], "r", encoding="utf-8") as handle:
    value = json.load(handle)
if value.get("schema") != "statesync-gkr.risc0-route-b-guest-identity.expected.v1":
    raise SystemExit("unexpected expected identity schema")
if value.get("canonical_source_path") != "/workspace/source":
    raise SystemExit("canonical source path is not /workspace/source")
recipe = value["recipe"]
artifacts = value["artifacts"]
program = artifacts["program_binary"]
input_image = recipe["measured_input_image"]
fields = [
    recipe["source_manifest_sha256"],
    program["sha256"],
    str(program["size_bytes"]),
    artifacts["image_id"],
    artifacts["raw_guest_elf_sha256"],
    artifacts["methods_rs_sha256"],
    artifacts["host_binary_sha256"],
    artifacts["diagnostic_program_binary_sha256"],
    artifacts["diagnostic_raw_guest_elf_sha256"],
]
if not all(isinstance(item, str) and "\n" not in item for item in fields):
    raise SystemExit("expected identity fields must be single-line strings")
if not all(re.fullmatch(r"[0-9a-f]{64}", item) for item in fields[0:2] + fields[3:]):
    raise SystemExit("expected identity contains a malformed SHA-256")
if not isinstance(input_image, str) or not re.fullmatch(r"sha256:[0-9a-f]{64}", input_image):
    raise SystemExit("measured input image is not a pinned evidence ID")
if not re.fullmatch(r"[1-9][0-9]*", fields[2]):
    raise SystemExit("expected program-binary size is invalid")
print("\n".join(fields))
PY
  then
    die "expected identity JSON validation failed"
  fi
  mapfile -t expected_identity_values <"$work/expected-identity.values"
  (( ${#expected_identity_values[@]} == 9 )) || die "expected identity field count mismatch"
  EXPECTED_SOURCE_MANIFEST_GUARD=${expected_identity_values[0]}
  EXPECTED_PROGRAM_BINARY_GUARD=${expected_identity_values[1]}
  EXPECTED_PROGRAM_SIZE_GUARD=${expected_identity_values[2]}
  EXPECTED_IMAGE_ID_GUARD=${expected_identity_values[3]}
  EXPECTED_RAW_ELF_GUARD=${expected_identity_values[4]}
  EXPECTED_METHODS_GUARD=${expected_identity_values[5]}
  EXPECTED_HOST_GUARD=${expected_identity_values[6]}
  EXPECTED_DIAGNOSTIC_PROGRAM_GUARD=${expected_identity_values[7]}
  EXPECTED_DIAGNOSTIC_RAW_ELF_GUARD=${expected_identity_values[8]}
fi

TOOLCHAIN_IMAGE_REF=ssgkr-route-b-toolchain-acquired:rust-1.96.1
TOOLCHAIN_LOCAL_REF=ssgkr-route-b-toolchain-local:payload-v1
PINNED_BASE=docker.io/risczero/risc0-guest-builder@sha256:3e12f71bacd27527a61dea96fa0e53e468c99aa261d3a1019b593f6dbd943eb3
HOST_LOCK_SHA256=c030936ed7810cb2fbf1e037a365a5d9aa37b44ec00e7be3cb2c70cae7fe7715
GUEST_LOCK_SHA256=be809dbac9425af0f84c70ef322a122ade9957820434c7644b83f109504f8eb0
CACHE_ARCHIVE_SHA256=050c369d0b52bfbd2584e85425ac259634fc230a930e61eaa50499b1e66ba975
CACHE_MANIFEST_SHA256=f1f751a88f832711a4ec31c7aafcfa90e1983120465376749594ed9821612b86
CACHE_FILE_COUNT=13966
HISTORICAL_PROGRAM_BINARY_SHA256=2283ea1d0433c7e208a5463635570782ac0b56581099fc60b6bef739b33aa7dc
HISTORICAL_IMAGE_ID=2631baa8be7595712cc7275a0133dd78c19448e3cc7d04b7b6d093bfb688e1e2

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
PROFILE_NAMES=()
for line in "${SUPPORTED_RELEASE_LINES[@]}"; do
  PROFILE_NAMES+=("toolchain-payload-profile-$line.json")
done
PAYLOAD_PROFILE=$SCRIPT_DIR/toolchain-payload-profile-$RELEASE_LINE.json
[[ -f "$PAYLOAD_PROFILE" ]] || die "payload profile is absent for release line $RELEASE_LINE"
EXPECTED_IDENTITY_NAME=risc0-route-b-guest-expected-$RELEASE_LINE.json
PAYLOAD_VALIDATOR=$SCRIPT_DIR/validate-toolchain-payload-v1.py
RECIPE_PATH=spikes/zkvm-wrap/reproducible/risc0-route-b
recipe_files=(Dockerfile build-guest.sh verify-two-clean-builds.sh toolchain-checksums.txt README.md "${PROFILE_NAMES[@]}" validate-toolchain-payload-v1.py)
mkdir -p "$work/recipe-snapshot"
for file in "${recipe_files[@]}"; do cp -- "$SCRIPT_DIR/$file" "$work/recipe-snapshot/$file"; done
(cd "$work/recipe-snapshot" && sha256sum "${recipe_files[@]}" >recipe-snapshot.sha256)
cp "$work/recipe-snapshot/recipe-snapshot.sha256" "$EVIDENCE_ROOT/recipe-snapshot.sha256"

replace_refs=$(git -C "$SOURCE_REPO" for-each-ref --format='%(refname) %(objectname)' refs/replace)
printf '%s\n' "$replace_refs" >"$EVIDENCE_ROOT/git-replace-refs.txt"
[[ -z "$replace_refs" ]] || die "Git replace refs are forbidden"
git -C "$SOURCE_REPO" cat-file -e "$EXPECTED_SOURCE_COMMIT^{commit}"
# The published repository carries a clean, single-root history, so the anchor
# is that root commit rather than a development checkpoint that is not reachable
# here. Requiring exactly one root keeps the check fail-closed: a grafted or
# unrelated history cannot satisfy it.
mapfile -t source_roots < <(git -C "$SOURCE_REPO" rev-list --max-parents=0 "$EXPECTED_SOURCE_COMMIT")
(( ${#source_roots[@]} == 1 )) || die "expected source commit does not have exactly one root commit"
BASE_CHECKPOINT=${source_roots[0]}
printf '%s\n' "$BASE_CHECKPOINT" >"$EVIDENCE_ROOT/source-root-commit.txt"
git -C "$SOURCE_REPO" merge-base --is-ancestor "$BASE_CHECKPOINT" "$EXPECTED_SOURCE_COMMIT" \
  || die "expected source commit does not descend from the repository root commit"
for file in "${recipe_files[@]}"; do
  tracked_hash=$(git -C "$SOURCE_REPO" show "$EXPECTED_SOURCE_COMMIT:$RECIPE_PATH/$file" | sha256sum | awk '{print $1}')
  snapshot_hash=$(sha256sum "$work/recipe-snapshot/$file" | awk '{print $1}')
  [[ "$tracked_hash" == "$snapshot_hash" ]] || die "recipe snapshot differs from expected commit: $file"
done

pin() { awk -v label="$1" '$2 == label { print $1 }' "$work/recipe-snapshot/toolchain-checksums.txt"; }
GUEST_RUSTC_SHA256=$(pin guest-rustc-binary)
[[ "$(pin risc0-guest-builder-repo-digest)" == "${PINNED_BASE##*@sha256:}" ]] || die "base pin mismatch"
for profile_name in "${PROFILE_NAMES[@]}"; do
  profile_pin=$(pin "$profile_name")
  [[ -n "$profile_pin" ]] || die "toolchain payload profile is unpinned: $profile_name"
  [[ "$(sha256sum "$SCRIPT_DIR/$profile_name" | awk '{print $1}')" == "$profile_pin" ]] \
    || die "toolchain payload profile checksum mismatch: $profile_name"
done
[[ "$(pin risc0-host-Cargo.lock)" == "$HOST_LOCK_SHA256" \
   && "$(pin risc0-guest-Cargo.lock)" == "$GUEST_LOCK_SHA256" ]] || die "lock pin mismatch"
[[ "$(pin canonical-cargo-cache.tar)" == "$CACHE_ARCHIVE_SHA256" \
   && "$(pin canonical-cargo-cache-manifest)" == "$CACHE_MANIFEST_SHA256" ]] || die "cache pin mismatch"
[[ "$(sha256sum "$CACHE_ARCHIVE" | awk '{print $1}')" == "$CACHE_ARCHIVE_SHA256" ]] \
  || die "canonical Cargo cache archive checksum mismatch"
[[ "$(sha256sum "$CACHE_MANIFEST" | awk '{print $1}')" == "$CACHE_MANIFEST_SHA256" ]] \
  || die "canonical Cargo cache manifest checksum mismatch"
cp "$CACHE_MANIFEST" "$EVIDENCE_ROOT/canonical-cache-manifest.sha256"

tar -tf "$CACHE_ARCHIVE" >"$EVIDENCE_ROOT/cache-tar-members.txt"
tar -tvf "$CACHE_ARCHIVE" >"$EVIDENCE_ROOT/cache-tar-members-verbose.txt"
cache_root_member_count=0
while IFS= read -r member; do
  if [[ "$member" == ./ ]]; then
    (( cache_root_member_count += 1 ))
    continue
  fi
  normalized=${member#./}
  [[ -n "$normalized" && "$normalized" != /* && ! "$normalized" =~ (^|/)\.\.(/|$) ]] \
    || die "unsafe cache tar member path"
  [[ "$normalized" != config && "$normalized" != config.toml \
     && "$normalized" != .cargo/config && "$normalized" != .cargo/config.toml ]] \
    || die "Cargo cache archive contains a configuration file"
done <"$EVIDENCE_ROOT/cache-tar-members.txt"
(( cache_root_member_count == 1 )) \
  || die "cache archive must contain exactly one canonical root directory member"
expected_idx_hardlink='./git/db/creusot-1ab658fd39688aa3/objects/pack/pack-509beb6242eb7658f971a740bc177fa9c0016d67.idx link to ./git/checkouts/creusot-1ab658fd39688aa3/7af97e0/.git/objects/pack/pack-509beb6242eb7658f971a740bc177fa9c0016d67.idx'
expected_pack_hardlink='./git/db/creusot-1ab658fd39688aa3/objects/pack/pack-509beb6242eb7658f971a740bc177fa9c0016d67.pack link to ./git/checkouts/creusot-1ab658fd39688aa3/7af97e0/.git/objects/pack/pack-509beb6242eb7658f971a740bc177fa9c0016d67.pack'
hardlink_count=0 idx_hardlink_count=0 pack_hardlink_count=0
while IFS= read -r verbose_member; do
  case ${verbose_member:0:1} in
    -|d) ;;
    h)
      (( hardlink_count += 1 ))
      if [[ "$verbose_member" == *"$expected_idx_hardlink" ]]; then
        (( idx_hardlink_count += 1 ))
      elif [[ "$verbose_member" == *"$expected_pack_hardlink" ]]; then
        (( pack_hardlink_count += 1 ))
      else
        die "cache archive contains an unapproved hardlink"
      fi
      ;;
    *) die "cache archive contains a symlink, device or other special member" ;;
  esac
done <"$EVIDENCE_ROOT/cache-tar-members-verbose.txt"
(( hardlink_count == 2 && idx_hardlink_count == 1 && pack_hardlink_count == 1 )) \
  || die "cache archive hardlink set differs from the exact approved pair"
manifest_line_count=$(wc -l <"$CACHE_MANIFEST")
(( manifest_line_count == CACHE_FILE_COUNT )) || die "canonical cache manifest file count mismatch"
while IFS= read -r line; do
  [[ "$line" =~ ^[0-9a-f]{64}\ \  ]] || die "cache manifest is not canonical sha256sum format"
  member=${line:66}
  [[ -n "$member" && "$member" != /* && ! "$member" =~ (^|/)\.\.(/|$) ]] \
    || die "unsafe cache manifest path"
done <"$CACHE_MANIFEST"
awk '{print substr($0,67)}' "$CACHE_MANIFEST" | LC_ALL=C sort | uniq -d \
  >"$EVIDENCE_ROOT/cache-manifest-duplicate-paths.txt"
[[ ! -s "$EVIDENCE_ROOT/cache-manifest-duplicate-paths.txt" ]] \
  || die "canonical cache manifest contains duplicate paths"
IMMUTABLE_CACHE_MANIFEST="$work/immutable-dependency-cache.sha256"
awk 'substr($0,67) ~ /^\.\/(registry\/src|registry\/cache|git\/checkouts|git\/db)(\/|$)/' \
  "$CACHE_MANIFEST" >"$IMMUTABLE_CACHE_MANIFEST"
immutable_cache_count=$(wc -l <"$IMMUTABLE_CACHE_MANIFEST")
(( immutable_cache_count > 0 )) || die "immutable dependency cache subset is empty"
cp "$IMMUTABLE_CACHE_MANIFEST" "$EVIDENCE_ROOT/immutable-dependency-cache.sha256"
printf 'canonical_file_count=%s\nimmutable_subset_file_count=%s\napproved_hardlink_count=%s\n' \
  "$CACHE_FILE_COUNT" "$immutable_cache_count" "$hardlink_count" \
  >"$EVIDENCE_ROOT/cache-structure-summary.txt"

allowlist=(
  Cargo.toml Cargo.lock rust-toolchain.toml src crates
  spikes/zkvm-wrap/common spikes/zkvm-wrap/risc0-host spikes/zkvm-wrap/risc0-methods
  tests/vectors/inner-proof-v1/membership-d24.bin
)
mkdir -p "$work/context/source"
git -C "$SOURCE_REPO" ls-tree -r -z "$EXPECTED_SOURCE_COMMIT" -- "${allowlist[@]}" >"$work/source-tree.zlist"
git -C "$SOURCE_REPO" ls-tree -r "$EXPECTED_SOURCE_COMMIT" -- "${allowlist[@]}" \
  >"$EVIDENCE_ROOT/source-git-tree.txt"
git -C "$SOURCE_REPO" archive --format=tar --output="$work/source.tar" \
  "$EXPECTED_SOURCE_COMMIT" -- "${allowlist[@]}"
sha256sum "$work/source.tar" >"$EVIDENCE_ROOT/source-archive.sha256"
tar -xf "$work/source.tar" -C "$work/context/source"
[[ -z "$(find "$work/context/source" -type l -print -quit)" ]] || die "source export contains a symlink"
[[ -z "$(find "$work/context/source" ! -type f ! -type d -print -quit)" ]] \
  || die "source export contains a special file"

: >"$work/context/source-manifest.txt"
: >"$work/context/source-content.sha256"
tree_count=0
while IFS= read -r -d '' entry; do
  header=${entry%%$'\t'*}; path=${entry#*$'\t'}
  IFS=' ' read -r mode type object <<<"$header"
  [[ "$type" == blob && ( "$mode" == 100644 || "$mode" == 100755 ) ]] \
    || die "source allowlist contains a symlink, submodule or special Git mode"
  [[ "$path" != *$'\n'* && "$path" != *$'\t'* && "$path" != *'\\'* ]] \
    || die "source allowlist contains an unsupported path"
  [[ -f "$work/context/source/$path" ]] || die "source archive omitted a declared blob"
  content_sha=$(sha256sum "$work/context/source/$path" | awk '{print $1}')
  printf '%s\t%s\t%s\n' "$mode" "$content_sha" "$path" >>"$work/context/source-manifest.txt"
  printf '%s  ./%s\n' "$content_sha" "$path" >>"$work/context/source-content.sha256"
  (( tree_count += 1 ))
done <"$work/source-tree.zlist"
actual_file_count=$(find "$work/context/source" -type f | wc -l)
(( tree_count == actual_file_count && tree_count > 0 )) || die "source export file-set discrepancy"
SOURCE_MANIFEST_SHA256=$(sha256sum "$work/context/source-manifest.txt" | awk '{print $1}')
if [[ -n "$IDENTITY_GUARD" ]]; then
  [[ "$SOURCE_MANIFEST_SHA256" == "$EXPECTED_SOURCE_MANIFEST_GUARD" ]] \
    || die "identity guard source manifest differs from the stabilized measurement"
fi
cp "$work/context/source-manifest.txt" "$work/context/source-content.sha256" "$EVIDENCE_ROOT/"
printf '%s\n' "$EXPECTED_SOURCE_COMMIT" >"$work/context/source-commit.txt"
printf '%s\n' "$EXPECTED_SOURCE_COMMIT" >"$EVIDENCE_ROOT/source-commit.txt"
git -C "$SOURCE_REPO" show \
  "$EXPECTED_SOURCE_COMMIT:spikes/zkvm-wrap/identity/$EXPECTED_IDENTITY_NAME" \
  >"$work/profile-expected-identity.json"

printf '%s  %s\n' "$HOST_LOCK_SHA256" "$work/context/source/spikes/zkvm-wrap/risc0-host/Cargo.lock" | sha256sum -c -
printf '%s  %s\n' "$GUEST_LOCK_SHA256" "$work/context/source/spikes/zkvm-wrap/risc0-methods/guest/Cargo.lock" | sha256sum -c -
cp "$work/recipe-snapshot/Dockerfile" "$work/recipe-snapshot/build-guest.sh" "$work/context/"

docker buildx version >"$EVIDENCE_ROOT/buildx-version.txt"
docker buildx inspect >"$EVIDENCE_ROOT/buildx-inspect.txt"
grep -Eq '^Driver:[[:space:]]+docker[[:space:]]*$' "$EVIDENCE_ROOT/buildx-inspect.txt" \
  || die "Buildx driver must be the local docker driver"
grep -Eq '^Status:[[:space:]]+running[[:space:]]*$' "$EVIDENCE_ROOT/buildx-inspect.txt" \
  || die "Buildx builder is not running"
grep -Eq '^Platforms:.*(^|,|[[:space:]])linux/amd64\*?(,|[[:space:]]|$)' "$EVIDENCE_ROOT/buildx-inspect.txt" \
  || die "Buildx builder does not advertise linux/amd64"
docker image inspect "$PINNED_BASE" "$TOOLCHAIN_IMAGE_REF" >"$EVIDENCE_ROOT/toolchain-images.inspect.json"
docker image history --no-trunc "$TOOLCHAIN_IMAGE_REF" >"$EVIDENCE_ROOT/toolchain-image-history.txt"
grep -Fq 'ENV RUSTUP_TOOLCHAIN=1.96.1' "$EVIDENCE_ROOT/toolchain-image-history.txt" \
  || die "toolchain image history lacks the exact RUSTUP_TOOLCHAIN environment"
grep -Fq 'rustup toolchain install 1.96.1 --profile minimal' "$EVIDENCE_ROOT/toolchain-image-history.txt" \
  || die "toolchain image history lacks the exact host Rust acquisition command"
python3 "$PAYLOAD_VALIDATOR" \
  --profile "$PAYLOAD_PROFILE" --image "$TOOLCHAIN_IMAGE_REF" --pinned-base "$PINNED_BASE" \
  --cache-archive "$CACHE_ARCHIVE" --cache-manifest "$CACHE_MANIFEST" \
  --source-repo "$SOURCE_REPO" --source-commit "$EXPECTED_SOURCE_COMMIT" \
  --expected-identity "$work/profile-expected-identity.json" \
  --evidence-output "$EVIDENCE_ROOT/toolchain-payload-before.json" \
  --self-test-mutations >"$EVIDENCE_ROOT/toolchain-payload-before.stdout.json"
TOOLCHAIN_RUNTIME_MANIFEST=$(python3 - "$EVIDENCE_ROOT/toolchain-payload-before.json" <<'PY'
import json, sys
value = json.load(open(sys.argv[1], encoding="utf-8"))
if value.get("toolchain_payload_equivalence") != "PASS":
    raise SystemExit("toolchain payload did not pass")
print(value["packaging_observation"]["runtime_manifest_digest"])
PY
)
binding_created=0
if docker image inspect "$TOOLCHAIN_LOCAL_REF" >"$EVIDENCE_ROOT/toolchain-local-binding-before.inspect.json" 2>"$EVIDENCE_ROOT/toolchain-local-binding-before.stderr.txt"; then
  python3 "$PAYLOAD_VALIDATOR" \
    --profile "$PAYLOAD_PROFILE" --image "$TOOLCHAIN_LOCAL_REF" --pinned-base "$PINNED_BASE" \
    --cache-archive "$CACHE_ARCHIVE" --cache-manifest "$CACHE_MANIFEST" \
    --source-repo "$SOURCE_REPO" --source-commit "$EXPECTED_SOURCE_COMMIT" \
    --expected-identity "$work/profile-expected-identity.json" \
    --evidence-output "$EVIDENCE_ROOT/toolchain-local-binding-before.json" \
    >"$EVIDENCE_ROOT/toolchain-local-binding-before.stdout.json"
else
  docker image tag "$TOOLCHAIN_IMAGE_REF" "$TOOLCHAIN_LOCAL_REF"
  binding_created=1
fi
docker image inspect "$TOOLCHAIN_LOCAL_REF" >"$EVIDENCE_ROOT/toolchain-local-binding-after-create.inspect.json"
[[ "$(docker image inspect --platform linux/amd64 --format '{{.Id}}' "$TOOLCHAIN_LOCAL_REF")" \
   == "$TOOLCHAIN_RUNTIME_MANIFEST" ]] \
  || die "dedicated local toolchain binding did not retain the inspected runtime manifest"
printf 'binding_ref=%s\nbinding_created=%s\nruntime_manifest=%s\n' \
  "$TOOLCHAIN_LOCAL_REF" "$binding_created" "$TOOLCHAIN_RUNTIME_MANIFEST" \
  >"$EVIDENCE_ROOT/toolchain-local-binding.txt"
base_layers=$(docker image inspect --format '{{join .RootFS.Layers " "}}' "$PINNED_BASE")
toolchain_layers=$(docker image inspect --platform linux/amd64 --format '{{join .RootFS.Layers " "}}' "$TOOLCHAIN_LOCAL_REF")
[[ "$toolchain_layers" == "$base_layers"* ]] || die "toolchain image does not extend pinned base layers"

input_tag="ssgkr-route-b-input:${EXPECTED_SOURCE_COMMIT:0:12}-${SOURCE_MANIFEST_SHA256:0:12}"
docker buildx build --load --pull=false --network=none --platform linux/amd64 --target input \
  --metadata-file "$EVIDENCE_ROOT/input-image-build-metadata.json" \
  --file "$work/context/Dockerfile" \
  --build-arg "TOOLCHAIN_IMAGE=$TOOLCHAIN_LOCAL_REF" \
  --build-arg "EXPECTED_SOURCE_COMMIT=$EXPECTED_SOURCE_COMMIT" \
  --build-arg "EXPECTED_SOURCE_MANIFEST_SHA256=$SOURCE_MANIFEST_SHA256" \
  --tag "$input_tag" "$work/context" >"$EVIDENCE_ROOT/image-build.stdout.txt" \
  2>"$EVIDENCE_ROOT/image-build.stderr.txt"
[[ -s "$EVIDENCE_ROOT/input-image-build-metadata.json" ]] \
  || die "BuildKit metadata file is absent or empty"
metadata_compact=$(tr -d '[:space:]' <"$EVIDENCE_ROOT/input-image-build-metadata.json")
[[ "$(printf '%s' "$metadata_compact" | head -c 1)" == '{' \
   && "$(printf '%s' "$metadata_compact" | tail -c 1)" == '}' ]] \
  || die "BuildKit metadata does not look like a JSON object"
python3 "$PAYLOAD_VALIDATOR" \
  --profile "$PAYLOAD_PROFILE" --image "$TOOLCHAIN_LOCAL_REF" --pinned-base "$PINNED_BASE" \
  --cache-archive "$CACHE_ARCHIVE" --cache-manifest "$CACHE_MANIFEST" \
  --source-repo "$SOURCE_REPO" --source-commit "$EXPECTED_SOURCE_COMMIT" \
  --expected-identity "$work/profile-expected-identity.json" \
  --evidence-output "$EVIDENCE_ROOT/toolchain-payload-after-input-build.json" \
  >"$EVIDENCE_ROOT/toolchain-payload-after-input-build.stdout.json"
[[ "$(docker image inspect --platform linux/amd64 --format '{{.Id}}' "$TOOLCHAIN_LOCAL_REF")" \
   == "$TOOLCHAIN_RUNTIME_MANIFEST" ]] \
  || die "dedicated local toolchain binding changed during input-image construction"
docker image inspect "$TOOLCHAIN_LOCAL_REF" >"$EVIDENCE_ROOT/toolchain-local-binding-after-build.inspect.json"
printf 'toolchain-payload-equivalence=PASS\nprofile-sha256=%s\nruntime-manifest=%s\n' \
  "$(sha256sum "$PAYLOAD_PROFILE" | awk '{print $1}')" "$TOOLCHAIN_RUNTIME_MANIFEST" \
  >"$EVIDENCE_ROOT/toolchain-payload-summary.txt"
INPUT_IMAGE_ID=$(docker image inspect --format '{{.Id}}' "$input_tag")
docker image inspect "$input_tag" >"$EVIDENCE_ROOT/input-image.inspect.json"
[[ "$(docker image inspect --format '{{.Os}}/{{.Architecture}}' "$INPUT_IMAGE_ID")" == linux/amd64 ]] \
  || die "input image platform is not linux/amd64"
[[ "$(docker image inspect --format '{{index .Config.Labels "io.oraclizer.statesync-gkr.source-commit"}}' "$INPUT_IMAGE_ID")" \
   == "$EXPECTED_SOURCE_COMMIT" ]] || die "input image source-commit label mismatch"
[[ "$(docker image inspect --format '{{index .Config.Labels "io.oraclizer.statesync-gkr.source-manifest-sha256"}}' "$INPUT_IMAGE_ID")" \
   == "$SOURCE_MANIFEST_SHA256" ]] || die "input image source-manifest label mismatch"
input_layers=$(docker image inspect --format '{{join .RootFS.Layers " "}}' "$INPUT_IMAGE_ID")
[[ "$input_layers" == "$toolchain_layers"* ]] || die "input image is not rooted in exact toolchain image"

verify_immutable_cache() {
  local root=$1 evidence=$2 label=$3 phase=$4 actual
  actual="$evidence/$label-cache-immutable-$phase.sha256"
  (cd "$root" && sha256sum -c "$IMMUTABLE_CACHE_MANIFEST") \
    >"$evidence/$label-cache-immutable-$phase-check.txt"
  (cd "$root" && find ./registry/src ./registry/cache ./git/checkouts ./git/db \
    -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum) >"$actual"
  diff -u "$IMMUTABLE_CACHE_MANIFEST" "$actual" \
    >"$evidence/$label-cache-immutable-$phase-discrepancy.diff" \
    || die "$label immutable dependency cache changed during $phase verification"
}

seed_cache() {
  local destination=$1 evidence=$2 label=$3
  mkdir -p "$destination"
  tar -xf "$CACHE_ARCHIVE" -C "$destination"
  [[ -z "$(find "$destination" -type l -print -quit)" ]] || die "$label cache extract contains a symlink"
  [[ -z "$(find "$destination" ! -type f ! -type d -print -quit)" ]] \
    || die "$label cache extract contains a special file"
  [[ ! -e "$destination/config" && ! -e "$destination/config.toml" \
     && ! -e "$destination/.cargo/config" && ! -e "$destination/.cargo/config.toml" ]] \
    || die "$label cache extract contains Cargo configuration"
  (cd "$destination" && sha256sum -c "$CACHE_MANIFEST") >"$evidence/$label-cache-check.txt"
  local regular_file_count
  regular_file_count=$(find "$destination" -type f | wc -l)
  (( regular_file_count == CACHE_FILE_COUNT )) || die "$label cache extract file count mismatch"
  (cd "$destination" && find . -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum) \
    >"$evidence/$label-cache-tree.sha256"
  diff -u "$CACHE_MANIFEST" "$evidence/$label-cache-tree.sha256" \
    >"$evidence/$label-cache-full-set-discrepancy.diff" \
    || die "$label cache extract differs from the unique canonical file set"
  verify_immutable_cache "$destination" "$evidence" "$label" prebuild
}

run_once() {
  local ordinal=$1 run="$work/run-$1" evidence="$EVIDENCE_ROOT/run-$1"
  mkdir -p "$run/host-cargo-home" "$run/nested-home/.cargo" "$run/target" "$evidence"
  seed_cache "$run/host-cargo-home" "$evidence" host
  seed_cache "$run/nested-home/.cargo" "$evidence" nested
  local name="ssgkr-route-b-${EXPECTED_SOURCE_COMMIT:0:12}-$ordinal-$$"
  container_names+=("$name")
  docker create --platform linux/amd64 --name "$name" --network none --read-only \
    --tmpfs /tmp:rw,exec,nosuid,nodev,size=4g \
    --mount "type=bind,src=$run/host-cargo-home,dst=/workspace/host-cargo-home" \
    --mount "type=bind,src=$run/nested-home,dst=/workspace/nested-home" \
    --mount "type=bind,src=$run/target,dst=/workspace/source/spikes/zkvm-wrap/risc0-host/target" \
    --mount "type=bind,src=$evidence,dst=/evidence" \
    --env "EXPECTED_SOURCE_COMMIT=$EXPECTED_SOURCE_COMMIT" \
    --env "EXPECTED_SOURCE_MANIFEST_SHA256=$SOURCE_MANIFEST_SHA256" \
    --env "EXPECTED_GUEST_RUSTC_SHA256=$GUEST_RUSTC_SHA256" \
    --env "BUILD_LABEL=clean-$ordinal" --env EVIDENCE_ROOT=/evidence \
    --env HOST_CARGO_HOME=/workspace/host-cargo-home --env NESTED_HOME=/workspace/nested-home \
    "$INPUT_IMAGE_ID" >"$evidence/container-id.txt"
  docker inspect "$name" >"$evidence/container-before.inspect.json"
  [[ "$(docker inspect --format '{{.HostConfig.NetworkMode}}' "$name")" == none ]] \
    || die "container network mode is not none"
  [[ "$(docker inspect --format '{{.HostConfig.ReadonlyRootfs}}' "$name")" == true ]] \
    || die "container root filesystem is not read-only"
  local tmpfs_config
  tmpfs_config=$(docker inspect --format '{{index .HostConfig.Tmpfs "/tmp"}}' "$name")
  [[ "$tmpfs_config" == *rw* && "$tmpfs_config" == *exec* \
     && "$tmpfs_config" == *nosuid* && "$tmpfs_config" == *nodev* \
     && ( "$tmpfs_config" == *size=4g* || "$tmpfs_config" == *size=4294967296* ) ]] \
    || die "container /tmp tmpfs policy mismatch"
  [[ "$(docker inspect --format '{{.Image}}' "$name")" == "$INPUT_IMAGE_ID" ]] \
    || die "container image differs from exact input image"
  set +e
  docker start --attach "$name" >"$evidence/container.stdout.txt" 2>"$evidence/container.stderr.txt"
  local start_exit=$?
  set -e
  docker inspect "$name" >"$evidence/container-after.inspect.json"
  printf '%s\n' "$start_exit" >"$evidence/container-start-exit.txt"
  [[ "$(docker inspect --format '{{.State.Status}}' "$name")" == exited ]] \
    || die "container did not reach exited state"
  [[ "$(docker inspect --format '{{.State.ExitCode}}' "$name")" == 0 && "$start_exit" == 0 ]] \
    || die "clean build $ordinal failed"
  [[ "$(docker inspect --format '{{.Image}}' "$name")" == "$INPUT_IMAGE_ID" ]] \
    || die "container image identity changed"
  [[ "$(<"$evidence/build-exit.txt")" == 0 && "$(<"$evidence/build-result.txt")" == PASS ]] \
    || die "inner build did not record PASS/0"
  [[ -s "$evidence/host-metadata.json" && -s "$evidence/guest-metadata.json" ]] \
    || die "full Cargo metadata evidence is absent"
  grep -q '^{"packages"' "$evidence/host-metadata.json" || die "host metadata JSON prefix is invalid"
  grep -q '^{"packages"' "$evidence/guest-metadata.json" || die "guest metadata JSON prefix is invalid"
  verify_immutable_cache "$run/host-cargo-home" "$evidence" host postbuild
  verify_immutable_cache "$run/nested-home/.cargo" "$evidence" nested postbuild
}

run_once 1
actual_program_binary=$(<"$EVIDENCE_ROOT/run-1/main-guest-program-binary.sha256")
actual_image_id=$(<"$EVIDENCE_ROOT/run-1/main-guest-image-id.txt")

if [[ -n "$IDENTITY_GUARD" ]]; then
  actual_program_size=$(<"$EVIDENCE_ROOT/run-1/main-program-binary-size.txt")
  raw_elf_path=$(awk -F= '$1 == "main_raw_user_elf" { print $2 }' \
    "$EVIDENCE_ROOT/run-1/artifact-paths.txt")
  methods_path=$(awk -F= '$1 == "methods" { print $2 }' \
    "$EVIDENCE_ROOT/run-1/artifact-paths.txt")
  host_path=$(awk -F= '$1 == "host" { print $2 }' \
    "$EVIDENCE_ROOT/run-1/artifact-paths.txt")
  diagnostic_program_path=$(awk -F= '$1 == "diagnostic_program_binary" { print $2 }' \
    "$EVIDENCE_ROOT/run-1/artifact-paths.txt")
  diagnostic_raw_path=$(awk -F= '$1 == "diagnostic_raw_user_elf" { print $2 }' \
    "$EVIDENCE_ROOT/run-1/artifact-paths.txt")
  actual_raw_elf=$(awk -v path="$raw_elf_path" '$2 == path { print $1 }' \
    "$EVIDENCE_ROOT/run-1/artifacts.sha256")
  actual_methods=$(awk -v path="$methods_path" '$2 == path { print $1 }' \
    "$EVIDENCE_ROOT/run-1/artifacts.sha256")
  actual_host=$(awk -v path="$host_path" '$2 == path { print $1 }' \
    "$EVIDENCE_ROOT/run-1/artifacts.sha256")
  actual_diagnostic_program=$(awk -v path="$diagnostic_program_path" '$2 == path { print $1 }' \
    "$EVIDENCE_ROOT/run-1/artifacts.sha256")
  actual_diagnostic_raw=$(awk -v path="$diagnostic_raw_path" '$2 == path { print $1 }' \
    "$EVIDENCE_ROOT/run-1/artifacts.sha256")
  [[ "$actual_program_binary" == "$EXPECTED_PROGRAM_BINARY_GUARD" ]] \
    || die "canonical ProgramBinary identity regression"
  [[ "$actual_program_size" == "$EXPECTED_PROGRAM_SIZE_GUARD" ]] \
    || die "canonical ProgramBinary size regression"
  [[ "$actual_image_id" == "$EXPECTED_IMAGE_ID_GUARD" ]] \
    || die "canonical Image ID regression"
  [[ "$actual_raw_elf" == "$EXPECTED_RAW_ELF_GUARD" ]] \
    || die "canonical raw guest ELF identity regression"
  [[ "$actual_methods" == "$EXPECTED_METHODS_GUARD" ]] \
    || die "canonical generated methods identity regression"
  [[ "$actual_host" == "$EXPECTED_HOST_GUARD" ]] \
    || die "canonical release host identity regression"
  [[ "$actual_diagnostic_program" == "$EXPECTED_DIAGNOSTIC_PROGRAM_GUARD" ]] \
    || die "canonical diagnostic ProgramBinary identity regression"
  [[ "$actual_diagnostic_raw" == "$EXPECTED_DIAGNOSTIC_RAW_ELF_GUARD" ]] \
    || die "canonical diagnostic raw guest ELF identity regression"
  sha256sum "$expected_identity_real" >"$EVIDENCE_ROOT/expected-identity.sha256"
  {
    printf 'identity-regression=0\n'
    printf 'source_commit=%s\n' "$EXPECTED_SOURCE_COMMIT"
    printf 'source_manifest_sha256=%s\n' "$SOURCE_MANIFEST_SHA256"
    printf 'input_image_id=%s\n' "$INPUT_IMAGE_ID"
    printf 'program_binary_sha256=%s\n' "$actual_program_binary"
    printf 'program_binary_size_bytes=%s\n' "$actual_program_size"
    printf 'image_id=%s\n' "$actual_image_id"
    printf 'raw_guest_elf_sha256=%s\n' "$actual_raw_elf"
    printf 'methods_rs_sha256=%s\n' "$actual_methods"
    printf 'host_binary_sha256=%s\n' "$actual_host"
    printf 'diagnostic_program_binary_sha256=%s\n' "$actual_diagnostic_program"
    printf 'diagnostic_raw_guest_elf_sha256=%s\n' "$actual_diagnostic_raw"
  } >"$EVIDENCE_ROOT/identity-guard-summary.txt"
else
  run_once 2
  diff -u "$EVIDENCE_ROOT/run-1/host-cache-tree.sha256" "$EVIDENCE_ROOT/run-2/host-cache-tree.sha256" \
    >"$EVIDENCE_ROOT/host-cache-seed-discrepancy.diff" || die "host cache seeds differ"
  diff -u "$EVIDENCE_ROOT/run-1/nested-cache-tree.sha256" "$EVIDENCE_ROOT/run-2/nested-cache-tree.sha256" \
    >"$EVIDENCE_ROOT/nested-cache-seed-discrepancy.diff" || die "nested cache seeds differ"
  diff -u "$EVIDENCE_ROOT/run-1/artifacts.sha256" "$EVIDENCE_ROOT/run-2/artifacts.sha256" \
    >"$EVIDENCE_ROOT/artifact-discrepancy.diff" || die "two clean builds produced different artifacts"
  [[ "$actual_program_binary" == "$(<"$EVIDENCE_ROOT/run-2/main-guest-program-binary.sha256")" \
     && "$actual_image_id" == "$(<"$EVIDENCE_ROOT/run-2/main-guest-image-id.txt")" ]] \
    || die "two clean builds disagree on canonical guest identity"
fi
identity_result=CHANGED
if [[ "$actual_program_binary" == "$HISTORICAL_PROGRAM_BINARY_SHA256" \
   && "$actual_image_id" == "$HISTORICAL_IMAGE_ID" ]]; then
  identity_result=SAME
fi
printf 'identity-result=%s\nactual-program-binary-sha256=%s\nhistorical-program-binary-sha256=%s\nactual-image-id=%s\nhistorical-image-id=%s\n' \
  "$identity_result" "$actual_program_binary" "$HISTORICAL_PROGRAM_BINARY_SHA256" \
  "$actual_image_id" "$HISTORICAL_IMAGE_ID" \
  >"$EVIDENCE_ROOT/historical-identity-comparison.txt"
if [[ -z "$IDENTITY_GUARD" ]]; then
  printf 'build-discrepancy=0\nidentity-result=%s\nsource_commit=%s\nsource_manifest_sha256=%s\ncache_archive_sha256=%s\ncache_manifest_sha256=%s\ninput_image_id=%s\n' \
    "$identity_result" "$EXPECTED_SOURCE_COMMIT" "$SOURCE_MANIFEST_SHA256" \
    "$CACHE_ARCHIVE_SHA256" "$CACHE_MANIFEST_SHA256" "$INPUT_IMAGE_ID" \
    >"$EVIDENCE_ROOT/comparison-summary.txt"
fi
(cd "$EVIDENCE_ROOT" && find . -type f ! -name evidence-manifest.sha256 -print0 \
  | LC_ALL=C sort -z | xargs -0 sha256sum) >"$EVIDENCE_ROOT/evidence-manifest.sha256"
if [[ -n "$IDENTITY_GUARD" ]]; then
  printf 'PASS: one fresh network-none build matches the source-controlled canonical guest identity (%s)\n' \
    "$identity_result"
else
  printf 'PASS: two clean builds produced identical artifacts and guest identity; historical comparison is reference-only (%s)\n' \
    "$identity_result"
fi
