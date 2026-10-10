#!/usr/bin/env python3
"""Validate the exact Route B toolchain payload while recording OCI packaging."""

import argparse
import copy
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path


DIGEST = re.compile(r"^sha256:[0-9a-f]{64}$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")
OCI_INDEX_MEDIA_TYPE = "application/vnd.oci.image.index.v1+json"
OCI_MANIFEST_MEDIA_TYPE = "application/vnd.oci.image.manifest.v1+json"


def fail(message):
    raise ValueError(message)


def require(condition, message):
    if not condition:
        fail(message)


def unique_object(pairs):
    value = {}
    for key, item in pairs:
        if key in value:
            fail(f"duplicate JSON key: {key}")
        value[key] = item
    return value


def load_json_bytes(raw, label):
    try:
        return json.loads(raw, object_pairs_hook=unique_object)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        fail(f"{label} is not strict UTF-8 JSON: {exc}")


def require_keys(value, expected, label):
    require(isinstance(value, dict), f"{label} must be an object")
    actual = set(value)
    expected = set(expected)
    require(actual == expected, f"{label} keys differ: missing={sorted(expected-actual)} unknown={sorted(actual-expected)}")


def run(command, *, input_bytes=None):
    result = subprocess.run(
        command,
        input=input_bytes,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode != 0:
        fail(f"command failed ({result.returncode}): {' '.join(command)}: {result.stderr.decode(errors='replace').strip()}")
    return result.stdout


def sha256_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def sha256_file(path):
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def content_get(digest):
    require(DIGEST.fullmatch(digest or ""), f"malformed OCI digest: {digest}")
    raw = run(["ctr", "-n", "moby", "content", "get", digest])
    require(f"sha256:{sha256_bytes(raw)}" == digest, f"OCI content-address mismatch: {digest}")
    return raw


def content_json(digest, label):
    return load_json_bytes(content_get(digest), label)


def docker_inspect(reference, platform=None):
    command = ["docker", "image", "inspect"]
    if platform:
        command += ["--platform", platform]
    command.append(reference)
    value = load_json_bytes(run(command), f"docker inspect {reference}")
    require(isinstance(value, list) and len(value) == 1, f"docker inspect {reference} must return exactly one image")
    return value[0]


def descriptor_for(index, *, architecture, os_name):
    descriptors = [
        item for item in index.get("manifests", [])
        if item.get("platform") == {"architecture": architecture, "os": os_name}
    ]
    require(len(descriptors) == 1, f"OCI index must contain exactly one {os_name}/{architecture} descriptor")
    return descriptors[0]


def attestation_for(index, runtime_digest, content_json_fn=content_json):
    descriptors = [
        item for item in index.get("manifests", [])
        if item.get("annotations", {}).get("vnd.docker.reference.type") == "attestation-manifest"
    ]
    require(len(descriptors) == 1, "OCI index must contain exactly one attestation manifest")
    descriptor = descriptors[0]
    require(
        descriptor.get("annotations", {}).get("vnd.docker.reference.digest") == runtime_digest,
        "OCI index attestation annotation does not name the runtime manifest",
    )
    attestation = content_json_fn(descriptor["digest"], "attestation manifest")
    require(attestation.get("subject", {}).get("digest") == runtime_digest, "attestation subject differs from runtime manifest")
    return descriptor, attestation


def packaging_records(profile):
    packaging = profile["packaging_evidence"]
    historical = packaging["historical"]
    current = packaging["current_observation"]
    required = {
        "runtime_manifest_digest", "runtime_config_digest", "attestation_subject_digest",
    }
    for label, record in (("historical", historical), ("current_observation", current)):
        require(isinstance(record, dict), f"packaging_evidence.{label} must be an object")
        missing = required - set(record)
        require(not missing, f"packaging_evidence.{label} missing fields: {sorted(missing)}")
    return historical, current


def validate_packaging_profile_binding(profile, runtime_digest, runtime_config_digest):
    historical, current = packaging_records(profile)
    records = (historical, current)
    runtime_digests = [record["runtime_manifest_digest"] for record in records]
    config_digests = [record["runtime_config_digest"] for record in records]
    attestation_subjects = [record["attestation_subject_digest"] for record in records]
    require(
        all(digest == runtime_digest for digest in runtime_digests),
        "historical/current runtime manifest profile records differ from selected runtime",
    )
    require(
        all(digest == runtime_config_digest for digest in config_digests),
        "historical/current runtime config profile records differ from selected manifest config",
    )
    attestation_binding = all(digest == runtime_digest for digest in attestation_subjects)
    require(attestation_binding, "historical/current attestation subjects differ from selected runtime")
    return {
        "linux_amd64_descriptor_count": len(set(runtime_digests)),
        "attestation_subject_matches_runtime": attestation_binding,
    }


def resolve_packaging_root(root_digest, root_json, profile, content_json_fn):
    require(DIGEST.fullmatch(root_digest or ""), f"malformed OCI root digest: {root_digest}")
    require(isinstance(root_json, dict), "OCI packaging root must be an object")
    historical, current = packaging_records(profile)
    media_type = root_json.get("mediaType")

    if media_type == OCI_INDEX_MEDIA_TYPE:
        runtime_descriptors = [
            item for item in root_json.get("manifests", [])
            if item.get("platform") == {"architecture": "amd64", "os": "linux"}
        ]
        runtime_descriptor = descriptor_for(root_json, architecture="amd64", os_name="linux")
        runtime_digest = runtime_descriptor["digest"]
        attestation_descriptor, attestation = attestation_for(
            root_json, runtime_digest, content_json_fn
        )
        runtime_manifest = content_json_fn(runtime_digest, "runtime manifest")
        runtime_config_descriptor = runtime_manifest.get("config", {})
        runtime_config_digest = runtime_config_descriptor.get("digest")
        runtime_config = content_json_fn(runtime_config_digest, "runtime config")
        profile_binding = validate_packaging_profile_binding(
            profile, runtime_digest, runtime_config_digest
        )

        historical_index = content_json_fn(historical["oci_index_digest"], "historical OCI index")
        historical_runtime = descriptor_for(historical_index, architecture="amd64", os_name="linux")
        historical_attestation_descriptor, historical_attestation = attestation_for(
            historical_index, historical_runtime["digest"], content_json_fn
        )
        require(
            historical_runtime["digest"] == historical["runtime_manifest_digest"],
            "historical runtime descriptor mismatch",
        )
        require(
            historical_attestation_descriptor["digest"] == historical["attestation_manifest_digest"],
            "historical attestation descriptor mismatch",
        )
        require(
            historical_attestation["layers"][0]["digest"] == historical["attestation_layer_digest"],
            "historical attestation layer mismatch",
        )
        live_attestation_binding = attestation.get("subject", {}).get("digest") == runtime_digest
        require(live_attestation_binding, "live attestation subject differs from selected runtime")
        return {
            "input_representation": "oci-index",
            "root_digest": root_digest,
            "runtime_digest": runtime_digest,
            "runtime_manifest": runtime_manifest,
            "runtime_config_descriptor": runtime_config_descriptor,
            "runtime_config": runtime_config,
            "linux_amd64_descriptor_count": len(runtime_descriptors),
            "attestation_subject_matches_runtime": live_attestation_binding,
            "packaging_observation": {
                "input_representation": "oci-index",
                "root_digest": root_digest,
                "oci_index_digest": root_digest,
                "runtime_manifest_digest": runtime_digest,
                "runtime_config_digest": runtime_config_digest,
                "attestation_present": True,
                "attestation_manifest_digest": attestation_descriptor["digest"],
                "attestation_subject_digest": attestation["subject"]["digest"],
                "attestation_layer_digest": attestation["layers"][0]["digest"],
                "attestation_layer_size_bytes": attestation["layers"][0]["size"],
                "role": "record-only-not-payload-authority",
            },
            "profile_binding": profile_binding,
        }

    if media_type == OCI_MANIFEST_MEDIA_TYPE:
        runtime_digest = root_digest
        require(
            runtime_digest == historical["runtime_manifest_digest"]
            and runtime_digest == current["runtime_manifest_digest"],
            "direct runtime manifest root differs from historical/current profile records",
        )
        runtime_manifest = root_json
        runtime_config_descriptor = runtime_manifest.get("config", {})
        runtime_config_digest = runtime_config_descriptor.get("digest")
        runtime_config = content_json_fn(runtime_config_digest, "runtime config")
        profile_binding = validate_packaging_profile_binding(
            profile, runtime_digest, runtime_config_digest
        )
        return {
            "input_representation": "runtime-manifest",
            "root_digest": root_digest,
            "runtime_digest": runtime_digest,
            "runtime_manifest": runtime_manifest,
            "runtime_config_descriptor": runtime_config_descriptor,
            "runtime_config": runtime_config,
            "linux_amd64_descriptor_count": profile_binding["linux_amd64_descriptor_count"],
            "attestation_subject_matches_runtime": profile_binding["attestation_subject_matches_runtime"],
            "packaging_observation": {
                "input_representation": "runtime-manifest",
                "root_digest": root_digest,
                "runtime_manifest_digest": runtime_digest,
                "runtime_config_digest": runtime_config_digest,
                "attestation_present": False,
                "role": "record-only-not-payload-authority",
            },
            "profile_binding": profile_binding,
        }

    fail(f"unsupported OCI packaging root media type: {media_type}")


def normalized_history(config):
    return [
        {
            "created_by": item.get("created_by", ""),
            "comment": item.get("comment", ""),
            "empty_layer": item.get("empty_layer", False),
        }
        for item in config.get("history", [])
    ]


def docker_entrypoint(reference, entrypoint, arguments):
    return run([
        "docker", "run", "--rm", "--network", "none", "--read-only",
        "--entrypoint", entrypoint, reference, *arguments,
    ])


def compiler_observation(reference, expected):
    observed = {}
    for name, item in expected.items():
        path = item["path"]
        version_args = ["--version"] if name == "rzup" else ["--version", "--verbose"]
        version_raw = docker_entrypoint(reference, path, version_args)
        sha_line = docker_entrypoint(reference, "/usr/bin/sha256sum", [path]).decode("utf-8").strip()
        size_line = docker_entrypoint(reference, "/usr/bin/wc", ["-c", path]).decode("utf-8").strip()
        first_line = version_raw.decode("utf-8").splitlines()[0]
        version_hash_key = "version_output_sha256" if name == "rzup" else "version_verbose_sha256"
        observed[name] = {
            "path": path,
            "version": first_line,
            version_hash_key: sha256_bytes(version_raw),
            "size_bytes": int(size_line.split()[0]),
            "binary_sha256": sha_line.split()[0],
        }
    return observed


def git_blob(repo, commit, path):
    return run(["git", "-C", str(repo), "show", f"{commit}:{path}"])


def expected_outputs(identity):
    artifacts = identity["artifacts"]
    return {
        "program_binary_sha256": artifacts["program_binary"]["sha256"],
        "program_binary_size_bytes": artifacts["program_binary"]["size_bytes"],
        "image_id": artifacts["image_id"],
        "raw_guest_elf_sha256": artifacts["raw_guest_elf_sha256"],
        "methods_rs_sha256": artifacts["methods_rs_sha256"],
        "host_binary_sha256": artifacts["host_binary_sha256"],
        "diagnostic_program_binary_sha256": artifacts["diagnostic_program_binary_sha256"],
        "diagnostic_raw_guest_elf_sha256": artifacts["diagnostic_raw_guest_elf_sha256"],
    }


def validate_profile_shape(profile):
    require_keys(profile, {
        "schema", "authority", "base_image", "toolchain_payload", "compiler_binaries",
        "fixed_inputs", "expected_outputs", "packaging_evidence", "claim_ceiling",
    }, "profile")
    require(profile["schema"] == "statesync-gkr.risc0-route-b.toolchain-payload-profile.v1", "profile schema mismatch")
    require(profile["authority"].get("payload_acceptance") == "exact", "payload acceptance must be exact")
    require(profile["authority"].get("packaging_digests") == "observed-only-not-payload-authority", "packaging authority boundary mismatch")
    require(profile["claim_ceiling"].get("config_id_replacement") is False, "config-ID replacement must remain false")
    for section in ("historical", "current_observation"):
        for key, value in profile["packaging_evidence"][section].items():
            if key.endswith("_digest"):
                require(DIGEST.fullmatch(value or ""), f"malformed packaging digest: {section}.{key}")
    for item in profile["toolchain_payload"]["ordered_layers"]:
        require(DIGEST.fullmatch(item["compressed_digest"]), "malformed compressed layer digest")
        require(DIGEST.fullmatch(item["diff_id"]), "malformed layer diff ID")
    for item in profile["compiler_binaries"].values():
        require(SHA256.fullmatch(item["binary_sha256"]), "malformed compiler binary SHA-256")


def validate_acceptance(expected, actual):
    require(actual == expected, "toolchain payload/fixed-input acceptance object differs from profile")


def mutation_self_tests(expected):
    results = []

    # Packaging coordinates are deliberately outside the acceptance object.
    validate_acceptance(expected, copy.deepcopy(expected))
    results.append("packaging-identifiers-record-only-pass")

    mutations = {
        "base-layer": lambda value: value["base_rootfs_diff_ids"].__setitem__(0, "sha256:" + "0" * 64),
        "runtime-layer-order": lambda value: value["ordered_layers"].reverse(),
        "environment": lambda value: value["config"]["Env"].append("UNAPPROVED=1"),
        "entrypoint": lambda value: value["config"].__setitem__("Entrypoint", ["/bin/bash"]),
        "history": lambda value: value["normalized_ordered_history"].__setitem__(0, {"created_by": "mutated", "comment": "", "empty_layer": True}),
        "compiler": lambda value: value["compiler_binaries"]["host_rustc"].__setitem__("binary_sha256", "0" * 64),
        "cache": lambda value: value["fixed_inputs"].__setitem__("cargo_cache_archive_sha256", "0" * 64),
        "lock": lambda value: value["fixed_inputs"].__setitem__("host_cargo_lock_sha256", "0" * 64),
        "source-manifest": lambda value: value["fixed_inputs"].__setitem__("source_manifest_sha256", "0" * 64),
        "expected-output": lambda value: value["expected_outputs"].__setitem__("image_id", "0" * 64),
        "attestation-subject": lambda value: value.__setitem__("attestation_subject_matches_runtime", False),
        "runtime-descriptor-count": lambda value: value.__setitem__("linux_amd64_descriptor_count", 2),
    }
    for name, mutate in mutations.items():
        candidate = copy.deepcopy(expected)
        mutate(candidate)
        try:
            validate_acceptance(expected, candidate)
        except ValueError:
            results.append(f"{name}-rejected")
        else:
            fail(f"mutation unexpectedly passed: {name}")

    try:
        load_json_bytes(b'{"a":1,"a":2}', "duplicate-key self-test")
    except ValueError:
        results.append("duplicate-json-key-rejected")
    else:
        fail("duplicate JSON key mutation unexpectedly passed")

    shape = {key: copy.deepcopy(value) for key, value in expected.items()}
    del shape["architecture"]
    try:
        validate_acceptance(expected, shape)
    except ValueError:
        results.append("missing-field-rejected")
    else:
        fail("missing acceptance field mutation unexpectedly passed")
    return results


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--profile", type=Path, required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--pinned-base", required=True)
    parser.add_argument("--cache-archive", type=Path, required=True)
    parser.add_argument("--cache-manifest", type=Path, required=True)
    parser.add_argument("--source-repo", type=Path, required=True)
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--expected-identity", type=Path, required=True)
    parser.add_argument("--evidence-output", type=Path, required=True)
    parser.add_argument("--self-test-mutations", action="store_true")
    args = parser.parse_args()

    profile_raw = args.profile.read_bytes()
    profile = load_json_bytes(profile_raw, str(args.profile))
    validate_profile_shape(profile)
    require(args.pinned_base == profile["base_image"]["reference"], "pinned base reference differs from profile")

    default_image = docker_inspect(args.image)
    root_digest = default_image.get("Id")
    root_json = content_json(root_digest, "current OCI packaging root")
    packaging = resolve_packaging_root(root_digest, root_json, profile, content_json)
    runtime_digest = packaging["runtime_digest"]
    runtime_manifest = packaging["runtime_manifest"]
    runtime_config_descriptor = packaging["runtime_config_descriptor"]
    runtime_config = packaging["runtime_config"]
    historical = profile["packaging_evidence"]["historical"]

    base = docker_inspect(args.pinned_base, "linux/amd64")
    base_diff_ids = base.get("RootFS", {}).get("Layers", [])
    layers = runtime_manifest.get("layers", [])
    diff_ids = runtime_config.get("rootfs", {}).get("diff_ids", [])
    require(len(layers) == len(diff_ids), "compressed layer and diff-ID counts differ")
    actual_layers = [
        {
            "compressed_digest": layer.get("digest"),
            "compressed_size_bytes": layer.get("size"),
            "diff_id": diff_id,
        }
        for layer, diff_id in zip(layers, diff_ids)
    ]

    top_layer = layers[-1]
    top_raw = content_get(top_layer["digest"])
    tar_names = run(["tar", "-tzf", "-"], input_bytes=top_raw)
    verbose_tar = run(["tar", "-tvzf", "-", "--numeric-owner"], input_bytes=top_raw)
    member_names = tar_names.decode("utf-8").splitlines()
    whiteouts = [name for name in member_names if Path(name).name.startswith(".wh.")]
    top_observation = {
        "compressed_digest": top_layer["digest"],
        "compressed_size_bytes": top_layer["size"],
        "diff_id": diff_ids[-1],
        "tar_member_count": len(member_names),
        "whiteout_count": len(whiteouts),
        "tar_member_path_list_sha256": sha256_bytes(tar_names),
        "gnu_tar_numeric_owner_verbose_list_sha256": sha256_bytes(verbose_tar),
        "tar_listing_hash_role": "supplemental-tool-specific-evidence",
    }

    identity = load_json_bytes(args.expected_identity.read_bytes(), str(args.expected_identity))
    fixed_inputs = {
        "cargo_cache_archive_sha256": sha256_file(args.cache_archive),
        "cargo_cache_manifest_sha256": sha256_file(args.cache_manifest),
        "cargo_cache_manifest_file_count": sum(1 for _ in args.cache_manifest.open("rb")),
        "host_cargo_lock_sha256": sha256_bytes(git_blob(args.source_repo, args.source_commit, "spikes/zkvm-wrap/risc0-host/Cargo.lock")),
        "guest_cargo_lock_sha256": sha256_bytes(git_blob(args.source_repo, args.source_commit, "spikes/zkvm-wrap/risc0-methods/guest/Cargo.lock")),
        "source_manifest_sha256": identity["recipe"]["source_manifest_sha256"],
    }

    actual = {
        "base_reference": args.pinned_base,
        "base_rootfs_diff_ids": base_diff_ids,
        "architecture": runtime_config.get("architecture"),
        "os": runtime_config.get("os"),
        "created": runtime_config.get("created"),
        "config": runtime_config.get("config"),
        "ordered_layers": actual_layers,
        "top_layer": top_observation,
        "normalized_ordered_history": normalized_history(runtime_config),
        "compiler_binaries": compiler_observation(args.image, profile["compiler_binaries"]),
        "fixed_inputs": fixed_inputs,
        "expected_outputs": expected_outputs(identity),
        "linux_amd64_descriptor_count": packaging["linux_amd64_descriptor_count"],
        "attestation_subject_matches_runtime": packaging["attestation_subject_matches_runtime"],
    }
    profile_binding = packaging["profile_binding"]
    expected = {
        "base_reference": profile["base_image"]["reference"],
        "base_rootfs_diff_ids": profile["base_image"]["ordered_rootfs_diff_ids"],
        "architecture": profile["toolchain_payload"]["architecture"],
        "os": profile["toolchain_payload"]["os"],
        "created": profile["toolchain_payload"]["created"],
        "config": profile["toolchain_payload"]["config"],
        "ordered_layers": profile["toolchain_payload"]["ordered_layers"],
        "top_layer": profile["toolchain_payload"]["top_layer"],
        "normalized_ordered_history": profile["toolchain_payload"]["normalized_ordered_history"],
        "compiler_binaries": profile["compiler_binaries"],
        "fixed_inputs": profile["fixed_inputs"],
        "expected_outputs": profile["expected_outputs"],
        "linux_amd64_descriptor_count": profile_binding["linux_amd64_descriptor_count"],
        "attestation_subject_matches_runtime": profile_binding["attestation_subject_matches_runtime"],
    }
    validate_acceptance(expected, actual)
    mutations = mutation_self_tests(expected) if args.self_test_mutations else []

    observation = {
        "schema": "statesync-gkr.risc0-route-b.toolchain-payload-observation.v1",
        "status": "PASS",
        "toolchain_payload_equivalence": "PASS",
        "profile_sha256": sha256_bytes(profile_raw),
        "packaging_observation": packaging["packaging_observation"],
        "historical_packaging": historical,
        "acceptance": actual,
        "mutation_tests": mutations,
    }
    args.evidence_output.write_text(
        json.dumps(observation, sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(json.dumps({
        "status": "PASS",
        "toolchain_payload_equivalence": "PASS",
        "profile_sha256": observation["profile_sha256"],
        "runtime_manifest_digest": runtime_digest,
        "mutation_tests": mutations,
    }, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
