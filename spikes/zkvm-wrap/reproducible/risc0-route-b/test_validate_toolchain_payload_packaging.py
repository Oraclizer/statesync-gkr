#!/usr/bin/env python3
"""Pure packaging-root tests for the Route B payload validator."""

import copy
import hashlib
import importlib.util
import os
import subprocess
import sys
import unittest
from pathlib import Path


REPO = Path(__file__).resolve().parents[4]
VALIDATOR = REPO / "spikes/zkvm-wrap/reproducible/risc0-route-b/validate-toolchain-payload-v1.py"
SPEC = importlib.util.spec_from_file_location("route_b_payload_validator", VALIDATOR)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)
IDENTITY_SOURCE = Path(os.environ.get("SSGKR_IDENTITY_SOURCE", REPO))
LICENSE_SPEC = importlib.util.spec_from_file_location("licensing_distribution_policy", REPO / "release/v1.1/license_distribution.py")
LICENSE_POLICY = importlib.util.module_from_spec(LICENSE_SPEC)
LICENSE_SPEC.loader.exec_module(LICENSE_POLICY)

IDENTITY_ALLOWLIST = (
    "Cargo.toml", "Cargo.lock", "rust-toolchain.toml", "src", "crates",
    "spikes/zkvm-wrap/common", "spikes/zkvm-wrap/risc0-host",
    "spikes/zkvm-wrap/risc0-methods",
    "tests/vectors/inner-proof-v1/membership-d24.bin",
)
EXPECTED_IDENTITY_SOURCE_MANIFEST = "13eacaa5bf18f26c8089ec6ddf27a7410bb436f28330e12f1135abf5684cf31c"


def digest(character):
    return "sha256:" + character * 64


RUNTIME = digest("1")
CONFIG = digest("2")
CURRENT_INDEX = digest("3")
HISTORICAL_INDEX = digest("4")
CURRENT_ATTESTATION = digest("5")
HISTORICAL_ATTESTATION = digest("6")
CURRENT_ATTESTATION_LAYER = digest("7")
HISTORICAL_ATTESTATION_LAYER = digest("8")


def profile_fixture():
    return {
        "packaging_evidence": {
            "historical": {
                "oci_index_digest": HISTORICAL_INDEX,
                "runtime_manifest_digest": RUNTIME,
                "runtime_config_digest": CONFIG,
                "attestation_manifest_digest": HISTORICAL_ATTESTATION,
                "attestation_subject_digest": RUNTIME,
                "attestation_layer_digest": HISTORICAL_ATTESTATION_LAYER,
            },
            "current_observation": {
                "oci_index_digest": CURRENT_INDEX,
                "runtime_manifest_digest": RUNTIME,
                "runtime_config_digest": CONFIG,
                "attestation_manifest_digest": CURRENT_ATTESTATION,
                "attestation_subject_digest": RUNTIME,
                "attestation_layer_digest": CURRENT_ATTESTATION_LAYER,
            },
        },
    }


def runtime_descriptor():
    return {
        "digest": RUNTIME,
        "platform": {"architecture": "amd64", "os": "linux"},
    }


def attestation_descriptor(attestation_digest):
    return {
        "digest": attestation_digest,
        "annotations": {
            "vnd.docker.reference.type": "attestation-manifest",
            "vnd.docker.reference.digest": RUNTIME,
        },
    }


def runtime_manifest():
    return {
        "mediaType": MODULE.OCI_MANIFEST_MEDIA_TYPE,
        "config": {"digest": CONFIG},
        "layers": [],
    }


def attestation(layer_digest, subject=RUNTIME):
    return {
        "subject": {"digest": subject},
        "layers": [{"digest": layer_digest, "size": 17}],
    }


def index_fixture(*, duplicate_runtime=False, duplicate_attestation=False):
    manifests = [runtime_descriptor(), attestation_descriptor(CURRENT_ATTESTATION)]
    if duplicate_runtime:
        manifests.insert(1, copy.deepcopy(runtime_descriptor()))
    if duplicate_attestation:
        manifests.append(copy.deepcopy(attestation_descriptor(CURRENT_ATTESTATION)))
    return {"mediaType": MODULE.OCI_INDEX_MEDIA_TYPE, "manifests": manifests}


def historical_index_fixture():
    return {
        "mediaType": MODULE.OCI_INDEX_MEDIA_TYPE,
        "manifests": [
            runtime_descriptor(),
            attestation_descriptor(HISTORICAL_ATTESTATION),
        ],
    }


def content_reader(store):
    def read(digest_value, label):
        if digest_value not in store:
            raise AssertionError(f"unexpected content fetch for {label}: {digest_value}")
        return copy.deepcopy(store[digest_value])

    return read


def index_store():
    return {
        RUNTIME: runtime_manifest(),
        CONFIG: {"architecture": "amd64", "os": "linux"},
        CURRENT_ATTESTATION: attestation(CURRENT_ATTESTATION_LAYER),
        HISTORICAL_INDEX: historical_index_fixture(),
        HISTORICAL_ATTESTATION: attestation(HISTORICAL_ATTESTATION_LAYER),
    }


def acceptance_fixture():
    return {
        "base_reference": "base",
        "base_rootfs_diff_ids": [digest("a")],
        "architecture": "amd64",
        "os": "linux",
        "created": "fixed",
        "config": {"Env": [], "Entrypoint": ["/bin/sh"]},
        "ordered_layers": [
            {"compressed_digest": digest("b")},
            {"compressed_digest": digest("c")},
        ],
        "top_layer": {"compressed_digest": digest("c")},
        "normalized_ordered_history": [
            {"created_by": "fixed", "comment": "", "empty_layer": False}
        ],
        "compiler_binaries": {"host_rustc": {"binary_sha256": "1" * 64}},
        "fixed_inputs": {
            "cargo_cache_archive_sha256": "2" * 64,
            "host_cargo_lock_sha256": "3" * 64,
            "source_manifest_sha256": "4" * 64,
        },
        "expected_outputs": {"image_id": "5" * 64},
        "linux_amd64_descriptor_count": 1,
        "attestation_subject_matches_runtime": True,
    }


def identity_source_manifest(repo):
    raw_index = subprocess.check_output([
        "git", "-c", f"safe.directory={repo}", "-C", str(repo),
        "ls-files", "-s", "-z", "--", *IDENTITY_ALLOWLIST,
    ])
    rows = []
    for entry in raw_index.split(b"\0"):
        if not entry:
            continue
        header, path_raw = entry.split(b"\t", 1)
        mode, _object_id, stage = header.decode("ascii").split()
        path = path_raw.decode("utf-8")
        if stage != "0" or mode not in {"100644", "100755"}:
            raise AssertionError(f"unsupported identity source entry: {entry!r}")
        content_digest = hashlib.sha256((repo / path).read_bytes()).hexdigest()
        rows.append(f"{mode}\t{content_digest}\t{path}\n".encode("utf-8"))
    return len(rows), hashlib.sha256(b"".join(rows)).hexdigest()


class PackagingRootTests(unittest.TestCase):
    def test_current_and_historical_identity_source_boundaries(self):
        count, manifest_digest = identity_source_manifest(IDENTITY_SOURCE)
        self.assertEqual(count, 64)
        self.assertEqual(manifest_digest, LICENSE_POLICY.CURRENT_SOURCE_SHA256)
        manifest = LICENSE_POLICY.load_record(REPO / "release/v1.1/PROTECTED_SOURCE_MANIFEST.json")
        projected_count, raw_digest, projected_digest = LICENSE_POLICY.identity_source_digests(IDENTITY_SOURCE, manifest)
        self.assertEqual(projected_count, 64)
        self.assertEqual(raw_digest, manifest_digest)
        self.assertEqual(projected_digest, EXPECTED_IDENTITY_SOURCE_MANIFEST)

    def test_expected_identity_file_agrees_with_the_recorded_identity(self):
        # The expected-identity file and this test are two independent records
        # of the same accepted build, so a silent edit to either one fails here.
        path = REPO / "spikes/zkvm-wrap/identity/risc0-route-b-guest-expected-v1.1.json"
        value = MODULE.load_json_bytes(path.read_bytes(), str(path))
        self.assertEqual(
            value["schema"], "statesync-gkr.risc0-route-b-guest-identity.expected.v1"
        )
        self.assertEqual(value["canonical_source_path"], "/workspace/source")
        self.assertEqual(
            value["recipe"]["source_manifest_sha256"], EXPECTED_IDENTITY_SOURCE_MANIFEST
        )
        self.assertEqual(value["artifacts"], {
            "program_binary": {
                "sha256": "9bb3740d9c0e35f55a42adafa5bfd5cc89fe2520e1c391632807c4e33931cb04",
                "size_bytes": 699408,
            },
            "image_id": "dc9a5f0da608178bbe56e98604cb895060c555c18329846b453f71d562d16530",
            "raw_guest_elf_sha256":
                "38b337c16334226f9dcd2ea319b5e6924aa583ba637126c9d7a8cfacb5cb9a5d",
            "methods_rs_sha256":
                "3b8c0c23d5f0ceb84e1224b472428772c1f53bcd5c97b5ff1502acc1a6878e03",
            "host_binary_sha256":
                "cad5e07c07465c9f8baddbf6364ad52ae8f35529954d742f5a1449c0ee77aab9",
            "diagnostic_program_binary_sha256":
                "0ea12e7bb8a02b0003aa3b190b0707c6e2ef22df00648ca96896909fb01a4610",
            "diagnostic_raw_guest_elf_sha256":
                "ca7cdb1de37397232ae5cd799e0ca09217a08fe90a2556292db8f227cfee4b89",
        })

    def test_every_payload_profile_matches_its_release_line_identity(self):
        # A profile is only ever compared with the expected-identity file the
        # caller passes, so a profile left behind on a previous line fails
        # nowhere until a real controlled build wastes hours proving it. Pair
        # them here by release line instead.
        recipe = REPO / "spikes/zkvm-wrap/reproducible/risc0-route-b"
        pins = {}
        for line in (recipe / "toolchain-checksums.txt").read_text(
            encoding="utf-8"
        ).splitlines():
            parts = line.split("  ")
            if len(parts) == 2:
                pins[parts[1]] = parts[0]

        profiles = sorted(recipe.glob("toolchain-payload-profile-v*.json"))
        self.assertTrue(profiles)
        for profile_path in profiles:
            release_line = profile_path.stem.rsplit("-", 1)[-1]
            identity_path = (
                REPO
                / "spikes/zkvm-wrap/identity"
                / f"risc0-route-b-guest-expected-{release_line}.json"
            )
            with self.subTest(release_line=release_line):
                self.assertTrue(
                    identity_path.is_file(),
                    "profile has no expected-identity record for its line",
                )
                profile_bytes = profile_path.read_bytes()
                profile = MODULE.load_json_bytes(profile_bytes, str(profile_path))
                identity = MODULE.load_json_bytes(
                    identity_path.read_bytes(), str(identity_path)
                )
                MODULE.validate_profile_shape(profile)
                self.assertEqual(
                    profile["fixed_inputs"]["source_manifest_sha256"],
                    identity["recipe"]["source_manifest_sha256"],
                )
                self.assertEqual(
                    profile["expected_outputs"], MODULE.expected_outputs(identity)
                )
                self.assertEqual(
                    pins.get(profile_path.name),
                    hashlib.sha256(profile_bytes).hexdigest(),
                    "profile checksum pin is absent or stale",
                )

    def test_positive_index_root_preserves_live_attestation(self):
        resolved = MODULE.resolve_packaging_root(
            CURRENT_INDEX,
            index_fixture(),
            profile_fixture(),
            content_reader(index_store()),
        )
        self.assertEqual(resolved["input_representation"], "oci-index")
        self.assertEqual(resolved["runtime_digest"], RUNTIME)
        self.assertEqual(resolved["linux_amd64_descriptor_count"], 1)
        self.assertTrue(resolved["attestation_subject_matches_runtime"])
        observation = resolved["packaging_observation"]
        self.assertTrue(observation["attestation_present"])
        self.assertEqual(observation["oci_index_digest"], CURRENT_INDEX)
        self.assertEqual(observation["attestation_manifest_digest"], CURRENT_ATTESTATION)

    def test_positive_direct_root_needs_only_config_content(self):
        resolved = MODULE.resolve_packaging_root(
            RUNTIME,
            runtime_manifest(),
            profile_fixture(),
            content_reader({CONFIG: {"architecture": "amd64", "os": "linux"}}),
        )
        self.assertEqual(resolved["input_representation"], "runtime-manifest")
        self.assertEqual(resolved["root_digest"], RUNTIME)
        self.assertEqual(resolved["runtime_digest"], RUNTIME)
        self.assertEqual(resolved["linux_amd64_descriptor_count"], 1)
        self.assertTrue(resolved["attestation_subject_matches_runtime"])
        observation = resolved["packaging_observation"]
        self.assertFalse(observation["attestation_present"])
        self.assertNotIn("oci_index_digest", observation)
        self.assertNotIn("attestation_manifest_digest", observation)
        self.assertNotIn("attestation_subject_digest", observation)

    def test_direct_root_rejects_wrong_digest(self):
        with self.assertRaisesRegex(ValueError, "direct runtime manifest root differs"):
            MODULE.resolve_packaging_root(
                digest("9"),
                runtime_manifest(),
                profile_fixture(),
                content_reader({CONFIG: {}}),
            )

    def test_rejects_unknown_root_media_type(self):
        with self.assertRaisesRegex(ValueError, "unsupported OCI packaging root media type"):
            MODULE.resolve_packaging_root(
                RUNTIME,
                {"mediaType": "application/example"},
                profile_fixture(),
                content_reader({}),
            )

    def test_direct_root_rejects_profile_runtime_or_config_split(self):
        runtime_split = profile_fixture()
        runtime_split["packaging_evidence"]["current_observation"]["runtime_manifest_digest"] = digest("9")
        config_split = profile_fixture()
        config_split["packaging_evidence"]["current_observation"]["runtime_config_digest"] = digest("9")
        with self.subTest("runtime"):
            with self.assertRaises(ValueError):
                MODULE.resolve_packaging_root(
                    RUNTIME, runtime_manifest(), runtime_split, content_reader({CONFIG: {}})
                )
        with self.subTest("config"):
            with self.assertRaisesRegex(ValueError, "runtime config profile records differ"):
                MODULE.resolve_packaging_root(
                    RUNTIME, runtime_manifest(), config_split, content_reader({CONFIG: {}})
                )

    def test_rejects_profile_or_live_attestation_subject_mismatch(self):
        profile_subject = profile_fixture()
        profile_subject["packaging_evidence"]["current_observation"]["attestation_subject_digest"] = digest("9")
        with self.subTest("profile"):
            with self.assertRaisesRegex(ValueError, "attestation subjects differ"):
                MODULE.resolve_packaging_root(
                    RUNTIME, runtime_manifest(), profile_subject, content_reader({CONFIG: {}})
                )
        live_store = index_store()
        live_store[CURRENT_ATTESTATION] = attestation(CURRENT_ATTESTATION_LAYER, digest("9"))
        with self.subTest("live-index"):
            with self.assertRaisesRegex(ValueError, "attestation subject differs"):
                MODULE.resolve_packaging_root(
                    CURRENT_INDEX,
                    index_fixture(),
                    profile_fixture(),
                    content_reader(live_store),
                )

    def test_rejects_runtime_or_attestation_descriptor_ambiguity(self):
        for label, root in (
            ("runtime", index_fixture(duplicate_runtime=True)),
            ("attestation", index_fixture(duplicate_attestation=True)),
        ):
            with self.subTest(label):
                with self.assertRaises(ValueError):
                    MODULE.resolve_packaging_root(
                        CURRENT_INDEX, root, profile_fixture(), content_reader(index_store())
                    )

    def test_existing_mutation_names_and_count_are_unchanged(self):
        expected_names = [
            "packaging-identifiers-record-only-pass",
            "base-layer-rejected",
            "runtime-layer-order-rejected",
            "environment-rejected",
            "entrypoint-rejected",
            "history-rejected",
            "compiler-rejected",
            "cache-rejected",
            "lock-rejected",
            "source-manifest-rejected",
            "expected-output-rejected",
            "attestation-subject-rejected",
            "runtime-descriptor-count-rejected",
            "duplicate-json-key-rejected",
            "missing-field-rejected",
        ]
        self.assertEqual(MODULE.mutation_self_tests(acceptance_fixture()), expected_names)

    def test_duplicate_and_missing_json_guards_remain_fail_closed(self):
        with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
            MODULE.load_json_bytes(b'{"a": 1, "a": 2}', "fixture")
        missing = profile_fixture()
        del missing["packaging_evidence"]["current_observation"]["runtime_config_digest"]
        with self.assertRaisesRegex(ValueError, "missing fields"):
            MODULE.packaging_records(missing)


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(PackagingRootTests)
    result = unittest.TextTestRunner(stream=sys.stdout, verbosity=2).run(suite)
    raise SystemExit(0 if result.wasSuccessful() else 1)
