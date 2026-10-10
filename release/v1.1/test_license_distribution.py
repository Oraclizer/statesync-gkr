"""Exercise exact licensing deltas and the real base-policy authority selector."""
from __future__ import annotations

from contextlib import contextmanager
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import license_distribution as policy
import run_source_policy as authority
import verify

REPO = Path(__file__).resolve().parents[2]


@contextmanager
def changed(path: Path, data: bytes):
    original = path.read_bytes()
    path.write_bytes(data)
    try:
        yield
    finally:
        path.write_bytes(original)


class LicensingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="ssgkr-licensing-fixture-")
        cls.root = Path(cls.temporary.name).resolve()
        cls.manifest = policy.load_record(REPO / "release/v1.1/PROTECTED_SOURCE_MANIFEST.json")
        cls.allowlist = policy.load_record(REPO / "release/v1.1/FROZEN_SOURCE_ALLOWLIST.json")
        names = {e["path"] for e in cls.manifest["entries"]}
        names.update({"LICENSE", "CITATION.cff", "release/v1.1/PROTECTED_SOURCE_MANIFEST.json",
                      "release/v1.1/FROZEN_SOURCE_ALLOWLIST.json", "release/v1.1/LICENSING_DISTRIBUTION.json",
                      "release/v1.1/SBOM.spdx.json", "benches/controlled-capacity-2026-10-07/Load/Cargo.toml",
                      "benches/controlled-capacity-2026-10-07/Load/LICENSE"})
        for name in names:
            target = cls.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(REPO / name, target)
            os.chmod(target, 0o644)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def check(self):
        verify.verify_protected(self.root, self.manifest, self.allowlist, False)
        return policy.verify_distribution(self.root)

    def test_exact_current_source_and_historical_projection_pass(self):
        value = self.check()
        self.assertIs(value["current_compiled_identity_reproduced"], False)
        self.assertEqual(policy.identity_source_digests(self.root, self.manifest),
                         (64, policy.CURRENT_SOURCE_SHA256, policy.BASE_SOURCE_SHA256))

    def test_kernel_byte_mutation_rejected(self):
        path = self.root / "crates/protocol/src/lib.rs"
        with changed(path, path.read_bytes() + b"\n// mutation\n"):
            with self.assertRaisesRegex(verify.VerificationError, "historical protected comparison drift"):
                self.check()

    def test_cargo_dependency_and_extra_default_changes_rejected(self):
        path = self.root / "Cargo.toml"
        original = path.read_bytes()
        mutations = [original.replace(b'p3-field = "=0.4.3"', b'p3-field = "=0.4.4"'),
                     original.replace(b'default = ["host"]', b'default = []'),
                     original + b'\n[package.metadata.fixture]\nlicense = "BUSL-1.1"\n']
        for candidate in mutations:
            self.assertNotEqual(candidate, original)
            with self.subTest(candidate=candidate[-50:]), changed(path, candidate):
                with self.assertRaisesRegex(verify.VerificationError, "outside the approved license-only delta"):
                    self.check()

    def test_record_false_claims_and_authority_changes_rejected(self):
        path = self.root / "release/v1.1/LICENSING_DISTRIBUTION.json"
        for field, value in [("license", "MIT"), ("current_compiled_identity_reproduced", True),
                             ("historical_protected_manifest_sha256", "0" * 64),
                             ("historical_allowlist_sha256", "0" * 64)]:
            candidate = policy.load_record(path)
            candidate[field] = value
            with self.subTest(field=field), changed(path, json.dumps(candidate).encode()):
                with self.assertRaises(ValueError):
                    policy.verify_distribution(self.root)
        for field, value in [("new_proof_generated", True), ("program_comparison_completed", True),
                             ("program_comparison_completed", 0), ("status", "PASS")]:
            candidate = policy.load_record(path)
            candidate["bounded_build_observation"][field] = value
            with self.subTest(observation=field, value=value), changed(path, json.dumps(candidate).encode()):
                with self.assertRaises(ValueError):
                    policy.verify_distribution(self.root)

    def test_duplicate_json_and_modified_root_license_rejected(self):
        path = self.root / "release/v1.1/LICENSING_DISTRIBUTION.json"
        duplicate = path.read_text(encoding="utf-8").replace('{', '{"license":"MIT",', 1)
        with changed(path, duplicate.encode()):
            with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
                policy.verify_distribution(self.root)
        license_path = self.root / "LICENSE"
        with changed(license_path, license_path.read_bytes() + b"\nextra grant\n"):
            with self.assertRaisesRegex(ValueError, "root BSL"):
                policy.verify_distribution(self.root)

    def test_cff_comment_duplicate_and_historical_doi_rejected(self):
        valid = (self.root / "CITATION.cff").read_text(encoding="utf-8")
        candidates = [valid.replace("license: BUSL-1.1", "# license: BUSL-1.1\nlicense: MIT"),
                      valid + "\nlicense: MIT\n", valid.replace("10.5281/zenodo.23280552", "10.5281/zenodo.23136385"),
                      valid.replace('doi: "10.5281/zenodo.23280552"', "doi: 10.5281/zenodo.23136385"),
                      valid.replace("10.5281/zenodo.23280552", "10.5281/zenodo.99999999"),
                      valid + '\ndoi: "https://doi.org/10.5281/zenodo.23136385"\n',
                      valid + '\nversion: "1.1.0"\n']
        for candidate in candidates:
            with self.subTest(candidate=candidate[-80:]):
                with self.assertRaises(ValueError):
                    policy.verify_cff(candidate)
        policy.verify_cff(valid.replace("license: BUSL-1.1", 'license: "BUSL-1.1" # current grant'))

    def test_own_sbom_and_caller_metadata_rejected_when_mislabeled(self):
        path = self.root / "release/v1.1/SBOM.spdx.json"
        value = policy.load_record(path)
        next(p for p in value["packages"] if p["name"] == "statesync-gkr")["licenseDeclared"] = "MIT"
        with changed(path, json.dumps(value).encode()):
            with self.assertRaisesRegex(ValueError, "SBOM license"):
                policy.verify_distribution(self.root)
        caller = self.root / "benches/controlled-capacity-2026-10-07/Load/Cargo.toml"
        with changed(caller, caller.read_bytes().replace(b'license = "BUSL-1.1"', b'license = "MIT"')):
            with self.assertRaisesRegex(ValueError, "caller license"):
                policy.verify_distribution(self.root)

    def test_current_cargo_git_blob_and_mode_are_checked(self):
        modes = {e["path"]: (e["mode"], e["git_blob_oid"]) for e in self.manifest["entries"]}
        cargo = (self.root / "Cargo.toml").read_bytes()
        modes["Cargo.toml"] = ("100644", policy.git_blob_oid(cargo))
        from unittest.mock import patch
        with patch.object(verify, "entry_modes_from_git", return_value=modes):
            verify.verify_protected(self.root, self.manifest, self.allowlist, True)
        for value in [("100644", "0" * 40), ("100755", policy.git_blob_oid(cargo))]:
            wrong = dict(modes)
            wrong["Cargo.toml"] = value
            with self.subTest(value=value), patch.object(verify, "entry_modes_from_git", return_value=wrong):
                with self.assertRaisesRegex(verify.VerificationError, "current Cargo Git mode/blob"):
                    verify.verify_protected(self.root, self.manifest, self.allowlist, True)


class AuthorityPairTests(unittest.TestCase):
    def test_head_helper_cannot_replace_base_policy_and_is_restored(self):
        with tempfile.TemporaryDirectory(prefix="ssgkr-authority-fixture-") as folder:
            parent = Path(folder)
            remote = parent / "base"
            work = parent / "head"
            remote.mkdir()
            def git(path, *args):
                return subprocess.run(["git", "-C", str(path), *args], check=True, capture_output=True)
            git(remote, "init", "--initial-branch=main")
            git(remote, "config", "user.name", "Policy fixture")
            git(remote, "config", "user.email", "fixture.invalid")
            git(remote, "config", "commit.gpgsign", "false")
            policy_dir = remote / "release/v1.1"
            policy_dir.mkdir(parents=True)
            (policy_dir / "license_distribution.py").write_text('def accepts(text):\n    return text == "approved"\n', encoding="utf-8")
            (policy_dir / "verify.py").write_text('from pathlib import Path\nimport license_distribution\nraise SystemExit(0 if license_distribution.accepts(Path("payload").read_text()) else 1)\n', encoding="utf-8")
            (policy_dir / "run_source_policy.py").write_bytes((REPO / "release/v1.1/run_source_policy.py").read_bytes())
            (remote / "payload").write_text("approved", encoding="utf-8")
            git(remote, "add", ".")
            git(remote, "commit", "-m", "Establish fixture policy")
            subprocess.run(["git", "clone", str(remote), str(work)], check=True, capture_output=True)
            forged = b'def accepts(text):\n    return True\n'
            (work / "release/v1.1/license_distribution.py").write_bytes(forged)
            forged_wrapper = b'raise SystemExit(0)\n'
            (work / "release/v1.1/run_source_policy.py").write_bytes(forged_wrapper)
            (work / "payload").write_text("tampered", encoding="utf-8")
            import textwrap
            workflow = (REPO / ".github/workflows/ci.yml").read_text(encoding="utf-8")
            launcher = textwrap.dedent(workflow.split("# BEGIN source-authority-launcher\n", 1)[1].split("          # END source-authority-launcher", 1)[0])
            env = dict(os.environ, GITHUB_WORKSPACE=str(work), SOURCE_POLICY_EVENT="pull_request",
                       SOURCE_POLICY_BASE="main", SOURCE_POLICY_REPOSITORY="fixture/repo",
                       SOURCE_POLICY_HEAD_REPOSITORY="fixture/repo", SOURCE_POLICY_HEAD_REF="topic")
            launched = subprocess.run([sys.executable, "-B", "-c", launcher], env=env, capture_output=True)
            self.assertNotEqual(launched.returncode, 0)
            self.assertIn(b"base-verifier-helper-and-wrapper", launched.stdout)
            self.assertEqual((work / "release/v1.1/run_source_policy.py").read_bytes(), forged_wrapper)
            self.assertNotEqual(authority.run_policy(work, "pull_request", "main", "fixture/repo", "fixture/repo", "topic"), 0)
            self.assertEqual((work / "release/v1.1/license_distribution.py").read_bytes(), forged)
            (work / "payload").write_text("approved", encoding="utf-8")
            self.assertEqual(authority.run_policy(work, "pull_request", "main", "fixture/repo", "fixture/repo", "topic"), 0)
            (remote / "release/v1.1/license_distribution.py").unlink()
            git(remote, "add", "-u")
            git(remote, "commit", "-m", "Remove fixture helper")
            with self.assertRaisesRegex(ValueError, "incomplete outside"):
                authority.run_policy(work, "pull_request", "main", "fixture/repo", "fixture/repo", "topic")


if __name__ == "__main__":
    unittest.main(verbosity=2)
