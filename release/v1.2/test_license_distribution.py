"""Exercise the v1.2 identity record, the release-line authority and their rejections."""
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


class IdentityRecordTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="ssgkr-identity-fixture-")
        cls.root = Path(cls.temporary.name).resolve()
        cls.manifest = policy.load_record(REPO / policy.PROTECTED_MANIFEST)
        cls.allowlist = policy.load_record(REPO / "release/v1.2/FROZEN_SOURCE_ALLOWLIST.json")
        names = {e["path"] for e in cls.manifest["entries"]}
        names.update({
            "LICENSE", "CITATION.cff", policy.PROTECTED_MANIFEST, policy.IDENTITY_RECORD, policy.SBOM,
            "release/v1.2/FROZEN_SOURCE_ALLOWLIST.json", policy.EXPECTED_IDENTITY_RECORD,
            policy.HISTORICAL_PROOF_MANIFEST, "release/v1.1/PROTECTED_SOURCE_MANIFEST.json",
            "release/v1.1/FROZEN_SOURCE_ALLOWLIST.json",
        })
        for caller in policy.CALLERS:
            names.update({f"{caller}/Cargo.toml", f"{caller}/LICENSE"})
        for name in names:
            target = cls.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(REPO / name, target)
            os.chmod(target, 0o644)
        for entry in cls.manifest["entries"]:
            if entry["mode"] == "100755":
                os.chmod(cls.root / entry["path"], 0o755)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def check(self):
        verify.verify_protected(self.root, self.manifest, self.allowlist, False)
        return policy.verify_distribution(self.root)

    def entry_by_path(self):
        return {e["path"]: e for e in self.manifest["entries"]}

    def test_exact_current_source_and_recorded_identity_pass(self):
        value = self.check()
        self.assertIs(value["compiled_identity"]["reproduced"], True)
        self.assertEqual(value["proof"]["scope"], "historical-v1.1-program-only")
        self.assertEqual(policy.identity_source_digest(self.root, self.manifest), (64, policy.IDENTITY_SOURCE_SHA256))

    def test_kernel_byte_mutation_rejected(self):
        path = self.root / "crates/protocol/src/lib.rs"
        with changed(path, path.read_bytes() + b"\n// mutation\n"):
            with self.assertRaisesRegex(verify.VerificationError, "protected byte drift"):
                self.check()

    def test_cargo_dependency_and_metadata_changes_rejected(self):
        path = self.root / "Cargo.toml"
        original = path.read_bytes()
        mutations = [original.replace(b'p3-field = "=0.4.3"', b'p3-field = "=0.4.4"'),
                     original.replace(b'license = "BUSL-1.1"', b'license = "MIT"'),
                     original + b'\n[package.metadata.fixture]\nlicense = "BUSL-1.1"\n']
        for candidate in mutations:
            self.assertNotEqual(candidate, original)
            with self.subTest(candidate=candidate[-50:]), changed(path, candidate):
                with self.assertRaisesRegex(verify.VerificationError, "protected byte drift"):
                    self.check()

    def test_annotation_added_to_a_file_without_recorded_occurrences_rejected(self):
        # The v1.1 verifier rescanned only files that already held a recorded
        # occurrence; this one scans the whole protected surface.
        recorded = {o["path"] for o in self.allowlist["occurrences"]}
        name = "crates/wrap/src/encoding.rs"
        self.assertNotIn(name, recorded)
        path = self.root / name
        token = "W" + "9"
        with changed(path, path.read_bytes() + f"\n// {token}\n".encode()):
            with self.assertRaisesRegex(verify.VerificationError, "legacy occurrence multiset drift"):
                verify.verify_occurrences(self.root, self.allowlist["occurrences"],
                                          self.allowlist["policy"]["legacy_scan_regex"],
                                          verify.LEGACY_OCCURRENCES, self.entry_by_path(), "legacy")

    def test_enrolled_review_annotations_are_counted(self):
        families = self.allowlist["legacy_family_counts"]
        self.assertEqual(families["model_boundary_coordinate"], 1)
        self.assertEqual(families["review_wording"], 3)
        self.assertEqual(families["review_decision_coordinate"], 4)
        self.assertEqual(sum(families.values()), verify.LEGACY_OCCURRENCES)

    def test_stable_identifier_drift_rejected(self):
        recorded = {o["path"] for o in self.allowlist["stable_public_identifiers"]["occurrences"]}
        name = next(e["path"] for e in self.manifest["entries"]
                    if e["path"].endswith(".rs") and e["path"] not in recorded)
        path = self.root / name
        with changed(path, path.read_bytes() + b"\n// S-3\n"):
            with self.assertRaisesRegex(verify.VerificationError, "stable identifier occurrence multiset drift"):
                verify.verify_occurrences(self.root, self.allowlist["stable_public_identifiers"]["occurrences"],
                                          self.allowlist["policy"]["stable_identifier_scan_regex"],
                                          verify.STABLE_OCCURRENCES, self.entry_by_path(), "stable identifier")

    def test_record_false_claims_and_authority_changes_rejected(self):
        path = self.root / policy.IDENTITY_RECORD
        mutations = [
            ("license", lambda v: v.__setitem__("license", "MIT")),
            ("version", lambda v: v.__setitem__("distribution_version", "1.2.1")),
            ("reproduced", lambda v: v["compiled_identity"].__setitem__("reproduced", False)),
            ("builds", lambda v: v["compiled_identity"].__setitem__("clean_build_count", 1)),
            ("image", lambda v: v["compiled_identity"].__setitem__("image_id", "0" * 64)),
            ("covers", lambda v: v["proof"].__setitem__("covers_current_identity", True)),
            ("scope", lambda v: v["proof"].__setitem__("scope", "current-v1.2-program")),
            ("bound", lambda v: v["proof"].__setitem__("bound_image_id", v["compiled_identity"]["image_id"])),
            ("proof-bytes", lambda v: v["proof"].__setitem__("sha256", "0" * 64)),
            ("source", lambda v: v["identity_source"].__setitem__("sha256", "0" * 64)),
            ("baseline", lambda v: v["historical_baseline"].__setitem__("allowlist_sha256", "0" * 64)),
            ("citation-version", lambda v: v["citation"].__setitem__(
                "version", "1.1.1" if v["citation"]["version"] != "1.1.1" else "1.2.0")),
            ("citation-status", lambda v: v["citation"].__setitem__("status", "PREPARED")),
        ]
        for label, mutate in mutations:
            candidate = policy.load_record(path)
            mutate(candidate)
            with self.subTest(field=label), changed(path, json.dumps(candidate).encode()):
                with self.assertRaises(ValueError):
                    policy.verify_distribution(self.root)

    def test_expected_identity_record_change_rejected(self):
        path = self.root / policy.EXPECTED_IDENTITY_RECORD
        text = path.read_text(encoding="utf-8")
        record = policy.load_record(path)
        image = record["artifacts"]["image_id"]
        with changed(path, text.replace(image, "0" * 64).encode()):
            with self.assertRaisesRegex(ValueError, "expected identity record changed"):
                policy.verify_distribution(self.root)

    def test_duplicate_json_and_modified_root_license_rejected(self):
        path = self.root / policy.IDENTITY_RECORD
        duplicate = path.read_text(encoding="utf-8").replace('{', '{"license":"MIT",', 1)
        with changed(path, duplicate.encode()):
            with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
                policy.verify_distribution(self.root)
        license_path = self.root / "LICENSE"
        with changed(license_path, license_path.read_bytes() + b"\nextra grant\n"):
            with self.assertRaisesRegex(ValueError, "root BSL"):
                policy.verify_distribution(self.root)

    def test_cff_comment_duplicate_and_historical_doi_rejected(self):
        citation = policy.load_record(self.root / policy.IDENTITY_RECORD)["citation"]
        valid = (self.root / "CITATION.cff").read_text(encoding="utf-8")
        current = citation["doi"]
        self.assertEqual(valid.count(current), 1)
        candidates = [valid.replace("license: BUSL-1.1", "# license: BUSL-1.1\nlicense: MIT"),
                      valid + "\nlicense: MIT\n", valid.replace(current, "10.5281/zenodo.23136385"),
                      valid.replace(f'doi: "{current}"', "doi: 10.5281/zenodo.23136385"),
                      valid.replace(current, "10.5281/zenodo.99999999"),
                      valid + '\ndoi: "https://doi.org/10.5281/zenodo.23136385"\n',
                      valid + '\nversion: "1.1.0"\n']
        for candidate in candidates:
            with self.subTest(candidate=candidate[-80:]):
                self.assertNotEqual(candidate, valid)
                with self.assertRaises(ValueError):
                    policy.verify_cff(candidate, citation)
        policy.verify_cff(valid.replace("license: BUSL-1.1", 'license: "BUSL-1.1" # current grant'), citation)

    def test_citation_names_the_published_predecessor_or_a_published_v12_release(self):
        policy.verify_citation_pair("1.1.1", "10.5281/zenodo.23280552")
        policy.verify_citation_pair("1.2.0", "10.5281/zenodo.99999999")
        for pair in [("1.2.0", "10.5281/zenodo.23280552"), ("1.1.0", "10.5281/zenodo.23136385"),
                     ("1.2.1", "10.5281/zenodo.99999999"), ("1.2.0", "10.1234/other.1")]:
            with self.subTest(pair=pair):
                with self.assertRaises(ValueError):
                    policy.verify_citation_pair(*pair)

    def test_own_sbom_and_caller_metadata_rejected_when_mislabeled(self):
        path = self.root / policy.SBOM
        value = policy.load_record(path)
        next(p for p in value["packages"] if p["name"] == "statesync-gkr")["licenseDeclared"] = "MIT"
        with changed(path, json.dumps(value).encode()):
            with self.assertRaisesRegex(ValueError, "SBOM license"):
                policy.verify_distribution(self.root)
        value = policy.load_record(path)
        next(p for p in value["packages"] if p["SPDXID"] == "SPDXRef-Package-SourceArchive")["versionInfo"] = "1.1.1"
        with changed(path, json.dumps(value).encode()):
            with self.assertRaisesRegex(ValueError, "SBOM source archive version"):
                policy.verify_distribution(self.root)
        for caller in policy.CALLERS:
            manifest = self.root / caller / "Cargo.toml"
            with self.subTest(caller=caller), changed(manifest, manifest.read_bytes().replace(b'license = "BUSL-1.1"', b'license = "MIT"')):
                with self.assertRaisesRegex(ValueError, "caller license"):
                    policy.verify_distribution(self.root)

    def test_protected_git_blob_and_mode_are_checked(self):
        modes = {e["path"]: (e["mode"], e["git_blob_oid"]) for e in self.manifest["entries"]}
        from unittest.mock import patch
        with patch.object(verify, "entry_modes_from_git", return_value=modes):
            verify.verify_protected(self.root, self.manifest, self.allowlist, True)
        cargo = (self.root / "Cargo.toml").read_bytes()
        for value in [("100644", "0" * 40), ("100755", policy.git_blob_oid(cargo))]:
            wrong = dict(modes)
            wrong["Cargo.toml"] = value
            with self.subTest(value=value), patch.object(verify, "entry_modes_from_git", return_value=wrong):
                with self.assertRaisesRegex(verify.VerificationError, "protected Git mode/blob drift"):
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
            (policy_dir / "run_source_policy.py").write_bytes((REPO / "release/v1.2/run_source_policy.py").read_bytes())
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


class ReleaseLineTests(unittest.TestCase):
    """A successor line opens only with every existing release directory frozen."""

    @staticmethod
    def git(path, *args):
        return subprocess.run(["git", "-C", str(path), *args], check=True, capture_output=True)

    def fixture(self, parent: Path) -> Path:
        remote, work = parent / "base", parent / "head"
        remote.mkdir()
        self.git(remote, "init", "--initial-branch=main")
        self.git(remote, "config", "user.name", "Policy fixture")
        self.git(remote, "config", "user.email", "fixture.invalid")
        self.git(remote, "config", "commit.gpgsign", "false")
        wrapper = (REPO / "release/v1.2/run_source_policy.py").read_bytes()
        (remote / "release/v1.1").mkdir(parents=True)
        (remote / "release/v1.1/record.txt").write_text("earlier line\n", encoding="utf-8")
        line = remote / "release/v1.2"
        line.mkdir()
        (line / "license_distribution.py").write_text("ACCEPTS = False\n", encoding="utf-8")
        # The earlier line's verifier refuses every tree, so a pass below can
        # only come from the successor verifier.
        (line / "verify.py").write_text("raise SystemExit(1)\n", encoding="utf-8")
        (line / "run_source_policy.py").write_bytes(wrapper)
        self.git(remote, "add", ".")
        self.git(remote, "commit", "-m", "Establish the earlier line")
        subprocess.run(["git", "clone", str(remote), str(work)], check=True, capture_output=True)
        successor = work / "release/v1.3"
        successor.mkdir()
        (successor / "license_distribution.py").write_text("ACCEPTS = True\n", encoding="utf-8")
        (successor / "verify.py").write_text("raise SystemExit(0)\n", encoding="utf-8")
        (successor / "run_source_policy.py").write_bytes(wrapper)
        return work

    def run_pull_request(self, work: Path) -> int:
        return authority.run_policy(work, "pull_request", "main", "fixture/repo", "fixture/repo", "topic")

    def test_successor_line_judges_itself_only_with_existing_directories_frozen(self):
        with tempfile.TemporaryDirectory(prefix="ssgkr-line-fixture-") as folder:
            work = self.fixture(Path(folder))
            self.assertEqual(self.run_pull_request(work), 0)
            earlier = work / "release/v1.2/verify.py"
            with changed(earlier, b"raise SystemExit(0)\n"):
                with self.assertRaisesRegex(ValueError, "byte-identical"):
                    self.run_pull_request(work)
            extra = work / "release/v1.1/extra.txt"
            extra.write_text("added\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "byte-identical"):
                self.run_pull_request(work)
            extra.unlink()
            (work / "release/v1.3").rename(work / "release/v1.4")
            with self.assertRaisesRegex(ValueError, "skips"):
                self.run_pull_request(work)

    def test_push_runs_the_newest_complete_line(self):
        with tempfile.TemporaryDirectory(prefix="ssgkr-line-fixture-") as folder:
            work = self.fixture(Path(folder))
            self.assertEqual(authority.run_policy(work, "push", "main", "", "", ""), 0)
            (work / "release/v1.3/license_distribution.py").unlink()
            self.assertEqual(authority.run_policy(work, "push", "main", "", "", ""), 1)

    def test_direct_verifier_call_hands_off_to_a_later_line(self):
        with tempfile.TemporaryDirectory(prefix="ssgkr-line-fixture-") as folder:
            root = Path(folder)
            earlier = root / "release/v1.2"
            earlier.mkdir(parents=True)
            for name in ("verify.py", "license_distribution.py"):
                shutil.copyfile(REPO / "release/v1.2" / name, earlier / name)
            later = root / "release/v1.3"
            later.mkdir()
            (later / "verify.py").write_text(
                'import sys\nprint("later-line-verifier " + " ".join(sys.argv[1:]))\nraise SystemExit(3)\n',
                encoding="utf-8",
            )
            run = subprocess.run([sys.executable, "-B", str(earlier / "verify.py"), "--mode", "worktree"],
                                 capture_output=True, text=True, encoding="utf-8")
            self.assertEqual(run.returncode, 3)
            self.assertIn("release-line-handoff=release/v1.3", run.stdout)
            self.assertIn("later-line-verifier --mode worktree", run.stdout)


if __name__ == "__main__":
    unittest.main(verbosity=2)
