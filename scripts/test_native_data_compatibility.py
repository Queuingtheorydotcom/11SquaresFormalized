"""Regression checks for exact upstream authentication of computable field data."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import fetch_wand125_release as release
import native_data_compatibility as compatibility
from symlink_test_support import symlink_or_skip


class NativeDataTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.enterContext(mock.patch.object(compatibility, "ROOT", self.root))
        self.name = "Sqpack/S11Opt/F50/Data.lean"
        self.raw = (b"namespace Fixture\nnoncomputable def atom0 : List Nat := [314159, 27]\n"
                    b"noncomputable def atoms : List Nat := atom0\n"
                    b"noncomputable def opts5 : List Nat := atoms\n"
                    b"noncomputable def geometry : Nat := 3\nend Fixture\n")
        self.native = self.raw.replace(b"noncomputable def atom", b"def atom").replace(
            b"noncomputable def opts5", b"def opts5")
        self.entry = {"upstream_sha256": compatibility.digest(self.raw),
                      "sha256": compatibility.digest(self.native),
                      "declarations": ["atom0", "atoms", "opts5"]}
        self.manifest_path = self.root / compatibility.MANIFEST_NAME
        self.manifest_path.parent.mkdir()
        self.write_manifest()

    def write_manifest(self, name=None):
        self.manifest_path.write_text(json.dumps({"format_version": 1,
                                                  "files": {name or self.name: self.entry}}))

    def target(self, raw):
        path = self.root / self.name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        return path

    def test_exact_inverse_retains_numerals_and_other_noncomputable_definitions(self):
        expected = self.entry["upstream_sha256"]
        self.assertEqual(compatibility.upstream_bytes(self.name, self.native, expected), self.raw)
        self.assertEqual(compatibility.computable_bytes(self.name, self.raw, expected), self.native)
        self.assertEqual(compatibility.computable_bytes(self.name, self.native, expected), self.native)
        self.assertIn(b"noncomputable def geometry", self.native)

    def test_existing_variant_is_retained_without_weakening_raw_hash(self):
        path = self.target(self.native)
        inode = path.stat().st_ino
        self.assertFalse(release.check_target(self.root, self.name, self.entry["upstream_sha256"]))
        self.assertEqual(path.stat().st_ino, inode)
        self.assertEqual(path.read_bytes(), self.native)
        with self.assertRaises(release.ReleaseError):
            release.check_target(self.root, self.name, "0" * 64)

    def test_changed_number_rejected_even_if_transformed_hash_is_updated(self):
        altered = self.native.replace(b"314159", b"314160")
        for rewrite_manifest in (False, True):
            with self.subTest(rewrite_manifest=rewrite_manifest):
                if rewrite_manifest:
                    self.entry["sha256"] = compatibility.digest(altered)
                    self.write_manifest()
                self.target(altered)
                with self.assertRaises(release.ReleaseError):
                    release.check_target(self.root, self.name, self.entry["upstream_sha256"])

    def test_unknown_path_cannot_borrow_an_approved_transformation(self):
        other = self.name.replace("F50", "F49")
        with self.assertRaisesRegex(ValueError, "unrecognized"):
            compatibility.upstream_bytes(other, self.native, self.entry["upstream_sha256"])

    def test_wrong_manifest_output_hash_fails_before_conversion(self):
        self.entry["sha256"] = "0" * 64
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "output hash"):
            compatibility.computable_bytes(self.name, self.raw, self.entry["upstream_sha256"])

    def test_wrong_upstream_hash_rejected(self):
        self.entry["upstream_sha256"] = "0" * 64
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "upstream hash"):
            compatibility.computable_bytes(self.name, self.raw, compatibility.digest(self.raw))

    def test_manifest_rejects_other_names_paths_and_duplicate_definitions(self):
        for names in (["geometry"], ["opts5", "opts5"], []):
            self.entry["declarations"] = names
            self.write_manifest()
            with self.assertRaises(ValueError):
                compatibility.load_manifest()
        self.entry["declarations"] = ["opts5"]
        for path in ("../Data.lean", "Sqpack/S11Opt/F00/Data.lean", "Sqpack/S11Opt/F50/Cov5.lean"):
            self.write_manifest(path)
            with self.assertRaises(ValueError):
                compatibility.load_manifest()

    def test_missing_or_duplicate_declaration_rejected(self):
        self.entry["declarations"].append("atom99")
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "missing or repeated"):
            compatibility.computable_bytes(self.name, self.raw, self.entry["upstream_sha256"])

    def test_source_and_manifest_symlinks_rejected(self):
        path = self.target(self.native)
        saved = self.root / "saved"
        path.rename(saved)
        symlink_or_skip(self, path, saved)
        with self.assertRaisesRegex(release.ReleaseError, "symlink"):
            release.check_target(self.root, self.name, self.entry["upstream_sha256"])
        saved_manifest = self.root / "manifest"
        self.manifest_path.rename(saved_manifest)
        symlink_or_skip(self, self.manifest_path, saved_manifest)
        with self.assertRaisesRegex(ValueError, "symlink"):
            compatibility.load_manifest()


if __name__ == "__main__":
    unittest.main()
