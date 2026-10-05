"""Composition regressions for authenticated raw-source -> bundled setup."""
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import baseline_bundle_assembly as assembly
import baseline_bundle_ownership as ownership
import generate_baseline_coverage_bundles as coverage
import materialize_wand125 as materializer


class BundledSetupTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.own_path = "Sqpack/S11Opt/Bundled/Own/Mem.lean"
        self.leaf_path = "Sqpack/S11Opt/Bundled/Own/Leaves000.lean"
        self.assembly_path = "Sqpack/S11Opt/Bundled/Split/UField.lean"
        kernel_leaf = (b"namespace SquarePacking.S11Opt.Bundled.Own\n"
                       b"theorem t_o0_1_2_1 : True :=\n"
                       b"  soundDec 1 (by decide +kernel)\n"
                       b"end SquarePacking.S11Opt.Bundled.Own\n")
        self.kernel_own = {self.own_path: b"-- ownership fixture\n", self.leaf_path: kernel_leaf}
        self.own = {p: raw.replace(b"decide +kernel", b"native_decide")
                    for p, raw in self.kernel_own.items()}
        self.assembly = {self.assembly_path: b"-- assembly fixture\n"}
        self.own_inputs = {"original-own": "1" * 64}
        self.assembly_inputs = {"original-final": "2" * 64}
        self.build_own = self.enterContext(mock.patch.object(
            ownership, "build_ownership", side_effect=lambda root, native=True:
            (self.own if native else self.kernel_own, self.own_inputs)))
        self.build_assembly = self.enterContext(mock.patch.object(
            assembly, "build_assembly", return_value=(self.assembly, self.assembly_inputs)))
        self.generate = self.enterContext(mock.patch.object(
            coverage, "generate", side_effect=self.fake_coverage))
        self.enterContext(redirect_stdout(io.StringIO()))

    def fake_coverage(self, root, *, write):
        self.assertTrue(write)
        p = root / "Sqpack/S11Opt/Bundled/F04/source-manifest.json"
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text('{"fixture": true}\n')
        return [{"field": "F04", "output_modules": 2, "declarations": 12,
                 "legacy_manifest_sha256": "a" * 64,
                 "prior_native_manifest_sha256": "b" * 64}]

    def test_recognized_old_top_manifest_migrates(self):
        materializer.materialize_bundled_baseline(self.root)
        path = self.root / "Sqpack/S11Opt/Bundled/source-manifest.json"
        manifest = self.kernel_manifest(path)
        manifest["generator_sha256"]["generate_baseline_coverage_bundles.py"] = coverage.LEGACY_GENERATOR_SHA256
        manifest["generator_sha256"]["materialize_wand125.py"] = materializer.LEGACY_MATERIALIZER_SHA256
        manifest["coverage_manifests"] = {"Sqpack/S11Opt/Bundled/F04/source-manifest.json": "a" * 64}
        path.write_text(json.dumps(manifest, indent=2) + "\n")
        self.assertEqual(materializer.materialize_bundled_baseline(self.root)["created_files"], 1)

    def install_prior_native_top_manifest(self):
        materializer.materialize_bundled_baseline(self.root)
        path = self.root / "Sqpack/S11Opt/Bundled/source-manifest.json"
        manifest = self.kernel_manifest(path)
        manifest["generator_sha256"]["generate_baseline_coverage_bundles.py"] = coverage.PRIOR_NATIVE_GENERATOR_SHA256
        manifest["generator_sha256"]["materialize_wand125.py"] = materializer.PRIOR_NATIVE_MATERIALIZER_SHA256
        manifest["coverage_manifests"] = {"Sqpack/S11Opt/Bundled/F04/source-manifest.json": "b" * 64}
        path.write_text(json.dumps(manifest, indent=2) + "\n")
        return path

    def kernel_manifest(self, path):
        manifest = json.loads(path.read_text())
        manifest.pop("native_certificates")
        manifest["generator_sha256"]["baseline_bundle_ownership.py"] = ownership.KERNEL_GENERATOR_SHA256
        manifest["generator_sha256"]["materialize_wand125.py"] = materializer.KERNEL_OWNERSHIP_MATERIALIZER_SHA256
        for name, raw in self.kernel_own.items():
            manifest["outputs"][name] = {"sha256": ownership.digest(raw), "bytes": len(raw)}
        return manifest

    def test_exact_kernel_ownership_and_current_field_manifest_migrate(self):
        materializer.materialize_bundled_baseline(self.root)
        path = self.root / "Sqpack/S11Opt/Bundled/source-manifest.json"
        path.write_text(json.dumps(self.kernel_manifest(path), indent=2) + "\n")
        (self.root / self.leaf_path).write_bytes(self.kernel_own[self.leaf_path])
        self.assertEqual(materializer.materialize_bundled_baseline(self.root)["created_files"], 2)
        self.assertEqual((self.root / self.leaf_path).read_bytes(), self.own[self.leaf_path])
        self.assertEqual(materializer.materialize_bundled_baseline(self.root)["created_files"], 0)

    def test_tampered_kernel_ownership_rejected_before_coverage_write(self):
        p = self.root / self.leaf_path
        p.parent.mkdir(parents=True)
        altered = self.kernel_own[self.leaf_path].replace(b"soundDec 1", b"soundDec 2")
        p.write_bytes(altered)
        with self.assertRaises(ValueError):
            materializer.materialize_bundled_baseline(self.root)
        self.generate.assert_not_called()
        self.assertEqual(p.read_bytes(), altered)

    def test_exact_prior_native_top_manifest_migrates_and_is_resumable(self):
        self.install_prior_native_top_manifest()
        self.assertEqual(materializer.materialize_bundled_baseline(self.root)["created_files"], 1)
        self.assertEqual(materializer.materialize_bundled_baseline(self.root)["created_files"], 0)

    def test_tampered_prior_native_top_manifest_is_rejected(self):
        path = self.install_prior_native_top_manifest()
        altered = path.read_bytes().replace(b'"b' + b'b' * 63, b'"c' + b'c' * 63)
        self.assertNotEqual(altered, path.read_bytes())
        path.write_bytes(altered)
        with self.assertRaises(ValueError):
            materializer.materialize_bundled_baseline(self.root)
        self.assertEqual(path.read_bytes(), altered)

    def test_unknown_top_manifest_edit_is_rejected(self):
        materializer.materialize_bundled_baseline(self.root)
        path = self.root / "Sqpack/S11Opt/Bundled/source-manifest.json"
        path.write_bytes(path.read_bytes() + b" ")
        with self.assertRaises(ValueError):
            materializer.materialize_bundled_baseline(self.root)

    def test_setup_publishes_both_helpers_and_is_resumable(self):
        first = materializer.materialize_bundled_baseline(self.root)
        self.assertEqual(first["created_files"], 4)
        self.assertEqual((self.root / self.own_path).read_bytes(), self.own[self.own_path])
        self.assertEqual((self.root / self.assembly_path).read_bytes(), self.assembly[self.assembly_path])
        args, kwargs = self.build_assembly.call_args
        self.assertEqual(list(args[1]), list(range(1, 59)))
        self.assertEqual(kwargs, {"include_full": True, "bundled_ownership": True})
        manifest = json.loads((self.root / "Sqpack/S11Opt/Bundled/source-manifest.json").read_text())
        self.assertEqual(manifest["status"], "SOURCE_ONLY_NOT_COMPILED")
        self.assertEqual(manifest["assembly_and_ownership_inputs"],
                         {**self.own_inputs, **self.assembly_inputs})
        self.assertEqual(set(manifest["outputs"]), {self.own_path, self.leaf_path, self.assembly_path})
        self.assertEqual(set(manifest["native_certificates"]), {self.leaf_path})
        self.assertEqual(manifest["native_certificates"][self.leaf_path]["declarations"],
                         {"SquarePacking.S11Opt.Bundled.Own.t_o0_1_2_1": 1})
        self.assertEqual(materializer.materialize_bundled_baseline(self.root)["created_files"], 0)

    def test_differing_existing_helper_rejected_before_coverage_write(self):
        p = self.root / self.own_path
        p.parent.mkdir(parents=True)
        p.write_bytes(b"local edit")
        with self.assertRaisesRegex(ValueError, "existing destination differs"):
            materializer.materialize_bundled_baseline(self.root)
        self.generate.assert_not_called()
        self.assertEqual(p.read_bytes(), b"local edit")

    def test_conflicting_input_hashes_rejected_before_writing(self):
        self.assembly_inputs["original-own"] = "3" * 64
        with self.assertRaisesRegex(ValueError, "conflicting authenticated input"):
            materializer.materialize_bundled_baseline(self.root)
        self.generate.assert_not_called()

    def test_output_collision_rejected_before_writing(self):
        self.assembly[self.own_path] = b"different helper"
        with self.assertRaisesRegex(ValueError, "overlapping derived output"):
            materializer.materialize_bundled_baseline(self.root)
        self.generate.assert_not_called()

    def test_cli_raw_only_preserves_original_staging_workflow(self):
        with mock.patch.object(materializer, "materialize") as restore, \
                mock.patch.object(materializer, "materialize_bundled_baseline") as derive:
            for raw_only in (False, True):
                with self.subTest(raw_only=raw_only):
                    restore.reset_mock()
                    derive.reset_mock()
                    args = ["--destination", str(self.root)]
                    if raw_only:
                        args.append("--raw-only")
                    self.assertEqual(materializer.main(args), 0)
                    restore.assert_called_once()
                    if raw_only:
                        derive.assert_not_called()
                    else:
                        derive.assert_called_once_with(self.root)


if __name__ == "__main__":
    unittest.main()
