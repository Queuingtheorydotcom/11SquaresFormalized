#!/usr/bin/env python3
"""Offline byte-preservation, grammar, dependency and publication regressions."""
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import generate_baseline_coverage_bundles as bundles
from symlink_test_support import symlink_or_skip


PROP = "CovF G.Q G.M G.R G.hps1 opts1 0 2 0 2 0 2"


def declaration(name, proof=None, proposition=PROP):
    if proof is None:
        proof = "soundDec G.Q G.M G.R 4096 200 123456789 G.Q_pos G.R_pos G.hps1 opts1 (by decide +kernel)"
    return f"theorem {name} : {proposition} :=\n  {proof}\n"


def source(body, imports=("Sqpack.S11Opt.F04.Data",)):
    return ("\n".join("import " + name for name in imports) +
            "\n\nnamespace SquarePacking.S11Opt.F04\n\nopen FieldTree\n\n" +
            body + "\nend SquarePacking.S11Opt.F04\n").encode()


class CoverageBundlesTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.pinned = {}
        self.put("Data", b"pinned data fixture\n")
        self.leaf0 = source(declaration("cov1p0_1"))
        self.leaf1 = source(declaration("cov1p1_1"))
        self.put("Cov1P0", self.leaf0)
        self.put("Cov1P1", self.leaf1)
        self.aggregate = source(declaration("cov1g1", "CovF.splitX 1 cov1p0_1 cov1p1_1"),
                                ("Sqpack.S11Opt.F04.Cov1P0", "Sqpack.S11Opt.F04.Cov1P1"))
        self.put("Cov1", self.aggregate)

    def put(self, name, raw):
        path = f"Sqpack/S11Opt/F04/{name}.lean"
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
        self.pinned[path] = bundles.digest(raw)
        return target

    def plan(self, budget=bundles.BUDGET):
        return bundles.field_plan(self.root, 4, self.pinned, budget)

    def parse(self, raw):
        return bundles.parse_source("Sqpack/S11Opt/F04/Cov1P0.lean", raw, bundles.digest(raw))

    def test_verbatim_declarations_and_original_type_examples(self):
        plan = self.plan()
        outputs = dict(bundles.lean_outputs(self.root, plan))
        leaf = outputs["Sqpack/S11Opt/Bundled/F04/Leaves000.lean"]
        for name in ("cov1p0_1", "cov1p1_1"):
            self.assertEqual(leaf.count(declaration(name).encode()), 1)
            self.assertIn((f"example : {PROP} :=\n  SquarePacking.S11Opt.Bundled.F04.{name}").encode(), leaf)
            self.assertIn(f"#print axioms SquarePacking.S11Opt.Bundled.F04.{name}".encode(), leaf)
        self.assertEqual(leaf.count(b"soundDec"), 2)
        self.assertEqual(leaf.count(b"section\nopen SquarePacking.S11Opt.F04"), 2)
        self.assertEqual((self.root / "Sqpack/S11Opt/F04/Cov1P0.lean").read_bytes(), self.leaf0)

    def test_independent_batches_and_real_dependency_imports(self):
        # The unreferenced leaf must not become an import of Coverage or other leaf batches.
        self.put("Cov2P0", source(declaration("cov2p0_1", proposition=PROP.replace("hps1 opts1", "hps2 opts2"),
                                                    proof="soundDec G.Q G.M G.R 4096 200 1 G.Q_pos G.R_pos G.hps2 opts2 (by decide +kernel)")))
        plan = self.plan(budget=len(self.leaf0))
        outputs = dict(bundles.lean_outputs(self.root, plan))
        self.assertEqual(len(plan["batches"]), 3)
        for path, raw in outputs.items():
            imports = [line for line in raw.splitlines() if line.startswith(b"import ")]
            if "Leaves" in path:
                self.assertEqual(imports, [b"import Sqpack.S11Opt.F04.Data"])
            else:
                self.assertEqual(imports, [b"import Sqpack.S11Opt.Bundled.F04.Leaves000",
                                           b"import Sqpack.S11Opt.Bundled.F04.Leaves001"])

    def test_packing_and_output_are_deterministic(self):
        plan = self.plan(budget=len(self.leaf0))
        first = list(bundles.lean_outputs(self.root, plan))
        self.pinned = dict(reversed(list(self.pinned.items())))
        self.assertEqual(first, list(bundles.lean_outputs(self.root, self.plan(budget=len(self.leaf0)))))

    def test_oversize_leaf_is_never_split(self):
        plan = self.plan(budget=1)
        self.assertEqual([len(batch) for batch in plan["batches"]], [1, 1])
        report = bundles.materialize_field(self.root, plan)
        self.assertEqual(report["oversize_singletons"], 2)

    def test_empty_import_aggregator_preserves_dependency(self):
        self.put("Cov1", source("\n", ("Sqpack.S11Opt.F04.Cov1P0",)))
        outputs = dict(bundles.lean_outputs(self.root, self.plan()))
        self.assertIn(b"import Sqpack.S11Opt.Bundled.F04.Leaves000", outputs["Sqpack/S11Opt/Bundled/F04/Coverage.lean"])

    def test_rejects_unfamiliar_commands_and_proofs(self):
        mutations = [
            self.leaf0.replace(b"theorem ", b"private theorem "),
            self.leaf0.replace(b"theorem ", b"@[simp] theorem "),
            self.leaf0.replace(b"theorem ", b"set_option maxRecDepth 1000\ntheorem "),
            self.leaf0.replace(b"theorem ", b"open scoped BigOperators\ntheorem "),
            self.leaf0.replace(b"theorem ", b"variable (x : Nat)\ntheorem "),
            self.leaf0.replace(b"(by decide +kernel)", b"(by sorry)"),
            self.leaf0.replace(b"soundDec", b"SquarePacking.S11Opt.F05.soundDec"),
            self.leaf0.replace(b"\n", b"\r\n"),
            self.leaf0.replace(b"open FieldTree", b"open FieldTree -- comment"),
            self.leaf0.replace(b"G.hps1 opts1 (by", b"G.hps2 opts2 (by"),
        ]
        for raw in mutations:
            with self.subTest(raw=raw[:90]), self.assertRaises(bundles.BundleError):
                self.parse(raw)

    def test_rejects_forward_leaf_references_and_duplicates(self):
        for body in (declaration("cov1p0_1", "CovF.splitX 1 cov1p0_2 cov1p0_2"),
                     declaration("cov1p0_1") + "\n" + declaration("cov1p0_1")):
            with self.assertRaises(bundles.BundleError):
                self.parse(source(body))

    def test_earlier_leaf_reference_is_accepted(self):
        raw = source(declaration("cov1p0_1") + "\n" +
                     declaration("cov1p0_2", "CovF.splitX 1 cov1p0_1 cov1p0_1"))
        self.assertEqual(len(self.parse(raw).declarations), 2)

    def test_rejects_unknown_or_cross_field_imports(self):
        for module in ("Sqpack.S11Opt.F05.Data", "Sqpack.S11Opt.F04.Cov1P1", "Mathlib"):
            with self.assertRaises(bundles.BundleError):
                self.parse(source(declaration("cov1p0_1"), (module,)))

    def test_rejects_missing_aggregator_reference(self):
        self.put("Cov1", self.aggregate.replace(b"splitX 1 cov1p0_1 cov1p1_1", b"splitX 1 cov1p0_1 cov1p9_1"))
        with self.assertRaisesRegex(bundles.BundleError, "unavailable aggregator"):
            self.plan()

    def test_authentication_and_post_plan_changes_fail(self):
        plan = self.plan()
        (self.root / "Sqpack/S11Opt/F04/Cov1P0.lean").write_bytes(self.leaf0 + b"\n")
        with self.assertRaises(ValueError):
            self.plan()
        with self.assertRaises(ValueError):
            list(bundles.lean_outputs(self.root, plan))

    def test_dry_run_writes_nothing_and_records_provenance(self):
        plan = self.plan()
        report = bundles.materialize_field(self.root, plan)
        self.assertEqual(report["status"], "DRY_RUN")
        self.assertFalse((self.root / "Sqpack/S11Opt/Bundled").exists())
        manifest = bundles.source_manifest(plan, report["outputs"])
        self.assertEqual(manifest["generator_sha256"], bundles.release.sha256_file(Path(bundles.__file__)))
        self.assertEqual(manifest["sources"][0]["sha256"], self.pinned[manifest["sources"][0]["path"]])

    def test_reused_plan_reauthenticates_data(self):
        plan = self.plan()
        (self.root / plan["data"]).write_bytes(b"changed data")
        with self.assertRaises(ValueError):
            bundles.materialize_field(self.root, plan, write=True)
        self.assertFalse((self.root / "Sqpack/S11Opt/Bundled").exists())

    def test_write_is_idempotent_and_original_sources_unchanged(self):
        plan = self.plan()
        report = bundles.materialize_field(self.root, plan, write=True)
        target = self.root / report["aggregate"]
        inode = target.stat().st_ino
        second = bundles.materialize_field(self.root, plan, write=True)
        self.assertEqual(target.stat().st_ino, inode)
        self.assertEqual(second["new_bytes"], 0)
        for path, sha in self.pinned.items():
            self.assertEqual(bundles.digest((self.root / path).read_bytes()), sha)

    def test_collision_preflight_creates_no_other_outputs(self):
        folder = self.root / "Sqpack/S11Opt/Bundled/F04"
        folder.mkdir(parents=True)
        (folder / "Coverage.lean").write_bytes(b"conflict")
        with self.assertRaises(ValueError):
            bundles.materialize_field(self.root, self.plan(), write=True)
        self.assertEqual(sorted(p.name for p in folder.iterdir()), ["Coverage.lean"])

    def test_stale_bundle_and_output_symlink_are_rejected(self):
        folder = self.root / "Sqpack/S11Opt/Bundled/F04"
        folder.mkdir(parents=True)
        stale = folder / "Leaves999.lean"
        stale.write_bytes(b"stale")
        with self.assertRaisesRegex(bundles.BundleError, "stale"):
            bundles.materialize_field(self.root, self.plan())
        stale.unlink()
        symlink_or_skip(self, folder / "Leaves000.lean", self.root / "Sqpack/S11Opt/F04/Data.lean")
        with self.assertRaises(ValueError):
            bundles.materialize_field(self.root, self.plan(), write=True)

    def test_api_authenticates_manifest_and_never_accepts_f00(self):
        with mock.patch.object(bundles.release, "release_plan", return_value=[("fixture", "0"*64, self.pinned)]) as read:
            results = bundles.generate(self.root, [4, 4], budget=len(self.leaf0))
            read.assert_called_once_with("F", [4])
            self.assertEqual(len(results), 1)
        with self.assertRaises(bundles.BundleError):
            bundles.generate(self.root, [0])
        with mock.patch.object(bundles.release, "release_plan", side_effect=ValueError("pinned metadata hash mismatch")):
            with self.assertRaisesRegex(ValueError, "pinned metadata"):
                bundles.generate(self.root, [4])

    def test_shared_publisher_preflights_and_rejects_other_directories(self):
        names = ["Sqpack/S11Opt/Bundled/F04/A.lean", "Sqpack/S11Opt/Bundled/F04/B.lean"]
        second = self.root / names[1]
        second.parent.mkdir(parents=True)
        second.write_bytes(b"conflict")
        with self.assertRaises(ValueError):
            bundles.publish_outputs(self.root, {name: b"expected" for name in names})
        self.assertFalse((self.root / names[0]).exists())
        with self.assertRaises(bundles.BundleError):
            bundles.publish_outputs(self.root, {"Sqpack/S11Opt/F04/Extra.lean": b"no"})

    def test_concurrent_identical_publication_is_accepted(self):
        name = "Sqpack/S11Opt/Bundled/F04/Concurrent.lean"
        def concurrent(source, target):
            target.write_bytes(Path(source).read_bytes())
            raise FileExistsError()
        with mock.patch.object(bundles.os, "link", side_effect=concurrent):
            result = bundles.publish_outputs(self.root, {name: b"same bytes"})
        self.assertEqual(result["created_files"], 0)
        self.assertEqual((self.root / name).read_bytes(), b"same bytes")
        self.assertFalse(list((self.root / name).parent.glob(".bundle-*")))


if __name__ == "__main__":
    unittest.main()
