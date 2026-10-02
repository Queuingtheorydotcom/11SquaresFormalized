"""Offline byte-preservation and trust-boundary tests; no Lean execution."""
import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import baseline_bundle_assembly as assembly


# Minimal source-shaped fixtures. Proof markers are never compiled or published.
FINAL_BODY = """
open FieldTree

lemma cover1 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 1 c) :
    True := by
  exact source_cover1

lemma hcov : ∀ k ∈ pos, True := by
  exact source_hcov

theorem excluded (P : List ℕ) (hP : P.Nodup) (hPsub : ∀ k ∈ P, k ∈ pos)
    (hgap : ∑ a ∈ Finset.range atoms.length, wts.getD a 0 < (P.map (gam.getD · 0)).sum) :
    CaseExcluded (supp ++ P) :=
  source_excluded P hP hPsub hgap

noncomputable def applicable (J : List ℕ) : Bool :=
  supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range atoms.length, wts.getD a 0) <
      ((pos.filter (· ∈ J)).map (gam.getD · 0)).sum)

theorem applicable_sound {J : List ℕ} (h : applicable J = true) : CaseExcluded J := by
  exact source_sound h
""".encode()

FIELD_ALL_BODY = """
def app00 (J : List ℕ) : Bool := F00.supp.all (· ∈ J)

noncomputable def app (J : List ℕ) : Bool := app00 J

theorem app_sound {J : List ℕ} (h : app J = true) : CaseExcluded J := by
  exact source_app_sound h

noncomputable def excludedField : List (List ℕ) := canonicalMasks.filter fun J => app J || app (hmask J)

lemma excludedField_length : excludedField.length = 1904 := by decide +kernel

theorem excludedField_all : ∀ J ∈ excludedField, CaseExcluded J := by
  intro J hJ
  obtain h := source_excluded J hJ
  exact h
""".encode()


class AssemblyTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.pinned = {}
        self.common = {}
        patch = mock.patch.object(assembly.release, "release_plan", side_effect=self.plan)
        patch.start()
        self.addCleanup(patch.stop)
        self.add_final(4)

    def plan(self, unit, fields=None):
        if unit == "F":
            selected = {f"Sqpack/S11Opt/F{f:02d}/Final.lean" for f in fields}
            return [("fixture", "0" * 64, {p: h for p, h in self.pinned.items() if p in selected})]
        self.assertEqual(unit, "FCOMMON")
        return [("fixture-common", "0" * 64, dict(self.common))]

    def put(self, path, raw, pinned):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
        pinned[path] = hashlib.sha256(raw).hexdigest()
        return target

    def add_final(self, field):
        label = f"F{field:02d}"
        raw = (f"import Sqpack.S11Opt.{label}.Cov1\n"
               "import Sqpack.S11Opt.Own.Mem\nimport Sqpack.S11Opt.FieldGen\n\n"
               f"namespace SquarePacking.S11Opt.{label}\n").encode()
        raw += FINAL_BODY + f"\nend SquarePacking.S11Opt.{label}\n".encode()
        return self.put(f"Sqpack/S11Opt/{label}/Final.lean", raw, self.pinned)

    def full_fixture(self):
        for field in range(1, 59):
            self.add_final(field)
        imports = "".join(f"import Sqpack.S11Opt.F{i:02d}.Final\n" for i in range(1, 59))
        raw = (imports + "import Sqpack.S11Opt.F00.Final\n\nnamespace SquarePacking.S11Opt.FieldAll\n").encode()
        raw += FIELD_ALL_BODY + b"\nend SquarePacking.S11Opt.FieldAll\n"
        self.put("Sqpack/S11Opt/FieldAll.lean", raw, self.common)
        # This small tracked source also tests the independently pinned UField hash.
        source = Path(__file__).resolve().parents[1] / assembly.UFIELD_PATH
        self.put(assembly.UFIELD_PATH, source.read_bytes(), {})

    def test_deterministic_outputs_preserve_original_region_and_contracts(self):
        self.add_final(1)
        result = assembly.build_assembly(self.root, [4, 1, 4])
        self.assertEqual(result, assembly.build_assembly(self.root, [1, 4]))
        outputs, inputs = result
        self.assertEqual(len(outputs), 2)
        self.assertEqual(inputs, self.pinned)
        raw = outputs[assembly.PREFIX + "F04/Final.lean"]
        self.assertIn(FINAL_BODY, raw)
        self.assertIn(b"import Sqpack.S11Opt.Bundled.F04.Coverage\n", raw)
        self.assertNotIn(b"import Sqpack.S11Opt.F04.", raw)
        self.assertEqual(raw.count(b"example"), 5)
        self.assertIn(assembly._header(FINAL_BODY, "cover1"), raw)
        self.assertIn(assembly._header(FINAL_BODY, "excluded"), raw)
        self.assertIn(b") := rfl\n", raw)
        self.assertIn(b"#print axioms SquarePacking.S11Opt.Bundled.F04.applicable_sound\n", raw)
        self.assertFalse((self.root / assembly.PREFIX).exists())

    def test_ownership_flag_changes_only_the_import(self):
        default, _ = assembly.build_assembly(self.root, [4])
        bundled, _ = assembly.build_assembly(self.root, [4], bundled_ownership=True)
        name = assembly.PREFIX + "F04/Final.lean"
        self.assertEqual(default[name].replace(b"import Sqpack.S11Opt.Own.Mem\n",
                         b"import Sqpack.S11Opt.Bundled.Own.Mem\n"), bundled[name])

    def test_header_stops_before_proof_local_assignment(self):
        header = assembly._header(FIELD_ALL_BODY, "excludedField_all")
        self.assertEqual(header, " : ∀ J ∈ excludedField, CaseExcluded J".encode())

    def test_modified_source_is_rejected(self):
        target = self.root / "Sqpack/S11Opt/F04/Final.lean"
        target.write_bytes(target.read_bytes() + b"-- changed\n")
        with self.assertRaisesRegex(ValueError, "differs"):
            assembly.build_assembly(self.root, [4])

    def test_authenticated_unfamiliar_wrapper_is_rejected(self):
        name = "Sqpack/S11Opt/F04/Final.lean"
        raw = (self.root / name).read_bytes().replace(b"open FieldTree\n", b"open FieldTree\nset_option maxRecDepth 1\n")
        self.put(name, raw, self.pinned)
        with self.assertRaises(assembly.AssemblyError):
            assembly.build_assembly(self.root, [4])

    def test_symlink_source_is_rejected(self):
        source = self.root / "Sqpack/S11Opt/F04/Final.lean"
        target = self.root / "saved.lean"
        source.rename(target)
        source.symlink_to(target)
        with self.assertRaisesRegex(ValueError, "symlink"):
            assembly.build_assembly(self.root, [4])

    def test_missing_source_is_rejected(self):
        (self.root / "Sqpack/S11Opt/F04/Final.lean").unlink()
        with self.assertRaisesRegex(assembly.AssemblyError, "missing pinned"):
            assembly.build_assembly(self.root, [4])

    def test_invalid_or_partial_full_selection_is_rejected(self):
        for fields in ([], [0], [59], [True], ["4"]):
            with self.subTest(fields=fields), self.assertRaises(assembly.AssemblyError):
                assembly.build_assembly(self.root, fields)
        with self.assertRaisesRegex(assembly.AssemblyError, "all fields"):
            assembly.build_assembly(self.root, [4], include_full=True)

    def test_full_assembly_preserves_bodies_and_original_f00(self):
        self.full_fixture()
        outputs, inputs = assembly.build_assembly(self.root, range(1, 59), include_full=True)
        self.assertEqual(len(outputs), 60)
        self.assertEqual(len(inputs), 60)
        field_all = outputs[assembly.PREFIX + "FieldAll.lean"]
        self.assertIn(FIELD_ALL_BODY, field_all)
        self.assertIn(b"import Sqpack.S11Opt.F00.Final\n", field_all)
        self.assertEqual(field_all.count(b"import Sqpack.S11Opt.Bundled.F"), 58)
        self.assertFalse(any("/F00/" in name for name in outputs))
        ufield = outputs[assembly.PREFIX + "Split/UField.lean"]
        self.assertIn(b"import Sqpack.S11Opt.Split.Interface\n", ufield)
        self.assertIn(b"#print axioms SquarePacking.S11Opt.Bundled.Split.field_excluded\n", ufield)
        original = (self.root / assembly.UFIELD_PATH).read_bytes()
        _, body, _ = assembly._split(original, "SquarePacking.S11Opt.Split")
        self.assertIn(assembly._header(body, "field_excluded"), ufield)

    def test_ufield_hash_is_independently_pinned(self):
        self.full_fixture()
        target = self.root / assembly.UFIELD_PATH
        target.write_bytes(target.read_bytes() + b"-- changed\n")
        with self.assertRaisesRegex(ValueError, "differs"):
            assembly.build_assembly(self.root, range(1, 59), include_full=True)


if __name__ == "__main__":
    unittest.main()
