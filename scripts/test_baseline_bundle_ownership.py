"""Source-only regressions for authenticating/copying ownership certificates."""
from pathlib import Path
import tempfile
import unittest

import baseline_bundle_ownership as own


def point_fixture(point="o0_1_2"):
    owner, x, y = own.POINT.fullmatch(point).groups()
    return (f"import Sqpack.S11Opt.Shared.Grid\n\nnamespace {own.ORIGINAL}\n\nopen FieldTree\n\n"
            f"def opt_{point} : List (List (List (ℕ × ℕ))) := [[[({x}, {y})]]]\n\n"
            f"theorem t_{point}_1 : CovF G.Q G.M G.R G.hps{owner} opt_{point} 0 1 0 1 0 1 :=\n"
            f"  soundDec G.Q G.M G.R 4096 200 1 G.Q_pos G.R_pos G.hps{owner} opt_{point} (by decide +kernel)\n"
            f"\nend {own.ORIGINAL}\n").encode()


class OwnershipTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.point = "o0_1_2"
        self.path = own.PREFIX + self.point + ".lean"
        self.raw = point_fixture()

    def parse(self, raw=None):
        raw = self.raw if raw is None else raw
        return own.parse_point(self.path, raw, own.digest(raw))

    def write(self, path, raw):
        p = self.root / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(raw)
        return own.digest(raw)

    def fixture_plan(self, budget=own.BUDGET):
        points = ("o0_1_2", "o1_3_4")
        pinned = {own.PREFIX + p + ".lean": self.write(own.PREFIX + p + ".lean", point_fixture(p))
                  for p in points}
        pinned[own.GRID] = self.write(own.GRID, b"-- grid fixture\n")
        pinned[own.PREFIX + "Data.lean"] = self.write(own.PREFIX + "Data.lean", b"-- original registry fixture\n")
        mem = "".join(f"import Sqpack.S11Opt.Own.{p}\n" for p in points)
        mem += ("import Sqpack.S11Opt.Own.Data\nimport Sqpack.S11Opt.FieldBridge\n"
                f"\nnamespace {own.ORIGINAL}\n\nopen FieldTree\n\n")
        mem += "\n".join(own.mem_lemma(p) for p in points) + "\n"
        mem += (f"theorem reg_mem : {own.REG_TYPE} := by\n"
                "  intro e he\n"
                "  simp only [reg, List.mem_cons, List.not_mem_nil, or_false] at he\n"
                "  rcases he with rfl | rfl\n"
                "  · exact fun hin hc => mem_o0_1_2 hin hc\n"
                "  · exact fun hin hc => mem_o1_3_4 hin hc\n"
                f"\nend {own.ORIGINAL}\n")
        pinned[own.PREFIX + "Mem.lean"] = self.write(own.PREFIX + "Mem.lean", mem.encode())
        self.write(own.BRIDGE, b"-- bridge fixture\n")
        return own._plan(self.root, pinned, budget)

    def test_authentication_precedes_parsing(self):
        with self.assertRaisesRegex(own.OwnershipBundleError, "hash mismatch"):
            own.parse_point(self.path, self.raw + b"\n", own.digest(self.raw))

    def test_exact_numeric_definition_is_required(self):
        changed = self.raw.replace(b"[[[(1, 2)]]]", b"[[[(1, 3)]]]")
        with self.assertRaisesRegex(own.OwnershipBundleError, "definition"):
            self.parse(changed)

    def test_unexpected_command_or_proof_is_rejected(self):
        cases = [self.raw.replace(b"\nend ", b"\nset_option maxRecDepth 0\nend "),
                 self.raw.replace(b"(by decide +kernel)", b"(by sorry)"),
                 self.raw.replace(b"  soundDec", b"  Other.soundDec")]
        for changed in cases:
            with self.subTest(changed=changed[-180:]):
                with self.assertRaises(own.OwnershipBundleError):
                    self.parse(changed)

    def test_forward_and_cross_point_references_are_rejected(self):
        start = self.raw.index(b"  soundDec")
        end = self.raw.index(b"\n", start)
        for proof in (b"  CovF.splitX 1 t_o0_1_2_2 t_o0_1_2_3",
                      b"  CovF.splitX 1 t_o0_1_2_1 t_o1_3_4_1"):
            with self.assertRaises(own.OwnershipBundleError):
                self.parse(self.raw[:start] + proof + self.raw[end:])

    def test_leaf_source_body_is_copied_exactly_and_imports_are_independent(self):
        plan = self.fixture_plan(budget=1400)
        outputs = dict(own.lean_outputs(self.root, plan))
        leaves = [(p, raw) for p, raw in outputs.items() if "/Leaves" in p]
        self.assertEqual(len(leaves), 2)
        for path, raw in leaves:
            self.assertLessEqual(len(raw), 1400)
            self.assertEqual([line for line in raw.splitlines() if line.startswith(b"import ")],
                             [b"import Sqpack.S11Opt.Shared.Grid"])
        for source in plan["sources"]:
            original = (self.root / source.path).read_bytes()
            body = original[source.body_start:source.body_end]
            self.assertEqual(sum(raw.count(body) for _, raw in leaves), 1)
        mem = outputs[own.OUTPUT + "Mem.lean"]
        self.assertIn(own.ORIGINAL_REG_TYPE.encode(), mem)
        self.assertIn(b"import Sqpack.S11Opt.Own.Data", mem)
        self.assertNotIn(b"import Sqpack.S11Opt.Own.o", mem)
        self.assertNotIn(b"import Sqpack.S11Opt.Own.Mem", mem)

    def test_modified_input_after_planning_is_rejected(self):
        plan = self.fixture_plan()
        self.write(self.path, self.raw + b"\n")
        with self.assertRaises(ValueError):
            list(own.lean_outputs(self.root, plan))

    def test_mem_dispatch_cannot_be_reordered_or_weakened(self):
        self.fixture_plan()
        raw = (self.root / (own.PREFIX + "Mem.lean")).read_bytes()
        changed = raw.replace(b"mem_o1_3_4 hin hc", b"mem_o0_1_2 hin hc")
        with self.assertRaisesRegex(own.OwnershipBundleError, "registry dispatch"):
            own.parse_mem(changed, ("o0_1_2", "o1_3_4"))

    def test_emitted_size_budget_cannot_be_exceeded(self):
        with self.assertRaisesRegex(own.OwnershipBundleError, "budget"):
            self.fixture_plan(budget=100)


if __name__ == "__main__":
    unittest.main()
