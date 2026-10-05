"""Exact source, literal, ordering, and predecessor audits for data splitting."""
from contextlib import redirect_stdout
import copy
import io
import json
from pathlib import Path
import tempfile
import unittest

import split_indexed_data as split
from symlink_test_support import symlink_or_skip

TRI = "[(1, (2, 3), (4, 5), (6, 7), [(8, 9)], [[10, 11, 12]])]"
NAME = "Sqpack/S11Opt/Split/U2R/C1849/Data.lean"


def source(triangles=None, targets=None):
    triangles = [TRI, TRI.replace("(2, 3)", "(20, 30)"), "[]"] if triangles is None else triangles
    targets = ["[(1, 2)]", "[(30, 40)]"] if targets is None else targets
    return ("import Sqpack.S11Opt.Split.U2P.Rules\n"
            "set_option maxRecDepth 100000\n"
            "namespace SquarePacking.S11Opt.Split.U2R.C1849\n"
            + split._render_table("traceTriangleTable", triangles)
            + "def traceTriangles (stage : Nat) := (traceTriangleTable[stage]?).getD []\n"
            + split._render_table("traceTargetTable", targets)
            + "def traceTargets (stage : Nat) := (traceTargetTable[stage]?).getD []\n"
            + "def traceOptions (stage : Nat) := if stage = 2 then triOpts (traceTriangles stage) "
              "else stepOpts (traceTriangles stage) (traceTargets stage)\n"
            + "end SquarePacking.S11Opt.Split.U2R.C1849\n")


class TransformTests(unittest.TestCase):
    def test_roundtrip_preserves_full_literals_and_public_lookup_bytes(self):
        original = source()
        changed, info = split.transform_source(original, 80)
        self.assertEqual(split.reconstruct_source(changed, info, 80), original)
        self.assertEqual(set(info["tables"]), {"traceTriangleTable"})
        self.assertEqual(changed.count(TRI), 1)
        self.assertIn("private def traceTriangleTableRow002 : List Tri := []\n", changed)
        self.assertIn("  traceTriangleTableRow000,\n  traceTriangleTableRow001,\n  traceTriangleTableRow002\n", changed)
        for line in original.splitlines():
            if line.startswith(("def ", "set_option ", "import ")):
                self.assertIn(line + "\n", changed)
        self.assertNotIn("native_decide", changed)

    def test_threshold_is_strict_and_small_tables_stay_unchanged(self):
        original = source()
        size = sum(len(v.encode()) for v in split.literal_rows(original, "traceTriangleTable"))
        self.assertEqual(split.transform_source(original, size), (original, None))
        self.assertIsNotNone(split.transform_source(original, size - 1)[1])

    def test_target_table_uses_the_original_entry_type(self):
        original = source(["[]", "[]", "[]", "[]"], ["[(1, 2)]"] * 3)
        changed, info = split.transform_source(original, 15)
        self.assertEqual(set(info["tables"]), {"traceTargetTable"})
        self.assertIn("private def traceTargetTableRow000 : List (ℕ × ℕ) := [(1, 2)]", changed)
        self.assertEqual(split.reconstruct_source(changed, info, 15), original)

    def test_both_tables_are_independently_reconstructed(self):
        original = source(targets=["[(1, 2)]"] * 12)
        changed, info = split.transform_source(original, 80)
        self.assertEqual(set(info["tables"]), set(split.TABLES))
        self.assertEqual(split.reconstruct_source(changed, info, 80), original)

    def test_a_single_oversized_row_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "Individual row"):
            split.transform_source(source(), 10)

    def test_unexpected_literals_and_duplicate_tables_are_rejected(self):
        for original in [source(["[arbitraryTerm]", "[]"]),
                         source(["[(1, 2]", "[]"]),
                         source() + split._render_table("traceTriangleTable", ["[]"])]:
            with self.subTest(source=original[:40]):
                with self.assertRaises(ValueError):
                    split.transform_source(original, 80)

    def test_changed_numbers_references_and_helper_order_fail_after_rehash(self):
        changed, info = split.transform_source(source(), 80)
        lines = changed.splitlines(keepends=True)
        first = next(i for i, line in enumerate(lines) if line.startswith("private def traceTriangleTableRow000"))
        swapped = lines[:]
        swapped[first], swapped[first + 1] = swapped[first + 1], swapped[first]
        mutations = [changed.replace("(20, 30)", "(21, 30)"),
                     changed.replace("  traceTriangleTableRow000,", "  traceTriangleTableRow001,"),
                     "".join(swapped),
                     changed.replace("traceTriangleTableRow001 : List Tri", "traceTriangleTableRow001 : List Nat")]
        for altered in mutations:
            with self.subTest(altered=altered[:60]):
                ledger = copy.deepcopy(info)
                ledger["after_sha256"] = split.digest(altered)
                with self.assertRaises(ValueError):
                    split.reconstruct_source(altered, ledger, 80)

    def test_unrelated_source_change_and_repeated_transform_are_rejected(self):
        changed, info = split.transform_source(source(), 80)
        altered = changed.replace("stage = 2", "stage = 1")
        info["after_sha256"] = split.digest(altered)
        with self.assertRaisesRegex(ValueError, "Original indexed source"):
            split.reconstruct_source(altered, info, 80)
        with self.assertRaisesRegex(ValueError, "already contains"):
            split.transform_source(changed, 80)


class ReceiptTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.original = source()
        target = self.root / NAME
        target.parent.mkdir(parents=True)
        target.write_text(self.original)
        values = [[(str(i), v) for i, v in enumerate(split.literal_rows(self.original, name))]
                  for name in split.TABLES]
        predecessor = {"files": {NAME: {"after_sha256": split.digest(self.original)}},
                       "cases": {"Fixture": {"data_path": NAME, "triangle_entries": len(values[0]),
                                            "target_entries": len(values[1]),
                                            "literal_sha256": split.digest(json.dumps(
                                                values, ensure_ascii=False, separators=(",", ":")))}}}
        prior = self.root / split.PREDECESSOR
        prior.parent.mkdir(parents=True)
        prior.write_text(json.dumps(predecessor))

    def install(self):
        outputs, ledger = split.plan(self.root, 80)
        for name, text in outputs.items():
            (self.root / name).write_text(text)
        (self.root / split.REPORT).write_text(json.dumps(ledger))
        return ledger

    def test_missing_optional_receipt_returns_no_reconstructions(self):
        self.assertEqual(split.reconstruct_inputs(self.root), {})
        with self.assertRaisesRegex(ValueError, "No indexed data compilation receipt"):
            split.main(["--root", str(self.root), "--check"])

    def test_broken_receipt_symlink_is_never_replaced(self):
        receipt = self.root / split.REPORT
        symlink_or_skip(self, receipt, self.root / "missing-ledger")
        with self.assertRaisesRegex(ValueError, "Compilation receipt already exists"):
            split.main(["--root", str(self.root), "--max-literal-bytes", "80", "--write"])
        self.assertTrue(receipt.is_symlink())
        with self.assertRaisesRegex(ValueError, "linked source"):
            split.reconstruct_inputs(self.root)

    def test_plan_is_read_only_and_saved_inverse_anchors_original_receipt(self):
        outputs, _ = split.plan(self.root, 80)
        self.assertEqual(set(outputs), {NAME})
        self.assertEqual((self.root / NAME).read_text(), self.original)
        self.install()
        self.assertEqual(split.reconstruct_inputs(self.root), {NAME: self.original})

    def test_rehashing_a_changed_literal_cannot_bypass_historical_anchor(self):
        ledger = self.install()
        altered = self.original.replace("(20, 30)", "(21, 30)")
        output, info = split.transform_source(altered, 80)
        (self.root / NAME).write_text(output)
        ledger["files"][NAME] = info
        with self.assertRaisesRegex(ValueError, "indexed-stage receipt"):
            split.reconstruct_inputs(self.root, ledger)

    def test_predecessor_literal_digest_is_checked_even_with_matching_source_hash(self):
        prior = self.root / split.PREDECESSOR
        data = json.loads(prior.read_text())
        data["cases"]["Fixture"]["literal_sha256"] = "0" * 64
        prior.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "Literals differ"):
            split.plan(self.root, 80)

    def test_changed_predecessor_receipt_is_rejected(self):
        self.install()
        prior = self.root / split.PREDECESSOR
        prior.write_text(prior.read_text() + " ")
        with self.assertRaisesRegex(ValueError, "receipt changed"):
            split.reconstruct_inputs(self.root)

    def test_cli_write_and_check(self):
        with redirect_stdout(io.StringIO()):
            split.main(["--root", str(self.root), "--max-literal-bytes", "80", "--write"])
            split.main(["--root", str(self.root), "--check"])
        self.assertEqual(split.reconstruct_inputs(self.root), {NAME: self.original})


if __name__ == "__main__":
    unittest.main()
