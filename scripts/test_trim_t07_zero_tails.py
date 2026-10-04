"""Check field selection, inverse reconstruction and exact comb preservation."""
import copy
from fractions import Fraction as Q
import itertools
from pathlib import Path
import tempfile
import unittest

from trim_t07_zero_tails import apply_receipt, audit_receipt, restore_source, transform_source


def certificate(tree, name="cert0"):
    # Unused numeric/list fields deliberately contain zero tails: the structural
    # selector must preserve them even though the simple parser can skip them.
    return (f"def {name} : List Sub := [⟨(0), (1), [(3), (0)], (0), "
            f"[((0), (0))], [], [⟨0, [], [[(0), (0)]]⟩], {tree}⟩]\n")


def comb(poly, weights):
    result = [Q(0)] * 3
    for plane, weight in zip(poly, weights):
        result = [a + weight * b for a, b in zip(result, plane)]
    return result


class TrimTest(unittest.TestCase):
    def check_transform(self, before, after):
        result, receipt = transform_source(before)
        self.assertEqual(result, after)
        self.assertEqual(restore_source(result, receipt), before)
        second, metadata = transform_source(result)
        self.assertEqual(second, result)
        self.assertEqual(metadata["edits"], [])
        return receipt

    def test_empty_leaf(self):
        self.check_transform(certificate("(.empty [(3/7), (0), (0)])"),
                             certificate("(.empty [(3/7)])"))

    def test_all_zero_and_empty(self):
        self.check_transform(certificate("(.keep 0 [[(0), (0)], []])"),
                             certificate("(.keep 0 [[], []])"))

    def test_internal_zero_kept(self):
        self.check_transform(certificate("(.collide 0 [[(0), (3/7), (0)]])"),
                             certificate("(.collide 0 [[(0), (3/7)]])"))

    def test_hull_indices_untouched(self):
        self.check_transform(certificate("(.forbidHull 0 [(0, 0), (1, 0)] [[(1), (0)]])"),
                             certificate("(.forbidHull 0 [(0, 0), (1, 0)] [[(1)]])"))

    def test_triangle_nonweights_untouched(self):
        before = "(.forbid 0 ⟨[(0), (0)], [(0), (0)], [(0), (0)], [[(1), (0)]]⟩)"
        after = "(.forbid 0 ⟨[(0), (0)], [(0), (0)], [(0), (0)], [[(1)]]⟩)"
        self.check_transform(certificate(before), certificate(after))

    def test_split_and_chain(self):
        before = ("(CTreeChain.build [(.right ⟨0, 0, 0⟩ (.empty [(1), (0)])), "
                  "(.left ⟨0, 0, 0⟩ (.empty [(0)]))] "
                  "(.split ⟨0, 0, 0⟩ (.keep 0 [[(1), (0)]]) (.empty [(0)])))")
        after = ("(CTreeChain.build [(.right ⟨0, 0, 0⟩ (.empty [(1)])), "
                 "(.left ⟨0, 0, 0⟩ (.empty []))] "
                 "(.split ⟨0, 0, 0⟩ (.keep 0 [[(1)]]) (.empty [])))")
        self.check_transform(certificate(before), certificate(after))

    def test_other_declarations_untouched(self):
        suffix = "def weights : List ℚ := [(1), (0)]\ntheorem ok : True := by trivial\n"
        self.check_transform(certificate("(.empty [(1), (0)])") + suffix,
                             certificate("(.empty [(1)])") + suffix)

    def test_multiple_certs_unicode_offsets(self):
        before = "-- λ ℚ\n" + certificate("(.empty [(1), (0)])") + certificate("(.empty [(0)])", "cert1")
        after = "-- λ ℚ\n" + certificate("(.empty [(1)])") + certificate("(.empty [])", "cert1")
        self.check_transform(before, after)

    def test_noncanonical_zero_literal_retained(self):
        self.check_transform(certificate("(.empty [(0/3), (0)])"),
                             certificate("(.empty [(0/3)])"))

    def test_unsupported_constructor_rejected(self):
        with self.assertRaises(ValueError):
            transform_source(certificate("(.mystery [(1), (0)])"))

    def test_nonliteral_vector_rejected(self):
        with self.assertRaises(ValueError):
            transform_source(certificate("(.empty weights)"))

    def test_parameterized_certificate_rejected(self):
        with self.assertRaises(ValueError):
            transform_source(certificate("(.empty [(0)])").replace("cert0 :", "cert0 (x : Nat) :"))

    def test_corrupt_receipt_rejected(self):
        after, receipt = transform_source(certificate("(.empty [(1), (0)])"))
        bad = copy.deepcopy(receipt)
        bad["edits"][0][1] = 2
        with self.assertRaises(ValueError):
            restore_source(after, bad)
        with self.assertRaises(ValueError):
            restore_source(after + "\n", receipt)

    def test_mixed_state_recovery_and_idempotence(self):
        original = certificate("(.empty [(1), (0)])")
        candidate, metadata = transform_source(original)
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            records = []
            for name, text in (("a.lean", original), ("b.lean", candidate)):
                (root / name).write_text(text)
                records.append({**metadata, "file": name})
            receipt = {"files": records}
            self.assertEqual(apply_receipt(receipt, root), {"applied": 1, "already_applied": 1})
            self.assertEqual(audit_receipt(receipt, root), {"after": 2})
            self.assertEqual(apply_receipt(receipt, root), {"already_applied": 2})
            self.assertEqual(list(root.glob(".zero-tail-*")), [])

    def test_full_preflight_prevents_partial_mutation(self):
        original = certificate("(.empty [(1), (0)])")
        _, metadata = transform_source(original)
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "a.lean").write_text(original)
            (root / "b.lean").write_text(original + "-- edited\n")
            receipt = {"files": [{**metadata, "file": name} for name in ("a.lean", "b.lean")]}
            with self.assertRaises(ValueError):
                apply_receipt(receipt, root)
            self.assertEqual((root / "a.lean").read_text(), original)

    def test_path_escape_rejected(self):
        original = certificate("(.empty [(1), (0)])")
        _, metadata = transform_source(original)
        with tempfile.TemporaryDirectory() as td:
            with self.assertRaises(ValueError):
                apply_receipt({"files": [{**metadata, "file": "../a.lean"}]}, Path(td))

    def test_check_requires_candidate(self):
        original = certificate("(.empty [(1), (0)])")
        _, metadata = transform_source(original)
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "a.lean").write_text(original)
            with self.assertRaises(ValueError):
                audit_receipt({"files": [{**metadata, "file": "a.lean"}]}, root)

    def test_unused_core_cleared_only_on_request(self):
        original = "def cert0 : List Sub := [⟨(0), (1), [], (0), [], [(1, 2)], [], (.empty [(1), (0)])⟩]\n"
        tail_only, _ = transform_source(original)
        self.assertIn("[(1, 2)]", tail_only)
        result, receipt = transform_source(original, clear_unused_cores=True)
        self.assertEqual(result, original.replace("[(1, 2)]", "[]").replace("[(1), (0)]", "[(1)]"))
        self.assertEqual(restore_source(result, receipt), original)
        again, metadata = transform_source(result, clear_unused_cores=True)
        self.assertEqual(again, result)
        self.assertEqual(metadata["core_edits"], [])

    def test_used_core_preserved(self):
        original = "def cert0 : List Sub := [⟨(0), (1), [], (0), [], [(1, 2)], [⟨0, [], []⟩], (.empty [])⟩]\n"
        result, metadata = transform_source(original, clear_unused_cores=True)
        self.assertEqual(result, original)
        self.assertEqual(metadata["core_edits"], [])

    def test_mixed_core_and_tail_receipt_application(self):
        original = "def cert0 : List Sub := [⟨(0), (1), [], (0), [], [(1, 2)], [], (.empty [(0)])⟩]\n"
        candidate, metadata = transform_source(original, clear_unused_cores=True)
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "a.lean").write_text(original)
            receipt = {"files": [{**metadata, "file": "a.lean"}]}
            self.assertEqual(apply_receipt(receipt, root), {"applied": 1})
            self.assertEqual((root / "a.lean").read_text(), candidate)
            self.assertEqual(audit_receipt(receipt, root), {"after": 1})

    def test_exact_rational_sums_short_equal_and_overlong_weights(self):
        planes = [(Q(2, 3), Q(-7, 5), Q(11, 13)),
                  (Q(-19, 23), Q(29, 31), Q(-37, 41)),
                  (Q(43, 47), Q(53, 59), Q(61, 67))]
        for size in range(5):
            for ws in itertools.product((Q(0), Q(1), Q(-2, 3)), repeat=size):
                for suffix in range(4):
                    original = list(ws) + [Q(0)] * suffix
                    trimmed = list(original)
                    while trimmed and trimmed[-1] == 0:
                        trimmed.pop()
                    for plen in range(4):
                        self.assertEqual(comb(planes[:plen], original), comb(planes[:plen], trimmed))
                        self.assertEqual(all(w >= 0 for w in original), all(w >= 0 for w in trimmed))


if __name__ == "__main__":
    unittest.main()
