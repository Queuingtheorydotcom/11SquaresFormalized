#!/usr/bin/env python3
"""Regression checks for literal-preserving indexed stage source rewrites."""
import unittest
from simplify_indexed_stages import transform_data, transform_consumer, extract_table

NS = 'SquarePacking.S11Opt.Split.U2P.C221'
CASE = {NS: {'stages': 3}}
DATA = f'''import Sqpack.S11Opt.Split.U2P.Rules
namespace {NS}
open FieldTree SquarePacking.S11Opt.Split.U2P
/-- Step 0: owner 1. -/
def tris0 : List Tri := []
def tgt0 : List (ℕ × ℕ) := [(1, 2), (30, 400)]
def opts0 : List (List (List (ℕ × ℕ))) := stepOpts tris0 tgt0

/-- Step 1: owner 3. -/
def tris1 : List Tri := [(1, (2, 3), (4, 5), (6, 7), [(8, 9)], [[10, 11, 12]])]
def tgt1 : List (ℕ × ℕ) := [(999999999999999999, 0)]
def opts1 : List (List (List (ℕ × ℕ))) := stepOpts tris1 tgt1

/-- Step 2: owner 5. -/
def tris2 : List Tri := []
def opts2 : List (List (List (ℕ × ℕ))) := triOpts tris2

end {NS}
'''

class IndexedStageTests(unittest.TestCase):
    def test_complete_literal_entries_are_preserved(self):
        output, count, _ = transform_data(DATA)
        self.assertEqual(count, 3)
        self.assertEqual(extract_table(output, 'traceTriangleTable', 'List Tri'), [
            ('0', '[]'),
            ('1', '[(1, (2, 3), (4, 5), (6, 7), [(8, 9)], [[10, 11, 12]])]'),
            ('2', '[]')])
        self.assertEqual(extract_table(output, 'traceTargetTable', 'List (ℕ × ℕ)'), [
            ('0', '[(1, 2), (30, 400)]'), ('1', '[(999999999999999999, 0)]')])
        self.assertIn('if stage = 2 then triOpts (traceTriangles stage)', output)
        self.assertIn('else stepOpts (traceTriangles stage) (traceTargets stage)', output)
        self.assertNotIn('  | ', output)
    def test_consumer_types_and_terms_are_indexed(self):
        before = f'namespace {NS}\ntheorem cov : Foo opts2 := bar tris1 tgt0\nend {NS}\n'
        output, references = transform_consumer(before, CASE)
        self.assertEqual(references, 3)
        self.assertEqual(output, f'namespace {NS}\ntheorem cov : Foo (traceOptions 2) := bar (traceTriangles 1) (traceTargets 0)\nend {NS}\n')
    def test_nonterminal_and_terminal_options_cannot_swap(self):
        with self.assertRaises(AssertionError): transform_data(DATA.replace('triOpts tris2', 'stepOpts tris2 tgt2'))
    def test_missing_stage_is_rejected(self):
        with self.assertRaises(AssertionError): transform_data(DATA.replace('def tris1 ', 'def tris4 '))
    def test_unexpected_declaration_is_rejected(self):
        with self.assertRaises(AssertionError): transform_data(DATA.replace('/-- Step 1:', 'def extra : Nat := 5\n/-- Step 1:'))
    def test_terminal_target_is_out_of_range(self):
        with self.assertRaises(AssertionError): transform_consumer(f'namespace {NS}\ndef x := tgt2\nend {NS}', CASE)
    def test_qualified_reference_requires_explicit_review(self):
        with self.assertRaises(AssertionError): transform_consumer(f'namespace {NS}\ndef x := {NS}.tris0\nend {NS}', CASE)
    def test_unfolding_tactic_reference_requires_explicit_review(self):
        with self.assertRaises(AssertionError): transform_consumer(f'namespace {NS}\ntheorem x : True := by simp [opts0]\nend {NS}', CASE)
    def test_different_case_namespace_is_untouched(self):
        source = 'namespace SquarePacking.S11Opt.Simplified.ReducedConditional.U2P.C221\ndef x := tris0\n'
        self.assertEqual(transform_consumer(source, CASE), (source, 0))
    def test_multiple_case_namespaces_are_rejected(self):
        with self.assertRaises(AssertionError): transform_consumer(f'namespace {NS}\ndef x := tris0\nend {NS}\nnamespace {NS}\n', CASE)

class StageRootAliasTests(unittest.TestCase):
    def source(self, alias_type='True', extra=''):
        return (f'namespace {NS}\n'
                'theorem cov1_1 : True :=\n  True.intro\n\n'
                f'theorem cov1 : {alias_type} := cov1_1\n\n'
                f'{extra}end {NS}\n')
    def test_public_statement_and_proof_body_are_preserved(self):
        from simplify_stage_aliases import transform
        source = self.source()
        output, receipt = transform(source)
        self.assertIn('theorem cov1 : True :=\n  True.intro\n', output)
        self.assertNotIn('cov1_1', output)
        self.assertEqual(receipt['before_lines'] - receipt['after_lines'], 2)
        self.assertTrue(receipt['exact_inverse_reconstruction'])
    def test_different_alias_statement_is_rejected(self):
        from simplify_stage_aliases import transform
        with self.assertRaises(AssertionError): transform(self.source(alias_type='False'))
    def test_another_local_old_name_use_is_rejected(self):
        from simplify_stage_aliases import transform
        with self.assertRaises(AssertionError): transform(self.source(extra='#check cov1_1\n'))
    def test_already_canonical_source_is_unchanged(self):
        from simplify_stage_aliases import transform
        output, _ = transform(self.source())
        self.assertIsNone(transform(output))

class StageRootAliasReceiptTests(unittest.TestCase):
    def fixture(self, root):
        import json
        from simplify_stage_aliases import transform
        source = StageRootAliasTests().source()
        output, receipt = transform(source)
        name = 'S1.lean'
        (root / name).write_text(output)
        report = {'exact_public_statements_preserved': 1, 'files': {name: receipt}}
        report_path = root / 'receipt.json'
        report_path.write_text(json.dumps(report))
        return report_path, report, output
    def test_stale_source_hash_is_rejected(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from simplify_stage_aliases import check_saved_report
        with TemporaryDirectory() as directory:
            root = Path(directory)
            report_path, _, output = self.fixture(root)
            self.assertEqual(check_saved_report(report_path, root)['files'], 1)
            (root / 'S1.lean').write_text(output + '-- changed after audit\n')
            with self.assertRaisesRegex(AssertionError, 'Stale source hash'):
                check_saved_report(report_path, root)
    def test_type_and_old_name_checks_survive_updated_file_hash(self):
        import json
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from simplify_stage_aliases import check_saved_report, sha
        with TemporaryDirectory() as directory:
            root = Path(directory)
            report_path, report, output = self.fixture(root)
            mutations = [(output.replace('cov1 : True', 'cov1 : False'), 'Changed public statement'),
                         (output + '#check cov1_1\n', 'Removed theorem name reintroduced')]
            for changed, error in mutations:
                with self.subTest(error=error):
                    (root / 'S1.lean').write_text(changed)
                    report['files']['S1.lean']['after_sha256'] = sha(changed)
                    report_path.write_text(json.dumps(report))
                    with self.assertRaisesRegex(AssertionError, error):
                        check_saved_report(report_path, root)

if __name__ == '__main__': unittest.main()
