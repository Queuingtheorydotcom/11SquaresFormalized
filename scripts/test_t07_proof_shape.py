"""Regressions for the single known generated row-block tactic failure."""
import unittest

from check_sources import code_only
from t07_proof_shape import check_row_block_proof


STAGE = 'ElevenSquare/Tasks/T07/Ext/Gen/P2/S11.lean'


def source(rows=104, separator=';'):
    return f'''theorem nrows : (prev.rows 3).length = {rows} := by decide +kernel

theorem step_ok : stepB prev 3 rs pcov certs = true := by
  apply stepB_of_row_blocks (width := 8) (blocks := 13) (by decide)
    (by rw [nrows]; rfl) (by rw [nrows]{separator} decide)
  intro b hb
  interval_cases b <;> native_decide

theorem promote_ok : True := by trivial
'''


class RowBlockProofTests(unittest.TestCase):
    def test_exact_full_block_failure(self):
        with self.assertRaisesRegex(ValueError, r'S11\.lean:5:.*No goals to be solved'):
            check_row_block_proof(STAGE, source())

    def test_strict_bound_keeps_the_decide_goal(self):
        check_row_block_proof(STAGE, source(rows=103))

    def test_insufficient_coverage_is_left_to_lean(self):
        check_row_block_proof(STAGE, source(rows=105))

    def test_goal_safe_separator_keeps_first_length_proof(self):
        check_row_block_proof(STAGE, source(separator=' <;>'))

    def test_whitespace_and_multiline_second_bound(self):
        code = source().replace('(by rw [nrows]; decide)',
                                '(by\n      rw [nrows]\n      ;\n      decide)')
        with self.assertRaisesRegex(ValueError, 'No goals to be solved'):
            check_row_block_proof(STAGE, code)

    def test_nonstage_paths_are_outside_scope(self):
        for path in ('Sqpack/S11Opt/F00/Final.lean',
                     'ElevenSquare/Tasks/T07/Ext/Gen/P2/Rules.lean',
                     'ElevenSquare/Tasks/T07/Ext/Gen/NearConn.lean',
                     'ElevenSquare/Tasks/T07/Ext/Gen/P2/nested/S11.lean'):
            with self.subTest(path=path):
                check_row_block_proof(path, source())

    def test_caller_masks_comments_and_strings(self):
        code = '/-\n' + source() + '\n-/\n'
        code += 'def note := "' + source().replace('\n', '\\n') + '"\n'
        check_row_block_proof(STAGE, code_only(code))

    def test_masked_comments_inside_real_proof_preserve_detection(self):
        code = source().replace('; decide)', '; /- explanatory note -/ decide)')
        with self.assertRaisesRegex(ValueError, 'No goals to be solved'):
            check_row_block_proof(STAGE, code_only(code))

    def test_mismatched_owner_is_outside_confirmed_shape(self):
        check_row_block_proof(STAGE, source().replace('stepB prev 3', 'stepB prev 4'))

    def test_other_proof_body_is_not_inferred_to_be_invalid(self):
        for code in (source().replace('interval_cases b <;> native_decide', 'exact other_proof b hb'),
                     source().replace('  intro b hb', '  have h := another_fact\n  intro b hb'),
                     source().replace('theorem step_ok', 'theorem another_proof'),
                     source().replace('theorem step_ok', 'end One\nnamespace Two\ntheorem step_ok')):
            with self.subTest(code=code):
                check_row_block_proof(STAGE, code)

    def test_extra_tactic_after_template_is_not_a_complete_match(self):
        code = source().replace('theorem promote_ok', '  exact another_fact\n\ntheorem promote_ok')
        check_row_block_proof(STAGE, code)

    def test_second_declaration_pair_is_also_checked(self):
        code = ('namespace First\n' + source(rows=103) + 'end First\n'
                'namespace Second\n' + source() + 'end Second\n')
        with self.assertRaisesRegex(ValueError, 'No goals to be solved'):
            check_row_block_proof(STAGE, code)

    def test_kernel_spelling_and_end_of_file_are_recognized(self):
        code = source().split('\ntheorem promote_ok')[0]
        code = code.replace('native_decide', 'decide +kernel')
        with self.assertRaisesRegex(ValueError, 'No goals to be solved'):
            check_row_block_proof(STAGE, code)


if __name__ == '__main__':
    unittest.main()
