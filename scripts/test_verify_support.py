"""Small verifier regressions; uses no Lean process or real build cache."""
import unittest

from verify_support import (PUBLIC_TARGETS, STANDARD_AXIOMS, admitted_targets,
                            public_audit_status, audit_axioms, input_digest,
                            priority_order, reusable_inputs)


class VerificationSupportTests(unittest.TestCase):
    def test_admission_permissions_follow_the_remaining_sites(self):
        baseline = 'ElevenSquare.Pending.baseline_certificate_exists'
        prior = 'ElevenSquare.Pending.prior_certificate_exists'
        returned = 'ElevenSquare.Pending.returned_certificate_exists'
        global_targets = {'ElevenSquare.Pending.global_lower_bound',
                          'ElevenSquare.optimality', 'ElevenSquare.optimal_side_lower_bound'}
        baseline_paths = ['ElevenSquare/Tasks/T01/Handoff/' + name + '.lean'
                          for name in ('LeafCalculations', 'PlanData', 'ProgramCalculations')]
        prior_path = 'ElevenSquare/Pending/S06_PriorSupport.lean'
        returned_path = 'ElevenSquare/Pending/S06_Returned.lean'
        capture_path = 'ElevenSquare/Tasks/T07/UnfinishedCapture.lean'
        cases = [
            (baseline_paths + [prior_path, returned_path, capture_path], PUBLIC_TARGETS),
            (baseline_paths + [returned_path, capture_path], {baseline, returned} | global_targets),
            ([returned_path, capture_path], {returned} | global_targets),
            ([prior_path], {prior} | global_targets),
            ([capture_path], global_targets),
            ([], set()),
        ]
        cases.extend(([path], {baseline} | global_targets) for path in baseline_paths)
        for paths, expected in cases:
            with self.subTest(paths=paths):
                self.assertEqual(admitted_targets([{'path': path, 'line': 1} for path in paths]), expected)

    def test_unknown_admission_does_not_expand_permissions(self):
        with self.assertRaisesRegex(ValueError, 'Unknown admission paths'):
            admitted_targets([{'path': 'ElevenSquare/Unexpected.lean', 'line': 1}])

    def test_closed_prior_and_baseline_cannot_inherit_sorry_ax(self):
        remaining = [{'path': 'ElevenSquare/Pending/S06_Returned.lean', 'line': 1},
                     {'path': 'ElevenSquare/Tasks/T07/UnfinishedCapture.lean', 'line': 1}]
        for name in ('baseline_certificate_exists', 'prior_certificate_exists'):
            target = 'ElevenSquare.Pending.' + name
            with self.subTest(target=target):
                with self.assertRaisesRegex(ValueError, 'Unapproved axioms'):
                    audit_axioms('#print axioms ' + target,
                                 "'" + target + "' depends on axioms: [sorryAx]\n",
                                 STANDARD_AXIOMS, admitted_targets(remaining))

    def test_public_queries_stay_required_with_zero_admissions(self):
        clean = {name: ['propext'] for name in PUBLIC_TARGETS}
        self.assertEqual(public_audit_status(clean, 0),
                         {'status': 'OPTIMALITY_PROVED', 'global_optimality_proved': True})
        self.assertEqual(public_audit_status(clean, 2),
                         {'status': 'PARTIAL_ASSEMBLY_COMPILES', 'global_optimality_proved': False})
        for target in PUBLIC_TARGETS:
            with self.subTest(target=target):
                with self.assertRaisesRegex(ValueError, 'Missing final public target'):
                    public_audit_status({name: axioms for name, axioms in clean.items()
                                         if name != target}, 0)

    def test_inherited_admission_prevents_complete_status(self):
        axioms = {name: [] for name in PUBLIC_TARGETS}
        axioms['ElevenSquare.optimality'] = ['sorryAx']
        self.assertFalse(public_audit_status(axioms, 0)['global_optimality_proved'])

    def test_shared_interfaces_first_and_audit_last(self):
        deps = {'Data': [], 'Shared': [], 'A': ['Shared'], 'B': ['Shared'],
                'Leaf': ['Data'], 'ElevenSquare.Verification': ['A', 'Leaf']}
        order = priority_order(deps, {m: 1 for m in deps})
        self.assertEqual(order[0], 'Shared')
        self.assertEqual(order[-1], 'ElevenSquare.Verification')
        for m, ds in deps.items():
            for dep in ds:
                self.assertLess(order.index(dep), order.index(m))

    def test_cycle_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'cycle'):
            priority_order({'A': ['B'], 'B': ['A']}, {'A': 1, 'B': 1})

    def test_legacy_receipt_reused_only_with_original_inputs_and_times(self):
        old = {'source': 'same', 'local_dependency_objects': {'A': 'object'}}
        current = dict(old, build_context={'manifest': 'pinned'},
                       local_dependency_inputs={'A': 'inputs'})
        self.assertTrue(reusable_inputs(old, current, legacy_baseline=True,
                                        checked_at=20, newest_input=10))
        self.assertFalse(reusable_inputs(old, current, legacy_baseline=True,
                                         checked_at=20, newest_input=21))
        self.assertFalse(reusable_inputs(old, current, legacy_baseline=False,
                                         checked_at=20, newest_input=10))

    def test_transitive_change_invalidates_even_with_same_dependency_object(self):
        before_a = {'source': 'before'}
        after_a = {'source': 'after'}
        before_b = {'source': 'same B', 'dependency': input_digest(before_a)}
        after_b = {'source': 'same B', 'dependency': input_digest(after_a)}
        before_c = {'source': 'same C', 'local_dependency_objects': {'B': 'same object'},
                    'local_dependency_inputs': {'B': input_digest(before_b)}, 'build_context': {}}
        after_c = dict(before_c, local_dependency_inputs={'B': input_digest(after_b)})
        self.assertFalse(reusable_inputs(before_c, after_c, legacy_baseline=True,
                                         checked_at=20, newest_input=10))
        self.assertTrue(reusable_inputs(after_c, after_c, legacy_baseline=False,
                                        checked_at=20, newest_input=30))

    def test_short_and_private_names_resolve_by_output_order(self):
        source = '#print axioms local_result\n#print axioms local_result\n'
        output = ("'A.local_result' depends on axioms: [propext]\n"
                  "'_private.X.0.B.local_result' does not depend on any axioms\n")
        self.assertEqual(audit_axioms(source, output, {'propext'}, set()),
                         {'A.local_result': ['propext'], '_private.X.0.B.local_result': []})

    def test_missing_output_and_unapproved_axiom_fail(self):
        with self.assertRaisesRegex(ValueError, 'Expected'):
            audit_axioms('#print axioms A.x', '', set(), set())
        with self.assertRaisesRegex(ValueError, 'Unapproved'):
            audit_axioms('#print axioms x', "'A.x' depends on axioms: [sorryAx]",
                         set(), {'Other.x'})
        self.assertEqual(audit_axioms('#print axioms x',
                         "'A.x' depends on axioms: [sorryAx]", set(), {'A.x'}),
                         {'A.x': ['sorryAx']})


if __name__ == '__main__':
    unittest.main()
