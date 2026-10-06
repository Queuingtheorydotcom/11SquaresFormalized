"""Small verifier regressions; uses no Lean process or real build cache."""
import unittest

from verify_support import (PUBLIC_TARGETS, STANDARD_AXIOMS, admitted_targets,
                            public_audit_status, audit_axioms, input_digest,
                            priority_order, reusable_inputs, positive_jobs,
                            lean_arguments, recorded_arguments, reusable_fingerprint,
                            native_trust_status)


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
        returned_component = {'ElevenSquare.Pending.returned_excluded'}
        capture_component = {'ElevenSquare.Tasks.T07.case438_near_certificate'}
        components = returned_component | capture_component
        cases = [
            (baseline_paths + [prior_path, returned_path, capture_path], PUBLIC_TARGETS | components),
            (baseline_paths + [returned_path, capture_path], {baseline, returned} | global_targets | components),
            ([returned_path, capture_path], {returned} | global_targets | components),
            ([prior_path], {prior} | global_targets),
            ([returned_path], {returned} | global_targets | returned_component),
            ([capture_path], global_targets | capture_component),
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

    def test_focused_components_allow_only_their_inventoried_admission(self):
        components = {
            'ElevenSquare/Pending/S06_Returned.lean':
                'ElevenSquare.Pending.returned_excluded',
            'ElevenSquare/Tasks/T07/UnfinishedCapture.lean':
                'ElevenSquare.Tasks.T07.case438_near_certificate',
        }
        for path, target in components.items():
            source = '#print axioms ' + target
            output = "'" + target + "' depends on axioms: [propext, sorryAx]\n"
            with self.subTest(target=target):
                permission = admitted_targets([{'path': path, 'line': 1}])
                self.assertEqual(audit_axioms(source, output, STANDARD_AXIOMS, permission),
                                 {target: ['propext', 'sorryAx']})
                for other in ([], [{'path': p, 'line': 1} for p in components if p != path]):
                    with self.assertRaisesRegex(ValueError, 'Unapproved axioms'):
                        audit_axioms(source, output, STANDARD_AXIOMS, admitted_targets(other))
                with self.assertRaisesRegex(ValueError, 'Unapproved axioms'):
                    audit_axioms(source, output.replace('sorryAx', 'uncheckedOracle'),
                                 STANDARD_AXIOMS, permission)

    def test_public_queries_stay_required_with_zero_admissions(self):
        clean = {name: ['propext'] for name in PUBLIC_TARGETS}
        self.assertEqual(public_audit_status(clean, 0),
                         {'status': 'OPTIMALITY_PROVED', 'global_optimality_proved': True,
                          'trust_model': 'lean_kernel', 'native_certificate_axioms': []})
        self.assertEqual(public_audit_status(clean, 2),
                         {'status': 'PARTIAL_ASSEMBLY_COMPILES', 'global_optimality_proved': False,
                          'trust_model': 'lean_kernel', 'native_certificate_axioms': []})
        for target in PUBLIC_TARGETS:
            with self.subTest(target=target):
                with self.assertRaisesRegex(ValueError, 'Missing final public target'):
                    public_audit_status({name: axioms for name, axioms in clean.items()
                                         if name != target}, 0)

    def test_inherited_admission_prevents_complete_status(self):
        axioms = {name: [] for name in PUBLIC_TARGETS}
        axioms['ElevenSquare.optimality'] = ['sorryAx']
        self.assertFalse(public_audit_status(axioms, 0)['global_optimality_proved'])

    def test_native_axioms_require_exact_approved_owner_and_suffix(self):
        declaration = 'Certificate.coverage'
        source = '#print axioms ElevenSquare.optimality'
        native = declaration + '._native.native_decide.ax_1_1'
        output = "'ElevenSquare.optimality' depends on axioms: [propext, " + native + ']'
        expected = {'ElevenSquare.optimality': sorted(['propext', native])}
        self.assertEqual(audit_axioms(source, output, STANDARD_AXIOMS, set(), {declaration}), expected)
        with self.assertRaisesRegex(ValueError, 'Unapproved'):
            audit_axioms(source, output, STANDARD_AXIOMS, set())
        for other in ('Certificate.coverageExtra._native.native_decide.ax_1_1',
                      'Certificate.coverage._native.bv_decide.ax_1_1',
                      'Certificate.coverage._native.native_decide.ax_1_1.extra',
                      'Certificate.coverage._native.native_decide.ax_one',
                      'Lean.ofReduceBool', 'Lean.trustCompiler', 'sorryAx'):
            with self.subTest(axiom=other), self.assertRaisesRegex(ValueError, 'Unapproved'):
                audit_axioms(source, output.replace(native, other), STANDARD_AXIOMS, set(), {declaration})

    def test_native_public_result_discloses_compiler_trust(self):
        native = 'Certificate.coverage._native.native_decide.ax_1_1'
        axioms = {name: [native, 'propext'] for name in PUBLIC_TARGETS}
        result = public_audit_status(axioms, 0)
        self.assertEqual(result['status'], 'OPTIMALITY_PROVED_WITH_NATIVE_CERTIFICATES')
        self.assertEqual(result['trust_model'], 'lean_kernel_and_native_compiler')
        self.assertEqual(result['native_certificate_axioms'], [native])
        self.assertTrue(result['global_optimality_proved'])
        axioms['ElevenSquare.optimality'].append('sorryAx')
        result = public_audit_status(axioms, 0)
        self.assertEqual(result['status'], 'PARTIAL_ASSEMBLY_COMPILES')
        self.assertFalse(result['global_optimality_proved'])

    def test_selected_native_source_without_queries_is_not_labelled_kernel_only(self):
        result = native_trust_status({}, has_native_sources=True)
        self.assertEqual(result['trust_model'], 'lean_kernel_and_native_compiler')
        self.assertEqual(result['native_certificate_axioms'], [])

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

    def test_jobs_are_canonical_positive_uint32_values(self):
        for value in ('1', '4', '8', '4294967295'):
            self.assertEqual(positive_jobs(value), int(value))
        for value in ('0', '-1', '+4', '04', '4.0', ' 4', '4 ', '٤', '4294967296', '', None, 4):
            with self.subTest(value=value), self.assertRaises(ValueError):
                positive_jobs(value)
        for value in (0, -1, True, 4.0, '4', 2**32):
            with self.subTest(value=value), self.assertRaises(ValueError):
                lean_arguments('ElevenSquare', value)

    def test_recorded_arguments_require_exact_proof_flags(self):
        for module in ('ElevenSquare', 'ElevenSquare.X', 'Sqpack', 'Sqpack.X'):
            for jobs in (1, 4, 8):
                expected = [f'-j{jobs}', '-M0', '-s65536',
                            '-DautoImplicit=' + ('true' if module.startswith('Sqpack') else 'false'),
                            '-DmaxHeartbeats=0']
                self.assertEqual(lean_arguments(module, jobs), expected)
                self.assertEqual(recorded_arguments(module, expected), expected)
        good = lean_arguments('ElevenSquare', 4)
        bad = [None, [], tuple(good), good[:-1], good + ['-t999'],
               good + ['-DElab.async=false'], good + ['-j8'],
               ['-M0', '-j4', *good[2:]]]
        bad.extend([flag, *good[1:]] for flag in ('-j0', '-j-1', '-j04', '-j+4', '-j4294967296'))
        for i, flag in ((1, '-M1'), (2, '-s1024'), (3, '-DautoImplicit=true'),
                        (4, '-DmaxHeartbeats=1')):
            bad.append(good[:i] + [flag] + good[i+1:])
        for arguments in bad:
            with self.subTest(arguments=arguments), self.assertRaisesRegex(ValueError, 'Noncanonical'):
                recorded_arguments('ElevenSquare', arguments)

    def test_new_job_request_reuses_actual_old_arguments_and_digest(self):
        old = {'source': 'source', 'local_dependency_objects': {'A': 'object'},
               'compiler': 'pinned', 'arguments': lean_arguments('ElevenSquare', 1),
               'build_context': {'manifest': 'pin'}, 'local_dependency_inputs': {'A': 'inputs'}}
        current = dict(old, arguments=lean_arguments('ElevenSquare', 8))
        cached = reusable_fingerprint('ElevenSquare', old, current, legacy_baseline=False,
                                      checked_at=20, newest_input=30)
        self.assertEqual(cached, old)
        self.assertEqual(input_digest(cached), input_digest(old))
        self.assertEqual(old['arguments'][0], '-j1')
        self.assertEqual(current['arguments'][0], '-j8')
        for key, changed in {
            'source': 'changed', 'local_dependency_objects': {'A': 'changed'},
            'compiler': 'different', 'build_context': {'manifest': 'different'},
            'local_dependency_inputs': {'A': 'different'},
        }.items():
            with self.subTest(changed=key):
                self.assertIsNone(reusable_fingerprint(
                    'ElevenSquare', old, dict(current, **{key: changed}),
                    legacy_baseline=True, checked_at=20, newest_input=10))
        for arguments in (None, old['arguments'] + ['-t999'], lean_arguments('Sqpack', 1)):
            with self.subTest(arguments=arguments):
                self.assertIsNone(reusable_fingerprint(
                    'ElevenSquare', dict(old, arguments=arguments), current,
                    legacy_baseline=True, checked_at=20, newest_input=10))

    def test_legacy_migration_retains_recorded_jobs_and_timestamp_guard(self):
        old = {'source': 'same', 'local_dependency_objects': {}, 'compiler': 'pinned',
               'arguments': lean_arguments('Sqpack', 1)}
        current = dict(old, arguments=lean_arguments('Sqpack', 4),
                       build_context={'manifest': 'pin'}, local_dependency_inputs={})
        for provenance, newest, accepted in ((True, 10, True), (True, 21, False), (False, 10, False)):
            with self.subTest(provenance=provenance, newest=newest):
                cached = reusable_fingerprint('Sqpack', old, current, legacy_baseline=provenance,
                                              checked_at=20, newest_input=newest)
                if accepted:
                    self.assertEqual(cached, dict(current, arguments=old['arguments']))
                else:
                    self.assertIsNone(cached)

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
