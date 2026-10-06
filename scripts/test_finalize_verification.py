"""Finalization rejects incomplete/stale evidence, using tiny synthetic receipts."""
from pathlib import Path
import hashlib
import json
import tempfile
import unittest

from finalize_verification import collect_audit, json_bytes, sha
from verify_support import PUBLIC_TARGETS, admitted_targets, input_digest, public_audit_status


BASELINE_PATHS = ['ElevenSquare/Tasks/T01/Handoff/' + name + '.lean'
                  for name in ('LeafCalculations', 'PlanData', 'ProgramCalculations')]
PRIOR_PATH = 'ElevenSquare/Pending/S06_PriorSupport.lean'
RETURNED_PATH = 'ElevenSquare/Pending/S06_Returned.lean'
CAPTURE_PATH = 'ElevenSquare/Tasks/T07/UnfinishedCapture.lean'


class FinalizationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for name, text in {
            'lean-toolchain': 'leanprover/lean4:v4.34.1\n',
            'lakefile.lean': '-- synthetic fixture\n',
            'lake-manifest.json': json.dumps({'packages': [{'name': 'mathlib', 'rev': 'pin'}]}),
        }.items():
            (self.root / name).write_text(text)
        self.make_fixture(BASELINE_PATHS + [PRIOR_PATH, RETURNED_PATH, CAPTURE_PATH])

    def make_fixture(self, admission_paths, *, missing_queries=(), axiom_overrides=None, jobs=None,
                     native=False):
        sites = [{'path': path, 'line': 1} for path in admission_paths]
        inventory = self.root / 'verification/admissions.json'
        inventory.parent.mkdir(exist_ok=True)
        inventory.write_bytes(json_bytes({'sites': sites}))
        unfinished = admitted_targets(sites)
        targets = PUBLIC_TARGETS - set(missing_queries)
        self.sources = {
            'ElevenSquare': '-- fixture over ℝ\n',
            'Sqpack': '-- fixture\n',
            'ElevenSquare.Verification': 'import ElevenSquare\nimport Sqpack\n' +
                ''.join('#print axioms ' + n + '\n' for n in sorted(targets)),
        }
        if native:
            self.sources['ElevenSquare.Verification'] += ('namespace Certificate\n'
                'theorem coverage : (1 : Nat) + 1 = 2 := by native_decide\n'
                'end Certificate\n')
        self.axioms = {n: ['sorryAx'] if n in unfinished else ['propext'] for n in sorted(targets)}
        self.axioms.update(axiom_overrides or {})
        if native:
            self.axioms = {n: ['Certificate.coverage._native.native_decide.ax_1_1']
                           for n in sorted(targets)}
            native_manifest = {'format_version': 1, 'files': {'ElevenSquare/Verification.lean': {
                'sha256': hashlib.sha256(self.sources['ElevenSquare.Verification'].encode()).hexdigest(),
                'declarations': {'Certificate.coverage': 1}}}}
            (self.root / 'verification/native-certificates.json').write_bytes(json_bytes(native_manifest))
        context = {p: sha(self.root / p) for p in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json']}
        object_hashes = {}; inputs = {}
        state = self.root / '.verification'; state.mkdir(exist_ok=True)
        for module, text in self.sources.items():
            source = self.root / (module.replace('.', '/') + '.lean')
            source.parent.mkdir(parents=True, exist_ok=True); source.write_bytes(text.encode('utf-8'))
            deps = ['ElevenSquare', 'Sqpack'] if module.endswith('.Verification') else []
            fingerprint = {
                'source': hashlib.sha256(text.encode()).hexdigest(),
                'local_dependency_objects': {d: object_hashes[d] for d in deps},
                'compiler': 'Lean (version 4.34.1, fixture)',
                'arguments': [f"-j{(jobs or {}).get(module, 1)}", '-M0', '-s65536',
                              '-DautoImplicit=' + ('true' if module == 'Sqpack' else 'false'),
                              '-DmaxHeartbeats=0'],
                'build_context': context,
                'local_dependency_inputs': {d: input_digest(inputs[d]) for d in deps},
            }
            obj = self.root / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
            obj.parent.mkdir(parents=True, exist_ok=True); obj.write_bytes(module.encode())
            object_hashes[module] = sha(obj); inputs[module] = fingerprint
            (state / (module + '.json')).write_bytes(json_bytes({
                'status': 'accepted', 'module': module, 'inputs': fingerprint,
                'object_sha256': object_hashes[module]}))
            output = ''.join("'" + n + "' depends on axioms: [" + ', '.join(self.axioms[n]) + "]\n"
                             for n in sorted(targets))
            # Lean logs retain UTF-8 diagnostics even when Python's locale is
            # a Windows code page; their axiom evidence must remain readable.
            (state / (module + '.log')).write_bytes(
                ('warning: fixture over ℝ\n' + output if deps else '').encode('utf-8'))
        self.result = {'status': 'PARTIAL_ASSEMBLY_COMPILES' if sites else 'OPTIMALITY_PROVED',
                       'checked_modules': 3, 'global_optimality_proved': not sites, 'axioms': self.axioms}
        if native:
            self.result.update(public_audit_status(self.axioms, len(sites)))
        self.save_result()
        self.source_check = {'status': 'SOURCE_ASSEMBLY_PASS', 'local_modules': 3,
                             'explicit_admissions': len(sites)}

    def save_result(self):
        (self.root / '.verification/result.json').write_bytes(json_bytes(self.result))

    def test_complete_matching_receipts_are_accepted_without_writing(self):
        audit = collect_audit(self.root, self.source_check)
        self.assertTrue(audit['full_upgrade_verified'])
        self.assertEqual(audit['checked_modules'], 3)
        self.assertFalse((self.root / 'verification/wand125-upgrade.json').exists())

    def test_native_evidence_retains_explicit_compiler_trust(self):
        self.make_fixture([], native=True)
        audit = collect_audit(self.root, self.source_check)
        self.assertEqual(audit['status'], 'OPTIMALITY_PROVED_WITH_NATIVE_CERTIFICATES')
        self.assertEqual(audit['trust_model'], 'lean_kernel_and_native_compiler')
        self.assertEqual(audit['native_certificate_axioms'],
                         ['Certificate.coverage._native.native_decide.ax_1_1'])
        self.assertTrue(audit['global_optimality_proved'])

    def test_native_evidence_cannot_be_relabelled_kernel_only(self):
        self.make_fixture([], native=True)
        self.result['status'] = 'OPTIMALITY_PROVED'
        self.save_result()
        with self.assertRaisesRegex(ValueError, 'Verifier proof status'):
            collect_audit(self.root, self.source_check)

    def test_native_evidence_requires_matching_trust_disclosure(self):
        self.make_fixture([], native=True)
        self.result['trust_model'] = 'lean_kernel'
        self.save_result()
        with self.assertRaisesRegex(ValueError, 'Verifier native trust disclosure'):
            collect_audit(self.root, self.source_check)

    def test_native_manifest_cannot_silently_change_source_permissions(self):
        self.make_fixture([], native=True)
        path = self.root / 'verification/native-certificates.json'
        manifest = json.loads(path.read_text())
        manifest['files']['ElevenSquare/Verification.lean']['sha256'] = '0' * 64
        path.write_bytes(json_bytes(manifest))
        with self.assertRaisesRegex(ValueError, 'hash|Hash|SHA|sha256'):
            collect_audit(self.root, self.source_check)

    def test_mixed_jobs_accept_full_audit_without_rewriting_receipts(self):
        self.make_fixture([], jobs={'ElevenSquare': 1, 'Sqpack': 4, 'ElevenSquare.Verification': 8})
        paths = sorted((self.root / '.verification').glob('*.json'))
        before = {p: p.read_bytes() for p in paths}
        audit = collect_audit(self.root, self.source_check)
        self.assertTrue(audit['global_optimality_proved'])
        self.assertEqual(audit['checked_modules'], 3)
        self.assertEqual({p: p.read_bytes() for p in paths}, before)

    def test_mixed_jobs_still_require_exact_transitive_input_hashes(self):
        self.make_fixture([], jobs={'Sqpack': 4, 'ElevenSquare.Verification': 8})
        path = self.root / '.verification/Sqpack.json'
        receipt = json.loads(path.read_text(encoding='utf-8'))
        # Even an otherwise valid different job count changes this input digest;
        # its dependent's receipt must not be silently relabeled or normalized.
        receipt['inputs']['arguments'][0] = '-j8'
        path.write_bytes(json_bytes(receipt))
        with self.assertRaisesRegex(ValueError, 'Stale source/configuration/dependency receipt'):
            collect_audit(self.root, self.source_check)

    def test_noncanonical_recorded_flags_reject_full_audit(self):
        self.make_fixture([], jobs={'Sqpack': 4, 'ElevenSquare.Verification': 8})
        path = self.root / '.verification/Sqpack.json'
        receipt = json.loads(path.read_text(encoding='utf-8'))
        good = receipt['inputs']['arguments'][:]
        bad = [None, [], good[:-1], good + ['-t999'], good + ['-DElab.async=false'],
               good + ['-j8'], ['-M0', '-j4', *good[2:]]]
        bad.extend([flag, *good[1:]] for flag in ('-j0', '-j04', '-j+4', '-j4294967296'))
        for i, flag in ((1, '-M1'), (2, '-s1024'), (3, '-DautoImplicit=false'),
                        (4, '-DmaxHeartbeats=1')):
            bad.append(good[:i] + [flag] + good[i+1:])
        for arguments in bad:
            with self.subTest(arguments=arguments):
                receipt['inputs']['arguments'] = arguments
                path.write_bytes(json_bytes(receipt))
                with self.assertRaisesRegex(ValueError, 'Noncanonical compiler arguments'):
                    collect_audit(self.root, self.source_check)

    def test_five_two_and_zero_admission_states_are_accepted(self):
        for paths in (BASELINE_PATHS + [RETURNED_PATH, CAPTURE_PATH],
                      [RETURNED_PATH, CAPTURE_PATH], []):
            with self.subTest(admissions=len(paths)):
                self.make_fixture(paths)
                audit = collect_audit(self.root, self.source_check)
                self.assertEqual(audit['explicit_native_admissions'], len(paths))
                self.assertEqual(audit['global_optimality_proved'], not paths)
                self.assertEqual(audit['status'],
                                 'PARTIAL_ASSEMBLY_COMPILES' if paths else 'OPTIMALITY_PROVED')
                self.assertTrue(audit['full_upgrade_verified'])

    def test_selected_only_result_is_rejected_even_with_full_module_count(self):
        self.result['status'] = 'SELECTED_MODULES_COMPILE'; self.save_result()
        with self.assertRaisesRegex(ValueError, 'No successful full-project'):
            collect_audit(self.root, self.source_check)

    def test_inventory_and_source_check_counts_must_match(self):
        self.make_fixture([RETURNED_PATH, CAPTURE_PATH])
        self.source_check['explicit_admissions'] = 6
        with self.assertRaisesRegex(ValueError, 'exactly the inventoried admissions'):
            collect_audit(self.root, self.source_check)

    def test_unknown_inventoried_path_is_rejected(self):
        inventory = self.root / 'verification/admissions.json'
        inventory.write_bytes(json_bytes({'sites': [{'path': 'ElevenSquare/Unexpected.lean', 'line': 1}]}))
        self.source_check['explicit_admissions'] = 1
        with self.assertRaisesRegex(ValueError, 'Unknown admission paths'):
            collect_audit(self.root, self.source_check)

    def test_missing_completed_public_queries_are_rejected(self):
        for name in ('baseline_certificate_exists', 'prior_certificate_exists'):
            with self.subTest(query=name):
                self.make_fixture([RETURNED_PATH, CAPTURE_PATH],
                                  missing_queries=['ElevenSquare.Pending.' + name])
                with self.assertRaisesRegex(ValueError, 'Missing final public target axiom queries'):
                    collect_audit(self.root, self.source_check)

    def test_closed_prior_and_baseline_reject_inherited_admissions(self):
        cases = [(BASELINE_PATHS + [RETURNED_PATH, CAPTURE_PATH], 'prior_certificate_exists'),
                 ([RETURNED_PATH, CAPTURE_PATH], 'baseline_certificate_exists')]
        for paths, name in cases:
            with self.subTest(query=name):
                self.make_fixture(paths, axiom_overrides={'ElevenSquare.Pending.' + name: ['sorryAx']})
                with self.assertRaisesRegex(ValueError, 'Unapproved axioms'):
                    collect_audit(self.root, self.source_check)

    def test_zero_admissions_cannot_accept_sorry_ax_or_custom_axioms(self):
        for axiom in ('sorryAx', 'customOracle'):
            with self.subTest(axiom=axiom):
                self.make_fixture([], axiom_overrides={'ElevenSquare.optimality': [axiom]})
                with self.assertRaisesRegex(ValueError, 'Unapproved axioms'):
                    collect_audit(self.root, self.source_check)

    def test_result_cannot_claim_completion_before_inventory_is_empty(self):
        self.make_fixture([RETURNED_PATH, CAPTURE_PATH])
        self.result.update(status='OPTIMALITY_PROVED', global_optimality_proved=True)
        self.save_result()
        with self.assertRaisesRegex(ValueError, 'Verifier proof status does not match'):
            collect_audit(self.root, self.source_check)

    def test_stale_partial_status_is_rejected_after_all_obligations_close(self):
        self.make_fixture([])
        self.result.update(status='PARTIAL_ASSEMBLY_COMPILES', global_optimality_proved=False)
        self.save_result()
        with self.assertRaisesRegex(ValueError, 'Verifier proof status does not match'):
            collect_audit(self.root, self.source_check)

    def test_partial_result_is_rejected(self):
        self.result['checked_modules'] = 2; self.save_result()
        with self.assertRaisesRegex(ValueError, 'every current local module'):
            collect_audit(self.root, self.source_check)

    def test_changed_source_rejects_old_success(self):
        (self.root / 'ElevenSquare.lean').write_text('-- changed since success\n')
        with self.assertRaisesRegex(ValueError, 'Stale source'):
            collect_audit(self.root, self.source_check)

    def test_changed_dependency_configuration_rejects_old_success(self):
        (self.root / 'lakefile.lean').write_text('-- changed pin/configuration\n')
        with self.assertRaisesRegex(ValueError, 'Stale source/configuration'):
            collect_audit(self.root, self.source_check)

    def test_changed_object_rejects_old_success(self):
        (self.root / '.lake/build/lib/lean/ElevenSquare.olean').write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'Changed compiled object'):
            collect_audit(self.root, self.source_check)

    def test_changed_or_missing_axiom_evidence_rejects_old_success(self):
        self.result['axioms'] = {}; self.save_result()
        with self.assertRaisesRegex(ValueError, 'current axiom logs'):
            collect_audit(self.root, self.source_check)


if __name__ == '__main__':
    unittest.main()
