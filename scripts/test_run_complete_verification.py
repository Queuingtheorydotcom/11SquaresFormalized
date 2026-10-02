"""Local handoff runner tests; no Lean, network, or Git commands are executed."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import run_complete_verification as runner
from verify_scheduler import CheckoutLock
from verify_support import input_digest, lean_arguments


class RunnerTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for folder in ('.verification/run', 'verification', 'scripts'):
            (self.root / folder).mkdir(parents=True)
        self.write('verification/admissions.json', {'sites': []})
        self.options = SimpleNamespace(skip_benchmark=True, workers=4, memory_percent=95,
                                       stop_file=None, resume_after_stop=False)
        self.calls = []
        self.verify_code = self.finalize_code = 0
        self.partial = self.stop_during_verifier = False

    def write(self, name, value):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value), encoding='utf-8')

    def fake_stage(self, root, name, command, folder, stop, wrapper):
        self.calls.append((name, command))
        if name == 'verifier':
            self.write('.verification/result.json', {
                'status': 'PARTIAL_ASSEMBLY_COMPILES' if self.partial else 'OPTIMALITY_PROVED',
                'global_optimality_proved': not self.partial, 'checked_modules': 3})
            if self.stop_during_verifier:
                stop.signaled = True
            return runner.StageResult(self.verify_code, {'ElevenSquare.A'},
                                      {'ElevenSquare.Bad', 'private@example.invalid'} if self.verify_code else set(),
                                      {'ElevenSquare.Blocked'} if self.verify_code else set())
        if name == 'finalizer':
            self.write('verification/wand125-upgrade.json', {
                'status': 'OPTIMALITY_PROVED', 'full_upgrade_verified': True,
                'global_optimality_proved': True, 'explicit_native_admissions': 0,
                'checked_modules': 3})
            self.write('verification/source-check.json', {
                'status': 'SOURCE_ASSEMBLY_PASS', 'explicit_admissions': 0, 'local_modules': 3})
            self.write('MANIFEST.json', {})
            return runner.StageResult(self.finalize_code)
        raise AssertionError('Unexpected stage: ' + name)

    def execute(self):
        with contextlib.redirect_stdout(io.StringIO()):
            return runner.execute(self.root, self.options, stage_runner=self.fake_stage)

    def summary(self):
        latest = runner.read_json(self.root / '.verification/run/latest.json')
        return runner.read_json(self.root / latest['summary'])

    def test_complete_workflow_uses_full_reuse_and_strict_finalizer(self):
        self.assertEqual(self.execute(), 0)
        self.assertEqual([stage for stage, _ in self.calls], ['verifier', 'finalizer'])
        command = self.calls[0][1]
        self.assertIn('--all', command)
        self.assertIn('--keep-going', command)
        self.assertNotIn('--fresh', command)
        self.assertEqual(command[command.index('--jobs') + 1], '4')
        self.assertEqual(command[command.index('--max-parallel') + 1], '1')
        self.assertIn('--write', self.calls[1][1])
        self.assertEqual(self.summary()['status'], 'OPTIMALITY_PROVED')
        self.assertTrue(self.summary()['complete'])
        self.assertEqual(self.summary()['explicit_admissions'], 0)

    def test_failure_preserves_resumability_and_redacts_summary(self):
        self.verify_code = 1
        original_log = self.root / '.verification/ElevenSquare.Bad.log'
        original_log.write_bytes(b'complete diagnostic\n' * 1000)
        self.write('.verification/ElevenSquare.Bad.json', {'status': 'failed_or_interrupted'})
        self.assertEqual(self.execute(), 1)
        failed = self.summary()
        self.assertEqual(failed['status'], 'VERIFICATION_FAILED')
        self.assertEqual(failed['failed_modules'], ['ElevenSquare.Bad'])
        self.assertEqual(failed['failed_module_count'], 1)
        self.assertEqual(failed['blocked_module_count'], 1)
        self.assertFalse(failed['complete'])
        self.assertNotIn('private@', json.dumps(failed))
        self.assertEqual(len(self.calls), 1)
        latest = runner.read_json(self.root / '.verification/run/latest.json')
        archived = self.root / latest['directory'] / 'failed-modules/ElevenSquare.Bad.log'
        self.assertEqual(archived.read_bytes(), original_log.read_bytes())
        original_log.write_bytes(b'later retry diagnostic')
        self.assertTrue(archived.read_bytes().startswith(b'complete diagnostic'))
        self.assertTrue(archived.with_suffix('.json').is_file())
        self.verify_code = 0
        self.assertEqual(self.execute(), 0)
        self.assertTrue(self.summary()['complete'])
        self.assertEqual(len(list((self.root / '.verification/run').glob('*/summary.json'))), 2)

    def test_partial_or_nonzero_admissions_never_reach_finalizer(self):
        self.partial = True
        self.assertEqual(self.execute(), 1)
        self.assertFalse(self.summary()['complete'])
        self.assertEqual(len(self.calls), 1)
        self.partial = False
        self.write('verification/admissions.json', {'sites': [{'path': 'unfinished'}]})
        self.assertEqual(self.execute(), 1)
        self.assertEqual(len(self.calls), 2)

    def test_finalizer_failure_cannot_accept_even_existing_success_files(self):
        self.finalize_code = 1
        self.assertEqual(self.execute(), 1)
        self.assertEqual(self.summary()['status'], 'FINALIZATION_FAILED')
        self.assertFalse(self.summary()['complete'])

    def test_existing_stop_request_requires_explicit_resume(self):
        stop = self.root / '.verification/run/stop-requested'
        stop.touch()
        self.assertEqual(self.execute(), 130)
        self.assertEqual(self.calls, [])
        self.assertTrue(stop.exists())
        self.options.resume_after_stop = True
        self.assertEqual(self.execute(), 0)
        self.assertFalse(stop.exists())

    def test_signal_stop_after_verifier_never_starts_finalizer(self):
        self.stop_during_verifier = True
        self.assertEqual(self.execute(), 130)
        self.assertEqual(len(self.calls), 1)
        self.assertEqual(self.summary()['status'], 'STOPPED')
        self.assertTrue((self.root / '.verification/run/stop-requested').is_file())

    def test_stop_file_cannot_target_source_or_clear_custom_path(self):
        source = self.root / 'lakefile.lean'
        source.write_text('source', encoding='utf-8')
        self.options.stop_file = source
        with self.assertRaises(ValueError):
            self.execute()
        self.assertEqual(source.read_text(), 'source')
        self.options.stop_file = self.root / '.verification/custom-stop'
        self.options.stop_file.write_text('keep', encoding='utf-8')
        self.options.resume_after_stop = True
        with self.assertRaises(ValueError):
            self.execute()
        self.assertEqual(self.options.stop_file.read_text(), 'keep')

    def test_busy_workflow_and_verifier_do_not_overwrite_latest_pointer(self):
        pointer = self.root / '.verification/run/latest.json'
        pointer.write_text('{"active": true}', encoding='utf-8')
        for path in ('.verification/run/complete-run.lock', '.verification/verifier.lock'):
            with self.subTest(path=path), CheckoutLock(self.root / path):
                with self.assertRaises(OSError):
                    self.execute()
                self.assertEqual(pointer.read_text(), '{"active": true}')
        self.assertEqual(self.calls, [])

    def test_stage_logs_raw_diagnostics_privately_and_prints_only_progress(self):
        folder = self.root / '.verification/run/fixture'
        folder.mkdir()
        raw = b'private@example.invalid C:/private/account/file\n[1/2] failed ElevenSquare.Bad\n'
        child = SimpleNamespace(stdout=io.BytesIO(raw), poll=lambda: 0, wait=lambda **_: 0)
        console, wrapper = io.StringIO(), io.BytesIO()
        with patch.object(runner.subprocess, 'Popen', return_value=child) as start, contextlib.redirect_stdout(console):
            outcome = runner.run_stage(self.root, 'verifier', ['fake'], folder,
                                      runner.StopControl(folder / 'stop'), wrapper)
        self.assertEqual(outcome.failed, {'ElevenSquare.Bad'})
        self.assertIn(raw, wrapper.getvalue())
        self.assertEqual((folder / 'verifier.log').read_bytes(), raw)
        self.assertNotIn('private', console.getvalue())
        self.assertIn('failed ElevenSquare.Bad', console.getvalue())
        self.assertEqual(start.call_args.kwargs['stdin'], runner.subprocess.DEVNULL)

    def test_startup_refusal_records_private_traceback_without_changing_latest(self):
        pointer = self.root / '.verification/run/latest.json'
        pointer.write_text('{"active": true}', encoding='utf-8')
        console = io.StringIO()
        with patch.object(runner, 'ROOT', self.root), CheckoutLock(self.root / '.verification/verifier.lock'), contextlib.redirect_stdout(console):
            self.assertEqual(runner.main(['--skip-benchmark']), 2)
        self.assertTrue((self.root / '.verification/run/runner-startup-error.log').is_file())
        self.assertEqual(pointer.read_text(), '{"active": true}')
        self.assertNotIn(str(self.root), console.getvalue())

    def test_stage_stop_notice_and_reaping_never_call_kill(self):
        folder = self.root / '.verification/run/stop-fixture'
        folder.mkdir()

        class Child:
            stdout = io.BytesIO(b'')
            finished = False
            waits = 0

            def poll(self):
                return 0 if self.finished else None

            def wait(self, **_):
                self.waits += 1
                self.finished = True
                return 0

            def terminate(self):
                raise AssertionError('Automatic termination is forbidden')

            kill = terminate

        child, console = Child(), io.StringIO()
        stop = runner.StopControl(folder / 'stop')
        stop.signaled = True
        with patch.object(runner.subprocess, 'Popen', return_value=child), contextlib.redirect_stdout(console):
            runner.run_stage(self.root, 'verifier', ['fake'], folder, stop, io.BytesIO())
        self.assertEqual(console.getvalue().count('Stop requested;'), 1)
        self.assertGreaterEqual(child.waits, 1)
        self.assertTrue(stop.path.is_file())


class BenchmarkTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.folder = self.root / '.verification/bench/matched-fixture'
        self.folder.mkdir(parents=True)
        for name in runner.CONFIG:
            (self.root / name).write_text(name, encoding='utf-8')
        compiler = self.root / 'work/tooling/lean-4.34.1-windows/bin/lean.exe'
        compiler.parent.mkdir(parents=True)
        compiler.write_bytes(b'fake compiler bytes only')
        self.compiler = compiler
        context = {name: runner.sha(self.root / name) for name in runner.CONFIG}
        records = {}
        for module, dependencies in [('ElevenSquare.Base', []), ('ElevenSquare.Cohort', ['ElevenSquare.Base'])]:
            source = self.root.joinpath(*module.split('.')).with_suffix('.lean')
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text(''.join('import ' + dep + '\n' for dep in dependencies)
                              + '#print axioms ' + module + '.proof\n', encoding='utf-8')
            obj = (self.root / '.lake/build/lib/lean').joinpath(*module.split('.')).with_suffix('.olean')
            obj.parent.mkdir(parents=True, exist_ok=True)
            obj.write_bytes(module.encode())
            record = {'status': 'accepted', 'object_sha256': runner.sha(obj), 'inputs': {
                'source': runner.sha(source), 'compiler': 'Lean version 4.34.1, fixture',
                'arguments': lean_arguments(module, 4), 'build_context': context,
                'local_dependency_objects': {dep: records[dep]['object_sha256'] for dep in dependencies},
                'local_dependency_inputs': {dep: input_digest(records[dep]['inputs']) for dep in dependencies}}}
            records[module] = record
            runner.save_json(self.root / '.verification' / (module + '.json'), record)
            (self.root / '.verification' / (module + '.log')).write_text(
                "'" + module + ".proof' depends on axioms: [propext]\n", encoding='utf-8')
        cohort = 'ElevenSquare.Cohort'
        self.report = {'status': 'MATCHED_BENCHMARK', 'canonical_files_unchanged': True,
            'compiler': records[cohort]['inputs']['compiler'], 'compiler_sha256': runner.sha(compiler),
            'order': [cohort], 'source_sha256': {cohort: records[cohort]['inputs']['source']}, 'modes': {}}
        for mode, count, elapsed in [('serial', 1, 10), ('parallel2', 2, 6)]:
            target = self.folder / mode
            target.mkdir()
            (target / 'scratch.olean').write_bytes(cohort.encode())
            (target / 'scratch.log').write_text("'ElevenSquare.Cohort.proof' depends on axioms: [propext]\n", encoding='utf-8')
            self.report['modes'][mode] = {'status': 'MATCHED', 'max_parallel': count,
                'order': [cohort], 'elapsed_seconds': elapsed, 'guard': {'memory_percent': 95},
                'memory': {'concurrent_processes_peak': count}, 'attempts': [{
                    'module': cohort, 'status': 'MATCHED', 'returncode': 0, 'arguments': lean_arguments(cohort, 4),
                    'output': 'scratch.olean', 'log': 'scratch.log', 'output_sha256': runner.sha(target / 'scratch.olean'),
                    'log_sha256': runner.sha(target / 'scratch.log'), 'axioms': {'ElevenSquare.Cohort.proof': ['propext']}}]}
        self.path = self.folder / 'report.json'
        runner.save_json(self.path, self.report)

    def choice(self):
        return runner.valid_benchmark(self.root, self.path, 4, 95)

    def test_matched_faster_report_selects_two_and_slower_selects_one(self):
        self.assertEqual(self.choice()['max_parallel'], 2)
        self.report['modes']['parallel2']['elapsed_seconds'] = 11
        runner.save_json(self.path, self.report)
        self.assertEqual(self.choice()['max_parallel'], 1)

    def test_changed_transitive_source_or_object_rejects_benchmark(self):
        source = self.root / 'ElevenSquare/Base.lean'
        previous = source.read_bytes()
        source.write_bytes(previous + b'-- changed\n')
        self.assertIsNone(self.choice())
        source.write_bytes(previous)
        obj = self.root / '.lake/build/lib/lean/ElevenSquare/Base.olean'
        obj.write_bytes(b'changed object')
        self.assertIsNone(self.choice())

    def test_missing_or_changed_runtime_and_dirty_axioms_reject(self):
        self.compiler.write_bytes(b'changed compiler')
        self.assertIsNone(self.choice())
        self.compiler.write_bytes(b'fake compiler bytes only')
        self.report.pop('compiler_sha256')
        runner.save_json(self.path, self.report)
        self.assertIsNone(self.choice())

    def test_unobserved_parallelism_or_wrong_worker_count_cannot_select_two(self):
        self.report['modes']['parallel2']['memory']['concurrent_processes_peak'] = 1
        runner.save_json(self.path, self.report)
        self.assertEqual(self.choice()['max_parallel'], 1)
        self.assertIsNone(runner.valid_benchmark(self.root, self.path, 8, 95))


if __name__ == '__main__':
    unittest.main()
