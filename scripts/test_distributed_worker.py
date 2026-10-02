"""Distributed orchestration regressions; never launches Lean or network tools."""
import contextlib
import io
import json
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

import distributed_worker as worker
from run_complete_verification import StageResult
from verify_scheduler import CheckoutLock
from verify_support import input_digest, lean_arguments


class DistributedWorkerTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.environment = patch.dict(worker.os.environ, {}, clear=False)
        self.environment.start()
        self.addCleanup(self.environment.stop)
        self.identity = {'version': 'Lean (version 4.34.1, x86_64-w64-windows-gnu, Release)',
                         'binary_sha256': 'a' * 64, 'platform': 'windows-x86_64'}
        for directory in ('verification', '.verification/distributed', 'scripts'):
            (self.root / directory).mkdir(parents=True)
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n', encoding='utf-8')
        (self.root / 'lakefile.lean').write_text('-- fixture\n', encoding='utf-8')
        self.write('lake-manifest.json', {'packages': []})
        self.write('verification/admissions.json', {'sites': []})
        self.graph = {'ElevenSquare.A': [], 'ElevenSquare.B': ['ElevenSquare.A'], 'ElevenSquare.C': []}
        self.sizes, self.hashes = {}, {}
        for module, deps in self.graph.items():
            path = self.root.joinpath(*module.split('.')).with_suffix('.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(''.join('import ' + dep + '\n' for dep in deps) + '-- fixture\n', encoding='utf-8')
            self.sizes[module], self.hashes[module] = path.stat().st_size, worker.sha(path)
        self.context = {name: worker.sha(self.root / name) for name in worker.CONFIG}
        self.receipts = {}
        self.receipt('ElevenSquare.A', 1)
        self.receipt('ElevenSquare.B', 4)
        with patch.object(worker.ci_plan, 'required_sources', return_value={}):
            self.plan = worker.create_plan(self.root, self.identity, graph_data=(self.graph, self.sizes, self.hashes))
        self.path = self.root / 'verification/distributed-plan.json'
        worker.save_json(self.path, self.plan)
        self.index = next(shard['index'] for shard in self.plan['shards'] if 'ElevenSquare.B' in shard['modules'])
        self.options = SimpleNamespace(command='run', worker=self.index, compiler=None,
            plan=self.path, plan_sha256=worker.sha(self.path), jobs_file=Path('.verification/distributed/jobs.json'),
            stop_file=None, budget_seconds=None, resume_after_stop=False, max_parallel=2, memory_percent=95)

    def write(self, path, value):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps(value), encoding='utf-8')

    def receipt(self, module, jobs):
        obj = (self.root / '.lake/build/lib/lean').joinpath(*module.split('.')).with_suffix('.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        obj.write_bytes(module.encode())
        inputs = {'source': self.hashes[module], 'compiler': self.identity['version'],
            'arguments': lean_arguments(module, jobs), 'build_context': self.context,
            'local_dependency_objects': {dep: self.receipts[dep]['object_sha256'] for dep in self.graph[module]},
            'local_dependency_inputs': {dep: input_digest(self.receipts[dep]['inputs']) for dep in self.graph[module]}}
        receipt = {'status': 'accepted', 'inputs': inputs, 'object_sha256': worker.sha(obj)}
        self.receipts[module] = receipt
        self.write('.verification/' + module + '.json', receipt)
        (self.root / '.verification' / (module + '.log')).write_text('', encoding='utf-8')

    def load_patches(self):
        return (patch.object(worker.ci_plan, 'required_sources', return_value={}),
                patch.object(worker.ci_plan, 'read_graph', return_value=(self.graph, self.sizes, self.hashes)))

    def test_plan_is_deterministic_with_full_actual_jobs_map(self):
        with patch.object(worker.ci_plan, 'required_sources', return_value={}):
            again = worker.create_plan(self.root, self.identity, graph_data=(self.graph, self.sizes, self.hashes))
        self.assertEqual(self.plan, again)
        self.assertEqual(self.plan['shard_count'], 18)
        self.assertEqual(self.plan['job_policy']['module_jobs'],
                         {'ElevenSquare.A': 1, 'ElevenSquare.B': 4, 'ElevenSquare.C': 4})
        self.assertNotIn(str(self.root), json.dumps(self.plan))
        self.assertEqual(worker.worker_closure(self.plan, self.index), {'ElevenSquare.A', 'ElevenSquare.B'})

    def test_plan_file_has_identical_lf_bytes_on_every_platform(self):
        expected = (json.dumps(self.plan, indent=2, sort_keys=True) + '\n').encode('utf-8')
        with patch.object(worker, 'ROOT', self.root), \
                patch.object(worker, 'compiler_identity', return_value=self.identity), \
                patch.object(worker, 'create_plan', return_value=self.plan), \
                contextlib.redirect_stdout(io.StringIO()):
            for _ in range(2):
                self.assertEqual(worker.main(['plan']), 0)
                self.assertEqual(self.path.read_bytes(), expected)
                self.assertNotIn(b'\r', self.path.read_bytes())

    def test_stale_transitive_receipts_do_not_override_default_jobs(self):
        obj = self.root / '.lake/build/lib/lean/ElevenSquare/A.olean'
        obj.write_bytes(b'changed')
        jobs = worker.accepted_jobs(self.root, self.graph, self.hashes, self.context, self.identity)
        self.assertEqual(jobs, dict.fromkeys(self.graph, 4))

    def test_source_config_assignment_and_incomplete_job_maps_are_rejected(self):
        first, second = self.load_patches()
        with first, second:
            self.assertEqual(worker.load_plan(self.root, self.path), self.plan)
            self.plan['shards'][self.index]['modules'] = []
            worker.save_json(self.path, self.plan)
            with self.assertRaisesRegex(ValueError, 'assignment'):
                worker.load_plan(self.root, self.path)
        self.plan['job_policy']['module_jobs'].pop('ElevenSquare.C')
        with self.assertRaisesRegex(ValueError, 'inventory'):
            worker.validate_structure(self.plan)

    def test_current_source_hash_change_requires_explicit_replan(self):
        first, second = self.load_patches()
        self.hashes['ElevenSquare.A'] = 'b' * 64
        with first, second, self.assertRaisesRegex(ValueError, 'source graph'):
            worker.load_plan(self.root, self.path)

    def test_budget_requests_stop_file_without_killing(self):
        now = [10]
        path = self.root / '.verification/distributed/stop-worker-00'
        stop = worker.BudgetStop(path, 5, clock=lambda: now[0])
        self.assertFalse(stop.requested())
        now[0] = 15
        self.assertTrue(stop.requested())
        self.assertTrue(path.is_file())

    def test_internal_child_expands_large_target_list_without_os_command(self):
        # This deliberately exceeds Windows' command-line length, but only the
        # short child command is passed to Popen; the large argv lives in Python.
        plan = dict(self.plan)
        plan['shards'] = [dict(shard) for shard in self.plan['shards']]
        targets = ['ElevenSquare.LongModule' + str(i) for i in range(2500)]
        plan['shards'][self.index]['modules'] = targets
        self.write('.verification/distributed/jobs.json', self.plan['job_policy']['module_jobs'])
        self.options.stop_file = Path('.verification/distributed/stop-worker-00')
        saved = list(worker.sys.argv)
        worker.os.environ['ELAN_TOOLCHAIN'] = 'unexpected-toolchain'
        try:
            with patch.object(worker, 'load_plan', return_value=plan), \
                    patch.object(worker, 'compiler_identity', return_value=self.identity), \
                    patch.object(worker.runpy, 'run_path') as run:
                self.assertEqual(worker.child_verify(self.root, self.options), 0)
                self.assertEqual(worker.sys.argv.count('--module'), len(targets))
                self.assertGreater(len(' '.join(worker.sys.argv)), 32767)
                self.assertIn('--jobs-file', worker.sys.argv)
                self.assertNotIn('--fresh', worker.sys.argv)
                self.assertEqual(worker.os.environ['ELAN_TOOLCHAIN'], self.plan['lean_toolchain'])
                run.assert_called_once()
        finally:
            worker.sys.argv = saved

    def test_empty_worker_does_not_accidentally_run_default_final_target(self):
        empty = next(shard['index'] for shard in self.plan['shards'] if not shard['modules'])
        self.options.worker = empty
        self.write('.verification/distributed/jobs.json', self.plan['job_policy']['module_jobs'])
        with patch.object(worker, 'compiler_identity', return_value=self.identity), \
                patch.object(worker.runpy, 'run_path') as run, contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(worker.child_verify(self.root, self.options), 0)
            run.assert_not_called()

    def test_selected_worker_success_never_claims_global_completion(self):
        commands = []

        def stage(root, name, command, folder, stop, log):
            commands.append(command)
            self.write('.verification/selected-result.json', {'status': 'SELECTED_MODULES_COMPILE',
                'targets': self.plan['shards'][self.index]['modules'], 'checked_modules': 2})
            return StageResult(0, {'ElevenSquare.A', 'ElevenSquare.B'})

        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(worker.run_checks(self.root, self.options, self.plan, self.path, stage_runner=stage), 0)
        self.assertEqual(len(commands), 1)
        self.assertLess(len(' '.join(commands[0])), 32767)
        self.assertIn('_verify', commands[0])
        latest = worker.read_json(self.root / f'.verification/distributed/latest-worker-{self.index:02d}.json')
        summary = worker.read_json(self.root / latest['directory'] / 'summary.json')
        self.assertEqual(summary['status'], 'WORKER_CHECKPOINT_ACCEPTED')
        self.assertFalse(summary['global_optimality_proved'])

    def test_stop_and_failed_worker_never_claim_success(self):
        self.options.budget_seconds = 1
        def stage(root, name, command, folder, stop, log):
            stop.signaled = True
            return StageResult(1, {'ElevenSquare.A'}, {'ElevenSquare.B'})
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(worker.run_checks(self.root, self.options, self.plan, self.path, stage_runner=stage), 130)
        latest = worker.read_json(self.root / f'.verification/distributed/latest-worker-{self.index:02d}.json')
        self.assertEqual(latest['status'], 'STOPPED')

    def test_busy_existing_runner_refuses_before_any_runtime_or_child(self):
        with CheckoutLock(self.root / '.verification/run/complete-run.lock'), \
                patch.object(worker, 'ROOT', self.root), \
                patch.object(worker, 'compiler_identity') as identity, \
                patch.object(worker, 'run_checks') as checks, contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(worker.main(['run', '--worker', str(self.index)]), 2)
            identity.assert_not_called()
            checks.assert_not_called()

    def test_plan_cannot_overwrite_admissions_or_live_result(self):
        admissions = (self.root / 'verification/admissions.json').read_bytes()
        for path in ('verification/admissions.json', '.verification/result.json'):
            with self.subTest(path=path), patch.object(worker, 'ROOT', self.root), \
                    patch.object(worker, 'compiler_identity') as identity, contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(worker.main(['plan', '--plan', path]), 2)
                identity.assert_not_called()
        self.assertEqual((self.root / 'verification/admissions.json').read_bytes(), admissions)

    def test_platform_mismatch_refuses_before_running(self):
        first, second = self.load_patches()
        mismatch = dict(self.identity, platform='linux-x86_64')
        with first, second, patch.object(worker, 'ROOT', self.root), \
                patch.object(worker, 'compiler_identity', return_value=mismatch), \
                patch.object(worker, 'run_checks') as checks, contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(worker.main(['run', '--worker', str(self.index)]), 2)
            checks.assert_not_called()

    def test_runtime_probe_uses_installed_pinned_toolchain_and_stores_no_path(self):
        elan = self.root / '.verification/toolchain-fixture'
        executable = elan / 'toolchains/leanprover--lean4---v4.34.1/bin' / ('lean.exe' if worker.os.name == 'nt' else 'lean')
        executable.parent.mkdir(parents=True)
        executable.write_bytes(b'compiler fixture')
        worker.os.environ['ELAN_HOME'] = str(elan)
        worker.os.environ['ELAN_TOOLCHAIN'] = 'unexpected-toolchain'
        with patch.object(worker.shutil, 'which', return_value='mock-lake'), \
                patch.object(worker, 'platform_id', return_value='windows-x86_64'), \
                patch.object(worker.subprocess, 'check_output', side_effect=[
                    json.dumps({'lean': str(executable)}), self.identity['version']]) as calls:
            identity = worker.compiler_identity(self.root, executable)
        self.assertEqual(identity['binary_sha256'], worker.sha(executable))
        self.assertNotIn(str(self.root), json.dumps(identity))
        self.assertEqual(calls.call_args_list[0].kwargs['env']['ELAN_TOOLCHAIN'], 'leanprover/lean4:v4.34.1')
        self.assertNotIn('install', calls.call_args_list[0].args[0])

    def test_final_route_uses_all_then_strict_write_and_requires_completion(self):
        self.options.command = 'final'
        commands = []
        def stage(root, name, command, folder, stop, log):
            commands.append((name, command))
            return StageResult(0)
        with patch.object(worker, 'complete_state', return_value=3) as complete, contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(worker.run_checks(self.root, self.options, self.plan, self.path, stage_runner=stage), 0)
            self.assertEqual([call.kwargs['finalized'] for call in complete.call_args_list], [False, True])
        self.assertIn('--all', commands[0][1])
        self.assertIn('--jobs-file', commands[0][1])
        self.assertIn('--write', commands[1][1])


if __name__ == '__main__':
    unittest.main()
