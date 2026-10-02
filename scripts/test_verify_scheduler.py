"""Dependency, cache, failure and child-lifetime tests without running Lean."""
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest

from verify_scheduler import (CheckFailed, CheckpointStop, CheckoutLock, schedule,
                              stop_processes)


class FakeProcess:
    next_pid = 100

    def __init__(self, ticks=10, code=0, trace=None, ignore_terminate=False):
        FakeProcess.next_pid += 1
        self.pid = FakeProcess.next_pid
        self.ticks, self.code = ticks, code
        self.returncode = None
        self.trace = trace if trace is not None else []
        self.ignore_terminate = ignore_terminate
        self.reaped = False

    def poll(self):
        if self.returncode is None:
            if self.ticks:
                self.ticks -= 1
            else:
                self.returncode = self.code
                self.reaped = True
        return self.returncode

    def terminate(self):
        self.trace.append(('terminate', self.pid))
        if not self.ignore_terminate:
            self.returncode = -15

    def kill(self):
        self.trace.append(('kill', self.pid))
        self.returncode = -9

    def wait(self, timeout=None):
        self.trace.append(('wait', self.pid))
        if self.returncode is None:
            raise subprocess.TimeoutExpired('fake', timeout)
        self.reaped = True
        return self.returncode


class PermissiveGuard:
    def assess(self, active):
        return SimpleNamespace(allow_start=True, terminate_module=None, reason='available')


class Harness:
    def __init__(self, dependencies, *, cached=(), failures=(), ticks=None):
        self.dependencies = dependencies
        self.cached, self.failures = set(cached), set(failures)
        self.ticks = ticks or {}
        self.published, self.running, self.partial = set(), set(), set()
        self.prepared, self.started, self.accepted, self.rejected = [], [], [], []
        self.jobs, self.snapshots = [], []
        self.max_active = 0
        self.prepare_error = self.start_error = self.accept_error = self.interrupt_start = None
        self.interrupt_accept = None

    def prepare(self, module):
        if module == self.prepare_error:
            raise ValueError('prepare error')
        if not set(self.dependencies[module]) <= self.published:
            raise AssertionError('Fingerprint prepared before dependencies were published')
        self.prepared.append(module)
        if module in self.cached:
            self.published.add(module)
            return None
        harness = self

        class Job:
            process = None
            started = None

            def start(self):
                if module in harness.running:
                    raise AssertionError('Duplicate active module')
                self.process = FakeProcess(harness.ticks.get(module, 10),
                                           1 if module in harness.failures else 0)
                self.started = self.process.pid
                harness.running.add(module)
                harness.partial.add(module)
                harness.started.append(module)
                harness.snapshots.append(set(harness.running))
                harness.max_active = max(harness.max_active, len(harness.running))
                if module == harness.start_error:
                    raise OSError('start error')
                if module == harness.interrupt_start:
                    signal.raise_signal(signal.SIGTERM)

            def accept(self):
                if module == harness.accept_error:
                    raise OSError('publication error')
                if not set(harness.dependencies[module]) <= harness.published:
                    raise AssertionError('Dependency was not published')
                harness.partial.discard(module)
                harness.running.remove(module)
                harness.published.add(module)
                harness.accepted.append(module)
                if module == harness.interrupt_accept:
                    signal.raise_signal(signal.SIGTERM)

            def reject(self, reason):
                if self.process is not None and not self.process.reaped:
                    raise AssertionError('Partial output cleaned before child was reaped')
                harness.partial.discard(module)
                harness.running.discard(module)
                harness.rejected.append((module, reason))

        job = Job()
        self.jobs.append(job)
        return job

    def run(self, **kwargs):
        return schedule(list(self.dependencies), self.dependencies, self.prepare,
                        poll_seconds=0, **kwargs)


class SchedulerTests(unittest.TestCase):
    def test_serial_default_checks_closed_graph_once(self):
        harness = Harness({'A': [], 'B': [], 'Join': ['A', 'B']})
        result = harness.run()
        self.assertEqual(harness.max_active, 1)
        self.assertEqual(harness.started, ['A', 'B', 'Join'])
        self.assertEqual(result.accepted, list(harness.dependencies))
        self.assertFalse(result.failed or result.blocked or harness.partial)

    def test_parallel_dependencies_wait_for_publication_and_final_waits_for_all(self):
        final = 'ElevenSquare.Verification'
        deps = {'A': [], 'B': [], 'Join': ['A', 'B'], final: ['Join'], 'Extra': []}
        harness = Harness(deps, ticks={'Extra': 80})
        result = harness.run(max_parallel=2, guard=PermissiveGuard())
        self.assertEqual(harness.max_active, 2)
        self.assertEqual(harness.started[-1], final)
        self.assertLess(harness.accepted.index('Extra'), harness.accepted.index(final))
        self.assertEqual(result.accepted, list(deps))
        self.assertEqual(len(harness.started), len(set(harness.started)))
        self.assertEqual(harness.published, set(deps))

    def test_cached_dependency_chain_is_published_without_processes(self):
        deps = {'A': [], 'B': ['A'], 'C': ['B'], 'D': ['A', 'C']}
        harness = Harness(deps, cached={'A', 'B', 'C'})
        result = harness.run(max_parallel=2, guard=PermissiveGuard())
        self.assertEqual(harness.started, ['D'])
        self.assertEqual(harness.prepared, list(deps))
        self.assertEqual(result.accepted, list(deps))

    def test_all_cached_closure_finishes_even_when_guard_denies_start(self):
        class Deny:
            def assess(self, active):
                return SimpleNamespace(allow_start=False, terminate_module=None, reason='busy')
        harness = Harness({'A': [], 'B': ['A']}, cached={'A', 'B'})
        result = harness.run(max_parallel=2, guard=Deny())
        self.assertEqual(result.accepted, ['A', 'B'])
        self.assertFalse(harness.started)

    def test_failed_dependencies_block_descendants_but_independent_work_finishes(self):
        deps = {'Bad': [], 'Good': [], 'B': ['Bad'], 'C': ['B', 'Good'], 'D': ['Good']}
        harness = Harness(deps, failures={'Bad'})
        result = harness.run(max_parallel=2, guard=PermissiveGuard(), keep_going=True)
        self.assertEqual(result.failed, ['Bad'])
        self.assertEqual(result.blocked, {'B': ['Bad'], 'C': ['B']})
        self.assertEqual(result.accepted, ['Good', 'D'])
        self.assertEqual(set(harness.started), {'Bad', 'Good', 'D'})
        self.assertFalse(harness.partial or harness.running)

    def test_fail_fast_cancels_and_reaps_other_active_job(self):
        harness = Harness({'Bad': [], 'Slow': [], 'Child': ['Bad']},
                          failures={'Bad'}, ticks={'Bad': 5, 'Slow': 10000})
        with self.assertRaises(CheckFailed) as caught:
            harness.run(max_parallel=2, guard=PermissiveGuard())
        self.assertEqual(caught.exception.module, 'Bad')
        self.assertIn(('Slow', 'interrupted'), harness.rejected)
        self.assertTrue(all(job.process.reaped for job in harness.jobs))
        self.assertFalse(harness.partial or harness.running or harness.accepted)

    def test_pressure_retry_runs_alone_and_is_not_a_failed_dependency(self):
        class Pressure(PermissiveGuard):
            triggered = False

            def assess(self, active):
                if len(active) == 2 and not self.triggered:
                    self.triggered = True
                    return SimpleNamespace(allow_start=False, terminate_module='B', reason='pressure')
                return super().assess(active)
        deps = {'A': [], 'B': [], 'C': [], 'D': [], 'Join': ['A', 'B', 'C', 'D']}
        harness = Harness(deps, ticks={'A': 50})
        result = harness.run(max_parallel=2, guard=Pressure())
        self.assertEqual(harness.started.count('B'), 2)
        self.assertIn(('B', 'resource_pressure'), harness.rejected)
        retry_index = [i for i, m in enumerate(harness.started) if m == 'B'][1]
        self.assertEqual(harness.snapshots[retry_index], {'B'})
        self.assertEqual(result.accepted, list(deps))
        self.assertFalse(result.failed or result.blocked or harness.partial)

    def test_guard_denial_can_relax_without_skipping_a_module(self):
        class Delay(PermissiveGuard):
            calls = 0

            def assess(self, active):
                self.calls += 1
                if self.calls < 8:
                    return SimpleNamespace(allow_start=False, terminate_module=None, reason='busy')
                return super().assess(active)
        harness = Harness({'A': [], 'B': ['A']})
        result = harness.run(max_parallel=2, guard=Delay())
        self.assertEqual(result.accepted, ['A', 'B'])
        self.assertEqual(harness.started, ['A', 'B'])

    def test_prepare_start_and_publication_errors_reap_every_child(self):
        for attribute, bad_module in [('prepare_error', 'B'), ('start_error', 'B'), ('accept_error', 'A')]:
            with self.subTest(stage=attribute):
                harness = Harness({'A': [], 'B': []}, ticks={'A': 10, 'B': 10000})
                setattr(harness, attribute, bad_module)
                with self.assertRaises((ValueError, OSError)):
                    harness.run(max_parallel=2, guard=PermissiveGuard())
                self.assertTrue(all(job.process is None or job.process.reaped for job in harness.jobs))
                self.assertFalse(harness.partial or harness.running)

    def test_interrupt_during_registration_reaps_new_child_and_restores_handlers(self):
        previous = {sig: signal.getsignal(sig) for sig in (signal.SIGINT, signal.SIGTERM)}
        harness = Harness({'A': []}, ticks={'A': 10000})
        harness.interrupt_start = 'A'
        with self.assertRaises(KeyboardInterrupt):
            harness.run()
        self.assertTrue(harness.jobs[0].process.reaped)
        self.assertEqual(harness.rejected, [('A', 'interrupted')])
        self.assertFalse(harness.partial or harness.running)
        self.assertEqual(previous, {sig: signal.getsignal(sig) for sig in previous})

    def test_interrupt_after_publication_preserves_checkpoint_and_reaps_others(self):
        harness = Harness({'A': [], 'B': []}, ticks={'A': 5, 'B': 10000})
        harness.interrupt_accept = 'A'
        with self.assertRaises(KeyboardInterrupt):
            harness.run(max_parallel=2, guard=PermissiveGuard())
        self.assertEqual(harness.published, {'A'})
        self.assertEqual(harness.accepted, ['A'])
        self.assertEqual(harness.rejected, [('B', 'interrupted')])
        self.assertTrue(all(job.process.reaped for job in harness.jobs))
        self.assertFalse(harness.partial or harness.running)

    def test_invalid_graph_or_unguarded_parallelism_never_starts(self):
        for order, deps, options in [
            (['A', 'A'], {'A': []}, {}),
            (['A'], {'A': ['Missing']}, {}),
            (['A', 'B'], {'A': ['B'], 'B': []}, {}),
            (['A'], {'A': []}, {'max_parallel': 2}),
            (['A'], {'A': []}, {'max_parallel': True}),
            (['ElevenSquare.Verification', 'A'],
             {'ElevenSquare.Verification': [], 'A': ['ElevenSquare.Verification']}, {}),
        ]:
            with self.subTest(order=order, deps=deps, options=options):
                with self.assertRaises(ValueError):
                    schedule(order, deps, lambda _: self.fail('prepare must not run'), **options)

    def test_invalid_guard_victim_aborts_without_acceptance(self):
        class BadGuard:
            def assess(self, active):
                return SimpleNamespace(allow_start=True, terminate_module='Missing', reason='bad')
        with self.assertRaisesRegex(ValueError, 'invalid auxiliary'):
            Harness({'A': []}).run(max_parallel=2, guard=BadGuard())

    def test_checkpoint_stop_drains_current_jobs_without_launching_dependents(self):
        harness = Harness({'A': [], 'B': [], 'Join': ['A', 'B'], 'Extra': []})
        requested = False

        def should_stop():
            nonlocal requested
            requested |= len(harness.started) == 2
            return requested

        with self.assertRaises(CheckpointStop):
            harness.run(max_parallel=2, guard=PermissiveGuard(), stop_requested=should_stop)
        self.assertEqual(harness.started, ['A', 'B'])
        self.assertEqual(harness.published, {'A', 'B'})
        self.assertFalse(harness.rejected or harness.partial or harness.running)

    def test_existing_stop_request_launches_nothing(self):
        harness = Harness({'A': []})
        with self.assertRaises(CheckpointStop):
            harness.run(stop_requested=lambda: True)
        self.assertFalse(harness.prepared or harness.started)

    def test_checkpoint_drain_retains_memory_backoff_without_relaunching(self):
        class Pressure(PermissiveGuard):
            def assess(self, active):
                if len(active) == 2:
                    return SimpleNamespace(allow_start=False, terminate_module='B', reason='pressure')
                return super().assess(active)
        harness = Harness({'A': [], 'B': [], 'Join': ['A', 'B']})
        with self.assertRaises(CheckpointStop):
            harness.run(max_parallel=2, guard=Pressure(),
                        stop_requested=lambda: len(harness.started) == 2)
        self.assertEqual(harness.started, ['A', 'B'])
        self.assertEqual(harness.published, {'A'})
        self.assertEqual(harness.rejected, [('B', 'resource_pressure')])
        self.assertFalse(harness.partial or harness.running)


class ProcessLifetimeTests(unittest.TestCase):
    def test_all_children_are_terminated_before_waiting_and_killed_if_needed(self):
        trace = []
        processes = [FakeProcess(ticks=10000, trace=trace, ignore_terminate=True) for _ in range(2)]
        stop_processes([SimpleNamespace(process=p) for p in processes], grace=0, kill_grace=0)
        self.assertEqual(trace[:2], [('terminate', p.pid) for p in processes])
        self.assertEqual([entry for entry in trace if entry[0] == 'kill'], [('kill', p.pid) for p in processes])
        self.assertTrue(all(p.reaped for p in processes))

    def test_real_python_children_are_reaped_without_any_compiler(self):
        processes = [subprocess.Popen([sys.executable, '-B', '-c', 'import time; time.sleep(60)'],
                                      stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                     for _ in range(2)]
        try:
            stop_processes([SimpleNamespace(process=p) for p in processes], grace=0.2)
            self.assertTrue(all(p.returncode is not None for p in processes))
        finally:
            for p in processes:
                if p.poll() is None:
                    p.kill()
                p.wait()

    def test_checkout_lock_is_exclusive_and_released(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'verifier.lock'
            with CheckoutLock(path):
                with self.assertRaises(OSError):
                    CheckoutLock(path).acquire()
            with CheckoutLock(path):
                pass
            self.assertTrue(path.is_file())


if __name__ == '__main__':
    unittest.main()
