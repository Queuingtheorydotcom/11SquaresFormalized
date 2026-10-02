"""Pure memory-guard tests: no child processes or live telemetry."""
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

import verify_resources as guard


def child(pid, started):
    return SimpleNamespace(process=SimpleNamespace(pid=pid), started=started)


class ResourceGuardTests(unittest.TestCase):
    def make_guard(self, available=8000, commit=8000, total=10000, usages=None, now=20):
        usages = usages or {1: guard.ProcessMemory(1000, 2000, 1000, 2000),
                            2: guard.ProcessMemory(1000, 2000, 1000, 2000)}
        return guard.ResourceGuard(
            reserve_bytes=0, minimum_process_bytes=100,
            system_reader=lambda: guard.MemorySnapshot(total, available, commit),
            process_reader=lambda pid: usages.get(pid), clock=lambda: now)

    def test_serial_slot_remains_available_without_telemetry(self):
        resource = guard.ResourceGuard(system_reader=lambda: None)
        self.assertTrue(resource.assess({}).allow_start)
        result = resource.assess({'A': child(1, 0)})
        self.assertFalse(result.allow_start)
        self.assertIsNone(result.terminate_module)

    def test_unknown_system_telemetry_selects_only_newest_auxiliary(self):
        resource = guard.ResourceGuard(system_reader=lambda: None)
        result = resource.assess({'A': child(1, 0), 'B': child(2, 1)})
        self.assertEqual(result.terminate_module, 'B')
        self.assertEqual(result.reason, 'system_memory_unavailable')

    def test_physical_pressure_at_95_percent_stops_auxiliary(self):
        result = self.make_guard(available=499).assess({'A': child(1, 0), 'B': child(2, 1)})
        self.assertEqual(result.terminate_module, 'B')
        self.assertEqual(result.reason, 'physical_memory_pressure')

    def test_commit_pressure_independently_stops_auxiliary(self):
        result = self.make_guard(commit=499).assess({'A': child(1, 0), 'B': child(2, 1)})
        self.assertEqual(result.terminate_module, 'B')
        self.assertEqual(result.reason, 'commit_memory_pressure')

    def test_pressure_does_not_signal_the_only_primary(self):
        result = self.make_guard(available=1, commit=1).assess({'A': child(1, 0)})
        self.assertFalse(result.allow_start)
        self.assertIsNone(result.terminate_module)

    def test_exact_ceiling_blocks_admission_without_evicting(self):
        result = self.make_guard(available=500).assess({'A': child(1, 0), 'B': child(2, 1)})
        self.assertIsNone(result.terminate_module)
        self.assertFalse(result.allow_start)

    def test_startup_does_not_overadmit_on_small_initial_sample(self):
        result = self.make_guard().assess({'A': child(1, 19)})
        self.assertFalse(result.allow_start)
        self.assertEqual(result.reason, 'startup_warmup')

    def test_admission_reserves_growth_for_active_and_new_children(self):
        # RSS reserve: 500 + (1250 - 1000) + 1250 = 2000.
        # Commit reserve: 500 + (2500 - 2000) + 2500 = 3500.
        ready = self.make_guard(available=2000, commit=3500).assess({'A': child(1, 0)})
        self.assertTrue(ready.allow_start)
        self.assertFalse(self.make_guard(available=1999).assess({'A': child(1, 0)}).allow_start)
        self.assertFalse(self.make_guard(commit=3499).assess({'A': child(1, 0)}).allow_start)

    def test_high_water_mark_is_not_forgotten_after_process_shrinks(self):
        usages = {1: guard.ProcessMemory(100, 200, 3000, 4000)}
        resource = self.make_guard(available=8000, commit=8000, usages=usages)
        self.assertFalse(resource.assess({'A': child(1, 0)}).allow_start)
        usages[1] = guard.ProcessMemory(100, 200, 100, 200)
        self.assertFalse(resource.assess({'A': child(1, 0)}).allow_start)

    def test_heavy_batch_peak_resets_only_after_every_active_child_finishes(self):
        usages = {1: guard.ProcessMemory(3000, 5000, 6000, 8000),
                  2: guard.ProcessMemory(500, 1000, 500, 1000)}
        resource = self.make_guard(available=6000, commit=6000, usages=usages)
        self.assertFalse(resource.assess({'Heavy': child(1, 0), 'Light': child(2, 1)}).allow_start)
        # The light survivor still belongs to the observed heavy batch.
        self.assertFalse(resource.assess({'Light': child(2, 1)}).allow_start)
        self.assertEqual(resource.peak_private, 8000)
        self.assertTrue(resource.assess({}).allow_start)
        self.assertEqual((resource.peak_resident, resource.peak_private), (0, 0))
        # A later lightweight batch can scale using its own measured footprint.
        self.assertTrue(resource.assess({'Next': child(2, 1)}).allow_start)

    def test_missing_process_telemetry_stops_only_auxiliary(self):
        result = self.make_guard(usages={1: guard.ProcessMemory(1, 1, 1, 1)}).assess(
            {'A': child(1, 0), 'B': child(2, 1)})
        self.assertEqual(result.terminate_module, 'B')
        self.assertEqual(result.reason, 'process_memory_unavailable')

    def test_invalid_configuration_is_rejected(self):
        for options in ({'memory_percent': 96}, {'memory_percent': 0},
                        {'reserve_bytes': -1}, {'warmup_seconds': -1},
                        {'minimum_process_bytes': 0}):
            with self.subTest(options=options), self.assertRaises(ValueError):
                guard.ResourceGuard(**options)

    def test_proc_kilobyte_parser_ignores_non_numeric_lines(self):
        self.assertEqual(guard._kb_fields('VmRSS: 123 kB\nName: lean\nThreads: 4\n'),
                         {'VmRSS': 123 * 1024, 'Threads': 4})

    def test_native_reader_failure_falls_back_to_serial(self):
        with mock.patch.object(guard.sys, 'platform', 'win32'), mock.patch.object(
                guard, '_windows_memory', side_effect=OSError('unavailable')):
            self.assertIsNone(guard.read_system_memory())
        with mock.patch.object(guard.sys, 'platform', 'unsupported'):
            self.assertIsNone(guard.read_system_memory())
            self.assertIsNone(guard.read_process_memory(1))

    def test_linux_uses_nested_cgroup_and_ancestor_limits(self):
        files = {
            '/proc/meminfo': 'MemTotal: 10000 kB\nMemAvailable: 8000 kB\n'
                             'CommitLimit: 20000 kB\nCommitted_AS: 1000 kB\n',
            '/proc/self/cgroup': '0::/parent/child\n',
            '/sys/fs/cgroup/memory.max': 'max',
            '/sys/fs/cgroup/parent/memory.max': '4096000',
            '/sys/fs/cgroup/parent/memory.current': '3072000',
            '/sys/fs/cgroup/parent/child/memory.max': '5120000',
            '/sys/fs/cgroup/parent/child/memory.current': '1024000',
        }
        with mock.patch.object(Path, 'is_file', lambda p: p.as_posix() in files), mock.patch.object(
                Path, 'read_text', lambda p, **kwargs: files[p.as_posix()]):
            result = guard._linux_memory()
        self.assertEqual(result.total_physical, 4096000)
        self.assertEqual(result.available_physical, 1024000)
        self.assertEqual(result.available_commit, 19000 * 1024)

    def test_linux_unresolved_cgroup_disables_parallelism(self):
        files = {
            '/proc/meminfo': 'MemTotal: 10000 kB\nMemAvailable: 8000 kB\n'
                             'CommitLimit: 20000 kB\nCommitted_AS: 1000 kB\n',
            '/proc/self/cgroup': '0::/unresolved\n',
        }
        with mock.patch.object(guard.sys, 'platform', 'linux'), mock.patch.object(
                Path, 'is_file', return_value=False), mock.patch.object(
                Path, 'read_text', lambda p, **kwargs: files[p.as_posix()]):
            self.assertIsNone(guard.read_system_memory())

    def test_linux_process_reserves_data_and_stack_beyond_resident_memory(self):
        text = 'VmRSS: 1000 kB\nVmHWM: 2000 kB\nVmData: 3000 kB\nVmStk: 100 kB\nVmSwap: 20 kB\n'
        with mock.patch.object(guard.sys, 'platform', 'linux'), mock.patch.object(
                Path, 'read_text', return_value=text):
            result = guard.read_process_memory(1)
        self.assertEqual(result.resident, 1000 * 1024)
        self.assertEqual(result.private, 3100 * 1024)
        self.assertEqual(result.peak_resident, 2000 * 1024)


if __name__ == '__main__':
    unittest.main()
