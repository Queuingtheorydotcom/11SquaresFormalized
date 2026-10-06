#!/usr/bin/env python3
"""Offline checkpoint safety tests; never invoke the compiler or hosted setup."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest import mock

import ci_replay as ci


class Checkpoints(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        (self.root / '.verification').mkdir()

    def accepted(self, module='Sqpack.A', body=b'object', **kwargs):
        names = ci.triple(module)
        values = [body, json.dumps({'status':'accepted', 'inputs':{'source':'abc'},
                  'object_sha256':hashlib.sha256(body).hexdigest(), **kwargs}).encode(), b'checked\n']
        for name, value in zip(names, values):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(value)
        return names

    def destination(self):
        dest = self.root / 'destination'
        (dest / '.verification').mkdir(parents=True)
        return dest

    def test_round_trip_and_leaf_exclusion_from_join_cache(self):
        names = self.accepted()
        archive = self.root / 'shard-00.tar.gz'
        self.assertTrue(ci.pack(self.root, archive))
        dest = self.destination()
        ci.merge(dest, [archive])
        self.assertEqual((dest / names[0]).read_bytes(), b'object')
        out = dest / 'join.tar.gz'
        ci.pack(dest, out, join=True)
        with tarfile.open(out) as bundle:
            self.assertEqual(bundle.getnames(), [])

    def test_prior_join_progress_is_retained_in_join_checkpoint(self):
        self.accepted()
        archive = self.root / 'shard-16.tar.gz'
        ci.pack(self.root, archive)
        dest = self.destination()
        ci.merge(dest, [archive])
        output = dest / 'next-join.tar.gz'
        ci.pack(dest, output, join=True)
        with tarfile.open(output) as bundle:
            self.assertEqual(len(bundle.getnames()), 3)

    def test_incomplete_triples_are_rejected(self):
        archive = self.root / 'partial.tar.gz'
        with tarfile.open(archive, 'w:gz') as bundle:
            member = tarfile.TarInfo(ci.triple('Sqpack.A')[0])
            member.size = 1
            bundle.addfile(member, io.BytesIO(b'x'))
        with self.assertRaisesRegex(ValueError, 'has no receipt'):
            ci.merge(self.destination(), [archive])

    def test_accepted_hash_tampering_is_rejected(self):
        names = self.accepted()
        (self.root / names[0]).write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'object hash differs'):
            ci.pack(self.root, self.root / 'out.tar.gz')

    def test_failed_receipts_are_excluded(self):
        self.accepted(status='failed_or_interrupted')
        archive = self.root / 'out.tar.gz'
        ci.pack(self.root, archive)
        with tarfile.open(archive) as bundle:
            self.assertEqual(bundle.getnames(), [])

    def test_oversize_is_not_exported(self):
        self.accepted()
        output = self.root / 'out.tar.gz'
        with self.assertRaisesRegex(ValueError, 'Compressed checkpoint exceeds'):
            ci.pack(self.root, output, limit=1)
        self.assertFalse(output.exists())

    def test_compressible_objects_use_compressed_budget(self):
        self.accepted(body=b'x' * (128 * 1024))
        output = self.root / 'compressed.tar.gz'
        self.assertTrue(ci.pack(self.root, output, limit=16 * 1024))
        self.assertLess(output.stat().st_size, 16 * 1024)
        ci.merge(self.destination(), [output])

    def test_expanded_size_limit_is_checked(self):
        self.accepted(body=b'x' * 1000)
        output = self.root / 'expanded.tar.gz'
        ci.pack(self.root, output)
        with mock.patch.object(ci, 'EXPANDED_LIMIT', 10):
            with self.assertRaisesRegex(ValueError, 'declared size'):
                ci.merge(self.destination(), [output])

    def test_conflicting_duplicate_objects_are_dropped_for_rebuild(self):
        self.accepted()
        first = self.root / 'shard-00.tar.gz'; ci.pack(self.root, first)
        self.accepted(body=b'different')
        second = self.root / 'shard-01.tar.gz'; ci.pack(self.root, second)
        dest = self.destination()
        self.assertEqual(ci.merge(dest, [first, second]), {'Sqpack.A'})
        self.assertFalse((dest / '.lake').exists())

    def test_identical_objects_and_inputs_allow_different_receipt_times(self):
        self.accepted(checked_at_ns=1)
        first = self.root / 'shard-00.tar.gz'; ci.pack(self.root, first)
        self.accepted(checked_at_ns=2)
        second = self.root / 'shard-01.tar.gz'; ci.pack(self.root, second)
        ci.merge(self.destination(), [first, second])

    def test_unsafe_archive_and_symlink_are_rejected(self):
        for name, kind in [('../escape', tarfile.REGTYPE), ('.verification/Sqpack.A.log', tarfile.SYMTYPE)]:
            archive = self.root / 'bad.tar.gz'
            with tarfile.open(archive, 'w:gz') as bundle:
                member = tarfile.TarInfo(name); member.type = kind
                bundle.addfile(member, io.BytesIO(b''))
            with self.assertRaisesRegex(ValueError, 'Invalid checkpoint member'):
                ci.merge(self.root, [archive])

    def test_setup_refuses_user_filesystem(self):
        with mock.patch.dict(ci.os.environ, {}, clear=True), mock.patch.object(ci.subprocess, 'Popen') as run:
            with self.assertRaisesRegex(ValueError, 'disposable GitHub-hosted'):
                ci.prepare()
            run.assert_not_called()


class Preparation(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name).resolve()
        (self.root / '.verification').mkdir()
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
        for patch in [mock.patch.object(ci, 'ROOT', self.root),
                      mock.patch.object(ci, 'STATE', self.root / '.verification'),
                      mock.patch.dict(ci.os.environ, {'GITHUB_ACTIONS': 'true',
                          'RUNNER_ENVIRONMENT': 'github-hosted', 'RUNNER_OS': 'Linux',
                          'GITHUB_WORKSPACE': str(self.root)}),
                      mock.patch.object(ci.shutil, 'disk_usage', return_value=mock.Mock(free=33 * 1024**3))]:
            patch.start()
            self.addCleanup(patch.stop)

    def test_privileged_timeout_runs_inside_noninteractive_sudo(self):
        with mock.patch.object(ci.subprocess, 'Popen') as spawn, mock.patch('builtins.print') as output:
            spawn.return_value.wait.return_value = 0
            ci.setup_command('cleanup', ['rm', '-rf', '--', '/opt/ghc'], 90, ci.time.monotonic() + 600, True)
            self.assertEqual(spawn.call_args.args[0], ['sudo', '-n', 'timeout', '--signal=TERM',
                '--kill-after=15s', '90s', 'rm', '-rf', '--', '/opt/ghc'])
            self.assertTrue(spawn.call_args.kwargs['start_new_session'])
            self.assertIn('starting', output.call_args_list[0].args[0])
            self.assertIn('exited 0', output.call_args_list[-1].args[0])
            self.assertTrue(all(call.kwargs['flush'] for call in output.call_args_list))

    def test_waiting_commands_emit_flushed_heartbeats(self):
        with mock.patch.object(ci.subprocess, 'Popen') as spawn, mock.patch('builtins.print') as output:
            spawn.return_value.wait.side_effect = [ci.subprocess.TimeoutExpired('test', 60), 0]
            ci.setup_command('downloads', ['test-command'], 180, ci.time.monotonic() + 600)
            self.assertTrue(any('still running' in call.args[0] for call in output.call_args_list))
            self.assertTrue(all(call.kwargs['flush'] for call in output.call_args_list))
            self.assertLessEqual(spawn.return_value.wait.call_args_list[0].kwargs['timeout'], 60)

    def test_timeout_and_command_failure_are_not_success(self):
        for code, error in [(124, TimeoutError), (137, TimeoutError), (1, ci.subprocess.CalledProcessError)]:
            with self.subTest(code=code), mock.patch.object(ci.subprocess, 'Popen') as spawn:
                spawn.return_value.wait.return_value = code
                with self.assertRaises(error):
                    ci.setup_command('failed phase', ['test-command'], 90, ci.time.monotonic() + 600)

    def test_shared_deadline_reserves_termination_time(self):
        with mock.patch.object(ci.time, 'monotonic', return_value=100), mock.patch.object(ci.subprocess, 'Popen') as spawn:
            with self.assertRaisesRegex(TimeoutError, 'deadline reached'):
                ci.setup_command('too late', ['test-command'], 90, 200)
            spawn.assert_not_called()
            spawn.return_value.wait.return_value = 0
            ci.setup_command('remaining budget', ['test-command'], 900, 230)
            self.assertIn('30s', spawn.call_args.args[0])

    def test_stuck_wrapper_is_terminated_with_bounded_waits(self):
        with mock.patch.object(ci.time, 'monotonic', return_value=0) as clock, \
                mock.patch.object(ci.subprocess, 'Popen') as spawn, mock.patch.object(ci.os, 'killpg') as stop:
            def wait(**kwargs):
                clock.return_value = 200
                raise ci.subprocess.TimeoutExpired('test', kwargs['timeout'])
            spawn.return_value.wait.side_effect = lambda **kwargs: wait(**kwargs) if clock.return_value == 0 else 0
            with self.assertRaisesRegex(TimeoutError, 'exceeded its deadline'):
                ci.setup_command('stuck wrapper', ['test-command'], 90, 600)
            stop.assert_called_once_with(spawn.return_value.pid, ci.signal.SIGTERM)
            self.assertEqual(spawn.return_value.wait.call_args_list[-1].kwargs['timeout'], 15)

    def test_interrupted_privileged_command_is_stopped_and_reaped(self):
        with mock.patch.object(ci.subprocess, 'Popen') as spawn, mock.patch.object(ci.subprocess, 'run') as stop:
            spawn.return_value.pid = 12345
            spawn.return_value.wait.side_effect = [KeyboardInterrupt(), 0]
            with self.assertRaises(KeyboardInterrupt):
                ci.setup_command('apt', ['apt-get', 'update'], 180, ci.time.monotonic() + 600, True)
            self.assertEqual(stop.call_args.args[0], ['sudo', '-n', 'timeout', '--signal=KILL',
                '10s', 'kill', '-TERM', '--', '-12345'])
            self.assertEqual(stop.call_args.kwargs['timeout'], 15)
            self.assertEqual(spawn.return_value.wait.call_args_list[-1].kwargs['timeout'], 15)

    def test_session_stop_escalates_and_reap_is_bounded(self):
        child = mock.Mock(pid=12345)
        child.wait.side_effect = [ci.subprocess.TimeoutExpired('test', 15), 0]
        with mock.patch.object(ci.os, 'killpg') as stop:
            ci.stop_setup(child, False)
            self.assertEqual(stop.call_args_list, [mock.call(12345, ci.signal.SIGTERM),
                                                  mock.call(12345, ci.signal.SIGKILL)])
            self.assertEqual(child.wait.call_args_list, [mock.call(timeout=15), mock.call(timeout=15)])

    def test_sufficient_disk_skips_disposable_cleanup(self):
        with mock.patch.object(ci, 'setup_command') as run:
            ci.prepare()
            self.assertEqual(run.call_count, 6)
            self.assertFalse(any(call.args[0].startswith('remove disposable') for call in run.call_args_list))
            self.assertTrue(all(call.args[3] == run.call_args_list[0].args[3] for call in run.call_args_list))
            self.assertTrue(run.call_args_list[0].kwargs['privileged'])
            self.assertTrue(run.call_args_list[1].kwargs['privileged'])

    def test_cleanup_timeout_rechecks_disk_before_next_directory(self):
        with mock.patch.object(ci, 'setup_command') as run, mock.patch.object(ci.shutil, 'disk_usage') as disk:
            disk.side_effect = [mock.Mock(free=n * 1024**3) for n in (12, 33, 4)]
            run.side_effect = [TimeoutError('bounded cleanup'), None, None, None, None, None, None]
            ci.prepare()
            cleanup = [call for call in run.call_args_list if call.args[0].startswith('remove disposable')]
            self.assertEqual(len(cleanup), 1)
            self.assertEqual(cleanup[0].args[1], ['rm', '-rf', '--', '/usr/local/lib/android'])
            self.assertEqual(cleanup[0].args[2], 90)
            self.assertTrue(cleanup[0].kwargs['privileged'])

    def test_final_disk_gate_is_preserved(self):
        with mock.patch.object(ci, 'setup_command'), mock.patch.object(ci.shutil, 'disk_usage') as disk:
            disk.side_effect = [mock.Mock(free=n * 1024**3) for n in (33, 3)]
            with self.assertRaisesRegex(ValueError, 'Less than 4 GiB'):
                ci.prepare()


if __name__ == '__main__':
    unittest.main()
