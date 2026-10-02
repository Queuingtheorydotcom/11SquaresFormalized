"""Security-policy regressions using hostile inert fixtures; no Docker/Lean runs."""
import importlib.util
import io
import json
from pathlib import Path
import tarfile
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

import verify_container as launcher
original_lock = launcher.volume_lock

spec = importlib.util.spec_from_file_location('container_runner',
    Path(__file__).parent / 'container/container_runner.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


def options(**changes):
    return SimpleNamespace(**dict(cpus=4, memory='16g', max_parallel=2, jobs=2,
                                  volume=None, **changes))


class ContainerPolicyTests(unittest.TestCase):
    def test_every_submission_stage_is_offline_and_has_no_host_mounts(self):
        for stage in ('seed', 'verify', 'probe', 'report'):
            with self.subTest(stage=stage), patch('os.sched_getaffinity', return_value={2, 3, 4, 5}):
                command = launcher.run_arguments('sha256:fixture', 'private-volume', stage,
                                                 options(), Path('/tmp/host-secret-canary'))
                self.assertIn('--network=none', command)
                self.assertIn('--read-only', command)
                self.assertIn('--cap-drop=ALL', command)
                self.assertIn('--security-opt=no-new-privileges=true', command)
                self.assertIn('--security-opt=seccomp=builtin', command)
                self.assertIn('--user=10001:10001', command)
                self.assertIn('--memory-swap=16g', command)
                self.assertIn('--cpuset-cpus=2,3,4,5', command)
                self.assertIn('--pids-limit=4096', command)
                mounts = [arg for arg in command if arg.startswith('--mount=')]
                self.assertEqual(mounts, ['--mount=type=volume,source=private-volume,target=/workspace'])
                self.assertFalse(any(arg in command for arg in ('--privileged', '--pid=host', '--network=host')))
                self.assertFalse(any('docker.sock' in arg for arg in command))

    def test_existing_volume_never_receives_online_preparation(self):
        self.assertEqual(launcher.stages_for('all', True), ['verify'])
        for stage in ('verify', 'probe', 'report'):
            self.assertEqual(launcher.stages_for(stage, True), [stage])
        with self.assertRaisesRegex(ValueError, 'cannot re-enter online'):
            launcher.stages_for('prepare', True)
        self.assertEqual(launcher.stages_for('all', False), ['prepare', 'verify'])

    def test_main_resumes_existing_volume_offline_even_with_forged_workspace_markers(self):
        # Host policy does not inspect a writable prepared/snapshot marker.
        commit, image = 'a' * 40, 'sha256:fixture'
        labels = {launcher.LABEL: 'v1', launcher.LABEL + '.commit': commit,
                  launcher.LABEL + '.image': image}
        def output(command, **_):
            if 'status' in command:
                return ''
            if 'rev-parse' in command:
                return commit
            return image
        def run(command, **_):
            return SimpleNamespace(returncode=0,
                stdout=json.dumps([{'Labels': labels}]) if 'volume' in command else '')
        with tempfile.TemporaryDirectory() as locks, \
             patch.object(launcher, 'volume_lock', side_effect=lambda volume: original_lock(volume, Path(locks))), \
             patch.object(launcher, 'check_engine'), patch.object(launcher, 'context', return_value=b'recipe'), \
             patch.object(launcher, 'output', side_effect=output), \
             patch.object(launcher.subprocess, 'run', side_effect=run), \
             patch.object(launcher, 'execute_container') as execute, \
             patch('os.sched_getaffinity', return_value={0, 1, 2, 3}):
            launcher.main(['all'])
            self.assertEqual(execute.call_count, 1)
            self.assertIn('--network=none', execute.call_args.args[0])
            self.assertIn('verify', execute.call_args.args[0])
            execute.reset_mock()
            with self.assertRaisesRegex(ValueError, 'cannot re-enter online'):
                launcher.main(['prepare'])
            execute.assert_not_called()

    def test_volume_lock_prevents_overlapping_lifecycles_and_releases_on_failure(self):
        with tempfile.TemporaryDirectory() as folder:
            directory = Path(folder)
            with launcher.volume_lock('same-volume', directory):
                with self.assertRaisesRegex(ValueError, 'Another launcher'):
                    with launcher.volume_lock('same-volume', directory):
                        self.fail('Concurrent lifecycle acquired the same workspace')
                with launcher.volume_lock('different-volume', directory):
                    pass
            with self.assertRaises(RuntimeError):
                with launcher.volume_lock('same-volume', directory):
                    raise RuntimeError('interrupted preparation')
            with launcher.volume_lock('same-volume', directory):
                pass

    def test_volume_lock_rejects_symlinks_and_shared_storage(self):
        with tempfile.TemporaryDirectory() as folder:
            directory = Path(folder)
            (directory / 'bad.lock').symlink_to(directory / 'target')
            with self.assertRaises(OSError):
                with launcher.volume_lock('bad', directory):
                    pass
            directory.chmod(0o755)
            with self.assertRaises(ValueError):
                with launcher.volume_lock('other', directory):
                    pass

    def test_rootful_or_unenforced_runtime_is_rejected(self):
        for info in ({'SecurityOptions': ['name=seccomp']},
                     {'SecurityOptions': ['name=rootless'], 'CgroupVersion': '1', 'CgroupDriver': 'systemd'},
                     {'SecurityOptions': ['name=rootless'], 'CgroupVersion': '2', 'CgroupDriver': 'none'}):
            with self.subTest(info=info), patch.dict(launcher.os.environ, {}, clear=True), \
                 patch.object(launcher, 'output', side_effect=lambda command: 'unix:///run/user/1/docker.sock'
                              if 'context' in command else json.dumps(info)):
                with self.assertRaises(ValueError):
                    launcher.check_engine()
        with patch.dict(launcher.os.environ, {}, clear=True), \
             patch.object(launcher, 'output', side_effect=lambda command: 'unix:///run/user/1/docker.sock'
                          if 'context' in command else json.dumps(
                {'SecurityOptions': ['name=rootless'], 'CgroupVersion': '2', 'CgroupDriver': 'systemd'})):
            launcher.check_engine()
        with patch.dict(launcher.os.environ, {'DOCKER_HOST': 'ssh://remote'}, clear=True):
            with self.assertRaisesRegex(ValueError, 'local Docker daemon'):
                launcher.check_engine()

    def test_image_context_contains_only_reviewed_bootstrap_inputs(self):
        data = launcher.context(launcher.ROOT)
        with tarfile.open(fileobj=io.BytesIO(data)) as archive:
            names = archive.getnames()
            self.assertEqual(len(names), 15)
            self.assertTrue(all(name in ('Dockerfile', 'runner.py', 'fetch_wand125_release.py',
                                         'lake-manifest.json') or name.startswith('metadata/')
                                for name in names))
            self.assertFalse(any(name.endswith('.lean') or '.git' in name or '.aws' in name for name in names))

    def test_no_oversubscription_unlimited_memory_or_option_injection(self):
        with patch('os.sched_getaffinity', return_value={0, 1, 2, 3}):
            launcher.validate_options(options())
            for key, value in (('memory', '0'), ('memory', '16g --privileged'), ('volume', '-v/root:/root'),
                               ('cpus', 8), ('jobs', 3)):
                changed = vars(options()).copy()
                changed[key] = value
                with self.subTest(key=key), self.assertRaises(ValueError):
                    launcher.validate_options(SimpleNamespace(**changed))

    def test_cancellation_removes_container_before_releasing_client(self):
        process = Mock()
        process.wait.side_effect = [KeyboardInterrupt(), 0]
        process.poll.return_value = None
        with patch.object(launcher.subprocess, 'Popen', return_value=process), \
             patch.object(launcher.subprocess, 'run') as cleanup:
            with self.assertRaises(KeyboardInterrupt):
                launcher.execute_container(['docker', 'run', 'image', 'verify'])
            command = cleanup.call_args.args[0]
            self.assertEqual(command[:3], ['docker', 'rm', '--force'])
            self.assertTrue(command[3].startswith('eleven-square-run-'))
            process.terminate.assert_called_once()


class ProbeTests(unittest.TestCase):
    def test_probes_refuse_missing_restrictions_and_unexpected_environment(self):
        baseline = {'/proc/self/status': 'CapEff:\t00000000\nNoNewPrivs:\t1\nSeccomp:\t2\n',
                    '/proc/mounts': 'overlay / overlay ro,relatime 0 0\n',
                    '/sys/fs/cgroup/memory.max': str(16 * 1024**3),
                    '/sys/fs/cgroup/pids.max': '4096',
                    '/sys/fs/cgroup/cpu.max': '400000 100000'}
        environment = {'ISOLATION_CPU_BUDGET': '4', 'ISOLATION_MEMORY_BUDGET': str(16 * 1024**3),
                       'ISOLATION_HOST_CANARY_PATH': '/absent-host-canary-fixture'}
        original_read, original_iterdir = Path.read_text, Path.iterdir
        cases = [(None, None), ('/proc/self/status', baseline['/proc/self/status'].replace('Seccomp:\t2', 'Seccomp:\t0')),
                 ('/proc/mounts', 'overlay / overlay rw,relatime 0 0\n'),
                 ('/sys/fs/cgroup/memory.max', 'max'), ('/sys/fs/cgroup/pids.max', '5000'),
                 ('/sys/fs/cgroup/cpu.max', '500000 100000'), ('environment', 'AWS_SECRET_ACCESS_KEY')]
        for key, value in cases:
            files, variables = baseline.copy(), environment.copy()
            if key == 'environment':
                variables[value] = 'fixture'
            elif key:
                files[key] = value
            with self.subTest(restriction=key), tempfile.TemporaryDirectory() as folder, \
                 patch.object(runner, 'WORK', Path(folder)), \
                 patch.object(runner, 'TOOLS', Path(folder) / 'absent-readonly-image-tools'), \
                 patch.object(runner.os, 'getuid', return_value=10001), \
                 patch.dict(runner.os.environ, variables, clear=True), \
                 patch.object(Path, 'read_text', lambda path, **kw: files[str(path)] if str(path) in files
                              else original_read(path, **kw)), \
                 patch.object(Path, 'iterdir', lambda path: iter([Path('lo')]) if str(path) == '/sys/class/net'
                              else original_iterdir(path)), \
                 patch.object(runner.sys, 'stderr', io.StringIO()):
                if key is None:
                    runner.probe()
                else:
                    with self.assertRaises((RuntimeError, ValueError)):
                        runner.probe()


class SnapshotTests(unittest.TestCase):
    def archive(self, name, *, kind=tarfile.REGTYPE, mode=0o644):
        data = io.BytesIO()
        with tarfile.open(fileobj=data, mode='w') as archive:
            item = tarfile.TarInfo(name)
            item.type, item.mode = kind, mode
            if kind == tarfile.REGTYPE:
                item.size = 7
                archive.addfile(item, io.BytesIO(b'payload'))
            else:
                item.linkname = '/home/host/secrets'
                archive.addfile(item)
        data.seek(0)
        return data

    def test_rejects_traversal_links_devices_and_git_hooks(self):
        cases = [('..' + '/escape', tarfile.REGTYPE), ('/absolute', tarfile.REGTYPE),
                 ('x/.git/hooks/post-checkout', tarfile.REGTYPE), ('x\\escape', tarfile.REGTYPE),
                 ('link', tarfile.SYMTYPE), ('hardlink', tarfile.LNKTYPE), ('device', tarfile.CHRTYPE)]
        for name, kind in cases:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as folder:
                with self.assertRaises(ValueError):
                    runner.extract_snapshot(self.archive(name, kind=kind), Path(folder))
                self.assertEqual(list(Path(folder).rglob('*')), [])

    def test_source_contents_are_inert_and_special_mode_bits_are_stripped(self):
        with tempfile.TemporaryDirectory() as folder:
            destination = Path(folder)
            names = runner.extract_snapshot(self.archive('scripts/evil.py', mode=0o6755), destination)
            self.assertEqual(names, ['scripts/evil.py'])
            path = destination / names[0]
            self.assertEqual(path.read_bytes(), b'payload')
            self.assertEqual(path.stat().st_mode & 0o7777, 0o644)

    def test_extraction_never_overwrites_existing_files(self):
        with tempfile.TemporaryDirectory() as folder:
            destination = Path(folder)
            (destination / 'keep').write_text('original')
            with self.assertRaises(FileExistsError):
                runner.extract_snapshot(self.archive('keep'), destination)
            self.assertEqual((destination / 'keep').read_text(), 'original')


if __name__ == '__main__':
    unittest.main()
