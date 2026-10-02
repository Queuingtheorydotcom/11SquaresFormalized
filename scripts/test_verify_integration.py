"""Exercise the actual verifier on a tiny fixture with an explicitly fake compiler."""
import io
import json
from pathlib import Path
import re
import runpy
import signal
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

from test_verify_scheduler import FakeProcess, PermissiveGuard
from verify_scheduler import CheckoutLock
from verify_support import PUBLIC_TARGETS


class Output(io.StringIO):
    def reconfigure(self, **_):
        pass


class VerifierIntegrationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / 'ElevenSquare').mkdir()
        (self.root / 'Sqpack').mkdir()
        (self.root / 'verification').mkdir()
        self.write('lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        self.write('lakefile.lean', '-- fixture\n')
        self.write('lake-manifest.json', json.dumps({'packages': [{'name': 'mathlib', 'rev': 'fixture'}]}))
        self.write('verification/admissions.json', '{"sites": []}')
        self.write('verification/wand125-integration.json', json.dumps({
            'lean_toolchain': 'leanprover/lean4:v4.34.1', 'mathlib_revision': 'fixture'}))
        self.write('ElevenSquare.lean', '-- umbrella fixture\n')
        self.write('Sqpack.lean', '-- independent umbrella fixture\n')
        self.write('ElevenSquare/Seed.lean', '-- seed fixture\n')
        self.write('ElevenSquare/Branch.lean', 'import ElevenSquare.Seed\n')
        self.write('ElevenSquare/Other.lean', '#print axioms Other.clean\n')
        self.write('ElevenSquare/Verification.lean',
                   'import ElevenSquare.Branch\nimport ElevenSquare.Other\n' +
                   ''.join('#print axioms ' + target + '\n' for target in sorted(PUBLIC_TARGETS)))
        self.compiled = []
        self.guard_factory = lambda **_: PermissiveGuard()

    def write(self, path, text):
        (self.root / path).write_text(text, encoding='utf-8')

    def run_verifier(self, *options):
        checks = types.ModuleType('check_sources')
        checks.ROOT = self.root
        checks.check = lambda **_: {'admissions': 0}
        checks.code_only = lambda text: text
        checks.imports = lambda path: re.findall(r'^import (\S+)', path.read_text(encoding='utf-8'), re.M)
        resources = types.ModuleType('verify_resources')
        resources.ResourceGuard = self.guard_factory
        owners = []

        class Owner(CheckoutLock):
            def __init__(self, path):
                super().__init__(path)
                owners.append(self)

        def fake_compiler(command, **kwargs):
            self.assertEqual(command[0], 'explicit-fake-compiler')
            self.assertEqual(kwargs['cwd'], self.root)
            source = self.root / command[-1]
            module = '.'.join(source.relative_to(self.root).with_suffix('').parts)
            self.compiled.append(module)
            target = self.root / command[command.index('-o') + 1]
            # Keep fake object bytes unchanged across source edits: transitive
            # input hashes must still invalidate downstream receipts.
            target.write_bytes(('fake object: ' + module).encode())
            queries = re.findall(r'^#print axioms (\S+)', source.read_text(encoding='utf-8'), re.M)
            kwargs['stdout'].write(''.join(
                "'" + name + "' depends on axioms: [propext]\n" for name in queries).encode())
            return FakeProcess(ticks=2)

        previous_term = signal.getsignal(signal.SIGTERM)
        try:
            with patch.dict(sys.modules, {'check_sources': checks, 'verify_resources': resources}), \
                    patch('verify_scheduler.CheckoutLock', Owner), \
                    patch('atexit.register'), patch('shutil.which', side_effect=lambda name, **_: name), \
                    patch('subprocess.check_output', side_effect=[
                        json.dumps({'lean': 'explicit-fake-compiler', 'path': ''}), 'Lean 4.34.1']), \
                    patch('subprocess.Popen', side_effect=fake_compiler), \
                    patch.object(sys, 'argv', ['verify.py', '--all', *options]), \
                    patch.object(sys, 'stdout', Output()), patch.object(sys, 'stderr', Output()):
                return runpy.run_path(str(Path(__file__).with_name('verify.py')))
        finally:
            signal.signal(signal.SIGTERM, previous_term)
            for owner in owners:
                owner.close()

    def receipts(self):
        return {path.stem: path.read_bytes() for path in (self.root / '.verification').glob('*.json')
                if path.stem.startswith(('ElevenSquare', 'Sqpack'))}

    def test_parallel_resume_keeps_old_argv_and_rechecks_transitive_changes(self):
        self.run_verifier('--jobs', '1')
        before = self.receipts()
        self.assertEqual(len(before), 6)
        self.compiled.clear()
        self.run_verifier('--jobs', '4', '--max-parallel', '2')
        self.assertEqual(self.compiled, [])
        self.assertEqual(self.receipts(), before)
        self.write('ElevenSquare/Seed.lean', '-- changed seed fixture\n')
        self.run_verifier('--jobs', '4', '--max-parallel', '2')
        self.assertEqual(set(self.compiled), {
            'ElevenSquare.Seed', 'ElevenSquare.Branch', 'ElevenSquare.Verification'})
        for module, raw in self.receipts().items():
            expected = '-j4' if module in self.compiled else '-j1'
            self.assertEqual(json.loads(raw)['inputs']['arguments'][0], expected)
        result = json.loads((self.root / '.verification/result.json').read_text())
        self.assertEqual(result['checked_modules'], 6)
        self.assertTrue(result['global_optimality_proved'])
        self.assertFalse(list(self.root.rglob('*.checking')))

    def test_cached_logs_still_require_complete_clean_axiom_audits(self):
        self.run_verifier('--max-parallel', '2')
        self.compiled.clear()
        log = self.root / '.verification/ElevenSquare.Other.log'
        log.write_text("'Other.clean' depends on axioms: [sorryAx]\n", encoding='utf-8')
        with self.assertRaisesRegex(SystemExit, 'Unapproved axioms'):
            self.run_verifier('--max-parallel', '2')
        self.assertEqual(self.compiled, [])
        log.write_text('', encoding='utf-8')
        with self.assertRaisesRegex(SystemExit, 'Expected 1 axiom outputs'):
            self.run_verifier('--max-parallel', '2')
        log.write_bytes(b'\xe2\x82')
        with self.assertRaisesRegex(SystemExit, 'utf-8.*decode'):
            self.run_verifier('--max-parallel', '2')

    def test_shared_jobs_map_recompiles_mismatches_without_relabeling(self):
        self.run_verifier('--jobs', '1')
        before = self.receipts()
        self.compiled.clear()
        jobs = self.root / 'worker-counts.json'
        jobs.write_text(json.dumps({'ElevenSquare.Seed': 4}), encoding='utf-8')
        self.run_verifier('--jobs', '1', '--jobs-file', str(jobs))
        self.assertEqual(set(self.compiled), {
            'ElevenSquare.Seed', 'ElevenSquare.Branch', 'ElevenSquare.Verification'})
        after = self.receipts()
        self.assertEqual(json.loads(after['ElevenSquare.Seed'])['inputs']['arguments'][0], '-j4')
        self.assertEqual(after['ElevenSquare.Other'], before['ElevenSquare.Other'])
        self.compiled.clear()
        self.run_verifier('--jobs', '4', '--jobs-file', str(jobs))
        self.assertEqual(self.compiled, [])
        self.assertEqual(self.receipts(), after)

    def test_shared_jobs_map_rejects_invalid_module_and_worker_values(self):
        jobs = self.root / 'worker-counts.json'
        for value in ([4], {'ElevenSquare.Missing': 4}, {'ElevenSquare.Seed': True},
                      {'ElevenSquare.Seed': 0}, {'ElevenSquare.Seed': 1.5},
                      {'ElevenSquare.Seed': 2**32}):
            with self.subTest(value=value):
                jobs.write_text(json.dumps(value), encoding='utf-8')
                with self.assertRaisesRegex(SystemExit, 'Invalid shared worker-count map'):
                    self.run_verifier('--jobs-file', str(jobs))
        self.assertEqual(self.compiled, [])

    def test_truncated_interrupted_diagnostic_allows_exclusive_retry(self):
        class Pressure(PermissiveGuard):
            triggered = False

            def assess(self, active):
                if len(active) > 1 and not self.triggered:
                    self.triggered = True
                    victim = max(active, key=lambda m: active[m].started)
                    active[victim].stream.write(b'\xe2\x82')
                    return types.SimpleNamespace(allow_start=False, terminate_module=victim,
                                                 reason='test_pressure')
                return super().assess(active)
        self.guard_factory = lambda **_: Pressure()
        self.run_verifier('--max-parallel', '2')
        self.assertEqual(len(self.compiled), 7)
        result = json.loads((self.root / '.verification/result.json').read_text())
        self.assertEqual(result['checked_modules'], 6)
        self.assertTrue(result['global_optimality_proved'])
        self.assertFalse(list(self.root.rglob('*.checking')))


if __name__ == '__main__':
    unittest.main()
