#!/usr/bin/env python3
"""Exercise runner failure, privacy and cancellation behavior without invoking Lean."""
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tarfile
import tempfile
import time
import unittest

from verify_support import PUBLIC_TARGETS, public_audit_status

SCRIPT = Path(__file__).with_name('run_verification.sh')
GNU_TIMEOUT = shutil.which('timeout') or shutil.which('gtimeout')


class RunnerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'scripts').mkdir()
        (self.root / 'bin').mkdir()
        (self.root / '.verification').mkdir()
        for name in ('run_verification.sh', 'verification_artifacts.py', 'verify_support.py'):
            shutil.copy2(SCRIPT.with_name(name), self.root / 'scripts' / name)
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
        (self.root / 'lakefile.lean').write_text('-- fixture\n')
        (self.root / 'lake-manifest.json').write_text('{"packages": [], "packagesDir": ".lake/packages"}')
        for name in ['elan', 'lake']:
            self.executable(name, '#!/bin/sh\nexit 0\n')
        self.executable('git', '#!/bin/sh\nif [ "$1" = rev-parse ]; then printf "%040d\\n" 1; fi\n')
        self.env = dict(os.environ, PATH=str(self.root / 'bin') + os.pathsep + os.environ['PATH'],
                        ELAN_HOME=str(self.root / 'no-installed-elan'),
                        GITHUB_STEP_SUMMARY=str(self.root / '.verification/actions-summary.md'))
        self.proof_result = {
            **public_audit_status({name: ['propext'] for name in PUBLIC_TARGETS}, 0),
            'checked_modules': 1, 'axioms': {name: ['propext'] for name in PUBLIC_TARGETS}}
        self.write_success()

    def write_success(self, *, result_updates=None, audit_updates=None):
        result = dict(self.proof_result, **(result_updates or {}))
        audit = dict(self.proof_result, full_upgrade_verified=True, explicit_native_admissions=0)
        audit.update(audit_updates or {})
        self.write_verify('''
from pathlib import Path
import json
print("PRIVATE_DIAGNOSTIC /private/example")
print("[1/1] checking ElevenSquare.Verification")
print("[1/1] accepted ElevenSquare.Verification")
Path('.verification/result.json').write_text(%r)
''' % json.dumps(result))
        self.write_finalize("from pathlib import Path\nprint('private finalizer diagnostics')\n"
                            "Path('.verification/final-audit.json').write_text(%r)\n" % json.dumps(audit))

    def executable(self, name, text):
        path = self.root / 'bin' / name
        path.write_text(text)
        path.chmod(0o700)

    def write_verify(self, text):
        (self.root / 'scripts/verify.py').write_text(text)

    def write_finalize(self, text):
        (self.root / 'scripts/finalize_verification.py').write_text(text)

    def run_script(self, *args):
        return subprocess.run(['bash', 'scripts/run_verification.sh', *args], cwd=self.root,
                              env=self.env, capture_output=True, text=True, timeout=10)

    def summary(self):
        return json.loads((self.root / '.verification/runner-summary.json').read_text())

    def test_success_keeps_raw_logs_private(self):
        result = self.run_script('--ci', '--jobs', '4')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('[1/1] accepted ElevenSquare.Verification', result.stdout)
        self.assertIn('[1/1] checking ElevenSquare.Verification | elapsed', result.stdout)
        self.assertIn('100.00% of modules', result.stdout)
        self.assertIn('final audit pending', result.stdout)
        self.assertNotIn('PRIVATE_DIAGNOSTIC', result.stdout + result.stderr)
        self.assertNotIn('PRIVATE_DIAGNOSTIC', (self.root / '.verification/actions-summary.md').read_text())
        self.assertEqual(self.summary()['status'], 'OPTIMALITY_PROVED')
        logs = list((self.root / '.verification/runs').glob('*/replay.log'))
        self.assertIn('PRIVATE_DIAGNOSTIC', logs[0].read_text())

    def native_result(self):
        axioms = {name: ['Certificate.coverage._native.native_decide.ax_1_1'] for name in PUBLIC_TARGETS}
        return dict(public_audit_status(axioms, 0), checked_modules=1, axioms=axioms)

    def test_native_success_preserves_explicit_trust(self):
        self.proof_result = self.native_result()
        self.write_success()
        result = self.run_script('--ci')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        summary = self.summary()
        self.assertEqual(summary['status'], 'OPTIMALITY_PROVED_WITH_NATIVE_CERTIFICATES')
        self.assertEqual(summary['trust_model'], 'lean_kernel_and_native_compiler')
        self.assertEqual(summary['native_certificate_axioms'], self.proof_result['native_certificate_axioms'])
        self.assertEqual(summary['explicit_native_admissions'], 0)
        self.assertIn('additionally trust the Lean compiler', result.stdout)

    def test_native_success_rejects_bad_trust_and_admissions(self):
        self.proof_result = self.native_result()
        cases = [({'trust_model': 'lean_kernel'}, {}),
                 ({'native_certificate_axioms': []}, {}),
                 ({'status': 'OPTIMALITY_PROVED'}, {}),
                 ({}, {'explicit_native_admissions': 1}),
                 ({}, {'explicit_native_admissions': False}),
                 ({}, {'native_certificate_axioms': []}),
                 ({}, {'axioms': dict(self.proof_result['axioms'], unexpected=['sorryAx'])})]
        for result_changes, audit_changes in cases:
            with self.subTest(result=result_changes, audit=audit_changes):
                self.write_success(result_updates=result_changes, audit_updates=audit_changes)
                result = self.run_script()
                self.assertEqual(result.returncode, 1)
                self.assertEqual(self.summary()['status'], 'FAILED_NOT_VERIFIED')

    def test_missing_current_final_audit_cannot_reuse_previous_success(self):
        (self.root / '.verification/final-audit.json').write_text('{}')
        self.write_finalize('pass\n')
        result = self.run_script()
        self.assertEqual(result.returncode, 1)
        self.assertFalse((self.root / '.verification/final-audit.json').exists())
        self.assertEqual(self.summary()['status'], 'FAILED_NOT_VERIFIED')

    def test_progress_reports_percentage_and_rough_eta_without_cache_samples(self):
        self.write_verify('''
print('[1/20] cached ElevenSquare.Cached')
for index in range(2, 13):
    print(f'[{index}/20] accepted ElevenSquare.Module{index}')
raise SystemExit(1)
''')
        result = self.run_script()
        self.assertEqual(result.returncode, 1)
        lines = [line for line in result.stdout.splitlines() if '% of modules' in line]
        self.assertEqual(len(lines), 12)
        self.assertIn('5.00% of modules', lines[0])
        self.assertIn('collecting samples', lines[9])
        self.assertRegex(lines[10], r'55\.00% of modules \| elapsed \d+:\d+:\d+ \| rough ETA: \d+:\d+:\d+$')

    def test_progress_failure_does_not_report_completion_eta(self):
        self.write_verify("print('[1/1] failed ElevenSquare.Bad'); raise SystemExit(1)\n")
        result = self.run_script()
        self.assertEqual(result.returncode, 1)
        self.assertIn('rough ETA: unavailable (module failure)', result.stdout)
        self.assertNotIn('final audit pending', result.stdout)

    def test_failed_replay_cannot_reuse_previous_success(self):
        (self.root / '.verification/result.json').write_text('{"status": "OPTIMALITY_PROVED"}')
        self.write_verify("print('PRIVATE_DIAGNOSTIC'); raise SystemExit(3)\n")
        self.write_finalize("raise AssertionError('must not run')\n")
        result = self.run_script()
        self.assertEqual(result.returncode, 1)
        self.assertFalse((self.root / '.verification/result.json').exists())
        self.assertEqual(self.summary()['status'], 'FAILED_NOT_VERIFIED')
        self.assertNotIn('PRIVATE_DIAGNOSTIC', result.stdout + result.stderr)

    def test_failed_replay_surfaces_bounded_compiler_errors(self):
        module = 'Sqpack.S11Opt.Bundled.F50.Leaves023'
        source = module.replace('.', '/') + '.lean'
        error = (source + ":9:74: error: Tactic `native_decide` failed. Error: "
                 "failed to compile definition, consider marking it as 'noncomputable' "
                 "because it depends on 'opts5', which is 'noncomputable'")
        self.write_verify("print('[336/7920] checking %s')\n" % module
                          + "print('PRIVATE_DIAGNOSTIC /private/example')\n"
                          + "print(%r)\n" % error
                          + "print(\"declaration depends on axioms: [sorryAx]\")\n"
                          + "raise SystemExit(1)\n")
        result = self.run_script('--ci')
        self.assertEqual(result.returncode, 1)
        self.assertIn(error, result.stdout)
        self.assertIn('Module log: .verification/' + module + '.log', result.stdout)
        self.assertNotIn('PRIVATE_DIAGNOSTIC', result.stdout + result.stderr)
        self.assertNotIn('sorryAx', result.stdout)
        self.assertEqual(self.summary()['status'], 'FAILED_NOT_VERIFIED')

    def test_failed_axiom_audit_does_not_point_to_completed_module_log(self):
        for status in ('accepted', 'cached'):
            with self.subTest(final_module_status=status):
                self.write_verify("""
print('[1/2] checking ElevenSquare.Completed')
print('[1/2] accepted ElevenSquare.Completed')
if %r == 'accepted':
    print('[2/2] checking ElevenSquare.Verification')
print('[2/2] %s ElevenSquare.Verification')
raise SystemExit('ElevenSquare.Verification: unexpected axioms in declaration')
""" % (status, status))
                result = self.run_script('--ci')
                self.assertEqual(result.returncode, 1)
                self.assertIn('[1/2] accepted ElevenSquare.Completed', result.stdout)
                self.assertIn('[2/2] ' + status + ' ElevenSquare.Verification', result.stdout)
                self.assertNotIn('Module log:', result.stdout)
                self.assertEqual(self.summary()['status'], 'FAILED_NOT_VERIFIED')

    def test_compiler_error_excerpt_redacts_paths_and_limits_output(self):
        self.write_verify("""
from pathlib import Path
print('[1/1] checking ElevenSquare.Bad')
print(str(Path.cwd()) + '/ElevenSquare/Bad.lean:1:1: error: cannot open /Users/Private Person/secret')
print('ElevenSquare/Bad.lean:2:1: error: cannot open C:\\\\Users\\\\Private Person\\\\secret')
for index in range(3, 20):
    print(f'ElevenSquare/Bad.lean:{index}:1: error: ' + 'x' * 2000)
raise SystemExit(1)
""")
        result = self.run_script()
        self.assertEqual(result.returncode, 1)
        diagnostics = [line for line in result.stdout.splitlines() if ': error:' in line]
        self.assertEqual(len(diagnostics), 3)
        self.assertTrue(all(len(line) <= 602 for line in diagnostics))
        self.assertIn('cannot open [local path omitted]', result.stdout)
        self.assertNotIn('Private Person', result.stdout + result.stderr)
        self.assertNotIn(str(self.root), result.stdout + result.stderr)

    def test_finalizer_failure_prevents_success(self):
        self.write_finalize("raise SystemExit('PRIVATE_DIAGNOSTIC')\n")
        result = self.run_script()
        self.assertEqual(result.returncode, 1)
        self.assertEqual(self.summary()['status'], 'FAILED_NOT_VERIFIED')
        self.assertNotIn('PRIVATE_DIAGNOSTIC', result.stdout + result.stderr)

    def test_missing_new_result_fails_closed(self):
        (self.root / '.verification/result.json').write_text('{"status": "OPTIMALITY_PROVED"}')
        self.write_verify('pass\n')
        result = self.run_script()
        self.assertEqual(result.returncode, 1)
        self.assertEqual(self.summary()['status'], 'FAILED_NOT_VERIFIED')

    def test_plan_does_not_bootstrap_or_compile(self):
        self.write_verify("import sys; assert '--all' in sys.argv and '--plan' in sys.argv\n")
        self.executable('elan', '#!/bin/sh\nexit 99\n')
        self.write_finalize('raise AssertionError("must not run")\n')
        result = self.run_script('--plan', '--bootstrap')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.summary()['status'], 'SOURCE_PLAN_PASSED_NOT_COMPILED')

    def test_invalid_job_input_never_executes(self):
        result = self.run_script('--jobs', '1; touch unexpected')
        self.assertEqual(result.returncode, 2)
        self.assertFalse((self.root / 'unexpected').exists())

    def test_cancellation_stops_verifier_and_its_child(self):
        self.write_verify('''
from pathlib import Path
import os, signal, subprocess, sys, time
child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'])
def stop(*args):
    child.terminate()
    child.wait(timeout=5)
    raise SystemExit(130)
signal.signal(signal.SIGTERM, stop)
Path('.verification/children').write_text(str(os.getpid()) + ' ' + str(child.pid))
while True:
    time.sleep(1)
''')
        process = subprocess.Popen(['bash', 'scripts/run_verification.sh'], cwd=self.root,
                                   env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            marker = self.root / '.verification/children'
            until = time.monotonic() + 5
            while not marker.exists() and time.monotonic() < until:
                time.sleep(0.02)
            self.assertTrue(marker.exists(), 'Verifier fixture failed to start')
            child_pids = [int(value) for value in marker.read_text().split()]
            process.send_signal(signal.SIGTERM)
            stdout, stderr = process.communicate(timeout=12)
            self.assertEqual(process.returncode, 130, stdout + stderr)
            self.assertEqual(self.summary()['status'], 'INTERRUPTED_NOT_VERIFIED')
            for pid in child_pids:
                with self.assertRaises(ProcessLookupError):
                    os.kill(pid, 0)
        finally:
            if process.poll() is None:
                process.terminate()
                process.communicate(timeout=12)

    def check_interruption_with_stubborn_descendant(self, *, use_timeout=False):
        self.write_verify('''
from pathlib import Path
import hashlib, json, os, signal, subprocess, sys, time
state = Path('.verification')
obj = Path('.lake/build/lib/lean/Sqpack/Completed.olean')
obj.parent.mkdir(parents=True)
obj.write_bytes(b'accepted fixture object')
(state / 'Sqpack.Completed.log').write_text('accepted fixture log')
(state / 'Sqpack.Completed.json').write_text(json.dumps({
    'module': 'Sqpack.Completed', 'status': 'accepted', 'inputs': {},
    'object_sha256': hashlib.sha256(obj.read_bytes()).hexdigest()}))
print('[1/2] accepted Sqpack.Completed', flush=True)
print('[2/2] checking Sqpack.Working', flush=True)
signal.signal(signal.SIGTERM, lambda *_: os._exit(130))
child = subprocess.Popen([sys.executable, 'scripts/stubborn.py'])
Path('.verification/verifier-pid').write_text(str(os.getpid()))
while True:
    time.sleep(1)
''')
        (self.root / 'scripts/stubborn.py').write_text('''
from pathlib import Path
import os, signal, time
signal.signal(signal.SIGTERM, signal.SIG_IGN)
Path('.verification/stubborn-pid').write_text(str(os.getpid()))
while True:
    Path('.lake/build/lib/lean/Sqpack/Working.olean').write_text(str(time.monotonic()))
    time.sleep(0.01)
''')
        self.write_finalize("from pathlib import Path; Path('unexpected-finalizer').touch()\n")
        command = ['bash', 'scripts/run_verification.sh', '--ci']
        if use_timeout:
            command = [GNU_TIMEOUT, '--signal=TERM', '--kill-after=5s', '5s', *command]
        process = subprocess.Popen(command, cwd=self.root, env=self.env,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        pids = []
        try:
            markers = [self.root / '.verification' / name for name in
                       ('verifier-pid', 'stubborn-pid')]
            until = time.monotonic() + 4
            while not all(path.exists() for path in markers) and time.monotonic() < until:
                time.sleep(0.02)
            self.assertTrue(all(path.exists() for path in markers), 'Process fixture failed to start')
            pids = [int(path.read_text()) for path in markers]
            if not use_timeout:
                process.send_signal(signal.SIGTERM)
            stdout, stderr = process.communicate(timeout=15)
            self.assertEqual(process.returncode, 124 if use_timeout else 130, stdout + stderr)
            self.assertEqual(self.summary()['status'], 'INTERRUPTED_NOT_VERIFIED')
            self.assertFalse((self.root / 'unexpected-finalizer').exists())

            def running(pid):
                # Orphaned descendants may briefly remain as zombies on Linux.
                try:
                    os.kill(pid, 0)
                except ProcessLookupError:
                    return False
                if Path('/proc').is_dir():
                    try:
                        status = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()[0]
                    except FileNotFoundError:
                        return False
                    return status != 'Z'
                return True

            until = time.monotonic() + 2
            while any(running(pid) for pid in pids) and time.monotonic() < until:
                time.sleep(0.02)
            self.assertFalse(any(running(pid) for pid in pids), 'Compilation descendant survived shutdown')
            packaged = subprocess.run(['python3', 'scripts/verification_artifacts.py', 'package'],
                                     cwd=self.root, env=self.env, capture_output=True,
                                     text=True, timeout=10)
            self.assertEqual(packaged.returncode, 0, packaged.stdout + packaged.stderr)
            artifacts = self.root / '.verification/artifacts'
            with tarfile.open(artifacts / 'checkpoint.tar') as checkpoint:
                self.assertEqual(set(checkpoint.getnames()), {
                    '.verification/Sqpack.Completed.json', '.verification/Sqpack.Completed.log',
                    '.lake/build/lib/lean/Sqpack/Completed.olean'})
            self.assertEqual(json.loads((artifacts / 'evidence/summary.json').read_text())['status'],
                             'INTERRUPTED_NOT_VERIFIED')
            self.assertFalse((artifacts / 'evidence/result.json').exists())
            self.assertFalse((artifacts / 'evidence/final-audit.json').exists())
        finally:
            for marker in ('verifier-pid', 'stubborn-pid'):
                path = self.root / '.verification' / marker
                if path.exists():
                    try:
                        os.kill(int(path.read_text()), signal.SIGKILL)
                    except ProcessLookupError:
                        pass
            if process.poll() is None:
                process.kill()
            process.communicate(timeout=5)

    def test_cancellation_stops_descendant_even_when_verifier_exits_first(self):
        self.check_interruption_with_stubborn_descendant()

    @unittest.skipUnless(GNU_TIMEOUT, 'GNU timeout is unavailable on this platform')
    def test_soft_timeout_preserves_only_completed_checkpoint_modules(self):
        self.check_interruption_with_stubborn_descendant(use_timeout=True)


if __name__ == '__main__':
    unittest.main()
