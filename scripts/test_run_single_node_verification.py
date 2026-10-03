"""Exercise the actual batch shell flow with inert fixtures, without Slurm/Lean."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent


class BatchJobTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / 'scripts').mkdir()
        (self.root / 'bin').mkdir()
        (self.root / '.verification').mkdir()
        (self.root / 'verification').mkdir()
        self.write('scripts/verify.py', '''
import json, os, sys
from pathlib import Path
Path('verify-arguments.json').write_text(json.dumps(sys.argv[1:]))
code = int(os.environ.get('FIXTURE_VERIFY_EXIT', '0'))
if code:
    sys.exit(code)
Path('.verification/result.json').write_text(json.dumps({
    'status': 'OPTIMALITY_PROVED', 'global_optimality_proved': True,
    'checked_modules': 3}))
''')
        self.write('scripts/finalize_verification.py', '''
import json, os, sys
from pathlib import Path
Path('finalizer-called').touch()
assert sys.argv[1:] == ['--write']
code = int(os.environ.get('FIXTURE_FINALIZER_EXIT', '0'))
if code:
    sys.exit(code)
Path('verification/wand125-upgrade.json').write_text(json.dumps({
    'status': os.environ.get('FIXTURE_AUDIT_STATUS', 'OPTIMALITY_PROVED'),
    'global_optimality_proved': True, 'full_upgrade_verified': True,
    'explicit_native_admissions': 0, 'checked_modules': 3,
    'lean_toolchain': 'fixture-toolchain', 'mathlib_revision': 'fixture-mathlib'}))
Path('MANIFEST.json').write_text('{"fixture": true}')
''')
        self.write('bin/srun', f'#!{sys.executable}\n' + '''
import os, sys
args = sys.argv[1:]
while args[0].startswith('--'):
    args.pop(0)
os.execv(args[0], args)
''')
        (self.root / 'bin/srun').chmod(0o700)
        self.environment = {
            **os.environ,
            'PATH': str(self.root / 'bin') + os.pathsep + os.environ['PATH'],
            'SLURM_SUBMIT_DIR': str(self.root), 'SLURM_JOB_ID': '123',
            'ELEVEN_SQUARE_PYTHON': sys.executable,
            'ELEVEN_SQUARE_SETUP': '1', 'ELEVEN_SQUARE_MAX_PARALLEL': '3',
            'ELEVEN_SQUARE_JOBS': '2', 'ELEVEN_SQUARE_MEMORY_PERCENT': '85',
        }

    def write(self, path, content):
        (self.root / path).write_text(content, encoding='utf-8')

    def run_job(self, **overrides):
        return subprocess.run(
            ['bash', str(ROOT / 'scripts/run_single_node_verification.sbatch')],
            cwd=self.root, env={**self.environment, **overrides},
            capture_output=True, text=True, timeout=15)

    def receipt_path(self):
        return self.root / '.verification/completion-123.json'

    def check_documented_receipt(self):
        guide = (ROOT / 'LEAN_VERIFICATION_RUNBOOK.md').read_text()
        snippet = guide.split('python3.11 - "$proof_job_id" <<\'PY\'\n', 1)[1].split('\nPY\n', 1)[0]
        return subprocess.run([sys.executable, '-', '123'], input=snippet,
                              cwd=self.root, capture_output=True, text=True, timeout=15)

    def test_success_writes_job_specific_receipt_and_documented_check_passes(self):
        result = self.run_job()
        self.assertEqual(result.returncode, 0, result.stderr)
        receipt = json.loads(self.receipt_path().read_text())
        self.assertEqual(receipt['checked_modules'], 3)
        self.assertEqual(receipt['audit_sha256'], hashlib.sha256(
            (self.root / 'verification/wand125-upgrade.json').read_bytes()).hexdigest())
        self.assertEqual(receipt['manifest_sha256'], hashlib.sha256(
            (self.root / 'MANIFEST.json').read_bytes()).hexdigest())
        arguments = json.loads((self.root / 'verify-arguments.json').read_text())
        self.assertIn('--setup', arguments)
        self.assertEqual(arguments[arguments.index('--stop-file') + 1], '.verification/STOP')
        self.assertEqual(self.check_documented_receipt().returncode, 0)

    def test_resume_omits_setup_and_fresh(self):
        result = self.run_job(ELEVEN_SQUARE_SETUP='0')
        self.assertEqual(result.returncode, 0, result.stderr)
        arguments = json.loads((self.root / 'verify-arguments.json').read_text())
        self.assertNotIn('--setup', arguments)
        self.assertNotIn('--fresh', arguments)
        self.assertIn('--all', arguments)

    def test_verifier_failure_skips_finalization_and_receipt(self):
        self.assertEqual(self.run_job(FIXTURE_VERIFY_EXIT='9').returncode, 9)
        self.assertFalse((self.root / 'finalizer-called').exists())
        self.assertFalse(self.receipt_path().exists())

    def test_finalizer_failure_has_no_receipt(self):
        self.assertEqual(self.run_job(FIXTURE_FINALIZER_EXIT='7').returncode, 7)
        self.assertFalse(self.receipt_path().exists())

    def test_nonproof_audit_cannot_publish_completion(self):
        self.assertNotEqual(self.run_job(FIXTURE_AUDIT_STATUS='INCOMPLETE_BUILD').returncode, 0)
        self.assertFalse(self.receipt_path().exists())

    def test_stale_stop_request_refuses_before_verifier(self):
        (self.root / '.verification/STOP').touch()
        self.assertEqual(self.run_job().returncode, 2)
        self.assertFalse((self.root / 'verify-arguments.json').exists())

    def test_documented_check_rejects_changed_manifest(self):
        self.assertEqual(self.run_job().returncode, 0)
        self.write('MANIFEST.json', '{"changed": true}')
        self.assertNotEqual(self.check_documented_receipt().returncode, 0)


if __name__ == '__main__':
    unittest.main()
