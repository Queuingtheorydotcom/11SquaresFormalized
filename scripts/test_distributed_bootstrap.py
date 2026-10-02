"""Offline launch-gate, Windows parser/help, and scoped-environment regressions."""
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import textwrap
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / '.github/workflows/distributed-replay.yml'
TEXT = WORKFLOW.read_text(encoding='utf-8')
gate_text = TEXT.split('# BEGIN_GATE_PY\n', 1)[1].split('          # END_GATE_PY', 1)[0]
GATE = {'__name__': 'test_gate'}
exec(compile(textwrap.dedent(gate_text), '<distributed-launch-gate>', 'exec'), GATE)
POWERSHELL = shutil.which('powershell.exe') or shutil.which('pwsh.exe')


class LaunchGateTests(unittest.TestCase):
    def setUp(self):
        self.plan = json.dumps({'shard_count': 18, 'platform': 'windows-x86_64'}).encode()
        self.request = {'mode': 'pilot', 'plan_sha256': hashlib.sha256(self.plan).hexdigest(),
                        'previous_run_id': None}

    def test_pilot_is_one_worker_and_fleet_is_explicit_sixteen(self):
        self.assertEqual(GATE['validate_request'](self.request, self.plan), ({'worker': [2]}, None))
        fleet = dict(self.request, mode='fleet', previous_run_id='12345')
        self.assertEqual(GATE['validate_request'](fleet, self.plan), ({'worker': list(range(2, 18))}, '12345'))

    def test_bad_or_extra_request_fields_fail_closed(self):
        for changed in ({'mode': 'all'}, {'mode': None}, {'plan_sha256': '0' * 64},
                        {'previous_run_id': 123}, {'previous_run_id': '0'},
                        {'previous_run_id': '123\nunsafe'}, {'previous_run_id': '../123'},
                        {'previous_run_id': '9' * 21}, {'unapproved': True}):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                GATE['validate_request'](dict(self.request, **changed), self.plan)
        for field in self.request:
            missing = dict(self.request)
            missing.pop(field)
            with self.subTest(missing=field), self.assertRaises(ValueError):
                GATE['validate_request'](missing, self.plan)

    def test_exact_plan_bytes_and_windows_eighteen_are_required(self):
        with self.assertRaises(ValueError):
            GATE['validate_request'](self.request, self.plan + b'\n')
        for plan in ({'shard_count': 16, 'platform': 'windows-x86_64'},
                     {'shard_count': 18, 'platform': 'linux-x86_64'}):
            raw = json.dumps(plan).encode()
            request = dict(self.request, plan_sha256=hashlib.sha256(raw).hexdigest())
            with self.assertRaises(ValueError):
                GATE['validate_request'](request, raw)

    def test_duplicate_marker_keys_are_rejected(self):
        with self.assertRaises(ValueError):
            json.loads('{"mode":"pilot","mode":"fleet"}', object_pairs_hook=GATE['unique_object'])

    def test_missing_marker_never_emits_a_matrix(self):
        with tempfile.TemporaryDirectory() as temporary:
            old = Path.cwd()
            try:
                os.chdir(temporary)
                with mock.patch.dict(os.environ, {'LAUNCH_EVENT': 'push', 'GITHUB_OUTPUT': 'gate-output'}), \
                     contextlib.redirect_stdout(io.StringIO()) as output:
                    self.assertEqual(GATE['main'](), 1)
                self.assertFalse(Path('gate-output').exists())
                self.assertIn('LAUNCH_REFUSED', output.getvalue())
                self.assertNotIn(temporary, output.getvalue())
                self.assertTrue(Path('.verification/distributed/launch.log').is_file())
            finally:
                os.chdir(old)

    def test_workflow_only_launches_explicit_requests_and_uploads_one_bounded_archive(self):
        triggers = TEXT.split('\non:\n', 1)[1].split('\npermissions:', 1)[0]
        self.assertIn('branches: [codex/stronger-computer-handoff-20261002]', triggers)
        self.assertIn('paths: [.github/distributed-launch.json]', triggers)
        self.assertIn('default: pilot', triggers)
        self.assertNotIn('schedule:', triggers)
        self.assertNotIn('pull_request:', triggers)
        self.assertIn('  contents: read\n  actions: read', TEXT)
        self.assertNotIn('secrets.', TEXT)
        self.assertIn('github.event.repository.private == false', TEXT)
        self.assertIn('actions/checkout@11bd71901bbe5b1630ceea73d27597364c9af683', TEXT)
        self.assertIn('actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02', TEXT)
        self.assertIn('actions/download-artifact@d3f86a106a0bac45b974a628896c90dbdf5c8093', TEXT)
        self.assertEqual(TEXT.count('uses: actions/upload-artifact@'), 1)
        self.assertIn('path: ${{ steps.checkpoint.outputs.archive }}', TEXT)
        self.assertIn('retention-days: 1', TEXT)
        self.assertIn('compression-level: 0', TEXT)
        self.assertGreaterEqual(TEXT.count('536870912'), 2)
        self.assertIn('--max-parallel 1 --memory-percent 95 --budget-seconds 14400', TEXT)
        self.assertNotIn('distributed_worker.py final', TEXT)
        self.assertNotIn('finalize_verification.py', TEXT)

    def test_short_workspace_copy_is_hosted_only_non_destructive_and_disk_guarded(self):
        block = TEXT.split('- name: Prepare a short hosted-only workspace', 1)[1].split('- name: Explicitly restore', 1)[0]
        for check in ("$env:GITHUB_ACTIONS -cne 'true'", "$env:RUNNER_ENVIRONMENT -cne 'github-hosted'",
                      "$env:RUNNER_OS -cne 'Windows'", 'Test-Path -LiteralPath $destination',
                      'AvailableFreeSpace -lt 34359738368', 'Copy-Item -LiteralPath $env:GITHUB_WORKSPACE'):
            self.assertIn(check, block)
        self.assertNotIn('Remove-Item', block)
        self.assertNotIn('Move-Item', block)
        self.assertEqual(TEXT.count('working-directory: C:\\FORMALIZATION_CONTAINER'), 4)


@unittest.skipUnless(os.name == 'nt' and POWERSHELL, 'Windows PowerShell required')
class WindowsBootstrapTests(unittest.TestCase):
    def run_ps(self, arguments, cwd=ROOT, env=None):
        result = subprocess.run([POWERSHELL, '-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass', *arguments], cwd=cwd,
                                env=env, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, 'Offline PowerShell check failed; no installer was invoked')
        return result.stdout

    def test_help_has_no_setup_or_external_process_side_effects(self):
        for script in ('distributed_env.ps1', 'distributed_setup.ps1'):
            output = self.run_ps(['-File', 'scripts/' + script, '-Help'])
            self.assertNotIn(str(ROOT), output)
            self.assertNotIn('SETUP_PREFLIGHT_PASS', output)
        setup = (ROOT / 'scripts/distributed_setup.ps1').read_text(encoding='utf-8')
        self.assertLess(setup.index('if ($Help)'), setup.index("$ErrorActionPreference"))
        self.assertIn("if (-not $Install) { throw", setup)
        self.assertIn("'-y', '--no-modify-path', '--default-toolchain', 'none'", setup)
        self.assertIn('be5e92a2dfdd8176099b2db0b810c27237c9054f1e5db1126f4f2a1134773b25', setup)
        self.assertNotIn('-Headers', setup)
        self.assertNotIn('git config --global', setup)

    def test_powershell_sources_and_workflow_blocks_parse(self):
        blocks = []
        lines = TEXT.splitlines()
        for index, line in enumerate(lines):
            if line == '        run: |':
                body = []
                for following in lines[index + 1:]:
                    if following and not following.startswith('          '):
                        break
                    body.append(following[10:] if following else '')
                blocks.append('\n'.join(body))
        with tempfile.TemporaryDirectory() as temporary:
            stage = Path(temporary)
            sources = [ROOT / 'scripts/distributed_env.ps1', ROOT / 'scripts/distributed_setup.ps1']
            for index, block in enumerate(blocks):
                path = stage / f'workflow-{index}.ps1'
                path.write_text(block, encoding='utf-8')
                sources.append(path)
            for source in sources:
                quoted = str(source).replace("'", "''")
                command = "$errors=$null; $tokens=$null; [System.Management.Automation.Language.Parser]::ParseFile('" + quoted + "',[ref]$tokens,[ref]$errors) | Out-Null; if (@($errors).Count) { exit 1 }"
                self.run_ps(['-Command', command])

    def test_environment_is_repo_scoped_and_reuses_existing_scoped_elan(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'scripts').mkdir()
            shutil.copyfile(ROOT / 'scripts/distributed_env.ps1', root / 'scripts/distributed_env.ps1')
            (root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
            (root / 'lake-manifest.json').write_text('{"packages":[{"name":"mathlib"}]}')
            (root / 'work/tooling/elan').mkdir(parents=True)
            env = os.environ.copy()
            env.update(GIT_CONFIG_COUNT='1', GIT_CONFIG_KEY_0='test.preserved', GIT_CONFIG_VALUE_0='retained',
                       FORMALIZATION_DISTRIBUTED_ROOT='')
            command = r"""
            . ./scripts/distributed_env.ps1
            $root = (Get-Location).Path
            $paths = @($env:ELAN_HOME, $env:TEMP, $env:TMP, $env:XDG_CACHE_HOME, $env:MATHLIB_CACHE_DIR, $env:CURL_HOME)
            $scoped = @($paths | Where-Object { -not $_.StartsWith($root + '\', [StringComparison]::OrdinalIgnoreCase) }).Count -eq 0
            $firstCount = $env:GIT_CONFIG_COUNT
            . ./scripts/distributed_env.ps1
            @{ scoped=$scoped; reused=($env:ELAN_HOME -eq (Join-Path $root 'work\tooling\elan'));
               preserved=($env:GIT_CONFIG_KEY_0 -eq 'test.preserved' -and $env:GIT_CONFIG_VALUE_0 -eq 'retained');
               idempotent=($firstCount -eq $env:GIT_CONFIG_COUNT); packages=($env:GIT_CONFIG_COUNT -eq '3');
               resolver=([bool](Get-Command Resolve-DistributedPython)) } | ConvertTo-Json -Compress
            """
            result = json.loads(self.run_ps(['-Command', command], cwd=root, env=env))
            self.assertTrue(all(result.values()))


if __name__ == '__main__':
    unittest.main()
