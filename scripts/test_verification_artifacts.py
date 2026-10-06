"""Artifact isolation, checkpoint round trips, and automatic restore selection."""
import io
import json
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest
from unittest import mock

import verification_artifacts as artifacts
import test_finalize_verification as audit_fixtures
import finalize_verification
from finalize_verification import collect_audit
from verify_support import PUBLIC_TARGETS, public_audit_status


class ArtifactTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.state = self.root / '.verification'
        self.state.mkdir()
        for name in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json']:
            (self.root / name).write_text('fixture')
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True)
        subprocess.run(['git', '-C', str(self.root), '-c', 'user.name=Test',
                        '-c', 'user.email=test@example.invalid', 'commit', '--allow-empty',
                        '-qm', 'fixture'], check=True)
        self.receipt = self.state / 'ElevenSquare.Test.json'
        self.obj = self.root / '.lake/build/lib/lean/ElevenSquare/Test.olean'
        self.obj.parent.mkdir(parents=True)
        self.obj.write_bytes(b'compiled fixture')
        (self.state / 'ElevenSquare.Test.log').write_text('diagnostic')
        artifacts.write_json(self.receipt, {
            'module': 'ElevenSquare.Test', 'status': 'accepted',
            'object_sha256': artifacts.sha(self.obj), 'elapsed_seconds': 2.0,
            'inputs': {'arguments': ['-j64']}})
        artifacts.write_json(self.state / 'runner-summary.json', {'status': 'FAILED_NOT_VERIFIED'})

    def test_failed_run_preserves_checkpoint_and_diagnostics_but_not_false_success(self):
        artifacts.write_json(self.state / 'result.json', {'status': 'OPTIMALITY_PROVED'})
        (self.state / 'private-handoff.zip').write_text('excluded')
        (self.state / 'credentials.json').write_text('excluded')
        (self.state / 'elan-init').write_text('excluded')
        (self.root / '.lake/packages').mkdir()
        (self.root / '.lake/packages/credentials').write_text('excluded')
        artifacts.package(self.root)
        output = self.state / 'artifacts'
        self.assertFalse((output / 'evidence/result.json').exists())
        self.assertIn('2.0', (output / 'evidence/module-timings.csv').read_text())
        with tarfile.open(output / 'checkpoint.tar') as archive:
            self.assertEqual(set(archive.getnames()), {
                '.verification/ElevenSquare.Test.json', '.verification/ElevenSquare.Test.log',
                '.lake/build/lib/lean/ElevenSquare/Test.olean'})
        with tarfile.open(output / 'diagnostics.tar') as archive:
            self.assertIn('.verification/result.json', archive.getnames())
            self.assertNotIn('.verification/private-handoff.zip', archive.getnames())
            self.assertNotIn('.verification/credentials.json', archive.getnames())
        with tempfile.TemporaryDirectory() as target:
            restored = Path(target).resolve()
            artifacts.extract_checkpoint(restored, output / 'checkpoint.tar')
            self.assertEqual((restored / self.obj.relative_to(self.root)).read_bytes(), self.obj.read_bytes())
            self.assertEqual((restored / self.receipt.relative_to(self.root)).read_bytes(), self.receipt.read_bytes())

    def test_success_requires_final_audit_and_exports_it(self):
        artifacts.write_json(self.state / 'runner-summary.json', {'status': 'OPTIMALITY_PROVED'})
        axioms = {name: ['propext'] for name in PUBLIC_TARGETS}
        result = dict(public_audit_status(axioms, 0), checked_modules=1, axioms=axioms)
        artifacts.write_json(self.state / 'result.json', result)
        with self.assertRaisesRegex(ValueError, 'final-audit'):
            artifacts.package(self.root)
        audit = dict(result, explicit_native_admissions=0, full_upgrade_verified=True)
        artifacts.write_json(self.state / 'final-audit.json', audit)
        artifacts.write_json(self.state / 'runner-summary.json', artifacts.validated_success(result, audit))
        artifacts.package(self.root)
        self.assertTrue((self.state / 'artifacts/evidence/final-audit.json').is_file())

    def test_native_success_exports_matching_explicit_trust(self):
        axioms = {name: ['Certificate.coverage._native.native_decide.ax_1_1'] for name in PUBLIC_TARGETS}
        result = dict(public_audit_status(axioms, 0), checked_modules=1, axioms=axioms)
        audit = dict(result, explicit_native_admissions=0, full_upgrade_verified=True)
        summary = artifacts.validated_success(result, audit)
        for name, payload in [('result.json', result), ('final-audit.json', audit),
                              ('runner-summary.json', summary)]:
            artifacts.write_json(self.state / name, payload)
        artifacts.package(self.root)
        evidence = self.state / 'artifacts/evidence'
        self.assertEqual(json.loads((evidence / 'summary.json').read_text()), summary)
        self.assertEqual(json.loads((evidence / 'final-audit.json').read_text()), audit)
        self.assertIn('additionally trusts the Lean compiler', (evidence / 'README.txt').read_text())
        summary['status'] = 'OPTIMALITY_PROVED'
        artifacts.write_json(self.state / 'runner-summary.json', summary)
        with self.assertRaisesRegex(ValueError, 'summary'):
            artifacts.package(self.root)
        self.assertFalse((evidence / 'final-audit.json').exists())

    def test_corrupted_objects_and_symlink_logs_are_not_checkpointed(self):
        self.obj.write_bytes(b'corrupted')
        artifacts.package(self.root)
        with tarfile.open(self.state / 'artifacts/checkpoint.tar') as archive:
            self.assertEqual(archive.getnames(), [])
        self.obj.write_bytes(b'compiled fixture')
        log = self.state / 'ElevenSquare.Test.log'
        log.unlink()
        log.symlink_to(self.root / 'lean-toolchain')
        artifacts.package(self.root)
        with tarfile.open(self.state / 'artifacts/checkpoint.tar') as archive:
            self.assertEqual(archive.getnames(), [])

    def test_interrupted_receipt_is_saved_for_diagnosis_not_restored(self):
        self.receipt.write_text('{"status":')
        artifacts.package(self.root)
        with tarfile.open(self.state / 'artifacts/checkpoint.tar') as archive:
            self.assertEqual(archive.getnames(), [])
        with tarfile.open(self.state / 'artifacts/diagnostics.tar') as archive:
            self.assertIn('.verification/ElevenSquare.Test.json', archive.getnames())

    def test_interrupted_checkpoint_write_never_publishes_a_partial_tar(self):
        checkpoint = self.state / 'artifacts/checkpoint.tar'
        add = tarfile.TarFile.add

        def interrupt_after_first_member(archive, *args, **kwargs):
            add(archive, *args, **kwargs)
            raise RuntimeError('interrupted checkpoint write')

        for previous in (False, True):
            with self.subTest(previous_checkpoint=previous):
                if previous:
                    artifacts.package(self.root)
                    original = checkpoint.read_bytes()
                with mock.patch.object(tarfile.TarFile, 'add', interrupt_after_first_member):
                    with self.assertRaisesRegex(RuntimeError, 'interrupted checkpoint write'):
                        artifacts.package(self.root)
                if previous:
                    self.assertEqual(checkpoint.read_bytes(), original)
                else:
                    self.assertFalse(checkpoint.exists())
                self.assertEqual(list(checkpoint.parent.glob('.checkpoint-*.tar.tmp')), [])

    def test_completed_checkpoint_survives_later_diagnostics_failure(self):
        archive_open = tarfile.open

        def fail_diagnostics(name=None, *args, **kwargs):
            if name is not None and Path(name).name == 'diagnostics.tar':
                raise OSError('diagnostics unavailable')
            return archive_open(name, *args, **kwargs)

        with mock.patch.object(artifacts.tarfile, 'open', side_effect=fail_diagnostics):
            with self.assertRaisesRegex(OSError, 'diagnostics unavailable'):
                artifacts.package(self.root)
        checkpoint = self.state / 'artifacts/checkpoint.tar'
        with tempfile.TemporaryDirectory() as target:
            restored = Path(target).resolve()
            artifacts.extract_checkpoint(restored, checkpoint)
            self.assertEqual((restored / self.obj.relative_to(self.root)).read_bytes(), self.obj.read_bytes())
            self.assertEqual((restored / self.receipt.relative_to(self.root)).read_bytes(), self.receipt.read_bytes())

    def test_archive_rejects_traversal_links_and_non_checkpoint_paths_before_writes(self):
        for name, link in [('../escape', False), ('.git/config', False),
                           ('.verification/result.json', False),
                           ('.verification/ElevenSquare.Test.log', True)]:
            with self.subTest(name=name):
                archive_path = self.root / 'bad.tar'
                with tarfile.open(archive_path, 'w') as archive:
                    valid = tarfile.TarInfo('.verification/Sqpack.Valid.log')
                    valid.size = 1
                    archive.addfile(valid, io.BytesIO(b'x'))
                    bad = tarfile.TarInfo(name)
                    if link:
                        bad.type = tarfile.SYMTYPE
                        bad.linkname = '../escape'
                    archive.addfile(bad)
                with self.assertRaises(ValueError):
                    artifacts.extract_checkpoint(self.root, archive_path)
                self.assertFalse((self.state / 'Sqpack.Valid.log').exists())

    def test_automatic_restore_filters_branch_expired_and_current_runs(self):
        def item(run, branch='main', expired=False):
            return {'expired': expired, 'workflow_run': {'id': run, 'head_branch': branch}}
        responses = [
            {'artifacts': [item(20), item(19, 'other'), item(18, expired=True), item(17)]},
            {'status': 'completed', 'head_branch': 'main',
             'path': '.github/workflows/verify.yml', 'event': 'workflow_dispatch'},
        ]
        with mock.patch.dict(os.environ, GITHUB_REPOSITORY='org/repo', GITHUB_REF_NAME='main', GITHUB_RUN_ID='20'), \
             mock.patch.object(artifacts, 'gh_json', side_effect=responses) as api, \
             mock.patch.object(artifacts.subprocess, 'run') as download, \
             mock.patch.object(artifacts, 'extract_checkpoint') as extract:
            artifacts.restore(self.root, 'auto')
        self.assertIn('/runs/17', api.call_args.args[0])
        self.assertEqual(download.call_args.args[0][3], '17')
        extract.assert_called_once()

    def test_full_audit_survives_checkpoint_roundtrip_and_rejects_changed_source(self):
        fixture = audit_fixtures.FinalizationTests()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        self.addCleanup(fixture.temporary.cleanup)
        fixture.make_fixture([])
        original = fixture.root.resolve()
        subprocess.run(['git', 'init', '-q', str(original)], check=True)
        subprocess.run(['git', '-C', str(original), '-c', 'user.name=Test',
                        '-c', 'user.email=test@example.invalid', 'commit', '--allow-empty',
                        '-qm', 'fixture'], check=True)
        # Existing synthetic audit fixtures omit the module field used by real receipts.
        for receipt in (original / '.verification').glob('*.json'):
            if artifacts.RECEIPT.fullmatch(receipt.name):
                info = json.loads(receipt.read_text())
                info['module'] = receipt.stem
                artifacts.write_json(receipt, info)
        with mock.patch.object(finalize_verification, 'ROOT', original), \
             mock.patch.object(finalize_verification, 'check', return_value=fixture.source_check), \
             mock.patch('sys.argv', ['finalize_verification.py']):
            finalize_verification.main()
        result = json.loads((original / '.verification/result.json').read_text())
        audit = json.loads((original / '.verification/final-audit.json').read_text())
        artifacts.write_json(original / '.verification/runner-summary.json', artifacts.validated_success(result, audit))
        artifacts.package(original)
        audit = json.loads((original / '.verification/artifacts/evidence/final-audit.json').read_text())
        self.assertEqual(audit['source_sha256']['ElevenSquare'], artifacts.sha(original / 'ElevenSquare.lean'))
        for obj in (original / '.lake/build/lib/lean').rglob('*.olean'):
            obj.unlink()
        for receipt in (original / '.verification').glob('*.json'):
            if artifacts.RECEIPT.fullmatch(receipt.name):
                receipt.unlink()
        artifacts.extract_checkpoint(original, original / '.verification/artifacts/checkpoint.tar')
        self.assertTrue(collect_audit(original, fixture.source_check)['global_optimality_proved'])
        (original / 'ElevenSquare.lean').write_text('-- changed source')
        with self.assertRaisesRegex(ValueError, 'Stale source'):
            collect_audit(original, fixture.source_check)


if __name__ == '__main__':
    unittest.main()
