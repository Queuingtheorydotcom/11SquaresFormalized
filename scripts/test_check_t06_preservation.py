"""Focused source-preservation regressions; no compiler, verifier, or Git writes."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_t06_preservation as checker
from symlink_test_support import symlink_or_skip


def shard_fixture(branch=0):
    """Synthetic base and port, including a deliberately nonidentity dot vector."""
    tag = f'{branch:03d}'
    dots = [f'sparseDot{(j + 7) % 60:02d}' for j in range(33)]
    prefix = (
        'namespace ElevenSquare.Tasks.T06\n\n'
        'def numericPayload := ![123456789, 987654321]\n\n'
        f'def branchSparseDots{tag} : Fin 33 → (Fin 42 → ℕ) → ℤ :=\n'
        f'  ![{", ".join(dots)}]\n\n')
    statement = (
        f'theorem branchDots{tag} (n : Fin 42 → ℕ) (k : Fin 33) :\n'
        f'    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows {branch} i) k)'
        f' = branchSparseDots{tag} k n := by\n  fin_cases k\n')
    original_cases = ''.join(
        f'  · calc\n      _ = {dot} n := branchDot{tag}_{j} n\n'
        '      _ = _ := rfl\n' for j, dot in enumerate(dots))
    patched_cases = ''.join(
        f'  · calc\n      _ = {dot} n := branchDot{tag}_{j} n\n'
        f'      _ = _ := congrFun branchSparseDot{tag}_{j}.symm n\n'
        for j, dot in enumerate(dots))
    helpers = '-- Keep vector indexing opaque when transporting the large matrix sum.\n'
    helpers += ''.join(
        f'private theorem branchSparseDot{tag}_{j} :\n'
        f'    branchSparseDots{tag} {j} = {dot} := rfl\n\n'
        for j, dot in enumerate(dots))
    suffix = f'\ndef branchIntegerCurvature{tag} := ![1, 2, 3]\n\n'
    suffix += ''.join(
        f'theorem integerCheck{tag}_{j}_{s} :\n'
        f'    integerResidualCheck {branch} {j} {s} (dualNumerators{tag} {j} {s}) ∧\n'
        f'    integerMassCheck {branch} {j} {s} (dualNumerators{tag} {j} {s}) := by\n'
        f'  have he : residualNumerators {branch} {j} {s} = 33000000000000 := rfl\n'
        '  decide\n\n' for j in range(33) for s in range(2))
    suffix += 'end ElevenSquare.Tasks.T06\n'
    return ((prefix + statement + original_cases + suffix).encode(),
            (prefix + helpers + statement + patched_cases + suffix).encode())


def snapshot_fixture():
    base, current = {}, {}
    for branch, path in enumerate(checker.SHARDS):
        base[path], current[path] = shard_fixture(branch)
    base[checker.BRIDGE] = b'theorem rational_residual_of_integer := by\n' + checker.BRIDGE_BEFORE
    current[checker.BRIDGE] = base[checker.BRIDGE].replace(checker.BRIDGE_BEFORE, checker.BRIDGE_AFTER)
    base[checker.PACKET] = current[checker.PACKET] = b'-- exact packet fixture\n'
    data = checker.T06 + '/DataIntegral.lean'
    base[data] = current[data] = b'def numericalData := ![17, 29]\n'
    current[checker.AUDIT] = checker.AUDIT_SOURCE
    return base, current


class ShardTests(unittest.TestCase):
    def setUp(self):
        self.base, self.current = shard_fixture()

    def reject_edit(self, old, new, error):
        self.assertIn(old, self.current)
        mutated = self.current.replace(old, new, 1)
        self.assertNotEqual(mutated, self.current)
        with self.assertRaisesRegex(ValueError, error):
            checker.check_shard(self.base, mutated, 0)

    def test_exact_reconstruction_and_check_hash(self):
        result = checker.check_shard(self.base, self.current, 0)
        self.assertEqual(result['base_sha256'], result['reconstructed_sha256'])
        self.assertNotEqual(result['base_sha256'], result['current_sha256'])
        self.assertEqual(result['integer_checks'], 66)
        self.assertEqual(result['private_rfl_helpers'], 33)
        self.assertEqual(result['congrFun_transports'], 33)

    def test_numerical_data_inside_and_outside_checks_is_immutable(self):
        self.reject_edit(b'33000000000000', b'33000000000001', 'declarations changed')
        self.reject_edit(b'123456789', b'123456788', 'source differs outside')

    def test_public_statements_are_immutable(self):
        self.reject_edit(b'(k : Fin 33)', b'(k : Fin 32)', 'source differs outside')
        self.reject_edit(b'integerResidualCheck 0 0 0', b'integerResidualCheck 0 0 1',
                         'unexpected public statement')
        self.reject_edit(b'integerMassCheck 0 0 0', b'integerMassCheck 1 0 0',
                         'unexpected public statement')

    def test_missing_duplicate_and_wrong_coverage_are_rejected(self):
        source = self.current.decode()
        start = source.index('theorem integerCheck000_0_0 :')
        end = source.index('theorem integerCheck000_0_1 :')
        declaration = source[start:end]
        for mutated in (source[:start] + source[end:], source[:start] + declaration + source[start:],
                        source.replace('theorem integerCheck000_0_0', 'theorem integerCheck000_33_0')):
            with self.subTest(mutated=mutated[start:start + 50]):
                with self.assertRaisesRegex(ValueError, 'coverage'):
                    checker.check_shard(self.base, mutated.encode(), 0)

    def test_helper_rhs_privacy_and_proof_are_exact(self):
        self.reject_edit(b'branchSparseDots000 0 = sparseDot07',
                         b'branchSparseDots000 0 = sparseDot00', 'private rfl helpers')
        self.reject_edit(b'private theorem branchSparseDot000_0',
                         b'theorem branchSparseDot000_0', 'private rfl helpers')
        self.reject_edit(b'= sparseDot07 := rfl', b'= sparseDot07 := by rfl', 'private rfl helpers')

    def test_transports_have_correct_helper_direction_and_argument(self):
        for replacement in (b'congrFun branchSparseDot000_1.symm n',
                            b'congrFun branchSparseDot000_0 n',
                            b'congrFun branchSparseDot000_0.symm (fun _ => 0)', b'rfl'):
            with self.subTest(replacement=replacement):
                self.reject_edit(b'congrFun branchSparseDot000_0.symm n', replacement,
                                 'congrFun transport')

    def test_unchanged_unported_shard_is_not_accepted(self):
        with self.assertRaisesRegex(ValueError, 'private rfl helpers'):
            checker.check_shard(self.base, self.base, 0)

    def test_extra_code_comments_or_newline_changes_are_rejected(self):
        for extra in (b'\n-- arbitrary extra comment\n', b'\naxiom unexpected : False\n'):
            with self.assertRaisesRegex(ValueError, 'source differs outside'):
                checker.check_shard(self.base, self.current + extra, 0)
        with self.assertRaises(ValueError):
            checker.check_shard(self.base, self.current.replace(b'\n', b'\r\n'), 0)


class SnapshotTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.base, cls.current = snapshot_fixture()

    def test_full_cartesian_coverage(self):
        result = checker.check_snapshot(self.base, self.current)
        self.assertEqual(result['status'], 'T06_SOURCE_PRESERVATION_PASS')
        self.assertEqual(result['base_commit'], '525f4a68bd06a431ed81c19218b2666fe1cdff2e')
        self.assertEqual(result['coverage'], [128, 33, 2])
        self.assertEqual(result['integer_checks'], 8448)
        self.assertEqual(result['private_rfl_helpers'], 4224)
        self.assertEqual(result['congrFun_transports'], 4224)
        self.assertEqual(result['kernel_validation'], 'not_run')

    def test_shards_cannot_be_dropped_duplicated_or_added(self):
        missing = dict(self.current)
        del missing[checker.SHARDS[127]]
        extra = {**self.current, checker.T06 + '/CertificateInteger128.lean': self.current[checker.SHARDS[0]]}
        duplicate = {**self.current, checker.SHARDS[127]: self.current[checker.SHARDS[0]]}
        for current in (missing, extra, duplicate):
            with self.subTest(size=len(current)):
                with self.assertRaises(ValueError):
                    checker.check_snapshot(self.base, current)

    def test_packet_and_numerical_dependencies_cannot_change(self):
        for path in (checker.PACKET, checker.T06 + '/DataIntegral.lean'):
            with self.subTest(path=path):
                with self.assertRaisesRegex(ValueError, 'Unexpected change to'):
                    checker.check_snapshot(self.base, {**self.current, path: b'def weakened := 0\n'})

    def test_bridge_allows_only_the_zero_mul_insertion(self):
        base, current = self.base[checker.BRIDGE], self.current[checker.BRIDGE]
        result = checker.check_bridge(base, current)
        self.assertEqual(result['base_sha256'], result['reconstructed_sha256'])
        for mutated in (base, current + b'-- another change\n',
                        current.replace(b'zero_mul', b'one_mul'),
                        current.replace(b'1000000000000000000000000', b'1000000000000000000000001')):
            with self.subTest(mutated=mutated[-100:]):
                with self.assertRaisesRegex(ValueError, 'CertificateBridge'):
                    checker.check_bridge(base, mutated)

    def test_audit_cannot_be_weakened_or_redirected(self):
        source = checker.AUDIT_SOURCE
        cases = (source.replace(b'S08_ExactPacket', b'S07_LocalPacket'),
                 source.replace(b'#print axioms', b'-- #print axioms', 1),
                 source.replace(b'construction_locally_isolated', b'construction_exists'),
                 source[:source.rfind(b'#print axioms')],
                 source + b'import ElevenSquare.Optimality\n',
                 source + b'#print axioms False.elim\n',
                 source + b'axiom anything : False\n')
        for mutated in cases:
            with self.subTest(mutated=mutated[-80:]):
                with self.assertRaisesRegex(ValueError, 'LocalIsolationAudit'):
                    checker.check_audit(mutated)

    def test_cli_emits_json_failure_with_nonzero_status(self):
        output = io.StringIO()
        with patch.object(checker, 'load_base', side_effect=ValueError('missing fixed base')), \
                contextlib.redirect_stdout(output):
            status = checker.main([])
        self.assertEqual(status, 1)
        self.assertEqual(json.loads(output.getvalue())['status'], 'T06_SOURCE_PRESERVATION_FAIL')

    def test_cli_is_read_only_and_emits_hashes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, source in self.current.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(source)
            before = {p.relative_to(root): (p.read_bytes(), p.stat().st_mtime_ns)
                      for p in root.rglob('*') if p.is_file()}
            output = io.StringIO()
            with patch.object(checker, 'load_base', return_value=self.base), \
                    contextlib.redirect_stdout(output):
                status = checker.main(['--root', str(root)])
            after = {p.relative_to(root): (p.read_bytes(), p.stat().st_mtime_ns)
                     for p in root.rglob('*') if p.is_file()}
            self.assertEqual(status, 0)
            self.assertEqual(before, after)
            report = json.loads(output.getvalue())
            self.assertEqual(report['files'][checker.SHARDS[0]]['base_sha256'],
                             checker.sha256(self.base[checker.SHARDS[0]]))

    def test_symlinked_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / checker.T06).mkdir(parents=True)
            outside = root / 'outside.lean'
            outside.write_bytes(b'-- source\n')
            symlink_or_skip(self, root / checker.SHARDS[0], outside)
            with self.assertRaisesRegex(ValueError, 'Symlink'):
                checker.load_current(root)


class GitReadTests(unittest.TestCase):
    def test_load_base_reads_only_fixed_commit_and_exact_binary_blobs(self):
        root = Path('/unused-test-root')
        path = checker.SHARDS[0]
        oid = b'a' * 40
        source = b'first\r\nsecond\n\x00last'
        tree = b'100644 blob ' + oid + b'\t' + path.encode() + b'\0'
        batch = oid + b' blob ' + str(len(source)).encode() + b'\n' + source + b'\n'
        with patch.object(checker, 'git', side_effect=[tree, batch]) as git:
            self.assertEqual(checker.load_base(root), {path: source})
        self.assertEqual(git.call_args_list[0].args,
                         (root, 'ls-tree', '-rz', checker.BASE_COMMIT, '--', checker.T06, checker.PACKET))
        self.assertEqual(git.call_args_list[1].args, (root, 'cat-file', '--batch'))
        self.assertEqual(git.call_args_list[1].kwargs, {'input_bytes': oid + b'\n'})

    def test_git_replacement_objects_and_optional_writes_are_disabled(self):
        with patch.object(checker.subprocess, 'run') as run:
            run.return_value.returncode = 0
            run.return_value.stdout = b'read result'
            self.assertEqual(checker.git(Path('/unused-test-root'), 'status'), b'read result')
        self.assertEqual(run.call_args.args[0][:3],
                         ['git', '--no-replace-objects', '--no-optional-locks'])


if __name__ == '__main__':
    unittest.main()
