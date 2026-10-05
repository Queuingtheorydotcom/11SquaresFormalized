"""Small source-policy and migration regressions; no Lean or full data scan."""
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from contextlib import redirect_stdout
from unittest.mock import patch

import enable_native_certificates
from enable_native_certificates import convert
from native_certificates import (load_native_manifest, native_declarations,
                                 restore_kernel_source, validate_native_source)


SQPACK = 'Sqpack/S11Opt/Simplified/ReducedConditional/U2P/C1383/SharedStages000.lean'
T07 = 'ElevenSquare/Tasks/T07/Ext/Gen/Frozen/S13538.lean'
BUNDLED = 'Sqpack/S11Opt/Bundled/F01/C000.lean'
OWN = 'Sqpack/S11Opt/Bundled/Own/Leaves000.lean'
RESIDUAL = (OWN, 'Sqpack/S11Opt/F00/Cov1.lean', 'Sqpack/S11Opt/F00/Own36.lean',
            'Sqpack/S11Opt/Split/U2G/C1658/Main.lean',
            'Sqpack/S11Opt/Split/U2P/C652/S19.lean',
            'Sqpack/S11Opt/Split/U2R/C1311/S4.lean')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def entry(data, declarations=None, *, kernel=None):
    result = {'sha256': digest(data), 'declarations': declarations or {'Example.cov': 1}}
    if kernel is not None:
        result['kernel_sha256'] = digest(kernel)
    return result


class NativeMigrationTests(unittest.TestCase):
    def test_sqpack_rewrites_only_generated_sounddec_obligations(self):
        source = (b'namespace Example\n'
                  b'def data := [12345678901234567890, 2, 3]\n'
                  b'theorem cov : Checked data :=\n'
                  b'  MultiComplementaryTree.soundDec 12345678901234567890 (by decide +kernel)\n'
                  b'theorem soundness : True := by decide +kernel\n'
                  b'end Example\n')
        changed, declarations = convert(SQPACK, source)
        self.assertEqual(declarations, {'Example.cov': 1})
        self.assertIn(b'theorem soundness : True := by decide +kernel', changed)
        self.assertEqual(changed.replace(b'native_decide', b'decide +kernel'), source)

    def test_comments_and_strings_are_not_rewritten(self):
        source = (b'namespace Example\n'
                  b'-- A comment about native_decide and decide +kernel.\n'
                  b'def description := "native_decide decide +kernel"\n'
                  b'theorem cov : True :=\n'
                  b'  Tree.soundDec 987654321 (by decide +kernel) -- decide +kernel\n'
                  b'end Example\n')
        changed, declarations = convert(SQPACK, source)
        self.assertEqual(declarations, {'Example.cov': 1})
        self.assertIn(b'-- A comment about native_decide and decide +kernel.', changed)
        self.assertIn(b'"native_decide decide +kernel"', changed)
        self.assertIn(b'(by native_decide) -- decide +kernel', changed)

    def test_private_theorems_are_skipped(self):
        source = (b'namespace Example\nprivate theorem cov : True :=\n'
                  b'  Tree.soundDec 123 (by decide +kernel)\nend Example\n')
        self.assertEqual(convert(SQPACK, source), (source, {}))
        source = b'namespace Example\nprivate theorem step_ok : True := by decide +kernel\nend Example\n'
        self.assertEqual(convert(T07, source), (source, {}))

    def test_only_bundled_leaf_certificates_are_converted(self):
        source = (b'namespace Example\ntheorem cov : True :=\n'
                  b'  FieldTree.soundDec 123 (by decide +kernel)\nend Example\n')
        changed, declarations = convert('Sqpack/S11Opt/Bundled/F01/Leaves000.lean', source)
        self.assertEqual(declarations, {'Example.cov': 1})
        self.assertEqual(changed.replace(b'native_decide', b'decide +kernel'), source)
        self.assertEqual(convert('Sqpack/S11Opt/Bundled/F01/Main.lean', source), (source, {}))

    def test_residual_families_select_only_sounddec_hypotheses(self):
        source = (b'namespace Example\ndef points := [(1, 2)]\n'
                  b'theorem cov : Checked points :=\n'
                  b'  Tree.soundDec 123456789 (by decide +kernel)\n'
                  b'theorem geometry : True := by decide +kernel\n'
                  b'theorem assembly : True :=\n'
                  b'  CovF.weaken cov (by decide +kernel)\nend Example\n')
        for path in RESIDUAL:
            with self.subTest(path=path):
                changed, declarations = convert(path, source)
                self.assertEqual(declarations, {'Example.cov': 1})
                self.assertEqual(changed.replace(b'native_decide', b'decide +kernel'), source)
                self.assertIn(b'theorem geometry : True := by decide +kernel', changed)
                self.assertIn(b'CovF.weaken cov (by decide +kernel)', changed)
        for path in ('Sqpack/S11Opt/F00/Final.lean', 'Sqpack/S11Opt/F00/Data.lean',
                     'Sqpack/S11Opt/F01/Cov1.lean', 'Sqpack/S11Opt/Bundled/Own/Mem.lean',
                     'Sqpack/S11Opt/Split/U2P/Rules.lean',
                     'Sqpack/S11Opt/Split/U2P/C652/Data.lean',
                     'Sqpack/S11Opt/Split/U2P/C652/Proof.lean',
                     'Sqpack/S11Opt/Split/U5/C652/S19.lean'):
            with self.subTest(path=path):
                self.assertEqual(convert(path, source), (source, {}))

    def test_cli_scans_every_residual_family_and_preserves_exact_inverses(self):
        source = (b'namespace Example\ntheorem cov : True :=\n'
                  b'  Tree.soundDec 123 (by decide +kernel)\nend Example\n')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'verification').mkdir()
            for rel in RESIDUAL:
                path = root / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(source)
            with patch.object(enable_native_certificates, 'ROOT', root), \
                    patch('sys.argv', ['enable_native_certificates.py', '--write']), \
                    redirect_stdout(io.StringIO()):
                enable_native_certificates.main()
            manifest = load_native_manifest(root)
            self.assertEqual(set(manifest['files']), set(RESIDUAL))
            for rel in RESIDUAL:
                self.assertEqual(restore_kernel_source(rel, (root / rel).read_bytes(), manifest), source)

    def test_write_migration_is_idempotent(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / T07
            path.parent.mkdir(parents=True)
            path.write_bytes(b'namespace Example\ntheorem step_ok : True := by decide +kernel\nend Example\n')
            (root / 'verification').mkdir()
            with patch.object(enable_native_certificates, 'ROOT', root), \
                    patch('sys.argv', ['enable_native_certificates.py', '--write']), \
                    redirect_stdout(io.StringIO()):
                enable_native_certificates.main()
                first_source = path.read_bytes()
                manifest_path = root / 'verification/native-certificates.json'
                first_manifest = manifest_path.read_bytes()
                enable_native_certificates.main()
                self.assertEqual(path.read_bytes(), first_source)
                self.assertEqual(manifest_path.read_bytes(), first_manifest)

    def test_t07_selects_only_named_numerical_declarations(self):
        names = ('step_ok', 'promote_ok', 'pcov_ok', 'pc12_ok', 'ok7')
        source = ('namespace Example\n' + ''.join(
            'theorem ' + name + ' : True := by decide +kernel\n' for name in names) +
            'theorem geometry_sound : True := by decide +kernel\nend Example\n').encode()
        changed, declarations = convert(T07, source)
        self.assertEqual(declarations, {'Example.' + name: 1 for name in names})
        self.assertIn(b'theorem geometry_sound : True := by decide +kernel', changed)
        self.assertEqual(changed.replace(b'native_decide', b'decide +kernel'), source)

    def test_namespace_and_section_ownership(self):
        source = (b'namespace Outer\nsection Variables\nnamespace Inner\n'
                  b'theorem step_ok : True := by decide +kernel\nend Inner\n'
                  b'end Variables\nlemma pcov_ok : True := by decide +kernel\nend Outer\n')
        _, declarations = convert(T07, source)
        self.assertEqual(declarations, {'Outer.Inner.step_ok': 1, 'Outer.pcov_ok': 1})

    def test_no_ordinary_math_t03_or_raw_upstream_module_changes(self):
        source = (b'namespace Example\ntheorem step_ok : True := by decide +kernel\n'
                  b'theorem cov : True :=\n  Tree.soundDec 123 (by decide +kernel)\nend Example\n')
        paths = ('ElevenSquare/Tasks/T03/Proof.lean', 'Sqpack/S11Opt/Proof.lean',
                 'Sqpack/S11Opt/Simplified/MultiComplementaryTree.lean',
                 'Sqpack/S11Opt/Raw/F01/Proof.lean', 'ElevenSquare/Tasks/T07/Ext/Tree.lean')
        for path in paths:
            with self.subTest(path=path):
                self.assertEqual(convert(path, source), (source, {}))

    def test_statement_data_and_unselected_proof_bytes_are_identical(self):
        source = (b'namespace Example\ndef points := [(101, 303), (505, 707)]\n'
                  b'theorem step_ok : check points = true := by decide +kernel\n'
                  b'theorem ordinary : points = points := by rfl\nend Example\n')
        changed, declarations = convert(T07, source)
        self.assertEqual(declarations, {'Example.step_ok': 1})
        self.assertEqual(digest(changed.replace(b'native_decide', b'decide +kernel')), digest(source))


class NativeInventoryTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / 'verification').mkdir()

    def write_source(self, rel, data=b'theorem cov : True := by native_decide\n'):
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        return data

    def write_manifest(self, files):
        (self.root / 'verification/native-certificates.json').write_text(
            json.dumps({'format_version': 1, 'files': files}))

    def write_generated(self, files):
        path = self.root / 'Sqpack/S11Opt/Bundled/F01/source-manifest.json'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({'native_certificates': files}))

    def write_ownership_generated(self, files):
        path = self.root / 'Sqpack/S11Opt/Bundled/source-manifest.json'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({'native_certificates': files}))

    def test_missing_inventory_means_no_native_permission(self):
        manifest = load_native_manifest(self.root)
        self.assertEqual(native_declarations(manifest), set())
        with self.assertRaisesRegex(ValueError, 'Forbidden local proof form'):
            validate_native_source(SQPACK, b'theorem cov : True := by native_decide', manifest)

    def test_exact_source_hash_and_count_are_required(self):
        data = self.write_source(SQPACK)
        self.write_manifest({SQPACK: entry(data)})
        manifest = load_native_manifest(self.root)
        self.assertEqual(validate_native_source(SQPACK, data, manifest), ['Example.cov'])
        with self.assertRaisesRegex(ValueError, 'source hash mismatch'):
            validate_native_source(SQPACK, data.replace(b'True', b'False'), manifest)
        manifest['files'][SQPACK]['declarations']['Example.cov'] = 2
        with self.assertRaisesRegex(ValueError, 'occurrence mismatch'):
            validate_native_source(SQPACK, data, manifest)

    def test_comments_do_not_create_native_permissions_or_calls(self):
        data = b'-- native_decide\n/- decide (native := true) -/\ndef x := "native_decide"\n'
        self.assertEqual(validate_native_source(SQPACK, data, {'files': {}}), [])

    def test_alternate_native_decide_spellings_are_rejected(self):
        for tactic in ('decide +native', 'decide (native := true)',
                       'decide\n  (native := true)', 'decide +kernel (native := true)'):
            with self.subTest(tactic=tactic), self.assertRaisesRegex(ValueError, 'Uninventoried'):
                validate_native_source(SQPACK, ('theorem cov : True := by ' + tactic).encode(), {'files': {}})

    def test_matching_committed_and_generated_inventory_merge(self):
        data = self.write_source(BUNDLED)
        kernel = data.replace(b'native_decide', b'decide +kernel')
        self.write_manifest({BUNDLED: entry(data, kernel=kernel)})
        self.write_generated({BUNDLED: entry(data)})
        manifest = load_native_manifest(self.root)
        self.assertEqual(set(manifest['files']), {BUNDLED})
        self.assertEqual(manifest['files'][BUNDLED]['sha256'], digest(data))
        self.assertEqual(manifest['files'][BUNDLED]['kernel_sha256'], digest(kernel))

    def test_generated_inventory_can_supply_optional_kernel_hash(self):
        data = self.write_source(BUNDLED)
        kernel = data.replace(b'native_decide', b'decide +kernel')
        self.write_manifest({BUNDLED: entry(data)})
        self.write_generated({BUNDLED: entry(data, kernel=kernel)})
        manifest = load_native_manifest(self.root)
        self.assertEqual(manifest['files'][BUNDLED]['kernel_sha256'], digest(kernel))

    def test_conflicting_committed_and_generated_inventory_rejected(self):
        data = self.write_source(BUNDLED)
        self.write_manifest({BUNDLED: entry(data)})
        for conflict in (dict(entry(data), sha256='0' * 64),
                         entry(data, {'Other.cov': 1})):
            with self.subTest(conflict=conflict):
                self.write_generated({BUNDLED: conflict})
                with self.assertRaisesRegex(ValueError, 'Conflicting'):
                    load_native_manifest(self.root)

    def test_invalid_or_conflicting_kernel_inverse_hash_is_rejected(self):
        data = self.write_source(BUNDLED)
        for invalid in ('', 'not-a-hash', 'A' * 64, None, 123):
            with self.subTest(invalid=invalid):
                self.write_manifest({BUNDLED: dict(entry(data), kernel_sha256=invalid)})
                with self.assertRaisesRegex(ValueError, 'Invalid native certificate entry'):
                    load_native_manifest(self.root)
        self.write_manifest({BUNDLED: dict(entry(data), kernel_sha256='0' * 64)})
        self.write_generated({BUNDLED: dict(entry(data), kernel_sha256='1' * 64)})
        with self.assertRaisesRegex(ValueError, 'Conflicting'):
            load_native_manifest(self.root)

    def test_generated_ownership_inventory_is_limited_to_leaves(self):
        data = self.write_source(OWN)
        kernel = data.replace(b'native_decide', b'decide +kernel')
        self.write_ownership_generated({OWN: entry(data, kernel=kernel)})
        manifest = load_native_manifest(self.root)
        self.assertEqual(restore_kernel_source(OWN, data, manifest), kernel)
        for rel in (BUNDLED, 'Sqpack/S11Opt/Bundled/Own/Mem.lean',
                    'Sqpack/S11Opt/Bundled/Own/../Leaves000.lean'):
            self.write_ownership_generated({rel: entry(data)})
            with self.assertRaisesRegex(ValueError, 'escapes its generated ownership'):
                load_native_manifest(self.root)

    def test_matching_ownership_inventory_merges_and_conflicts_are_rejected(self):
        data = self.write_source(OWN)
        kernel = data.replace(b'native_decide', b'decide +kernel')
        self.write_manifest({OWN: entry(data, kernel=kernel)})
        self.write_ownership_generated({OWN: entry(data)})
        self.assertEqual(load_native_manifest(self.root)['files'][OWN]['kernel_sha256'], digest(kernel))
        self.write_ownership_generated({OWN: dict(entry(data), kernel_sha256='0' * 64)})
        with self.assertRaisesRegex(ValueError, 'Conflicting'):
            load_native_manifest(self.root)

    def test_path_escapes_and_noncanonical_paths_are_rejected(self):
        for rel in ('../Sqpack/Outside.lean', '/tmp/Outside.lean',
                    'Sqpack/../Outside.lean', 'Sqpack//Outside.lean',
                    'Sqpack/./Outside.lean', 'Outside.lean', 'Sqpack/Outside.txt'):
            with self.subTest(rel=rel):
                self.write_manifest({rel: entry(b'ignored')})
                with self.assertRaisesRegex(ValueError, 'Invalid native certificate path'):
                    load_native_manifest(self.root)

    def test_generated_inventory_cannot_escape_its_field(self):
        self.write_generated({'Sqpack/S11Opt/Bundled/F02/C000.lean': entry(b'ignored')})
        with self.assertRaisesRegex(ValueError, 'escapes its generated field'):
            load_native_manifest(self.root)

    def test_missing_inventoried_source_is_rejected(self):
        self.write_manifest({SQPACK: entry(b'ignored')})
        with self.assertRaisesRegex(ValueError, 'Missing or nonregular'):
            load_native_manifest(self.root)


class NativeInverseTests(unittest.TestCase):
    def test_exact_inverse_preserves_unicode_comments_strings_and_line_endings(self):
        source = ('namespace Example\r\n'
                  '-- ℕ native_decide decide +kernel\r\n'
                  '/- outer native_decide /- inner native_decide -/ -/\r\n'
                  'def description := "native_decide decide +kernel"\r\n'
                  'theorem cov : True :=\r\n'
                  '  Tree.soundDec 123 (by decide +kernel) -- native_decide\r\n'
                  'end Example\r\n').encode()
        changed, declarations = convert(SQPACK, source)
        manifest = {'files': {SQPACK: entry(changed, declarations, kernel=source)}}
        self.assertEqual(restore_kernel_source(SQPACK, changed, manifest), source)

    def test_changed_native_bytes_or_changed_literals_are_rejected(self):
        source = (b'namespace Example\ntheorem cov : True :=\n'
                  b'  Tree.soundDec 123 (by decide +kernel)\nend Example\n')
        changed, declarations = convert(SQPACK, source)
        changed_number = changed.replace(b'123', b'124')
        manifest = {'files': {SQPACK: entry(changed, declarations, kernel=source)}}
        with self.assertRaisesRegex(ValueError, 'source hash mismatch'):
            restore_kernel_source(SQPACK, changed_number, manifest)
        manifest['files'][SQPACK]['sha256'] = digest(changed_number)
        with self.assertRaisesRegex(ValueError, 'kernel inverse hash mismatch'):
            restore_kernel_source(SQPACK, changed_number, manifest)

    def test_missing_derived_inverse_or_incorrect_hash_cannot_authenticate_history(self):
        changed = b'theorem cov : True := by native_decide\n'
        manifest = {'files': {SQPACK: entry(changed)}}
        with self.assertRaisesRegex(ValueError, 'Missing or invalid.*kernel inverse hash'):
            restore_kernel_source(SQPACK, changed, manifest)
        manifest['files'][SQPACK]['kernel_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'kernel inverse hash mismatch'):
            restore_kernel_source(SQPACK, changed, manifest)

    def test_count_validation_precedes_inverse(self):
        changed = b'theorem cov : True := by native_decide\n'
        kernel = changed.replace(b'native_decide', b'decide +kernel')
        manifest = {'files': {SQPACK: entry(changed, {'Example.cov': 2}, kernel=kernel)}}
        with self.assertRaisesRegex(ValueError, 'occurrence mismatch'):
            restore_kernel_source(SQPACK, changed, manifest)

    def test_uninventoried_ordinary_sources_pass_through_but_native_is_rejected(self):
        ordinary = b'-- native_decide\nexample : True := by decide +kernel\n'
        self.assertEqual(restore_kernel_source(SQPACK, ordinary, {'files': {}}), ordinary)
        for tactic in (b'native_decide', b'decide +native', b'decide (native := true)'):
            with self.subTest(tactic=tactic), self.assertRaises(ValueError):
                restore_kernel_source(SQPACK, b'example : True := by ' + tactic + b'\n', {'files': {}})


if __name__ == '__main__':
    unittest.main()
