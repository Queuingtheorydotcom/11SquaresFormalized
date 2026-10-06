"""Historical receipts retain exact hashes through authenticated native inverses."""
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

import flatten_stage_bundles as flatten
import simplify_indexed_stages as indexed
import simplify_stage_aliases as aliases
from test_flatten_stage_bundles import fixture, module_path, TARGET, NAMESPACE


def save(root, name, source):
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source)
    return path


def native_file(root, name, kernel, declarations):
    native = kernel.replace('decide +kernel', 'native_decide')
    save(root, name, native)
    manifest = {'format_version': 1, 'files': {name: {
        'sha256': flatten.digest(native), 'kernel_sha256': flatten.digest(kernel),
        'declarations': declarations}}}
    save(root, 'verification/native-certificates.json', json.dumps(manifest))
    return manifest


class HistoricalNativeAuditTests(unittest.TestCase):
    def indexed_receipt(self, root, sources):
        report = {'files': {name: {'after_sha256': indexed.sha(source)}
                            for name, source in sources.items()}, 'cases': {}}
        return save(root, 'simplification/indexed-stages.json', json.dumps(report))

    def indexed_check(self, root, report):
        with redirect_stdout(io.StringIO()):
            return indexed.check_saved_report(report, root)

    def test_direct_indexed_source_accepts_only_its_authenticated_native_inverse(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            name = 'Sqpack/S11Opt/Split/U2R/C7/S1.lean'
            kernel = f'namespace {NAMESPACE}\ntheorem cov1 : (1 : Nat) = 1 := by decide +kernel\nend {NAMESPACE}\n'
            native_file(root, name, kernel, {NAMESPACE + '.cov1': 1})
            report = self.indexed_receipt(root, {name: kernel})
            self.assertEqual(self.indexed_check(root, report)['files'], 1)
            (root / name).write_text((root / name).read_text() + '-- edited\n')
            with self.assertRaisesRegex(ValueError, 'source hash mismatch'):
                self.indexed_check(root, report)

    def test_native_inverse_precedes_bundle_offsets_and_is_not_applied_twice(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            original, donors, expand = fixture()
            original = original.replace('  rfl\n', '  decide +kernel\n')
            donors = {name: source.replace('  rfl\n', '  decide +kernel\n')
                      for name, source in donors.items()}
            output, segments = flatten.assemble(TARGET, original, donors, expand)
            originals = {module_path(name): source for name, source in {**donors, TARGET: original}.items()}
            target_path = module_path(TARGET)
            outputs = {module_path(name): f'import {TARGET}\n' for name in donors}
            outputs[target_path] = output
            ledger = {'files': {}, 'compatibility_facades': {}}
            for name, source in outputs.items():
                save(root, name, source)
                ledger['files'][name] = {
                    'before_sha256': flatten.digest(originals[name]),
                    'after_sha256': flatten.digest(source),
                    'segments': segments if name == target_path else []}
            native_file(root, target_path, output,
                        {NAMESPACE + '.' + name: 1 for name in ('cov1', 'cov2', 'finished')})
            self.assertEqual(flatten.reconstruct_inputs(root, ledger), originals)
            save(root, flatten.REPORT, json.dumps(ledger))
            report = self.indexed_receipt(root, originals)
            # The inventoried current target differs from its pre-inlining
            # reconstruction. A second native inverse would reject this source.
            self.assertEqual(self.indexed_check(root, report)['files'], 3)

    def test_alias_and_indexed_receipts_keep_their_original_hash_chain(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            name = 'Sqpack/S11Opt/Split/U2R/C7/S1.lean'
            before = (f'namespace {NAMESPACE}\n'
                      'theorem cov1_1 : (1 : Nat) = 1 :=\n  decide +kernel\n\n'
                      'theorem cov1 : (1 : Nat) = 1 := cov1_1\n\n'
                      f'end {NAMESPACE}\n')
            kernel, info = aliases.transform(before)
            native_file(root, name, kernel, {NAMESPACE + '.cov1': 1})
            alias_report = {'files': {name: info}, 'exact_public_statements_preserved': 1}
            alias_path = save(root, 'simplification/stage-root-aliases.json', json.dumps(alias_report))
            indexed_path = self.indexed_receipt(root, {name: before})
            self.assertEqual(aliases.check_saved_report(alias_path, root)['files'], 1)
            self.assertEqual(self.indexed_check(root, indexed_path)['files'], 1)
            self.assertEqual(json.loads(alias_path.read_text()), alias_report)

    def test_uninventoried_native_tactic_is_not_an_accepted_historical_inverse(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            name = 'Sqpack/S11Opt/Split/U2R/C7/S1.lean'
            kernel = 'theorem cov1 : (1 : Nat) = 1 := by decide +kernel\n'
            save(root, name, kernel.replace('decide +kernel', 'native_decide'))
            report = self.indexed_receipt(root, {name: kernel})
            with self.assertRaisesRegex(ValueError, 'Forbidden local proof form'):
                self.indexed_check(root, report)

    def test_rehashing_native_output_cannot_hide_changed_certificate_values(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            name = 'Sqpack/S11Opt/Split/U2R/C7/S1.lean'
            kernel = f'namespace {NAMESPACE}\ntheorem cov1 : (314159 : Nat) = 314159 := by decide +kernel\nend {NAMESPACE}\n'
            manifest = native_file(root, name, kernel, {NAMESPACE + '.cov1': 1})
            report = self.indexed_receipt(root, {name: kernel})
            altered = (root / name).read_text().replace('314159', '314160')
            save(root, name, altered)
            manifest['files'][name]['sha256'] = flatten.digest(altered)
            save(root, 'verification/native-certificates.json', json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, 'inverse hash mismatch'):
                self.indexed_check(root, report)


if __name__ == '__main__':
    unittest.main()
