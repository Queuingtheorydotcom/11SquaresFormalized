#!/usr/bin/env python3
"""Exact-source and rejection checks for bounded stage-bundle inlining."""
from copy import deepcopy
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

import flatten_stage_bundles as flatten


TARGET = 'Sqpack.S11Opt.Split.U2G.C7.Main'
DONOR_A = 'Sqpack.S11Opt.Simplified.StageBundles.U2G.C7.SharedStages000'
DONOR_B = 'Sqpack.S11Opt.Simplified.StageBundles.U2G.C7.SharedStages001'
FACADE = 'Sqpack.S11Opt.Simplified.StageBundles.U2G.C7.B0'
NAMESPACE = 'SquarePacking.S11Opt.Split.U2G.C7'


def module_path(module):
    return module.replace('.', '/') + '.lean'


def body(name, note='Exact certificate: ℚ, ≤, and العربية.', extra=''):
    return (f'\nnamespace {NAMESPACE}\n'
            'set_option linter.style.longLine false\n\n'
            f'/-- {note} -/\n'
            f'theorem {name} : (1 : Nat) = 1 := by\n  rfl\n'
            f'{extra}\nend {NAMESPACE}\n\n')


def fixture():
    original = (
        '-- Original destination header.\nimport Base.Init\n'
        f'import {FACADE}\nimport Rules.Shared\nimport Base.Tail\n'
        + body('finished', 'Destination body keeps its original spacing.  '))
    donors = {
        DONOR_A: '-- Original donor A header.\nimport Rules.A\nimport Rules.Common\n'
        + body('cov1'),
        DONOR_B: 'import Rules.Shared\nimport Facades.Rules\n'
        + body('cov2', 'This donor appears first despite dictionary order.'),
    }
    facades = {
        FACADE: [DONOR_B, 'Rules.Shared', DONOR_A],
        'Facades.Rules': ['Rules.B', 'Rules.Common'],
    }

    def expand(module):
        return facades.get(module, [module])

    return original, donors, expand


class AssembleTests(unittest.TestCase):
    def test_exact_bodies_and_first_occurrence_import_order(self):
        original, donors, expand = fixture()
        output, segments = flatten.assemble(TARGET, original, donors, expand)
        header, _ = flatten.split_header(output)
        self.assertEqual(flatten.IMPORT.findall(header), [
            'Base.Init', 'Rules.Shared', 'Rules.B', 'Rules.Common',
            'Rules.A', 'Base.Tail'])
        self.assertTrue(header.startswith('-- Original destination header.\n'))
        sources = {**donors, TARGET: original}
        expected_order = [DONOR_B, DONOR_A, TARGET]
        self.assertEqual([s['path'] for s in segments],
                         [module_path(m) for m in expected_order])
        previous_end = len(header)
        for module, segment in zip(expected_order, segments):
            with self.subTest(module=module):
                source_header, source_body = flatten.split_header(sources[module])
                self.assertGreater(segment['start'], previous_end)
                self.assertEqual(output[segment['start']:segment['end']], source_body)
                self.assertEqual(segment['header'], source_header)
                self.assertEqual(segment['body_sha256'], flatten.digest(source_body))
                self.assertEqual(segment['before_sha256'], flatten.digest(sources[module]))
                self.assertEqual(output.count(source_body), 1)
                previous_end = segment['end']

    def test_unmoved_import_is_retained(self):
        original, donors, expand = fixture()
        output, segments = flatten.assemble(
            TARGET, original, {DONOR_A: donors[DONOR_A]}, expand)
        self.assertIn(DONOR_B, flatten.IMPORT.findall(flatten.split_header(output)[0]))
        self.assertEqual([s['path'] for s in segments],
                         [module_path(DONOR_A), module_path(TARGET)])

    def test_private_and_global_donor_commands_are_rejected(self):
        original, donors, expand = fixture()
        valid = donors[DONOR_A]
        cases = {
            'private theorem': valid.replace('theorem cov1', 'private theorem cov1'),
            'outside command': valid.replace(f'\nnamespace {NAMESPACE}',
                                               f'\nset_option pp.universes true\nnamespace {NAMESPACE}'),
            'attribute': valid.replace(f'\nend {NAMESPACE}',
                                      f'\nattribute [simp] cov1\nend {NAMESPACE}'),
            'global option': valid.replace('set_option linter.style.longLine false',
                                           'set_option linter.style.longLine false\nset_option maxRecDepth 100000'),
            'check command': valid.replace(f'\nend {NAMESPACE}',
                                          f'\n#check cov1\nend {NAMESPACE}'),
        }
        for label, changed in cases.items():
            with self.subTest(command=label), self.assertRaises(AssertionError):
                flatten.assemble(TARGET, original, {**donors, DONOR_A: changed}, expand)

    def test_duplicate_qualified_donor_declarations_are_rejected(self):
        original, donors, expand = fixture()
        donors[DONOR_A] = donors[DONOR_A].replace('theorem cov1', 'theorem cov2')
        with self.assertRaisesRegex(AssertionError, 'Duplicate donor declarations'):
            flatten.assemble(TARGET, original, donors, expand)

    def test_duplicate_declarations_within_one_donor_are_rejected(self):
        original, donors, expand = fixture()
        donors[DONOR_A] = donors[DONOR_A].replace(
            f'\nend {NAMESPACE}',
            f'\ntheorem cov1 : True := True.intro\nend {NAMESPACE}')
        with self.assertRaises(AssertionError):
            flatten.assemble(TARGET, original, donors, expand)

    def test_duplicate_qualified_destination_declaration_is_rejected(self):
        original, donors, expand = fixture()
        original = original.replace('theorem finished', 'theorem cov1')
        with self.assertRaisesRegex(AssertionError, 'Duplicate destination declaration'):
            flatten.assemble(TARGET, original, donors, expand)

    def test_unimported_donor_and_destination_back_edge_are_rejected(self):
        original, donors, expand = fixture()
        with self.assertRaisesRegex(AssertionError, 'Donor is not an imported module'):
            flatten.assemble(TARGET, original, {'Other.Donor': donors[DONOR_A]}, expand)
        donors[DONOR_A] = f'import {TARGET}\n' + donors[DONOR_A]
        with self.assertRaisesRegex(AssertionError, 'Donor imports destination'):
            flatten.assemble(TARGET, original, donors, expand)

    def test_byte_limit_includes_markers_and_utf8_bodies(self):
        original, donors, expand = fixture()
        output, _ = flatten.assemble(TARGET, original, donors, expand)
        self.assertEqual(flatten.LIMIT, 2 * 1024 * 1024)
        gap = flatten.LIMIT - len(output.encode('utf-8'))
        padded = original + ' ' * gap
        at_limit, _ = flatten.assemble(TARGET, padded, donors, expand)
        self.assertEqual(len(at_limit.encode('utf-8')), flatten.LIMIT)
        with self.assertRaisesRegex(AssertionError, 'exceeds 2 MiB'):
            flatten.assemble(TARGET, padded + ' ', donors, expand)
        # This destination has fewer characters than LIMIT, but too many bytes.
        unicode_padded = original + '-- ' + 'α' * (gap // 2 + 1)
        with self.assertRaisesRegex(AssertionError, 'exceeds 2 MiB'):
            flatten.assemble(TARGET, unicode_padded, donors, expand)


class ReconstructionTests(unittest.TestCase):
    def materialize(self, root):
        original, donors, expand = fixture()
        output, segments = flatten.assemble(TARGET, original, donors, expand)
        originals = {module_path(m): text for m, text in {**donors, TARGET: original}.items()}
        outputs = {module_path(TARGET): output}
        outputs.update({module_path(m): f'import {TARGET}\n' for m in donors})
        ledger = {'files': {}, 'compatibility_facades': {}}
        for name, current in outputs.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(current, encoding='utf-8')
            ledger['files'][name] = {
                'before_sha256': flatten.digest(originals[name]),
                'after_sha256': flatten.digest(current),
                'segments': segments if name == module_path(TARGET) else [],
            }
        facade_path = module_path(FACADE)
        facade = f'import {DONOR_B}\nimport {DONOR_A}\n'
        (root / facade_path).write_text(facade, encoding='utf-8')
        ledger['compatibility_facades'][facade_path] = flatten.digest(facade)
        return ledger, originals

    def test_reconstructs_exact_original_headers_and_unicode_bodies(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            ledger, originals = self.materialize(root)
            self.assertEqual(flatten.reconstruct_inputs(root, ledger), originals)
            receipt_path = root / flatten.REPORT
            receipt_path.parent.mkdir(parents=True)
            receipt_path.write_text(json.dumps(ledger), encoding='utf-8')
            self.assertEqual(flatten.reconstruct_inputs(root), originals)

    def test_changed_destination_and_compatibility_donor_are_rejected(self):
        for module in (TARGET, DONOR_A):
            with self.subTest(module=module), TemporaryDirectory() as directory:
                root = Path(directory)
                ledger, _ = self.materialize(root)
                path = root / module_path(module)
                path.write_text(path.read_text() + '-- changed\n', encoding='utf-8')
                with self.assertRaisesRegex(AssertionError, 'Changed transformed file'):
                    flatten.reconstruct_inputs(root, ledger)

    def test_changed_body_is_rejected_even_when_outer_hash_is_updated(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            ledger, _ = self.materialize(root)
            name = module_path(TARGET)
            path = root / name
            changed = path.read_text().replace('theorem cov2', 'theorem cov9')
            path.write_text(changed, encoding='utf-8')
            ledger['files'][name]['after_sha256'] = flatten.digest(changed)
            with self.assertRaisesRegex(AssertionError, 'Changed body segment'):
                flatten.reconstruct_inputs(root, ledger)

    def test_changed_segment_header_or_offsets_are_rejected(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            ledger, _ = self.materialize(root)
            for field, value, message in (
                    ('header', 'import Forged.Header\n', 'Original source mismatch'),
                    ('start', 0, 'Changed body segment')):
                with self.subTest(field=field):
                    changed = deepcopy(ledger)
                    changed['files'][module_path(TARGET)]['segments'][0][field] = value
                    with self.assertRaisesRegex(AssertionError, message):
                        flatten.reconstruct_inputs(root, changed)

    def test_missing_duplicate_or_unexpected_segment_is_rejected(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            ledger, _ = self.materialize(root)
            for mutation, message in (
                    ('missing', 'Incomplete inverse mapping'),
                    ('duplicate', 'Duplicate original segment'),
                    ('unexpected', 'Incomplete inverse mapping')):
                with self.subTest(mutation=mutation):
                    changed = deepcopy(ledger)
                    segments = changed['files'][module_path(TARGET)]['segments']
                    if mutation == 'missing':
                        segments.pop()
                    elif mutation == 'duplicate':
                        segments.append(deepcopy(segments[0]))
                    else:
                        segments[0]['path'] = 'Unexpected.lean'
                    with self.assertRaisesRegex(AssertionError, message):
                        flatten.reconstruct_inputs(root, changed)

    def test_changed_facade_and_inconsistent_original_digest_are_rejected(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            ledger, _ = self.materialize(root)
            changed = deepcopy(ledger)
            changed['files'][module_path(DONOR_A)]['before_sha256'] = flatten.digest('forged')
            with self.assertRaises(AssertionError):
                flatten.reconstruct_inputs(root, changed)
            (root / module_path(FACADE)).write_text('import Forged.Target\n', encoding='utf-8')
            with self.assertRaisesRegex(AssertionError, 'Changed facade'):
                flatten.reconstruct_inputs(root, ledger)


if __name__ == '__main__':
    unittest.main()
