#!/usr/bin/env python3
"""Guard public declarations and dependency boundaries in T07 stage bundling."""
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from bundle_t07_stages import merge_stage, reconstruct_inputs, split_source


STAGE = 'ElevenSquare.Tasks.T07.Ext.Gen.P2.S1'
NAMESPACE = 'ElevenSquare.Tasks.T07.Ext.P2.S1'
DATA = STAGE + 'D'
COMPACT = 'ElevenSquare.Tasks.T07.Ext.CompactWitness'
DONOR_MODULES = [STAGE + 'C0', STAGE + 'C1', STAGE + 'P']


def source(imports, declarations):
    return ('\n'.join('import ' + name for name in imports) + '\n\n'
            f'namespace {NAMESPACE}\n'
            'open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 '
            'ElevenSquare.Tasks.T07.Ext\n\n'
            'set_option maxRecDepth 100000\n'
            'set_option maxHeartbeats 0\n\n'
            + declarations + '\n\n'
            + f'end {NAMESPACE}\n')


CERT0 = ('def cert0 (prev : PoseState) (rs : List PoseRow) : List Sub := []')
CERT1 = ('def cert1 (prev : PoseState) (rs : List PoseRow) : List Sub := []')
PARTNER = '''theorem pc3_ok : pcovB prev 3 pc3 = true := by decide +kernel

theorem pcov_ok : ∀ j, pcov j ≠ [] → pcovB prev j (pcov j) = true := by
  intro j hj
  by_cases h3 : j = 3
  · subst h3; exact pc3_ok
  simp [pcov, h3] at hj'''
STAGE_DECLARATIONS = '''def certs : List (List Sub) := [cert0 prev rs, cert1 prev rs]

theorem step_ok : stepB prev 2 rs pcov certs = true := by decide +kernel

theorem prune : ExtStep prev mid := stepB_sound pcov_ok step_ok'''


class T07StageBundleTests(unittest.TestCase):
    def fixture(self):
        stage = source([DATA, *DONOR_MODULES], STAGE_DECLARATIONS)
        donors = {
            DONOR_MODULES[0]: source([COMPACT], CERT0),
            DONOR_MODULES[1]: source([COMPACT], CERT1),
            DONOR_MODULES[2]: source([DATA], PARTNER),
        }
        return stage, donors

    def test_full_public_bodies_and_finite_checks_are_preserved(self):
        stage, donors = self.fixture()
        output, wrappers, metadata = merge_stage(STAGE, stage, donors)
        for original in [*donors.values(), stage]:
            _, body, namespace = split_source(original)
            self.assertEqual(namespace, NAMESPACE)
            self.assertEqual(output.count(body), 1)
        self.assertIsInstance(metadata, dict)
        self.assertEqual(wrappers, {
            module: f'import {STAGE}\n' for module in donors
        })
        imports = [line for line in output.splitlines()
                   if line.startswith('import ')]
        self.assertEqual(imports.count('import ' + DATA), 1)
        self.assertEqual(imports.count('import ' + COMPACT), 1)
        for module in donors:
            self.assertNotIn('import ' + module, imports)
        self.assertLess(output.index(CERT0), output.index(STAGE_DECLARATIONS))
        self.assertLess(output.index(PARTNER), output.index(STAGE_DECLARATIONS))

    def test_different_namespace_is_rejected(self):
        stage, donors = self.fixture()
        donors[DONOR_MODULES[0]] = donors[DONOR_MODULES[0]].replace(
            NAMESPACE, NAMESPACE + 'Foreign')
        with self.assertRaises(AssertionError):
            merge_stage(STAGE, stage, donors)

    def test_colliding_declarations_are_rejected(self):
        for collision in ('another donor', 'original stage'):
            with self.subTest(collision=collision):
                stage, donors = self.fixture()
                if collision == 'another donor':
                    donors[DONOR_MODULES[1]] = donors[DONOR_MODULES[1]].replace(
                        'def cert1 ', 'def cert0 ')
                else:
                    stage = stage.replace(STAGE_DECLARATIONS,
                                          CERT0 + '\n\n' + STAGE_DECLARATIONS)
                with self.assertRaises(AssertionError):
                    merge_stage(STAGE, stage, donors)

    def test_differing_options_are_rejected(self):
        stage, donors = self.fixture()
        donors[DONOR_MODULES[0]] = donors[DONOR_MODULES[0]].replace(
            'set_option maxHeartbeats 0', 'set_option maxHeartbeats 100')
        with self.assertRaises(AssertionError):
            merge_stage(STAGE, stage, donors)

    def test_module_sensitive_commands_are_rejected(self):
        replacements = [
            'private ' + CERT0,
            'scoped notation "privateStage" => True\n' + CERT0,
            'attribute [simp] pcov_ok\n' + CERT0,
            'syntax "stageMarker" : term\n' + CERT0,
        ]
        for replacement in replacements:
            with self.subTest(replacement=replacement.splitlines()[0]):
                stage, donors = self.fixture()
                donors[DONOR_MODULES[0]] = donors[DONOR_MODULES[0]].replace(
                    CERT0, replacement)
                with self.assertRaises(AssertionError):
                    merge_stage(STAGE, stage, donors)

    def test_malformed_source_boundaries_are_rejected(self):
        _, donors = self.fixture()
        original = donors[DONOR_MODULES[0]]
        malformed = [
            original.replace(CERT0, 'namespace Extra\n' + CERT0 + '\nend Extra'),
            original.replace(f'end {NAMESPACE}', 'end Unrelated'),
            'set_option autoImplicit true\n' + original,
        ]
        for text in malformed:
            with self.subTest(text=text[:100]):
                with self.assertRaises(AssertionError):
                    split_source(text)

    def test_donor_roles_and_import_membership_are_checked(self):
        for mutation in ('certificate theorem', 'partner definition', 'not imported'):
            with self.subTest(mutation=mutation):
                stage, donors = self.fixture()
                if mutation == 'certificate theorem':
                    donors[DONOR_MODULES[0]] = source(
                        [COMPACT], 'theorem unexpected : True := True.intro')
                elif mutation == 'partner definition':
                    donors[DONOR_MODULES[2]] = source([DATA], 'def pcov_ok := true')
                else:
                    stage = stage.replace('import ' + DONOR_MODULES[1] + '\n', '')
                with self.assertRaises(AssertionError):
                    merge_stage(STAGE, stage, donors)

    def test_reexport_back_edge_is_rejected(self):
        stage, donors = self.fixture()
        donors[DONOR_MODULES[0]] = source([COMPACT, STAGE], CERT0)
        with self.assertRaises(AssertionError):
            merge_stage(STAGE, stage, donors)

    def write_merged_fixture(self, root):
        stage, donors = self.fixture()
        merged, wrappers, metadata = merge_stage(STAGE, stage, donors)
        for module, text in {STAGE: merged, **wrappers}.items():
            path = root / (module.replace('.', '/') + '.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        originals = {
            module.replace('.', '/') + '.lean': text
            for module, text in {STAGE: stage, **donors}.items()
        }
        return {'files': [metadata]}, originals

    def test_inverse_ledger_recovers_every_original_source_byte(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            ledger, originals = self.write_merged_fixture(root)
            self.assertEqual(reconstruct_inputs(root, ledger), originals)
            selected = DONOR_MODULES[0]
            selected_path = selected.replace('.', '/') + '.lean'
            self.assertEqual(
                reconstruct_inputs(root, ledger, modules=[selected]),
                {selected_path: originals[selected_path]})

    def test_inverse_ledger_rejects_a_changed_merged_body(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            ledger, _ = self.write_merged_fixture(root)
            path = root / (STAGE.replace('.', '/') + '.lean')
            original = path.read_text()
            changed = original.replace('by decide +kernel', 'by decide', 1)
            self.assertNotEqual(changed, original)
            path.write_text(changed)
            with self.assertRaisesRegex(AssertionError, 'Stale merged stage'):
                reconstruct_inputs(root, ledger)


if __name__ == '__main__':
    unittest.main()
