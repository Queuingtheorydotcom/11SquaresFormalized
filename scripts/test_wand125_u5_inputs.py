"""U5 generator regressions for executable checkpoints and Lean comment injection."""
import copy
import contextlib
import io
import json
from pathlib import Path
import pickle
import sys
import tempfile
import unittest
from fractions import Fraction as F
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / 'wand125_u5'))
import gen_all
import gen_node
from gen_p2 import ROLE_CELL, physical_site, seed_polygon
from gen_step import OWNER
from state_io import load_state, save_state


def seed_state():
    return ({o: [(F(0), F(1), seed_polygon(ROLE_CELL[o]))] for o in range(11)},
            {o: [gen_node.canon({'kind': 'seed'})] for o in range(11)},
            {o: [physical_site(ROLE_CELL[o])] for o in range(11)})


def node_fixture(label='node-1'):
    cell = next(iter(OWNER))
    return {'node_id': label, 'B': '1', 'constraints': [],
            'steps': [{'owner': cell, 'complete': False, 'rows': [],
                       'prior_owned_hulls': {}}]}


class GeneratorInputTests(unittest.TestCase):
    def test_exact_state_roundtrip_preserves_generator_types(self):
        state = seed_state()
        state[0][0].append((F(-123456789012345678901, 97), F(5, 11), []))
        state[1][0].append('reference with -/ and /- and Unicode: λ')
        state[0][10] = []
        state[1][10] = []
        state[2][10] = []
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'state.json'
            save_state(path, state)
            restored = load_state(path)
        self.assertEqual(restored, state)
        self.assertIs(type(restored), tuple)
        self.assertIs(type(restored[0][0][0]), tuple)
        self.assertIs(type(restored[0][0][0][0]), F)
        self.assertIs(type(restored[0][0][0][2][0]), tuple)
        self.assertIs(type(restored[2][0][0]), tuple)

    def test_executable_pickle_is_rejected_even_with_json_filename(self):
        with tempfile.TemporaryDirectory() as tmp:
            marker = Path(tmp) / 'executed'
            expression = f"__import__('pathlib').Path({str(marker)!r}).write_text('executed')"

            class Payload:
                def __reduce__(self):
                    return eval, (expression,)

            for protocol in (0, pickle.HIGHEST_PROTOCOL):
                with self.subTest(protocol=protocol):
                    path = Path(tmp) / 'state.json'
                    path.write_bytes(pickle.dumps(Payload(), protocol=protocol))
                    with self.assertRaises((ValueError, UnicodeError)):
                        load_state(path)
                    self.assertFalse(marker.exists())

    def test_malformed_or_object_shaped_json_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'state.json'
            save_state(path, seed_state())
            good = json.loads(path.read_text())
            variants = [[], {'__reduce__': 'builtins.eval'},
                        dict(good, format='future-format'), dict(good, extra='ignored?')]
            for field, owner, value in (
                    ('rows', '0', [[[0, 0], [1, 1], []]]),
                    ('rows', '0', [[[True, 1], [1, 1], []]]),
                    ('rows', '0', [[[0, 1], [1, 1], [[[1, 1], [2, 1]]]]]),
                    ('refs', '0', [{'__class__': 'eval'}]),
                    ('refs', '0', []),
                    ('owned', '0', [[[1.5, 1], [0, 1]]]),
                    ('owned', '11', [])):
                variant = copy.deepcopy(good)
                variant[field][owner] = value
                variants.append(variant)
            for variant in variants:
                with self.subTest(variant=variant):
                    path.write_text(json.dumps(variant))
                    with self.assertRaises(ValueError):
                        load_state(path)

    def test_parallel_generator_replay_and_step_use_json_checkpoints(self):
        node = node_fixture()
        state = seed_state()
        with tempfile.TemporaryDirectory() as tmp, contextlib.redirect_stderr(io.StringIO()):
            work, out = Path(tmp), Path(tmp) / 'out'
            jobs = []
            gen_all.replay(gen_all.chain(node, 'P2', state), node, 'P2', str(work), jobs)
            self.assertEqual(jobs, ['P2 0'])
            self.assertEqual(load_state(work / 'P2_0.json'), state)
            with patch.object(gen_all, 'load_node', return_value=node):
                gen_all.step('unused', str(work), str(out), 'P2', '0')
            self.assertIn('ExtTrace.refl', (out / 'P2' / 'S0.lean').read_text())
            self.assertEqual(list(work.glob('*.pkl')), [])

    def test_archive_label_cannot_escape_generated_lean_comment(self):
        labels = ['node-1', '-/\nrun_tac malicious_action\n/-',
                  '/- nested -/ -/- /-/', 'λ\r\n\x00\u2028']
        with tempfile.TemporaryDirectory() as tmp, contextlib.redirect_stderr(io.StringIO()):
            node_path, parent_path, output = (Path(tmp) / name for name in
                                               ('node.json', 'parent.json', 'out.lean'))
            parent_path.write_text(json.dumps({'final_state': {'cells': {str(next(iter(OWNER))): []}}}))
            for label in labels:
                with self.subTest(label=label):
                    node_path.write_text(json.dumps(node_fixture(label)))
                    gen_node.main(node_path, parent_path, '0', output)
                    source = output.read_text()
                    self.assertEqual(source.count('/-'), 1)
                    self.assertEqual(source.count('-/'), 1)
                    comment = source.split('/-', 1)[1].split('-/', 1)[0]
                    self.assertEqual(comment.count('\n'), 1)
                    self.assertNotIn('run_tac', source.split('-/', 1)[1])
            for label in (None, 1, ['node']):
                with self.subTest(label=label), self.assertRaises(ValueError):
                    gen_node.comment_label(label)


if __name__ == '__main__':
    unittest.main()
