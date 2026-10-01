"""Lexical source-audit regressions; no Lean process or repository scan."""
import itertools
import json
from pathlib import Path
import random
import re
import tempfile
import unittest
from unittest.mock import patch

import check_sources
from check_sources import code_only, import_names
from verify_support import priority_order


def legacy_code_only(text):
    """Frozen pre-optimization scanner for differential compatibility checks."""
    out = []
    i = depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1; out.extend('  '); i += 2
            elif text.startswith('-/', i):
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            out.append('\n' if text[i] == '\n' else ' ')
            if text[i] == '\\' and i + 1 < len(text):
                out.append(' '); i += 2
            else:
                if text[i] == '"': string = False
                i += 1
        elif text.startswith('/-', i):
            depth = 1; out.extend('  '); i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out.extend(' ' * (end - i)); i = end
        elif text[i] == '"':
            string = True; out.append(' '); i += 1
        else:
            out.append(text[i]); i += 1
    if depth or string:
        raise ValueError('Unterminated comment or string')
    return ''.join(out)


class CodeOnlyTests(unittest.TestCase):
    def test_ordinary_code_is_unchanged(self):
        source = 'import ElevenSquare.Foundations\n' + 'def xα := #[12, -34, 56 / 7]\n' * 2000
        self.assertEqual(code_only(source), source)
        self.assertEqual(code_only(''), '')

    def test_nested_comments_preserve_positions(self):
        source = 'a/- outer\n/- nested /- deep -/ -/\nend -/sorry\n'
        expected = 'a' + ' ' * 8 + '\n' + ' ' * 23 + '\n' + ' ' * 6 + 'sorry\n'
        self.assertEqual(code_only(source), expected)
        self.assertEqual(code_only(source).index('sorry'), source.index('sorry'))

    def test_line_comments_end_at_newline_or_eof(self):
        self.assertEqual(code_only('x-- "/- sorry\ny-- axiom'), 'x' + ' ' * 12 + '\ny' + ' ' * 8)
        self.assertEqual(code_only('--'), '  ')

    def test_strings_ignore_comment_delimiters_and_escaped_quotes(self):
        literal = '"/- -- -/ \\" axiom \\\\ sorry"'
        self.assertEqual(code_only('x' + literal + ' admit'), 'x' + ' ' * len(literal) + ' admit')

    def test_comments_ignore_quotes_and_line_comment_markers(self):
        comment = '/- " --\n/- " -/\n-/'
        expected = ''.join('\n' if char == '\n' else ' ' for char in comment)
        self.assertEqual(code_only(comment + 'axiom'), expected + 'axiom')

    def test_multiline_strings_and_unicode(self):
        self.assertEqual(code_only('"α\nβ"\nsorry'), '  \n  \nsorry')
        self.assertEqual(code_only('"α\r\nβ"'), '   \n  ')

    def test_escaped_newline_matches_historical_behavior(self):
        # The existing scanner blanks the character following a backslash even
        # when it is a newline. This optimization must not change audit results.
        self.assertEqual(code_only('"a\\\nb"\nsorry'), ' ' * 6 + '\nsorry')

    def test_unterminated_comments_and_strings_are_rejected(self):
        for source in ('/-', 'x/- outer /- nested -/', '"', '"abc',
                       '"abc\\', '"abc\\"', '/- " -/ "', '"/- -/'):
            with self.subTest(source=source):
                with self.assertRaisesRegex(ValueError, '^Unterminated comment or string$'):
                    code_only(source)

    def test_masking_does_not_join_identifiers(self):
        self.assertEqual(code_only('ax/- hidden -/iom ad"hidden"mit'),
                         'ax' + ' ' * 12 + 'iom ad' + ' ' * 8 + 'mit')

    def test_real_audit_tokens_and_imports_remain_visible(self):
        words = ('axiom', 'admit', 'native_decide', 'sorryAx', 'sorry')
        for word in words:
            source = ('/- ' + word + ' /- nested -/ -/\n'
                      '-- ' + word + '\n'
                      'def text := "' + word + ' /- -- \\" tail"\n'
                      'import ElevenSquare.Foundations\n' + word + '\n')
            with self.subTest(word=word):
                code = code_only(source)
                matches = list(re.finditer(r'\b' + word + r'\b', code))
                self.assertEqual(len(matches), 1)
                self.assertEqual(code.count('\n', 0, matches[0].start()) + 1, 5)
                self.assertEqual(re.findall(r'^import\s+(\S+)', code, re.M),
                                 ['ElevenSquare.Foundations'])
        source = ('/-\nimport Missing.Comment\n-/\n'
                  '"\nimport Missing.String\n"\n'
                  '-- import Missing.Line\nimport Sqpack.Basic\n')
        self.assertEqual(re.findall(r'^import\s+(\S+)', code_only(source), re.M),
                         ['Sqpack.Basic'])

    def assert_matches_legacy(self, source):
        try:
            expected = legacy_code_only(source)
        except ValueError:
            with self.assertRaises(ValueError, msg=repr(source)):
                code_only(source)
        else:
            self.assertEqual(code_only(source), expected, repr(source))

    def test_differential_short_delimiter_combinations(self):
        for length in range(6):
            for chars in itertools.product('/-"\\\nx', repeat=length):
                self.assert_matches_legacy(''.join(chars))

    def test_differential_representative_generated_patterns(self):
        rng = random.Random(20261001)
        fragments = ('/-', '-/', '--', '"', '\\', '\\"', '\\\\', '\\\n',
                     '\n', '\r\n', 'αβ', ' ', 'sorry', 'axiom', 'admit',
                     'native_decide', 'sorryAx', 'import Sqpack.Basic\n',
                     'def data := #[(123456789012345, -987654321 / 123)]\n')
        for _ in range(2000):
            self.assert_matches_legacy(''.join(rng.choices(fragments, k=rng.randrange(1, 80))))


class ImportHeaderTests(unittest.TestCase):
    def test_whitespace_and_comments_do_not_drop_imports(self):
        cases = (
            'import Sqpack.A\n    import Sqpack.B\n',
            '  import Sqpack.A\r\n\timport Sqpack.B\r\n',
            'import\n  Sqpack.A\nimport\n  Sqpack.B\n',
            '/- header /- nested -/ -/ import/- gap -/Sqpack.A import Sqpack.B',
            'import Sqpack.A -- import Missing.Hidden\n /- gap -/ import Sqpack.B',
        )
        for source in cases:
            with self.subTest(source=source):
                self.assertEqual(import_names(code_only(source)), ['Sqpack.A', 'Sqpack.B'])

    def test_module_header_modifiers_and_same_line_imports(self):
        cases = (
            'module prelude public meta import Sqpack.A import all Sqpack.B',
            'module\npublic\nmeta\nimport\nSqpack.A\nmeta import all\nSqpack.B',
            'prelude\nimport Sqpack.A import Sqpack.B\n',
        )
        for source in cases:
            with self.subTest(source=source):
                self.assertEqual(import_names(code_only(source)), ['Sqpack.A', 'Sqpack.B'])

    def test_quoted_and_unicode_module_names(self):
        source = 'import ElevenSquare.«Quoted Part».β import Sqpack.δ₁'
        self.assertEqual(import_names(code_only(source)),
                         ['ElevenSquare.Quoted Part.β', 'Sqpack.δ₁'])

    def test_keyword_boundaries_and_body_commands_end_the_header(self):
        for source in ('', 'module', 'prelude', '/- only a comment -/',
                       'moduleX\nimport Missing.X', 'preludeX\nimport Missing.X',
                       'publicFoo import Missing.X', 'metaFoo import Missing.X',
                       'importFoo Missing.X', 'public section\nimport Missing.X'):
            with self.subTest(source=source):
                self.assertEqual(import_names(code_only(source)), [])
        source = ('import Sqpack.A\ndef quotation := `(\n import Missing.Body\n)\n'
                  'def text := "import Missing.String"\n')
        self.assertEqual(import_names(code_only(source)), ['Sqpack.A'])


class SourcePolicyTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / 'verification').mkdir()
        (self.root / 'Sqpack.lean').write_text('')
        self.root_patch = patch.object(check_sources, 'ROOT', self.root)
        self.root_patch.start()
        self.addCleanup(self.root_patch.stop)
        self.cache_patch = patch.object(check_sources, '_IMPORT_CACHE', {})
        self.cache_patch.start()
        self.addCleanup(self.cache_patch.stop)

    def write_fixture(self, source, admissions):
        (self.root / 'ElevenSquare.lean').write_text(source)
        (self.root / 'verification/admissions.json').write_text(json.dumps({
            'sites': [{'path': 'ElevenSquare.lean', 'line': line} for line in admissions]}))

    def assert_matches_legacy_policy(self, source):
        # Compare the real checker against the original unguarded word-boundary
        # policy, including its exact first forbidden word and admission lines.
        code = legacy_code_only(source)
        forbidden = next((word for word in ('axiom', 'admit', 'native_decide', 'sorryAx')
                          if re.search(r'\b' + word + r'\b', code)), None)
        admissions = [code.count('\n', 0, match.start()) + 1
                      for match in re.finditer(r'\bsorry\b', code)]
        self.write_fixture(source, admissions)
        if forbidden:
            with self.assertRaises(ValueError) as error:
                check_sources.check()
            self.assertEqual(str(error.exception),
                             'Forbidden local proof form in ElevenSquare.lean: ' + forbidden)
        else:
            result = check_sources.check()
            self.assertEqual(result['status'], 'SOURCE_ASSEMBLY_PASS')
            self.assertEqual(result['explicit_admissions'], len(admissions))

    def test_differential_token_boundaries_comments_and_strings(self):
        templates = ('{}', '({})', 'x_{}', '{}_x', 'α{}', '{}β', '{}₂', "'{}'",
                     '/- {} /- nested -/ -/\ndef n := 1\n',
                     '-- {}\ndef n := 1\n', '"{}"\ndef n := 1\n',
                     '"escaped \\" {}"\n', '"escaped\\\n{}"\nsorry\n',
                     'def n := 1\n{}\n', '/- hidden -/{}-- trailing\n')
        for word, template in itertools.product(('axiom', 'admit', 'native_decide', 'sorryAx', 'sorry'),
                                                templates):
            source = 'import Sqpack\n' + template.format(word)
            with self.subTest(source=source):
                self.assert_matches_legacy_policy(source)
        self.assert_matches_legacy_policy('sorryAx admit axiom native_decide sorry\n')
        self.assert_matches_legacy_policy('def sorry_value := 1\nsorry\n/- sorry -/\nsorry\n')

    def test_numeric_sources_skip_absent_word_regexes(self):
        self.write_fixture('import Sqpack\ndef data := #[12345, -67890 / 123]\n', [])
        with patch.object(check_sources.re, 'search') as search, \
                patch.object(check_sources.re, 'finditer') as finditer:
            result = check_sources.check()
            search.assert_not_called()
            finditer.assert_not_called()
        self.assertEqual(result['explicit_admissions'], 0)

    def write_module(self, name, source):
        path = self.root / (name.replace('.', '/') + '.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
        return path

    def test_indented_transition_dependency_is_extracted_and_scheduled_first(self):
        self.write_fixture('import ElevenSquare.TransitionData\n', [])
        sources = {
            'ElevenSquare.Data': '',
            'ElevenSquare.RowTransitions': '',
            'ElevenSquare.TransitionData': ('import ElevenSquare.Data\n'
                                           '    import ElevenSquare.RowTransitions\n'),
        }
        paths = {name: self.write_module(name, source) for name, source in sources.items()}
        transition = paths['ElevenSquare.TransitionData']
        expected = ['ElevenSquare.Data', 'ElevenSquare.RowTransitions']
        # Exercise both direct imports(path) and the full checker's cached path.
        self.assertEqual(check_sources.imports(transition), expected)
        check_sources._IMPORT_CACHE.clear()
        self.assertEqual(check_sources.check()['status'], 'SOURCE_ASSEMBLY_PASS')
        self.assertEqual(check_sources.imports(transition), expected)
        dependencies = {name: check_sources.imports(path) for name, path in paths.items()}
        order = priority_order(dependencies, {name: path.stat().st_size for name, path in paths.items()})
        self.assertLess(order.index('ElevenSquare.RowTransitions'),
                        order.index('ElevenSquare.TransitionData'))

    def test_missing_indented_local_dependency_is_rejected(self):
        self.write_fixture('    import ElevenSquare.Missing\n', [])
        with self.assertRaisesRegex(ValueError, 'Missing local import: ElevenSquare.Missing'):
            check_sources.check()

    def test_cycle_through_indented_imports_is_rejected(self):
        self.write_fixture('    import ElevenSquare.Dependency\n', [])
        self.write_module('ElevenSquare.Dependency', '    import ElevenSquare\n')
        with self.assertRaisesRegex(ValueError, 'Local import cycle'):
            check_sources.check()

    def test_old_scanner_cache_does_not_hide_indented_import(self):
        self.write_fixture('    import ElevenSquare.Dependency\n', [])
        self.write_module('ElevenSquare.Dependency', '')
        check_sources.check(use_cache=True)
        cache_path = self.root / '.verification/source-scan.json'
        cache = json.loads(cache_path.read_text())
        cache['scanner'] = 'old-column-zero-only-scanner'
        cache['files']['ElevenSquare.lean']['imports'] = []
        cache_path.write_text(json.dumps(cache))
        check_sources._IMPORT_CACHE.clear()
        check_sources.check(use_cache=True)
        self.assertEqual(check_sources.imports(self.root / 'ElevenSquare.lean'),
                         ['ElevenSquare.Dependency'])
        updated = json.loads(cache_path.read_text())
        self.assertEqual(updated['files']['ElevenSquare.lean']['imports'], ['ElevenSquare.Dependency'])


if __name__ == '__main__':
    unittest.main()
