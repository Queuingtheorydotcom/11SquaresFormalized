#!/usr/bin/env python3
"""Factor generated stage data into exact indexed tables.

This is a source-preserving transformation, not a Lean acceptance test.
Every original triangle and target literal stays on its own table-entry line.
Consumer references must belong to a uniquely identified original case namespace;
qualified references and definition-unfolding tactic sites are rejected for review.

Without --write, report a complete dry run. --check checks the saved receipt.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
NS = re.compile(r'^namespace (SquarePacking\.S11Opt\.Split\.U\w+\.C\d+)$', re.M)
TRIS = re.compile(r'^def tris(\d+) : List Tri := (.+)$', re.M)
TARGETS = re.compile(r'^def tgt(\d+) : List \(ℕ × ℕ\) := (.+)$', re.M)
OPTIONS = re.compile(r'^def opts(\d+) : List \(List \(List \(ℕ × ℕ\)\)\) := (.+)$', re.M)
REFERENCES = re.compile(r'\b(tris|tgt|opts)(\d+)\b')
INDEXED = re.compile(r'\((traceTriangles|traceTargets|traceOptions) (\d+)\)')
NAMES = {'tris': 'traceTriangles', 'tgt': 'traceTargets', 'opts': 'traceOptions'}
REVERSE_NAMES = {v: k for k, v in NAMES.items()}
REPORT = ROOT / 'simplification/indexed-stages.json'


def sha(source):
    return hashlib.sha256(source.encode()).hexdigest()


def literal_digest(triangles, targets):
    return sha(json.dumps([triangles, targets], ensure_ascii=False, separators=(',', ':')))


def extract_table(source, name, typ):
    marker = f'private def {name} : Array ({typ}) := #[\n'
    body = source.split(marker, 1)[1].split('\n]\n', 1)[0]
    rows = body.splitlines()
    assert rows and all(row.startswith('  ') for row in rows)
    assert all(row.endswith(',') for row in rows[:-1])
    assert not rows[-1].endswith(',')
    return [(str(i), row[2:-1] if i < len(rows) - 1 else row[2:])
            for i, row in enumerate(rows)]


def transform_data(source):
    triangles, targets, options = TRIS.findall(source), TARGETS.findall(source), OPTIONS.findall(source)
    if not triangles:
        return None
    count = len(triangles)
    assert [int(n) for n, _ in triangles] == list(range(count))
    assert [int(n) for n, _ in targets] == list(range(count - 1))
    assert count > 1 and len(options) == count
    for i, (n, value) in enumerate(options):
        assert int(n) == i
        assert value == (f'triOpts tris{i}' if i == count - 1 else f'stepOpts tris{i} tgt{i}')
    start, end = source.index('/-- Step 0:'), source.rindex('\nend ')
    original = source[start:end]
    leftover = OPTIONS.sub('', TARGETS.sub('', TRIS.sub('', original)))
    leftover = re.sub(r'/-- Step \d+: owner \d+\. -/', '', leftover)
    assert not leftover.strip(), 'Unexpected declaration in generated data'

    def table(name, typ, values):
        return (f'private def {name} : Array ({typ}) := #[\n'
                + ',\n'.join('  ' + value for _, value in values) + '\n]\n\n')

    replacement = '/-- Original triangle witnesses, one literal entry per promotion stage. -/\n'
    replacement += table('traceTriangleTable', 'List Tri', triangles)
    replacement += 'def traceTriangles (stage : ℕ) : List Tri :=\n'
    replacement += '  (traceTriangleTable[stage]?).getD []\n\n'
    replacement += '/-- Original target points; the terminal stage has no target entry. -/\n'
    replacement += table('traceTargetTable', 'List (ℕ × ℕ)', targets)
    replacement += 'def traceTargets (stage : ℕ) : List (ℕ × ℕ) :=\n'
    replacement += '  (traceTargetTable[stage]?).getD []\n\n'
    replacement += '/-- The original shared rule, with the same unique terminal stage. -/\n'
    replacement += 'def traceOptions (stage : ℕ) : List (List (List (ℕ × ℕ))) :=\n'
    replacement += f'  if stage = {count - 1} then triOpts (traceTriangles stage)\n'
    replacement += '  else stepOpts (traceTriangles stage) (traceTargets stage)\n'
    output = source[:start] + replacement + source[end:]
    out_triangles = extract_table(output, 'traceTriangleTable', 'List Tri')
    out_targets = extract_table(output, 'traceTargetTable', 'List (ℕ × ℕ)')
    assert out_triangles == triangles and out_targets == targets
    # The serialized arrays reproduce each complete original literal, not merely
    # a list of matching numbers. The option expressions are checked above.
    assert output[:start] + original + output[start + len(replacement):] == source
    return output, count, literal_digest(triangles, targets)


def transform_consumer(source, cases):
    namespaces = NS.findall(source)
    matching = [namespace for namespace in namespaces if namespace in cases]
    if not matching:
        return source, 0
    assert len(namespaces) == 1, 'Case namespace is not unique'
    count = cases[matching[0]]['stages']
    # Do not silently turn a declaration name used by a tactic into a term.
    for line in source.splitlines():
        if REFERENCES.search(line):
            assert not re.search(r'\b(?:simp|simp_all|dsimp|unfold|rw)\b', line)
    assert not INDEXED.search(source), 'Already contains indexed stage references'
    references = 0
    def replace(match):
        nonlocal references
        kind, text_index = match.groups()
        assert not (match.start() and source[match.start() - 1] == '.'), 'Qualified reference needs review'
        assert int(text_index) < count - (kind == 'tgt'), 'Stage index out of range'
        assert str(int(text_index)) == text_index, 'Noncanonical stage index'
        references += 1
        return f'({NAMES[kind]} {text_index})'
    output = REFERENCES.sub(replace, source)
    # Includes theorem statements, proof terms, encoded certificates and imports.
    # Reversing just the indexed terms must reproduce every original byte.
    restored = INDEXED.sub(lambda m: REVERSE_NAMES[m[1]] + m[2], output)
    assert restored == source
    return output, references


def plan():
    cases, changes = {}, {}
    for path in sorted((ROOT / 'Sqpack/S11Opt/Split').glob('U*/C*/Data.lean')):
        source = path.read_text()
        transformed = transform_data(source)
        if transformed is None:
            continue
        output, count, digest = transformed
        namespace = NS.findall(source)
        assert len(namespace) == 1
        cases[namespace[0]] = {'stages': count, 'triangle_entries': count,
                              'target_entries': count - 1, 'literal_sha256': digest,
                              'data_path': str(path.relative_to(ROOT))}
        changes[path] = metadata(source, output, 'indexed data', 0)
    assert cases, 'No original per-stage data found; use --check for an already transformed tree'
    for base in ['ElevenSquare', 'Sqpack']:
        for path in sorted((ROOT / base).rglob('*.lean')):
            if path in changes:
                continue
            source = path.read_text()
            output, refs = transform_consumer(source, cases)
            if output != source:
                changes[path] = metadata(source, output, 'consumer references', refs)
    return cases, changes


def metadata(before, after, kind, refs):
    return {'kind': kind, 'before_sha256': sha(before), 'after_sha256': sha(after),
            'before_lines': len(before.splitlines()), 'after_lines': len(after.splitlines()),
            'before_bytes': len(before.encode()), 'after_bytes': len(after.encode()),
            'bounded_references': refs}


def check_saved_report(report_path=REPORT, root=ROOT):
    from native_certificates import load_native_manifest, restore_kernel_source
    root = Path(root)
    report = json.loads(Path(report_path).read_text())
    native_manifest = load_native_manifest(root)
    # Later import/body inlining retains an exact inverse, rather than claiming
    # that this older receipt directly validates the new physical file layout.
    inlining = root / 'simplification/stage-bundle-inlining.json'
    if inlining.exists():
        from flatten_stage_bundles import reconstruct_inputs
        previous_sources = reconstruct_inputs(root)
    else:
        previous_sources = {}
    # Large table initializers may subsequently be split into private row
    # definitions. Check this historical receipt against their exact inverse.
    from split_indexed_data import reconstruct_inputs as reconstruct_indexed_data
    previous_sources.update(reconstruct_indexed_data(root))
    def source_at(name):
        # Inlining reconstruction already removed the native conversion. Its
        # returned earlier source must not be authenticated as a current file.
        if name in previous_sources:
            return previous_sources[name]
        return restore_kernel_source(name, (root / name).read_bytes(), native_manifest).decode('utf-8')
    successor_path = root / 'simplification/stage-root-aliases.json'
    successors = json.loads(successor_path.read_text())['files'] if successor_path.exists() else {}
    for name, info in report['files'].items():
        current_hash = sha(source_at(name))
        if current_hash != info['after_sha256']:
            # The separately audited pure-alias pass may follow indexing. Its
            # input hash must match this receipt before accepting its output.
            successor = successors.get(name, {})
            assert successor.get('before_sha256') == info['after_sha256'], name
            assert successor.get('after_sha256') == current_hash, name
    for info in report['cases'].values():
        source = source_at(info['data_path'])
        triangles = extract_table(source, 'traceTriangleTable', 'List Tri')
        targets = extract_table(source, 'traceTargetTable', 'List (ℕ × ℕ)')
        assert len(triangles) == info['triangle_entries']
        assert len(targets) == info['target_entries']
        assert literal_digest(triangles, targets) == info['literal_sha256']
    result = {'status': 'SAVED_SOURCE_RECEIPT_MATCHES', 'lean_verified': False,
              'cases': len(report['cases']), 'files': len(report['files'])}
    print(json.dumps(result))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.check:
        check_saved_report()
        return
    cases, changes = plan()
    files = {str(p.relative_to(ROOT)): info for p, info in changes.items()}
    report = {'status': 'SOURCE_LITERAL_PRESERVATION_ONLY_NOT_LEAN_ACCEPTANCE',
              'lean_verified': False, 'array_lookup': 'Array.getElem? followed by Option.getD []',
              'public_type_preservation': 'Every old tris/tgt/opts reference maps to the exact same literal or option expression after indexed lookup; all consumers round-trip byte-for-byte. Lean elaboration remains unverified.',
              'cases': cases, 'files': files,
              'triangle_entries': sum(c['triangle_entries'] for c in cases.values()),
              'target_entries': sum(c['target_entries'] for c in cases.values()),
              'bounded_references': sum(v['bounded_references'] for v in files.values()),
              'removed_lines': sum(v['before_lines'] - v['after_lines'] for v in files.values()),
              'removed_bytes': sum(v['before_bytes'] - v['after_bytes'] for v in files.values())}
    if args.write:
        # Validate the full plan first and recheck each source before mutation.
        for path, info in changes.items():
            source = path.read_text()
            assert sha(source) == info['before_sha256'], f'Changed during planning: {path}'
            if info['kind'] == 'indexed data':
                output = transform_data(source)[0]
            else:
                output = transform_consumer(source, cases)[0]
            assert sha(output) == info['after_sha256']
            path.write_text(output)
        REPORT.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'cases': len(cases), 'files': len(files),
                      'triangle_entries': report['triangle_entries'],
                      'target_entries': report['target_entries'],
                      'bounded_references': report['bounded_references'],
                      'removed_lines': report['removed_lines'],
                      'removed_bytes': report['removed_bytes'], 'written': args.write}))


if __name__ == '__main__':
    main()
