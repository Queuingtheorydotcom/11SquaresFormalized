#!/usr/bin/env python3
"""Bypass generated import facades and inline bounded, single-consumer bundles.

The old module paths remain compatibility imports. The inverse receipt restores
every changed input byte from current body segments, without duplicating large
certificate bodies. No Lean is run. Default: dry run; --write applies; --check
validates current files, original-source reconstruction and the live graph.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
from check_sources import ROOT, code_only

REPORT = 'simplification/stage-bundle-inlining.json'
PREFIX = 'Sqpack.S11Opt.Simplified.StageBundles.'
LIMIT = 2 * 1024 * 1024
IMPORT = re.compile(r'^import ([A-Za-z0-9_.]+)[ \t]*(?:\n|$)', re.M)
MAIN = re.compile(r'Sqpack\.S11Opt\.Split\.(?:U2G|U2P|U2R)\.C\d+\.Main')


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def split_header(text):
    matches = list(IMPORT.finditer(text))
    assert matches, 'Missing generated import header'
    end = matches[-1].end()
    assert not IMPORT.sub('', code_only(text[:end])).strip(), 'Commands interleaved with imports'
    return text[:end], text[end:]


def rewrite_header(header, expand):
    seen = set()
    def replace(match):
        lines = []
        for module in expand(match[1]):
            if module not in seen:
                seen.add(module)
                lines.append('import ' + module + '\n')
        return ''.join(lines)
    return IMPORT.sub(replace, header)


def donor_namespace(body):
    code = code_only(body)
    ns = list(re.finditer(r'^namespace ([A-Za-z0-9_.]+)[ \t]*$', code, re.M))
    ends = list(re.finditer(r'^end ([A-Za-z0-9_.]+)[ \t]*$', code, re.M))
    assert len(ns) == len(ends) == 1 and ns[0][1] == ends[0][1], 'Namespace imbalance'
    assert not code[:ns[0].start()].strip() and not code[ends[0].end():].strip(), 'Outside commands'
    assert not re.search(r'^\s*(?:private|protected|attribute|notation|infix\w*|syntax|macro|elab|scoped|local|initialize|axiom|export|variable|section|noncomputable|unsafe|#)\b', code, re.M), 'Module-sensitive command'
    assert not re.search(r'\b(?:__FILE__|__DIR__|__LINE__)\b', code), 'Module-sensitive literal'
    assert re.findall(r'^set_option (.*)$', code, re.M) == ['linter.style.longLine false'], 'Unexpected options'
    declarations = re.findall(r'^(theorem|lemma|def|abbrev|opaque|instance|structure|inductive)\s+([^\s:(]+)', code, re.M)
    assert declarations and all(k == 'theorem' and re.fullmatch(r'cov\d+(?:_\d+)*', n) for k, n in declarations), 'Non-generated declarations'
    assert len({n for _, n in declarations}) == len(declarations), 'Duplicate donor declarations'
    return ns[0][1], [ns[0][1] + '.' + n for _, n in declarations]


def graph(root):
    paths = {'.'.join(p.relative_to(root).with_suffix('').parts): p
             for top in ('ElevenSquare', 'Sqpack') for p in (root / top).rglob('*.lean')}
    for top in ('ElevenSquare', 'Sqpack'):
        paths[top] = root / (top + '.lean')
    result = subprocess.run(['rg', '--no-heading', '--with-filename', '^import ',
                             'ElevenSquare', 'Sqpack', 'ElevenSquare.lean', 'Sqpack.lean'],
                            cwd=root, text=True, capture_output=True, check=True)
    deps = {m: [] for m in paths}
    for line in result.stdout.splitlines():
        name, command = line.split(':', 1)
        module = name[:-5].replace('/', '.')
        for dep in command[7:].split():
            if dep.startswith(('ElevenSquare.', 'Sqpack.')):
                assert dep in paths, 'Missing local import: ' + dep
            if dep in paths:
                deps[module].append(dep)
    return paths, deps


def closure(deps, target):
    seen, visiting = set(), set()
    def visit(module):
        assert module not in visiting, 'Import cycle at ' + module
        if module in seen:
            return
        visiting.add(module)
        for dep in deps.get(module, []):
            visit(dep)
        visiting.remove(module)
        seen.add(module)
    visit(target)
    return seen


def assemble(module, old, donors, expand):
    """Return a destination and exact inverse segments in original import order."""
    header, body = split_header(old)
    order = list(dict.fromkeys(d for m in IMPORT.findall(header) for d in expand(m)))
    assert set(donors) <= set(order), 'Donor is not an imported module'
    parts, names = [], set()
    for donor in [d for d in order if d in donors]:
        dh, db = split_header(donors[donor])
        _, dn = donor_namespace(db)
        assert not names.intersection(dn), 'Duplicate donor declarations'
        names.update(dn)
        assert module not in IMPORT.findall(dh), 'Donor imports destination'
        parts.append((donor, donors[donor], dh, db))
    target_code = code_only(body)
    target_ns = re.findall(r'^namespace ([A-Za-z0-9_.]+)[ \t]*$', target_code, re.M)
    assert len(target_ns) == 1, 'Unexpected destination namespaces'
    target_names = {target_ns[0] + '.' + n for n in re.findall(
        r'^(?:(?:private|protected)\s+)?(?:theorem|lemma|def|abbrev|opaque|instance)\s+([^\s:(]+)', target_code, re.M)}
    assert not names.intersection(target_names), 'Duplicate destination declaration'
    parts.append((module, old, header, body))
    def expand_move(name):
        return [x for d in expand(name) for x in
                ([z for dep in IMPORT.findall(split_header(donors[d])[0]) for z in expand(dep)]
                 if d in donors else [d])]
    output = rewrite_header(header, expand_move)
    segments = []
    for source_module, source, source_header, source_body in parts:
        marker = '\n-- BEGIN STAGE-BUNDLE BODY ' + source_module + '\n'
        assert marker not in source_body, 'Existing segment marker'
        output += marker
        start = len(output)
        output += source_body
        end = len(output)
        output += '\n-- END STAGE-BUNDLE BODY ' + source_module + '\n'
        segments.append({'path': source_module.replace('.', '/') + '.lean',
                         'header': source_header, 'start': start, 'end': end,
                         'body_sha256': digest(source_body), 'before_sha256': digest(source)})
    assert len(output.encode()) <= LIMIT, 'Merged destination exceeds 2 MiB'
    return output, segments


def reconstruct_inputs(root=ROOT, ledger=None):
    """Validated pre-transform sources, keyed by repository-relative path."""
    from native_certificates import load_native_manifest, restore_kernel_source
    root = Path(root)
    report = json.loads((root / REPORT).read_text()) if ledger is None else ledger
    native_manifest = load_native_manifest(root)
    originals = {}
    for name, info in report['files'].items():
        # Native conversion follows inlining. Authenticate and undo that exact
        # later conversion before checking historical hashes or character offsets.
        current = restore_kernel_source(name, (root / name).read_bytes(), native_manifest).decode('utf-8')
        assert digest(current) == info['after_sha256'], 'Changed transformed file: ' + name
        for segment in info.get('segments', []):
            body = current[segment['start']:segment['end']]
            assert digest(body) == segment['body_sha256'], 'Changed body segment'
            source = segment['header'] + body
            assert digest(source) == segment['before_sha256'], 'Original source mismatch'
            assert segment['path'] not in originals, 'Duplicate original segment'
            originals[segment['path']] = source
    assert set(originals) == set(report['files']), 'Incomplete inverse mapping'
    for name, source in originals.items():
        assert digest(source) == report['files'][name]['before_sha256']
    for name, expected in report['compatibility_facades'].items():
        assert digest((root / name).read_text()) == expected, 'Changed facade: ' + name
    return originals


def plan(root=ROOT):
    paths, before_graph = graph(root)
    facades = {}
    for module, path in paths.items():
        if module.startswith(PREFIX) and re.fullmatch(r'B\d+', path.stem):
            text = path.read_text()
            assert re.fullmatch(r'(?:\s*import [A-Za-z0-9_.]+\s*)+', text), 'Nontrivial facade'
            facades[module] = IMPORT.findall(text)
    def expand(module, ancestors=()):
        assert module not in ancestors, 'Facade cycle'
        return [z for d in facades[module] for z in expand(d, ancestors + (module,))] if module in facades else [module]
    flat_graph = {m: list(dict.fromkeys(z for d in ds for z in expand(d)))
                  for m, ds in before_graph.items() if m not in facades}
    reverse = defaultdict(set)
    for module, ds in flat_graph.items():
        for dep in ds:
            reverse[dep].add(module)
    originals, outputs, metadata = {}, {}, {}
    def read(module):
        if module not in originals:
            originals[module] = paths[module].read_text()
        return originals[module]
    def record(module, output, segments):
        outputs[module] = output
        metadata[module.replace('.', '/') + '.lean'] = {
            'before_sha256': digest(read(module)), 'after_sha256': digest(output),
            'before_bytes': len(read(module).encode()), 'after_bytes': len(output.encode()),
            'segments': segments}
    groups = defaultdict(list)
    for module, path in paths.items():
        if module.startswith(PREFIX) and re.fullmatch(r'SharedStages\d+', path.stem) and len(reverse[module]) == 1:
            target = next(iter(reverse[module]))
            if MAIN.fullmatch(target):
                donor_namespace(split_header(read(module))[1])
                groups[target].append(module)
    moved = {}
    for target, candidates in sorted(groups.items()):
        donors = {}
        for donor in sorted(candidates, key=lambda m: paths[m].stat().st_size):
            proposal = {**donors, donor: read(donor)}
            try:
                assemble(target, read(target), proposal, expand)
            except AssertionError as error:
                if str(error) != 'Merged destination exceeds 2 MiB':
                    raise
                continue
            donors = proposal
        if donors:
            output, segments = assemble(target, read(target), donors, expand)
            record(target, output, segments)
            for donor in donors:
                moved[donor] = target
                record(donor, 'import ' + target + '\n', [])
    for module, deps in before_graph.items():
        if module in facades or module in outputs or not any(d in facades for d in deps):
            continue
        assert module.startswith('Sqpack.'), 'Unexpected consumer outside Sqpack'
        old = read(module)
        header, body = split_header(old)
        new_header = rewrite_header(header, expand)
        if new_header != header:
            record(module, new_header + body, [{'path': module.replace('.', '/') + '.lean',
                'header': header, 'start': len(new_header), 'end': len(new_header + body),
                'body_sha256': digest(body), 'before_sha256': digest(old)}])
    after_graph = dict(before_graph)
    for module, text in outputs.items():
        after_graph[module] = [d for d in IMPORT.findall(text) if d in paths]
    for module in after_graph:
        closure(after_graph, module)
    target = 'ElevenSquare.Verification'
    before, after = closure(before_graph, target), closure(after_graph, target)
    removed = sorted(before - after)
    assert not (set(moved) | set(facades)).intersection(after), 'Compatibility modules remain active'
    lineage = {}
    for name in ('indexed-stages.json', 'stage-root-aliases.json', 'conditional-context-reuse.json'):
        path = root / 'simplification' / name
        if path.exists():
            lineage[str(path.relative_to(root))] = digest(path.read_text())
    report = {'schema': 1, 'kind': 'bounded-stage-bundle-import-inlining', 'lean_verified': False,
              'max_destination_bytes': LIMIT, 'target': target,
              'before_closure_modules': len(before), 'after_closure_modules': len(after),
              'removed_active_modules': removed, 'moved_bundles': moved,
              'merged_destinations': len(set(moved.values())), 'files': metadata,
              'compatibility_facades': {str(paths[m].relative_to(root)): digest(paths[m].read_text()) for m in facades},
              'prior_receipt_sha256': lineage,
              'ancestry_note': 'Earlier receipts are unchanged. Reconstruct this pass inputs before validating predecessor receipts; current file hashes are not their old output hashes.'}
    return paths, originals, outputs, report


def check_saved_report(root=ROOT):
    report = json.loads((root / REPORT).read_text())
    originals = reconstruct_inputs(root, report)
    _, deps = graph(root)
    for module in deps:
        closure(deps, module)
    active = closure(deps, report['target'])
    assert not set(report['removed_active_modules']).intersection(active), 'Bypassed modules became active'
    for path, expected in report['prior_receipt_sha256'].items():
        assert digest((root / path).read_text()) == expected, 'Predecessor receipt changed'
    print(json.dumps({'status': 'EXACT_INVERSE_AND_GRAPH_PASS', 'lean_verified': False,
                      'reconstructed_files': len(originals), 'removed_active_modules': len(report['removed_active_modules']),
                      'current_closure_modules': len(active)}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.check:
        check_saved_report()
        return
    assert not (ROOT / REPORT).exists(), 'Receipt already exists; use --check'
    paths, originals, outputs, report = plan()
    if args.write:
        for module in outputs:
            assert paths[module].read_text() == originals[module], 'Source changed during planning'
        for module, output in outputs.items():
            paths[module].write_text(output)
        (ROOT / REPORT).write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
        reconstruct_inputs(ROOT, report)
    print(json.dumps({k: v for k, v in report.items() if k not in
                      ('files', 'compatibility_facades', 'moved_bundles', 'removed_active_modules')}, sort_keys=True))


if __name__ == '__main__':
    main()
