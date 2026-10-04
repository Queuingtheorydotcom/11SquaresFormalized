#!/usr/bin/env python3
"""Move single-consumer T07 certificate/P modules into their stage modules.

This source transformation does not run Lean. Old module paths remain import-only
compatibility reexports. They leave the theorem closure, but --all still checks
them. Default: dry run; --write: apply; --check: verify the saved inverse receipt.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
from check_sources import ROOT, code_only, import_names

TARGET = 'ElevenSquare.Optimality'
REPORT = ROOT / 'simplification/t07-stage-bundling.json'
MAX_STAGE_BYTES = 10_000_000
PREFIX = 'ElevenSquare.Tasks.T07.Ext.Gen.'
DECL = re.compile(r'^(def|theorem|lemma|abbrev|instance|structure|inductive|axiom)\s+([^\s:(]+)', re.M)
FORBIDDEN = re.compile(r'^\s*(?:private|protected|noncomputable|unsafe|attribute|local|scoped|syntax|macro|initialize|section)\b', re.M)


def digest(text):
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def metrics(text):
    return {'sha256': digest(text), 'bytes': len(text.encode('utf-8')),
            'lines': text.count('\n') + bool(text and not text.endswith('\n'))}


def split_source(text):
    code = code_only(text)
    scopes = list(re.finditer(r'^namespace\s+([A-Za-z0-9_.]+)[ \t]*$', code, re.M))
    assert len(scopes) == 1, 'Expected exactly one namespace'
    start, namespace = scopes[0].start(), scopes[0][1]
    ends = list(re.finditer(r'^end(?:\s+([^\s]+))?[ \t]*$', code, re.M))
    assert len(ends) == 1 and ends[0][1] == namespace, 'Unexpected namespace ending'
    assert not code[ends[0].end():].strip(), 'Commands after namespace end'
    header = code[:start]
    rest = re.sub(r'\bimport[ \t]+[A-Za-z0-9_.]+\s*', '', header)
    assert not rest.strip(), 'Unsupported module header'
    imports = import_names(code)
    assert imports and len(imports) == len(set(imports)), 'Empty or duplicate import header'
    assert text.endswith('\n'), 'Missing final newline would join namespace boundaries'
    return imports, text[start:], namespace


def declaration_records(body, namespace):
    code = code_only(body)
    declarations = list(DECL.finditer(code))
    assert declarations, 'No declarations'
    finish = re.search(r'^end\s+' + re.escape(namespace) + r'[ \t]*$', code, re.M).start()
    records = []
    for index, match in enumerate(declarations):
        end = declarations[index + 1].start() if index + 1 < len(declarations) else finish
        block = body[match.start():end]
        records.append({'kind': match[1], 'name': match[2],
                        'qualified_name': namespace + '.' + match[2],
                        'declaration_block_sha256': digest(block)})
    return records


def merge_stage(stage_module, stage_text, donors):
    stage_imports, stage_body, namespace = split_source(stage_text)
    assert stage_module.startswith(PREFIX) and re.fullmatch(r'S\d+', stage_module.rsplit('.', 1)[1])
    assert donors and set(donors) <= set(stage_imports), 'Donor missing from stage imports'
    assert stage_module not in stage_imports, 'Stage imports itself'
    stage_options = re.findall(r'^set_option[^\n]+', code_only(stage_body), re.M)
    original_sources = []
    names = Counter()
    # Preserve the stage's original import order for every moved donor.
    for module in [m for m in stage_imports if m in donors] + [stage_module]:
        text = stage_text if module == stage_module else donors[module]
        imports, body, own_namespace = split_source(text)
        assert own_namespace == namespace, 'Namespace mismatch: ' + module
        assert stage_module not in imports, 'Donor imports its destination: ' + module
        assert not FORBIDDEN.search(code_only(body)), 'Module-sensitive command: ' + module
        assert re.findall(r'^set_option[^\n]+', code_only(body), re.M) == stage_options, 'Option mismatch: ' + module
        declarations = declaration_records(body, namespace)
        if module != stage_module:
            suffix = module.removeprefix(stage_module)
            if re.fullmatch(r'C\d+', suffix):
                assert all(d['kind'] == 'def' and re.fullmatch(r'cert\d+', d['name'])
                           for d in declarations), 'Non-certificate declaration: ' + module
            elif suffix == 'P':
                assert all(d['kind'] in ('theorem', 'lemma') and re.fullmatch(r'pc(?:\d+|ov)_ok', d['name'])
                           for d in declarations), 'Unexpected P declaration: ' + module
            else:
                raise AssertionError('Unsupported donor role: ' + module)
        names.update(d['qualified_name'] for d in declarations)
        original_sources.append((module, text, imports, body, declarations))
    assert not [n for n, count in names.items() if count > 1], 'Duplicate declaration names'

    imports = []
    # Keep existing non-donor imports first; append newly required donor imports.
    for deps in [stage_imports] + [item[2] for item in original_sources[:-1]]:
        for dep in deps:
            if dep not in donors and dep not in imports:
                assert dep != stage_module, 'Merged import back edge'
                imports.append(dep)
    merged = ''.join('import ' + dep + '\n' for dep in imports) + '\n'
    segments = []
    for module, text, deps, body, declarations in original_sources:
        start = len(merged)
        merged += body
        segments.append({'module': module, 'before': metrics(text), 'imports': deps,
                         'original_header': text[:-len(body)],
                         'body_sha256': digest(body), 'body_character_start': start,
                         'body_character_end': len(merged), 'declarations': declarations})
    assert len(merged.encode('utf-8')) <= MAX_STAGE_BYTES, 'Merged stage exceeds 10 MB: ' + stage_module
    wrappers = {module: 'import ' + stage_module + '\n' for module in donors}
    metadata = {'stage': stage_module, 'namespace': namespace, 'imports': imports,
                'before': metrics(stage_text), 'after': metrics(merged),
                'segments': segments,
                'reexports': {m: metrics(s) for m, s in sorted(wrappers.items())}}
    return merged, wrappers, metadata


def module_paths(root=ROOT):
    paths = sorted((root / 'ElevenSquare').rglob('*.lean')) + sorted((root / 'Sqpack').rglob('*.lean'))
    paths += [root / 'ElevenSquare.lean', root / 'Sqpack.lean']
    return {'.'.join(p.relative_to(root).with_suffix('').parts): p for p in paths}


def load_graph(paths):
    return {module: import_names(code_only(path.read_text())) for module, path in paths.items()}


def graph_audit(graph):
    done, active, missing, cycles = set(), [], set(), []
    def visit(module):
        if module not in graph:
            if module.startswith(('ElevenSquare', 'Sqpack')):
                missing.add(module)
            return
        if module in active:
            cycles.append(active[active.index(module):] + [module])
            return
        if module in done:
            return
        active.append(module)
        for dep in graph[module]:
            visit(dep)
        active.pop()
        done.add(module)
    visit(TARGET)
    closure = set(done)
    for module in sorted(graph):
        visit(module)
    audit = {'total_local_modules': len(graph), 'target': TARGET,
             'target_closure_modules': len(closure),
             'missing_local_imports': sorted(missing), 'cycles': cycles,
             'graph_sha256': digest(json.dumps(graph, sort_keys=True))}
    assert not missing and not cycles, 'Incomplete or cyclic import graph: ' + str(audit)
    return audit, closure


def plan():
    paths = module_paths()
    graph = load_graph(paths)
    before_graph, before_closure = graph_audit(graph)
    reverse = defaultdict(list)
    for module, imports in graph.items():
        for dep in imports:
            reverse[dep].append(module)
    donors = {m for m in paths if m.startswith(PREFIX)
              and re.fullmatch(r'S\d+(?:C\d+|P)', m.rsplit('.', 1)[1])}
    groups = defaultdict(list)
    for donor in sorted(donors):
        stage = re.sub(r'(?:C\d+|P)$', '', donor)
        assert reverse[donor] == [stage], 'Donor is not a sole-stage dependency: ' + donor
        assert donor in before_closure, 'Donor not in theorem closure: ' + donor
        groups[stage].append(donor)
    assert len(donors) == 1301 and len(groups) == 459, 'Unexpected generated source scope'
    plans = []
    new_graph = {m: list(ds) for m, ds in graph.items()}
    for stage, group in sorted(groups.items()):
        stage_text = paths[stage].read_text()
        source = {m: paths[m].read_text() for m in group}
        merged, wrappers, metadata = merge_stage(stage, stage_text, source)
        plans.append(metadata)
        new_graph[stage] = metadata['imports']
        for donor in group:
            new_graph[donor] = [stage]
    after_graph, after_closure = graph_audit(new_graph)
    assert before_closure - after_closure == donors, 'Unexpected removed dependency'
    assert not after_closure - before_closure, 'Unexpected new dependency'
    before_lines = sum(segment['before']['lines'] for item in plans for segment in item['segments'])
    after_lines = sum(item['after']['lines'] for item in plans)
    prior_path = ROOT / 'simplification/t07-witness-parametric-pilot.json'
    prior_text = prior_path.read_text()
    prior = json.loads(prior_text)
    before_sources = {s['module']: s['before']['sha256'] for item in plans for s in item['segments']}
    ancestry = []
    for item in [prior, prior['stage_consumer']]:
        module = item['file'].removesuffix('.lean').replace('/', '.')
        assert before_sources[module] == item['after_sha256'], 'Earlier witness receipt does not match merger input'
        ancestry.append({'file': item['file'], 'original_witness_input_sha256': item['before_sha256'],
                         'witness_output_and_bundle_input_sha256': item['after_sha256']})
    report = {'schema': 1, 'kind': 'exact-source-T07-stage-bundling',
              'status': 'SOURCE_PRESERVATION_ONLY_NOT_LEAN_ACCEPTANCE',
              'kernel_replay_performed': False,
              'scope': '842 certificate shards and 459 P modules into 459 stages; old paths are compatibility reexports.',
              'startup_scope': '1301 fewer reachable modules for the final-theorem build; --all still includes all reexports.',
              'certificate_shards': 842, 'P_modules': 459, 'stages': 459,
              'declarations_moved': sum(len(s['declarations']) for p in plans for s in p['segments'][:-1]),
              'target_closure_modules_removed': len(donors),
              'target_closure_lines_removed': before_lines - after_lines,
              'largest_merged_stage_bytes': max(p['after']['bytes'] for p in plans),
              'before_graph': before_graph, 'after_graph': after_graph, 'files': plans,
              'prior_receipts': [{'path': str(prior_path.relative_to(ROOT)),
                                  'sha256': digest(prior_text), 'source_links': ancestry}],
              'ancestry_note': 'Each segment reconstructs its complete original source and hash. Earlier compact-witness receipts are retained unchanged; S137C0 ancestry is recorded by its own segment.'}
    return paths, report


def reconstruct_inputs(root, ledger=None, modules=None):
    """Validate inverse source segments and return original relative-path texts.

    Pass module names in modules to reconstruct only selected stages' inputs.
    Without this filter the returned texts include all moved numerical data.
    No old bodies are stored in the receipt: they come from the merged source.
    """
    root = Path(root)
    ledger = json.loads((root / 'simplification/t07-stage-bundling.json').read_text()) if ledger is None else ledger
    requested = set(modules) if modules is not None else None
    result = {}
    path = lambda module: root / (module.replace('.', '/') + '.lean')
    for entry in ledger['files']:
        members = {s['module'] for s in entry['segments']}
        if requested is not None and not requested & members:
            continue
        stage = entry['stage']
        merged = path(stage).read_text()
        assert metrics(merged) == entry['after'], 'Stale merged stage: ' + stage
        assert import_names(code_only(merged)) == entry['imports'], 'Changed stage imports: ' + stage
        cursor = len(''.join('import ' + dep + '\n' for dep in entry['imports']) + '\n')
        for segment in entry['segments']:
            assert segment['body_character_start'] == cursor, 'Noncontiguous source segments'
            cursor = segment['body_character_end']
            body = merged[segment['body_character_start']:cursor]
            assert digest(body) == segment['body_sha256'], 'Changed moved source body'
            original = segment['original_header'] + body
            assert metrics(original) == segment['before'], 'Original source cannot be reconstructed'
            deps, parsed_body, ns = split_source(original)
            assert parsed_body == body and ns == entry['namespace'] and deps == segment['imports']
            assert declaration_records(body, ns) == segment['declarations'], 'Changed public declaration block'
            if requested is None or segment['module'] in requested:
                result[segment['module'].replace('.', '/') + '.lean'] = original
        assert cursor == len(merged), 'Unaccounted merged source suffix'
        for donor, expected in entry['reexports'].items():
            wrapper = path(donor).read_text()
            assert wrapper == 'import ' + stage + '\n', 'Changed compatibility reexport: ' + donor
            assert metrics(wrapper) == expected
    return result


def check_saved_report(report=None):
    report = json.loads(REPORT.read_text()) if report is None else report
    paths = module_paths()
    moved, declaration_count, before_hashes = set(), 0, {}
    for entry in report['files']:
        stage = entry['stage']
        merged = paths[stage].read_text()
        texts = reconstruct_inputs(ROOT, {'files': [entry]})
        reconstructed = {p.removesuffix('.lean').replace('/', '.'): text for p, text in texts.items()}
        for segment in entry['segments']:
            before_hashes[segment['module'].replace('.', '/') + '.lean'] = segment['before']['sha256']
            if segment['module'] != stage:
                moved.add(segment['module'])
                declaration_count += len(segment['declarations'])
        original_stage = reconstructed.pop(stage)
        rebuilt, wrappers, metadata = merge_stage(stage, original_stage, reconstructed)
        assert rebuilt == merged and metadata == entry, 'Non-deterministic source reconstruction'
        for donor, wrapper in wrappers.items():
            assert paths[donor].read_text() == wrapper, 'Changed compatibility reexport: ' + donor
            assert metrics(wrapper) == entry['reexports'][donor]
    graph, closure = graph_audit(load_graph(paths))
    assert not moved & closure, 'Compatibility reexports returned to theorem closure'
    assert len(moved) == report['target_closure_modules_removed'] == 1301
    assert declaration_count == report['declarations_moved']
    for receipt in report['prior_receipts']:
        assert digest((ROOT / receipt['path']).read_text()) == receipt['sha256'], 'Earlier witness receipt was changed'
        for link in receipt['source_links']:
            expected = link.get('active_bundle_input_sha256', link['witness_output_and_bundle_input_sha256'])
            assert before_hashes[link['file']] == expected, 'Broken witness ancestry'
    if report.get('excluded_compact_pilot'):
        assert 'ElevenSquare.Tasks.T07.Ext.CompactWitness' not in closure, 'Compact recipes remain in active proof'
    return {'status': 'SOURCE_ROUNDTRIP_PASS_NOT_LEAN_ACCEPTANCE',
            'stages': len(report['files']), 'reexports': len(moved),
            'public_declaration_blocks_preserved': declaration_count,
            'target_closure_modules': len(closure),
            'global_import_graph_matches_recorded_snapshot': graph['graph_sha256'] == report['after_graph']['graph_sha256'],
            'kernel_replay_performed': False}


def exclude_compact_pilot():
    """Restore just S137's literal HEAD inputs after the measured regression."""
    report_text = REPORT.read_text()
    report = json.loads(report_text)
    assert not report.get('excluded_compact_pilot'), 'Compact pilot already excluded'
    stage = PREFIX + 'P2.S137'
    index = next(i for i, entry in enumerate(report['files']) if entry['stage'] == stage)
    previous = report['files'][index]
    texts = reconstruct_inputs(ROOT, {'files': [previous]})
    original = {p.removesuffix('.lean').replace('/', '.'): text for p, text in texts.items()}
    receipt_meta = report['prior_receipts'][0]
    receipt_text = (ROOT / receipt_meta['path']).read_text()
    assert digest(receipt_text) == receipt_meta['sha256'], 'Earlier witness receipt changed'
    prior = json.loads(receipt_text)
    replacements = []
    for item in [prior, prior['stage_consumer']]:
        module = item['file'].removesuffix('.lean').replace('/', '.')
        assert digest(original[module]) == item['after_sha256'], 'Unexpected compact pilot input'
        literal = subprocess.check_output(['git', 'show', 'HEAD:' + item['file']], cwd=ROOT).decode('utf-8')
        assert digest(literal) == item['before_sha256'], 'HEAD is not the recorded literal baseline'
        original[module] = literal
        replacements.append({'file': item['file'], 'excluded_experiment_sha256': item['after_sha256'],
                             'restored_literal_sha256': digest(literal)})
    stage_source = original.pop(stage)
    merged, wrappers, updated = merge_stage(stage, stage_source, original)
    for donor, wrapper in wrappers.items():
        assert (ROOT / (donor.replace('.', '/') + '.lean')).read_text() == wrapper
    paths = module_paths()
    before_graph, before_closure = graph_audit(load_graph(paths))
    report['files'][index] = updated
    report['target_closure_lines_removed'] = sum(s['before']['lines'] for p in report['files'] for s in p['segments']) - sum(p['after']['lines'] for p in report['files'])
    report['excluded_compact_pilot'] = {
        'status': 'HISTORICAL_EXPERIMENT_NOT_IN_ACTIVE_PROOF',
        'reason': 'Complete S135 scout measured original literal CPU 54.126 s versus compact CPU 132.407 s (wall 69.65 s versus 235.11 s). Restore literal certificates; no full-build runtime inferred.',
        'previous_bundle_receipt_sha256': digest(report_text),
        'previous_S137_entry': previous,
        'replacements': replacements,
        'before_graph': before_graph,
        'kernel_replay_performed': False}
    receipt_meta['active_proof'] = False
    receipt_meta['status'] = 'HISTORICAL_EXPERIMENT_NOT_IN_ACTIVE_PROOF'
    for link in receipt_meta['source_links']:
        link['active_bundle_input_sha256'] = link['original_witness_input_sha256']
    report['ancestry_note'] = 'Current segments reconstruct every active pre-bundling source. S137 and S137C0 use the recorded original literal baseline. The unchanged parametric witness receipt and previous S137 bundle entry are retained as inactive experimental evidence.'
    # Only this production stage changes. Its four compatibility imports stay put.
    paths[stage].write_text(merged)
    after_graph, after_closure = graph_audit(load_graph(paths))
    assert not after_closure - before_closure, 'Restoring literals introduced new dependencies'
    assert 'ElevenSquare.Tasks.T07.Ext.CompactWitness' not in after_closure
    report['excluded_compact_pilot']['after_graph'] = after_graph
    report['excluded_compact_pilot']['additional_inactive_modules'] = sorted(before_closure - after_closure)
    REPORT.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    focused_path = ROOT / 'simplification/focused-checks-20261003.json'
    focused = json.loads(focused_path.read_text())
    match = next(row for row in focused['modules'] if row['module'] == stage + 'C0')
    assert match['source_sha256'] == prior['after_sha256']
    match.update(status='historical_experiment_accepted', active_proof=False,
                 note='Accepted parametric certificate definitions from the compact experiment. The active merged S137 now contains original literal certificates after a measured runtime regression; this receipt does not certify the current merged stage or compatibility reexport.')
    focused_path.write_text(json.dumps(focused, indent=2) + '\n')
    print(json.dumps({'status': 'COMPACT_PILOT_EXCLUDED_SOURCE_ONLY', 'stage': stage,
                      'target_closure_modules': len(after_closure), 'kernel_replay_performed': False}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--exclude-compact-pilot', action='store_true',
                      help='Restore only the recorded S137 literal inputs after the measured regression.')
    args = parser.parse_args()
    if args.check:
        print(json.dumps(check_saved_report(), sort_keys=True))
        return
    if args.exclude_compact_pilot:
        exclude_compact_pilot()
        return
    assert not REPORT.exists(), 'A receipt already exists; use --check, do not overwrite ancestry'
    paths, report = plan()
    if args.write:
        # Save the exact planned inverse map before the first source mutation.
        REPORT.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
        for entry in report['files']:
            stage = entry['stage']
            source = {segment['module']: paths[segment['module']].read_text()
                      for segment in entry['segments']}
            assert all(metrics(source[s['module']]) == s['before'] for s in entry['segments']), 'Source changed during planning'
            merged, wrappers, actual = merge_stage(stage, source.pop(stage), source)
            assert actual == entry
            paths[stage].write_text(merged)
            for donor, wrapper in wrappers.items():
                paths[donor].write_text(wrapper)
        print(json.dumps(check_saved_report(report), sort_keys=True))
    print(json.dumps({k: v for k, v in report.items() if k != 'files'}, sort_keys=True))


if __name__ == '__main__':
    main()
