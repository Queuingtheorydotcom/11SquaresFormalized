#!/usr/bin/env python3
"""Count and hash the actual local theorem import closure, including certificate data."""
from pathlib import Path
import argparse
import hashlib
import json
from check_sources import ROOT, code_only, import_names


def census(target):
    paths = sorted((ROOT / 'ElevenSquare').rglob('*.lean')) + sorted((ROOT / 'Sqpack').rglob('*.lean'))
    paths += [ROOT / 'ElevenSquare.lean', ROOT / 'Sqpack.lean']
    modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p for p in paths}
    if target not in modules:
        raise ValueError("Unknown local theorem target: " + target)
    active, done, external = [], {}, set()
    missing, cycles, links = [], [], []
    def visit(module):
        if module in active:
            cycles.append(active[active.index(module):] + [module])
            return
        if module in done:
            return
        if module not in modules:
            if module.startswith(('ElevenSquare', 'Sqpack')):
                missing.append(module)
            else:
                external.add(module)
            return
        p = modules[module]
        data = p.read_bytes()
        deps = import_names(code_only(data.decode('utf-8')))
        active.append(module)
        for dep in deps:
            visit(dep)
        active.pop()
        rel = p.relative_to(ROOT).as_posix()
        if p.is_symlink():
            links.append(rel)
        done[module] = {'module': module, 'path': rel, 'bytes': len(data),
                        'physical_lines': data.count(b'\n') + bool(data and not data.endswith(b'\n')),
                        'sha256': hashlib.sha256(data).hexdigest(), 'imports': deps}
    visit(target)
    files = sorted(done.values(), key=lambda f: f['path'])
    return {'status': 'SOURCE_CENSUS_ONLY_NOT_LEAN_ACCEPTANCE',
        'scope': 'Current local Lean theorem import closure, including all reached certificate data; excludes fixed Lean and Mathlib dependencies.',
        'target': target,
        'method': 'Lean header lexer from check_sources.py; physical lines counted directly from source bytes. No generated certificate sources are excluded.',
        'local_modules': len(files), 'physical_lines': sum(f['physical_lines'] for f in files),
        'bytes': sum(f['bytes'] for f in files), 'missing_local_imports': sorted(set(missing)),
        'import_cycles': cycles, 'symlink_sources': links, 'external_imports': sorted(external),
        'kernel_replay_performed': False, 'files': files}


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--target', default='ElevenSquare.Optimality')
    ap.add_argument('--write', action='store_true')
    args = ap.parse_args()
    result = census(args.target)
    assert not result['missing_local_imports'] and not result['import_cycles'] and not result['symlink_sources']
    if args.write:
        (ROOT / 'simplification/checkpoint-census.json').write_text(json.dumps(result, indent=2) + '\n')
        path = ROOT / 'simplification/source-manifest.json'
        manifest = json.loads(path.read_text())
        files = {f['path']: f for f in manifest['files']}
        closure = {f['path']: f for f in result['files']}
        for f in files.values():
            if f['kind'] == 'exact theorem closure' and f['path'] not in closure:
                f['kind'] = 'support outside counted theorem closure'
        for f in result['files']:
            files[f['path']] = {k: f[k] for k in ('path', 'bytes', 'sha256')}
            files[f['path']]['kind'] = 'exact theorem closure'
        for rel, f in files.items():
            data = (ROOT / rel).read_bytes()
            f.update(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
        manifest['files'] = [files[k] for k in sorted(files)]
        manifest['theorem_closure'] = {'lines': result['physical_lines'], 'bytes': result['bytes'],
                                      'modules': result['local_modules']}
        manifest['kernel_replay_performed'] = False
        path.write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('files', 'external_imports')}, indent=2))
