#!/usr/bin/env python3
"""Give a generated cover proof its public name directly, removing a pure alias.

Every selected covN and covN_1 must have identical statements, with no other
references to covN_1 anywhere in the local source tree. Certificates are untouched.
Use --write to apply, --check to verify its saved receipt, or neither for a dry run.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
NS = re.compile(r'^namespace (\S+)$', re.M)
ALIAS = re.compile(r'^theorem (cov(\d+)) : ([^\n]+) := (cov\d+_1)\n\n', re.M)
OLD_NAME = re.compile(r'(?<![\w.])((?:\w+\.)*)(cov\d+_1)\b')
REPORT = ROOT / 'simplification/stage-root-aliases.json'


def sha(s):
    return hashlib.sha256(s.encode()).hexdigest()


def transform(source):
    matches = list(ALIAS.finditer(source))
    if not matches:
        return None
    assert len(matches) == 1
    alias = matches[0]
    public, index, statement, original = alias.groups()
    assert original == public + '_1'
    head = f'theorem {original} : {statement} :=\n'
    assert source.count(head) == 1
    assert len(re.findall(r'\b' + re.escape(original) + r'\b', source)) == 2
    without_alias = source[:alias.start()] + source[alias.end():]
    replacement = f'theorem {public} : {statement} :=\n'
    output = without_alias.replace(head, replacement, 1)
    inverse = output.replace(replacement, head, 1)
    inverse = inverse[:alias.start()] + alias.group() + inverse[alias.start():]
    assert inverse == source
    namespaces = NS.findall(source)
    assert len(namespaces) == 1
    return output, {'namespace': namespaces[0], 'public_name': public,
                    'original_name': original, 'statement_sha256': sha(statement),
                    'before_sha256': sha(source), 'after_sha256': sha(output),
                    'before_lines': len(source.splitlines()), 'after_lines': len(output.splitlines()),
                    'before_bytes': len(source.encode()), 'after_bytes': len(output.encode()),
                    'exact_inverse_reconstruction': True}



def check_saved_report(report_path=REPORT, root=ROOT):
    """Check current files against the receipt without repeating the rewrite."""
    from native_certificates import load_native_manifest, restore_kernel_source
    report = json.loads(Path(report_path).read_text())
    native_manifest = load_native_manifest(root)
    files = report['files']
    assert files and report['exact_public_statements_preserved'] == len(files)
    for name, info in files.items():
        relative = Path(name)
        assert not relative.is_absolute() and '..' not in relative.parts, name
        source = restore_kernel_source(name, (Path(root) / relative).read_bytes(),
                                       native_manifest).decode('utf-8')
        assert sha(source) == info['after_sha256'], f'Stale source hash: {name}'
        assert NS.findall(source) == [info['namespace']], f'Changed namespace: {name}'
        assert info['original_name'] == info['public_name'] + '_1', name
        statements = re.findall(
            r'^theorem ' + re.escape(info['public_name']) + r' : ([^\n]+) :=\n',
            source, re.M)
        assert len(statements) == 1, f'Missing or duplicate public theorem: {name}'
        assert sha(statements[0]) == info['statement_sha256'], f'Changed public statement: {name}'
        assert not re.search(r'\b' + re.escape(info['original_name']) + r'\b', source), \
            f'Removed theorem name reintroduced: {name}'
    return {'status': 'SAVED_SOURCE_RECEIPT_MATCHES', 'lean_verified': False,
            'files': len(files), 'public_statements_checked': len(files),
            'removed_names_absent': len(files)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.check:
        print(json.dumps(check_saved_report()))
        return
    changes = {}
    symbols = {}
    for path in sorted((ROOT / 'Sqpack/S11Opt/Split').glob('U*/C*/S*.lean')):
        result = transform(path.read_text())
        if result is None:
            continue
        _, info = result
        changes[path] = info
        symbols[(info['namespace'], info['original_name'])] = path
    assert changes, 'No unprocessed pure aliases found'
    # Independent global usage audit, including qualified references.
    for base in ['Sqpack', 'ElevenSquare']:
        for path in (ROOT / base).rglob('*.lean'):
            source = path.read_text()
            namespaces = NS.findall(source)
            for match in OLD_NAME.finditer(source):
                prefix, name = match.groups()
                if prefix:
                    keys = [key for key in symbols if key[1] == name and key[0].endswith(prefix[:-1])]
                else:
                    keys = [(ns, name) for ns in namespaces if (ns, name) in symbols]
                    # No silent resolution through a specifically opened case.
                    opened = re.findall(r'^open (\S*\.C\d+)\b', source, re.M)
                    keys += [(ns, name) for ns in opened if (ns, name) in symbols]
                for key in keys:
                    assert symbols[key] == path, f'External use of {key} in {path.relative_to(ROOT)}'
    files = {str(p.relative_to(ROOT)): info for p, info in changes.items()}
    report = {'status': 'SOURCE_ALIAS_REFACTOR_NOT_LEAN_ACCEPTANCE', 'lean_verified': False,
              'exact_public_statements_preserved': len(files),
              'external_original_name_references': 0,
              'certificate_proof_bodies': 'Byte-identical; only the theorem name changes.',
              'files': files,
              'removed_lines': sum(f['before_lines'] - f['after_lines'] for f in files.values()),
              'removed_bytes': sum(f['before_bytes'] - f['after_bytes'] for f in files.values())}
    if args.write:
        for path, info in changes.items():
            source = path.read_text()
            assert sha(source) == info['before_sha256']
            output, actual = transform(source)
            assert actual == info
            path.write_text(output)
        REPORT.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'files': len(files), 'removed_lines': report['removed_lines'],
                      'removed_bytes': report['removed_bytes'], 'written': args.write}))


if __name__ == '__main__':
    main()
