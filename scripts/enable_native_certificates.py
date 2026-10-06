#!/usr/bin/env python3
"""Convert only generated numerical certificates; preserve statements and data.

This is a source migration, not a compiler overlay or a second proof project.
Only selected generated proof families are eligible. Every changed file records
an exact kernel-source inverse hash; source-restoration callers must authenticate
that inverse before checking older receipts or pinned upstream sources.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

from check_sources import ROOT, code_only


SQPACK = re.compile(
    r'Sqpack/S11Opt/(?:Simplified/(?:ReducedConditional|CombinedConditional|StageBundles)/'
    r'|Bundled/(?:F[0-9]{2}|Own)/Leaves[0-9]+\.lean$'
    r'|Split/U(?:2G|2P|2R)/C[0-9]+/(?:Main|S[0-9]+)\.lean$'
    r'|F00/(?:Cov|Own)[0-9]+\.lean$)')
T07 = re.compile(r'ElevenSquare/Tasks/T07/Ext/Gen/(?:[^/]+/S[0-9]+|NearConn)\.lean$')
DECL = re.compile(r'^(?P<private>private )?(?P<kind>theorem|lemma|def|abbrev) (?P<name>[A-Za-z_][A-Za-z_0-9]*)\b')
SOUND = re.compile(r'^\s*(?:[A-Za-z_][A-Za-z_0-9]*\.)*soundDec\b[^\n]*\(by decide \+kernel\)\s*$')
NUMERICAL = re.compile(r'^(?:step_ok|promote_ok|pcov_ok|pc[0-9]+_ok|ok[0-9]+)$')


def convert(rel, data):
    """Return changed bytes and the exact public declaration occurrence counts."""
    sqpack, t07 = bool(SQPACK.match(rel)), bool(T07.fullmatch(rel))
    if not sqpack and not t07:
        return data, {}
    text = data.decode('utf-8')
    code = code_only(text)
    if 'native_decide' in code:
        raise ValueError('Source already has native checks: ' + rel)
    lines, masked = text.splitlines(keepends=True), code.splitlines(keepends=True)
    stack, namespace, owner, numerical = [], '', None, False
    declarations = {}
    for index, line in enumerate(masked):
        ns = re.fullmatch(r'namespace ([A-Za-z_][A-Za-z_0-9.]*)\s*', line)
        if ns:
            stack.append(namespace)
            namespace = namespace + '.' + ns[1] if namespace else ns[1]
            owner, numerical = None, False
            continue
        if re.fullmatch(r'section(?: [A-Za-z_][A-Za-z_0-9.]*)?\s*', line):
            stack.append(namespace)
            continue
        if re.fullmatch(r'end(?: [A-Za-z_][A-Za-z_0-9.]*)?\s*', line):
            namespace = stack.pop() if stack else ''
            owner, numerical = None, False
            continue
        decl = DECL.match(line)
        if decl:
            owner = None if decl['private'] or decl['kind'] not in ('theorem', 'lemma') else (
                namespace + '.' + decl['name'] if namespace else decl['name'])
            numerical = bool(owner and NUMERICAL.fullmatch(decl['name']))
        selected = owner and ((sqpack and SOUND.fullmatch(line)) or (t07 and numerical))
        if not selected:
            continue
        occurrences = list(re.finditer(r'\bdecide \+kernel\b', line))
        if not occurrences:
            continue
        # Masked and original positions agree, so comments are never rewritten.
        changed = lines[index]
        for match in reversed(occurrences):
            changed = changed[:match.start()] + 'native_decide' + changed[match.end():]
        lines[index] = changed
        declarations[owner] = declarations.get(owner, 0) + len(occurrences)
    changed = ''.join(lines).encode('utf-8')
    if code_only(changed.decode('utf-8')).replace('native_decide', 'decide +kernel') != code:
        raise ValueError('Migration changed more than numerical tactic calls: ' + rel)
    return changed, declarations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    manifest_path = ROOT / 'verification/native-certificates.json'
    files = json.loads(manifest_path.read_text())['files'] if manifest_path.is_file() else {}
    roots = ['Sqpack/S11Opt/Simplified', 'Sqpack/S11Opt/Bundled',
             'Sqpack/S11Opt/Split', 'Sqpack/S11Opt/F00',
             'ElevenSquare/Tasks/T07/Ext/Gen']
    for directory in roots:
        for path in sorted((ROOT / directory).rglob('*.lean')):
            rel = path.relative_to(ROOT).as_posix()
            raw = path.read_bytes()
            if rel in files:
                if hashlib.sha256(raw).hexdigest() != files[rel]['sha256']:
                    raise ValueError('Previously migrated source changed: ' + rel)
                continue
            changed, declarations = convert(rel, raw)
            if not declarations:
                continue
            files[rel] = {'sha256': hashlib.sha256(changed).hexdigest(),
                          'kernel_sha256': hashlib.sha256(raw).hexdigest(),
                          'declarations': declarations}
            if args.write:
                path.write_bytes(changed)
    manifest = {'format_version': 1,
                'trust_model': 'lean_kernel_and_native_compiler',
                'scope': 'Generated numerical checks only; soundness and geometric proofs unchanged.',
                'files': files}
    if args.write:
        (ROOT / 'verification/native-certificates.json').write_text(
            json.dumps(manifest, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'changed_files': len(files),
                      'numerical_declarations': sum(len(x['declarations']) for x in files.values()),
                      'native_calls': sum(sum(x['declarations'].values()) for x in files.values())}))


if __name__ == '__main__':
    main()
