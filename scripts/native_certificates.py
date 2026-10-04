"""Exact source inventory for compiler-backed numerical certificate checks.

The inventory grants native evaluation only to named numerical declarations in
hash-pinned source files. It never grants a general permission for native axioms.
"""
import hashlib
import json
from pathlib import Path
import re


MANIFEST = 'verification/native-certificates.json'
NATIVE = re.compile(r'\bnative_decide\b')
NATIVE_OPTION = re.compile(r'\+\s*native\b|\bnative\s*:=\s*true\b')


def _merge_files(files, additions):
    if not isinstance(additions, dict):
        raise ValueError('Invalid native certificate file inventory')
    for rel, entry in additions.items():
        path = Path(rel)
        if (path.is_absolute() or '..' in path.parts or path.as_posix() != rel
                or path.suffix != '.lean' or not rel.startswith(('Sqpack/', 'ElevenSquare/'))):
            raise ValueError('Invalid native certificate path: ' + rel)
        if (not isinstance(entry, dict)
                or not re.fullmatch(r'[0-9a-f]{64}', entry.get('sha256', ''))
                or not isinstance(entry.get('declarations'), dict)
                or not entry['declarations']):
            raise ValueError('Invalid native certificate entry: ' + rel)
        for name, count in entry['declarations'].items():
            if (not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', name)
                    or type(count) is not int or count <= 0):
                raise ValueError('Invalid native certificate declaration: ' + str(name))
        if rel in files and any(files[rel][key] != entry[key]
                                for key in ('sha256', 'declarations')):
            raise ValueError('Conflicting native certificate inventory: ' + rel)
        files[rel] = {**entry, **files.get(rel, {})}


def load_native_manifest(root):
    root = Path(root)
    files = {}
    path = root / MANIFEST
    if path.is_file():
        payload = json.loads(path.read_text(encoding='utf-8'))
        if payload.get('format_version') != 1:
            raise ValueError('Unknown native certificate inventory version')
        _merge_files(files, payload['files'])
    # These sources are derived locally from authenticated upstream releases.
    # The generator writes the same exact hash/declaration inventory per field.
    for field in range(1, 59):
        path = root / f'Sqpack/S11Opt/Bundled/F{field:02d}/source-manifest.json'
        if not path.is_file():
            continue
        payload = json.loads(path.read_text(encoding='utf-8'))
        additions = payload.get('native_certificates', {})
        prefix = f'Sqpack/S11Opt/Bundled/F{field:02d}/'
        if any(not rel.startswith(prefix) for rel in additions):
            raise ValueError('Native inventory escapes its generated field: ' + str(path))
        _merge_files(files, additions)
    for rel in files:
        if not (root / rel).is_file() or (root / rel).is_symlink():
            raise ValueError('Missing or nonregular native certificate source: ' + rel)
    return {'format_version': 1, 'files': files}


def native_declarations(manifest):
    return {name for entry in manifest['files'].values() for name in entry['declarations']}


def validate_native_source(relpath, data, manifest):
    entry = manifest['files'].get(relpath)
    if entry is None and b'native' not in data:
        return []
    # Import lazily so the lexical checker can use this module itself.
    from check_sources import code_only
    code = code_only(data.decode('utf-8'))
    count = len(NATIVE.findall(code))
    if NATIVE_OPTION.search(code):
        raise ValueError('Uninventoried native evaluation spelling in ' + relpath)
    if entry is None:
        if count:
            raise ValueError('Forbidden local proof form in ' + relpath + ': native_decide')
        return []
    if hashlib.sha256(data).hexdigest() != entry['sha256']:
        raise ValueError('Native certificate source hash mismatch: ' + relpath)
    if count != sum(entry['declarations'].values()):
        raise ValueError('Native certificate occurrence mismatch: ' + relpath)
    return sorted(entry['declarations'])
