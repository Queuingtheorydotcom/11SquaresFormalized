#!/usr/bin/env python3
"""Read-only, source-only guard for the narrowly scoped T06 transport port.

Run with Python 3 and Git; no Lean, Lake, verifier cache, or saved preservation
report is consulted. JSON goes to stdout (including failures), and no files are
written. This establishes source preservation, not kernel acceptance or axioms.
The fixed base commit must be present in the selected repository.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


BASE_COMMIT = '525f4a68bd06a431ed81c19218b2666fe1cdff2e'
T06 = 'ElevenSquare/Tasks/T06'
PACKET = 'ElevenSquare/Pending/S08_ExactPacket.lean'
BRIDGE = T06 + '/CertificateBridge.lean'
AUDIT = T06 + '/LocalIsolationAudit.lean'
SHARDS = [T06 + f'/CertificateInteger{i:03d}.lean' for i in range(128)]
AUDIT_TARGETS = [
    'ElevenSquare.Pending.exact_local_packet_exists',
    'ElevenSquare.Pending.construction_locally_isolated',
]
AUDIT_SOURCE = (
    'import ElevenSquare.Pending.S08_ExactPacket\n\n'
    '/-! Axiom audit of the actual exact local-isolation certificate chain. -/\n\n'
    + ''.join('#print axioms ' + name + '\n' for name in AUDIT_TARGETS)
).encode()
BRIDGE_BEFORE = (
    b'        1000000000000000000000000 by norm_num, '
    b'mul_ite, mul_zero, mul_comm] using hcheck)\n'
)
BRIDGE_AFTER = BRIDGE_BEFORE.replace(b'mul_zero, ', b'mul_zero, zero_mul, ')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(source):
    return hashlib.sha256(source).hexdigest()


def record(base, current, reconstructed=None):
    result = {'base_sha256': sha256(base), 'current_sha256': sha256(current)}
    if reconstructed is not None:
        result['reconstructed_sha256'] = sha256(reconstructed)
    return result


def integer_checks(source, branch):
    """Require the ordered Cartesian coverage and retain whole declarations."""
    tag = f'{branch:03d}'
    declarations = re.findall(
        r'^theorem (integerCheck\d+_\d+_\d+) :\n'
        r'([\s\S]*?)(?=\n(?:theorem|def|end)\b|\Z)', source, re.M)
    expected = [f'integerCheck{tag}_{j}_{s}' for j in range(33) for s in range(2)]
    require([name for name, _ in declarations] == expected,
            f'{tag}: integerCheck coverage must be exactly 33 x 2')
    for (name, body), (j, s) in zip(
            declarations, ((j, s) for j in range(33) for s in range(2))):
        statement = (
            f'    integerResidualCheck {branch} {j} {s} (dualNumerators{tag} {j} {s}) ∧\n'
            f'    integerMassCheck {branch} {j} {s} (dualNumerators{tag} {j} {s}) := by\n')
        require(body.startswith(statement), f'{name}: unexpected public statement')
    return declarations


def branch_dots_span(source, tag):
    start = f'theorem branchDots{tag} '
    end = f'\ndef branchIntegerCurvature{tag} '
    require(source.count(start) == source.count(end) == 1,
            f'{tag}: expected one branchDots and curvature boundary')
    first, last = source.index(start), source.index(end)
    require(first < last, f'{tag}: reversed branchDots boundaries')
    return first, last


def check_shard(base_bytes, current_bytes, branch):
    """Reverse only exact allowed additions, then compare the complete bytes."""
    tag = f'{branch:03d}'
    base, current = base_bytes.decode('utf-8'), current_bytes.decode('utf-8')
    base_checks = integer_checks(base, branch)
    current_checks = integer_checks(current, branch)
    require(current_checks == base_checks, f'{tag}: integerCheck declarations changed')

    # Independently derive each helper's RHS from the BASE vector, not from the
    # patched proofs, the patch generator, or any saved preservation report.
    vectors = re.findall(
        rf'^def branchSparseDots{tag} : Fin 33 → \(Fin 42 → ℕ\) → ℤ :=\n'
        r'  !\[([^\n]+)\]\n\n', base, re.M)
    require(len(vectors) == 1, f'{tag}: expected one base sparse-dot vector')
    dots = vectors[0].split(', ')
    require(len(dots) == 33 and all(re.fullmatch(r'sparseDot\d+', dot) for dot in dots),
            f'{tag}: base sparse-dot vector must have 33 entries')
    helpers = '-- Keep vector indexing opaque when transporting the large matrix sum.\n'
    helpers += ''.join(
        f'private theorem branchSparseDot{tag}_{j} :\n'
        f'    branchSparseDots{tag} {j} = {dot} := rfl\n\n'
        for j, dot in enumerate(dots))
    begin, end = branch_dots_span(current, tag)
    require(current.count(helpers) == 1 and current[:begin].endswith(helpers),
            f'{tag}: missing or changed private rfl helpers')
    body = current[begin:end]
    base_begin, base_end = branch_dots_span(base, tag)
    base_body = base[base_begin:base_end]
    for j, dot in enumerate(dots):
        prefix = f'      _ = {dot} n := branchDot{tag}_{j} n\n      _ = _ := '
        old = prefix + 'rfl\n'
        new = prefix + f'congrFun branchSparseDot{tag}_{j}.symm n\n'
        require(base_body.count(old) == 1, f'{tag}/{j}: unexpected base calc branch')
        require(body.count(new) == 1, f'{tag}/{j}: missing or changed congrFun transport')
        body = body.replace(new, old, 1)
    reconstructed = (current[:begin - len(helpers)] + body + current[end:]).encode('utf-8')
    require(reconstructed == base_bytes,
            f'{tag}: source differs outside the allowed helpers and transports')
    check_bytes = ''.join('theorem ' + name + ' :\n' + body
                          for name, body in current_checks).encode('utf-8')
    return {**record(base_bytes, current_bytes, reconstructed),
            'integer_checks': 66, 'integer_checks_sha256': sha256(check_bytes),
            'private_rfl_helpers': 33, 'congrFun_transports': 33}


def check_bridge(base, current):
    require(base.count(BRIDGE_BEFORE) == 1, 'CertificateBridge: unexpected base proof')
    require(current.count(BRIDGE_AFTER) == 1, 'CertificateBridge: missing zero_mul change')
    reconstructed = current.replace(BRIDGE_AFTER, BRIDGE_BEFORE, 1)
    require(reconstructed == base, 'CertificateBridge: unexpected change beyond zero_mul')
    return record(base, current, reconstructed)


def check_audit(current):
    # Exact source also excludes extra imports, local shadowing, hidden queries,
    # commented-out targets, and options that could weaken this small audit.
    require(current == AUDIT_SOURCE, 'LocalIsolationAudit: unexpected audit source')
    return {'current_sha256': sha256(current), 'imports': ['ElevenSquare.Pending.S08_ExactPacket'],
            'axiom_queries': AUDIT_TARGETS}


def check_snapshot(base, current):
    """Check all T06 files plus S08; other repository paths are out of scope."""
    require(set(SHARDS + [BRIDGE, PACKET]).issubset(base), 'Base is missing required sources')
    require(AUDIT not in base, 'Base unexpectedly already contains LocalIsolationAudit')
    require(set(current) == set(base) | {AUDIT},
            'Source inventory changed: missing=' + ','.join(sorted(set(base) - set(current)))
            + '; unexpected=' + ','.join(sorted(set(current) - set(base) - {AUDIT})))
    expected_shards = set(SHARDS)
    require({path for path in base if re.search(r'/CertificateInteger\d+\.lean$', path)}
            == expected_shards, 'Base shard inventory must be exactly 000 through 127')
    files = {}
    for branch, path in enumerate(SHARDS):
        files[path] = check_shard(base[path], current[path], branch)
    files[BRIDGE] = check_bridge(base[BRIDGE], current[BRIDGE])
    files[AUDIT] = check_audit(current[AUDIT])
    unchanged = sorted(set(base) - expected_shards - {BRIDGE})
    for path in unchanged:
        require(current[path] == base[path], f'Unexpected change to {path}')
        files[path] = record(base[path], current[path])
    return {'status': 'T06_SOURCE_PRESERVATION_PASS', 'base_commit': BASE_COMMIT,
            'scope': [T06, PACKET], 'kernel_validation': 'not_run',
            'shards': 128, 'coverage': [128, 33, 2], 'integer_checks': 8448,
            'private_rfl_helpers': 4224, 'congrFun_transports': 4224,
            'unchanged_files': len(unchanged), 'files': files}


def git(root, *args, input_bytes=None):
    result = subprocess.run(['git', '--no-replace-objects', '--no-optional-locks', '-C', str(root), *args], input=input_bytes,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    require(result.returncode == 0,
            'Git read failed: ' + result.stderr.decode('utf-8', errors='replace').strip())
    return result.stdout


def load_base(root):
    """Read pinned Git blobs in one batch; never read HEAD or working-tree reports."""
    entries = git(root, 'ls-tree', '-rz', BASE_COMMIT, '--', T06, PACKET).split(b'\0')
    objects = []
    for entry in filter(None, entries):
        info, path = entry.split(b'\t', 1)
        mode, kind, oid = info.split()
        require(kind == b'blob' and mode in (b'100644', b'100755'),
                'Base contains a non-regular source')
        objects.append((path.decode('utf-8'), oid))
    data = git(root, 'cat-file', '--batch', input_bytes=b''.join(oid + b'\n' for _, oid in objects))
    base, offset = {}, 0
    for path, oid in objects:
        end = data.index(b'\n', offset)
        returned_oid, kind, size = data[offset:end].split()
        require(returned_oid == oid and kind == b'blob', 'Unexpected Git batch response')
        offset = end + 1
        base[path] = data[offset:offset + int(size)]
        offset += int(size)
        require(data[offset:offset + 1] == b'\n', 'Truncated Git blob response')
        offset += 1
    require(offset == len(data), 'Trailing Git batch response')
    return base


def load_current(root):
    directory = root / T06
    require(directory.is_dir() and not directory.is_symlink(), 'T06 source directory is missing or symlinked')
    paths = list(directory.rglob('*')) + [root / PACKET]
    current = {}
    for path in paths:
        require(not path.is_symlink(), 'Symlink in source scope: ' + path.relative_to(root).as_posix())
        if path.is_dir():
            continue
        require(path.is_file(), 'Missing or non-regular source: ' + path.relative_to(root).as_posix())
        current[path.relative_to(root).as_posix()] = path.read_bytes()
    return current


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1],
                        help='repository to read (default: parent of this script directory)')
    args = parser.parse_args(argv)
    try:
        report = check_snapshot(load_base(args.root), load_current(args.root))
    except (OSError, ValueError) as error:
        report = {'status': 'T06_SOURCE_PRESERVATION_FAIL', 'base_commit': BASE_COMMIT,
                  'error': str(error), 'kernel_validation': 'not_run'}
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report['status'] == 'T06_SOURCE_PRESERVATION_PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
