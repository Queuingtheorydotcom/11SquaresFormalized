#!/usr/bin/env python3
"""Hosted-runner preparation, bounded serial replay, and accepted-receipt transfer.

Never run `prepare` on a user machine. The workflow uses only disposable public
GitHub-hosted Ubuntu runners. Cache bundles contain local .olean/receipt/log
triples, never sources, release archives, toolchains, or mathlib.
"""
import argparse
from contextlib import nullcontext
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
STATE = ROOT / '.verification'
BUNDLE_LIMIT = 480 * 1024**2  # Leaves >30 MiB for the Actions cache tar/compression envelope.
LEAF_BUNDLE_LIMIT = 448 * 1024**2
EXPANDED_LIMIT = 8 * 1024**3
MODULE = re.compile(r'(?:ElevenSquare|Sqpack)(?:\.[A-Za-z0-9_]+)*\Z')


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(4 * 1024**2), b''):
            h.update(chunk)
    return h.hexdigest()


def triple(module):
    if not MODULE.fullmatch(module):
        raise ValueError('Invalid module name: ' + module)
    return ['.lake/build/lib/lean/' + module.replace('.', '/') + '.olean',
            '.verification/' + module + '.json', '.verification/' + module + '.log']


def member_module(name):
    return (name[len('.lake/build/lib/lean/'):-6].replace('/', '.')
            if name.endswith('.olean') else Path(name).stem)


class LimitedWriter:
    def __init__(self, raw, limit):
        self.raw, self.limit = raw, limit

    def write(self, data):
        if self.raw.tell() + len(data) > self.limit:
            raise ValueError('Compressed checkpoint exceeds cache budget; previous cache retained')
        return self.raw.write(data)

    def __getattr__(self, name):
        return getattr(self.raw, name)


def pack(root, output, limit=BUNDLE_LIMIT, join=False):
    """Export only accepted local triples; an oversized snapshot is not cached."""
    paths = []
    imported_path = root / '.verification/ci-leaf-inputs.json'
    imported = json.loads(imported_path.read_text()) if join and imported_path.is_file() else {}
    for receipt in sorted((root / '.verification').glob('*.json')):
        module = receipt.stem
        if not MODULE.fullmatch(module):
            continue
        data = json.loads(receipt.read_text())
        if data.get('status') != 'accepted':
            continue
        names = triple(module)
        if not all((root / name).is_file() and not (root / name).is_symlink() for name in names):
            continue
        if sha(root / names[0]) != data.get('object_sha256'):
            raise ValueError('Accepted object hash differs: ' + module)
        if imported.get(module) == [data.get('object_sha256'), data.get('inputs')]:
            continue
        paths.extend(names)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.unlink(missing_ok=True)
    expanded = sum((root / name).stat().st_size for name in paths)
    if expanded > EXPANDED_LIMIT:
        raise ValueError('Checkpoint expanded size exceeds 8 GiB')
    if shutil.disk_usage(root).free < limit + 64 * 1024**2:
        raise ValueError('Insufficient disk for a bounded compressed checkpoint')
    try:
        with output.open('wb') as raw, tarfile.open(fileobj=LimitedWriter(raw, limit),
                mode='w:gz', compresslevel=1, format=tarfile.PAX_FORMAT) as bundle:
            for name in paths:
                bundle.add(root / name, arcname=name, recursive=False)
    except BaseException:
        output.unlink()
        raise
    print(f'Checkpoint: {len(paths) // 3} accepted modules, {output.stat().st_size} bytes', flush=True)
    return True


def merge(root, archives):
    """Reject malformed bundles; invalidate conflicting triples for serial replay."""
    with tempfile.TemporaryDirectory(prefix='ci-merge-', dir=root / '.verification') as temporary:
        stage = Path(temporary)
        have = {}
        imported = {}
        invalid = set()
        for archive in archives:
            if archive.is_symlink() or archive.stat().st_size > BUNDLE_LIMIT:
                raise ValueError('Invalid checkpoint archive: ' + str(archive))
            with tarfile.open(archive, 'r:gz') as bundle:
                seen, size = set(), 0
                archive_hashes, archive_receipts = {}, {}
                for member in bundle:
                    name = member.name
                    match = re.fullmatch(r'\.verification/((?:ElevenSquare|Sqpack)(?:\.[A-Za-z0-9_]+)*)\.(json|log)', name)
                    obj = re.fullmatch(r'\.lake/build/lib/lean/((?:ElevenSquare|Sqpack)(?:/[A-Za-z0-9_]+)*)\.olean', name)
                    if not member.isreg() or member.issparse() or not (match or obj) or name in seen:
                        raise ValueError('Invalid checkpoint member: ' + name)
                    seen.add(name); size += member.size
                    if member.size < 0 or size > EXPANDED_LIMIT or (name.endswith('.json') and member.size > 4 * 1024**2):
                        raise ValueError('Checkpoint declared size exceeds bound')
                    target = stage / name
                    target.parent.mkdir(parents=True, exist_ok=True)
                    if name not in have and shutil.disk_usage(root).free < member.size + 1024**3:
                        raise ValueError('Insufficient disk for the next unique checkpoint member')
                    hasher, chunks, copied = hashlib.sha256(), [], 0
                    output = target.open('wb') if name not in have else nullcontext(None)
                    with bundle.extractfile(member) as source, output as stream:
                        for block in iter(lambda: source.read(4 * 1024**2), b''):
                            hasher.update(block); copied += len(block)
                            if stream is not None: stream.write(block)
                            if name.endswith('.json'): chunks.append(block)
                    if copied != member.size:
                        raise ValueError('Truncated checkpoint member: ' + name)
                    digest = hasher.hexdigest()
                    module = member_module(name)
                    archive_hashes[name] = digest
                    receipt = json.loads(b''.join(chunks)) if name.endswith('.json') else None
                    if receipt is not None and receipt.get('status') != 'accepted':
                        raise ValueError('Checkpoint contains an unaccepted receipt: ' + name)
                    if receipt is not None:
                        archive_receipts[module] = receipt
                    if receipt is not None and archive.name != 'shard-16.tar.gz':
                        imported[Path(name).stem] = [receipt.get('object_sha256'), receipt.get('inputs')]
                    if name in have:
                        if receipt is not None:
                            old = json.loads(target.read_bytes())
                            if (old.get('inputs'), old.get('object_sha256')) != (receipt.get('inputs'), receipt.get('object_sha256')):
                                invalid.add(module)
                        elif have[name] != digest:
                            invalid.add(module)
                    else:
                        have[name] = digest
                # Authenticate each bundle's complete triples independently;
                # a second bundle cannot fill holes in a malformed first one.
                for module, receipt in archive_receipts.items():
                    names = triple(module)
                    if not all(name in archive_hashes for name in names):
                        raise ValueError('Incomplete checkpoint triple: ' + module)
                    if archive_hashes[names[0]] != receipt.get('object_sha256'):
                        raise ValueError('Checkpoint object hash mismatch: ' + module)
                if any(member_module(name) not in archive_receipts for name in archive_hashes):
                    raise ValueError('Checkpoint object/log has no receipt')
        for module in invalid:
            for name in triple(module):
                have.pop(name, None)
                (stage / name).unlink(missing_ok=True)
            imported.pop(module, None)
        for receipt in (stage / '.verification').glob('*.json'):
            data = json.loads(receipt.read_text())
            names = triple(receipt.stem)
            if data.get('status') != 'accepted' or not all(name in have for name in names):
                raise ValueError('Incomplete/unaccepted receipt: ' + receipt.stem)
            if have[names[0]] != data.get('object_sha256'):
                raise ValueError('Checkpoint object hash mismatch: ' + receipt.stem)
        for name in have:
            if name.endswith(('.olean', '.log')):
                module = member_module(name)
                if triple(module)[1] not in have:
                    raise ValueError('Object/log has no receipt: ' + name)
            target = root / name
            parents = []
            for parent in target.parents:
                if parent == root.parent:
                    break
                parents.append(parent)
            if target.is_symlink() or any(p.is_symlink() for p in parents):
                raise ValueError('Symlink checkpoint destination: ' + name)
            if target.exists() and sha(target) != have[name]:
                raise ValueError('Existing checkpoint destination differs: ' + name)
        for name in have:
            target = root / name
            if not target.exists():
                target.parent.mkdir(parents=True, exist_ok=True)
                os.link(stage / name, target)  # No second copy of every object.
        (root / '.verification/ci-leaf-inputs.json').write_text(json.dumps(imported))
    print(f'Merged {len(have)} checkpoint files; final verifier will validate all fingerprints.', flush=True)
    if invalid:
        print('Invalidated conflicting modules for full replay: ' + ', '.join(sorted(invalid)), flush=True)
    return invalid


def prepare():
    if (os.environ.get('GITHUB_ACTIONS') != 'true' or os.environ.get('RUNNER_ENVIRONMENT') != 'github-hosted'
            or os.environ.get('RUNNER_OS') != 'Linux' or Path(os.environ.get('GITHUB_WORKSPACE', '/')).resolve() != ROOT):
        raise ValueError('Preparation is restricted to disposable GitHub-hosted Linux workspaces')
    (STATE / 'ci-job-started').write_text(str(time.time()))
    disposable = ['/usr/local/lib/android', '/usr/share/dotnet', '/opt/ghc',
                  '/opt/hostedtoolcache/CodeQL', '/usr/local/share/powershell']
    subprocess.run(['sudo', 'rm', '-rf', '--', *disposable], check=True)
    subprocess.run(['sudo', 'apt-get', 'update', '-qq'], check=True)
    subprocess.run(['sudo', 'apt-get', 'install', '-y', 'elan', 'zstd'], check=True)
    subprocess.run(['elan', 'toolchain', 'install', (ROOT / 'lean-toolchain').read_text().strip()], check=True)
    subprocess.run([sys.executable, 'scripts/materialize_wand125.py'], check=True, cwd=ROOT)
    shutil.rmtree(STATE / 'wand125/releases', ignore_errors=True)
    subprocess.run(['lake', 'exe', 'cache', 'get'], check=True, cwd=ROOT)
    free = shutil.disk_usage(ROOT).free
    print(f'Prepared pinned toolchain/dependencies and all sources; free disk: {free / 1024**3:.2f} GiB', flush=True)
    if free < 4 * 1024**3:
        raise ValueError('Less than 4 GiB free for local objects/checkpoints; stopping')


def replay(shard=None):
    started = float((STATE / 'ci-job-started').read_text())
    seconds = max(1, min(300 * 60, 310 * 60 - (time.time() - started)))
    command = [sys.executable, 'scripts/verify.py', '--keep-going']
    if shard is None:
        command.append('--all')
    else:
        plan = json.loads((STATE / 'ci-plan.json').read_text())
        targets = plan['shards'][shard]['modules']
        if not targets:
            print('Empty certificate shard')
            return 0
        for module in targets:
            command.extend(['--module', module])
    # Terminate the verifier first so it records the interrupted module; then
    # its existing signal handler terminates Lean. Accepted receipts survive.
    child = subprocess.Popen(command, cwd=ROOT)
    try:
        return child.wait(timeout=seconds)
    except subprocess.TimeoutExpired:
        child.send_signal(signal.SIGTERM)
        try:
            child.wait(timeout=45)
        except subprocess.TimeoutExpired:
            child.kill(); child.wait()
        print('Replay deadline reached; accepted receipts can be resumed.', flush=True)
        return 124


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('prepare', 'run', 'pack', 'merge'))
    parser.add_argument('--shard', type=int, choices=range(17), help='16 is the final join checkpoint')
    args = parser.parse_args()
    STATE.mkdir(exist_ok=True)
    if args.mode == 'prepare':
        prepare()
    elif args.mode == 'run':
        return replay(args.shard)
    elif args.mode == 'pack':
        if args.shard is None: parser.error('pack requires --shard')
        pack(ROOT, STATE / f'ci-cache/shard-{args.shard:02d}.tar.gz',
             BUNDLE_LIMIT if args.shard == 16 else LEAF_BUNDLE_LIMIT, join=args.shard == 16)
    else:
        pattern = f'shard-{args.shard:02d}.tar.gz' if args.shard is not None else 'shard-*.tar.gz'
        merge(ROOT, sorted((STATE / 'ci-cache').glob(pattern)))
    return 0


if __name__ == '__main__':
    sys.exit(main())
