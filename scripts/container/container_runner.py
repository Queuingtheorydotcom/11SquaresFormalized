"""Reviewed image entrypoint. Never import repository code during online setup."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tarfile

sys.dont_write_bytecode = True
WORK = Path('/workspace')
REPO = WORK / 'repo'
TOOLS = Path('/opt/eleven-square')
TOOLCHAIN = 'leanprover/lean4:v4.34.1'
MATHLIB = 'd13f23b723b8a846827a245b89c10fc7d3f11612'


def run(argv, **kwargs):
    subprocess.run(argv, check=True, **kwargs)


def probe(offline=True):
    """Fail before repository execution if essential restrictions are absent."""
    if os.getuid() == 0:
        raise RuntimeError('Container must run as a non-root user')
    fields = dict(line.split(':', 1) for line in Path('/proc/self/status').read_text().splitlines()
                  if ':' in line)
    if int(fields['CapEff'].strip(), 16) != 0 or fields['NoNewPrivs'].strip() != '1':
        raise RuntimeError('Capabilities or privilege escalation remain enabled')
    if fields['Seccomp'].strip() != '2':
        raise RuntimeError('Seccomp filtering is not enabled')
    mounts = [line.split() for line in Path('/proc/mounts').read_text().splitlines()]
    if not any(mount[1] == '/' and 'ro' in mount[3].split(',') for mount in mounts):
        raise RuntimeError('Container root mount is not read-only')
    cgroup = Path('/sys/fs/cgroup')
    if int((cgroup / 'memory.max').read_text()) > int(os.environ['ISOLATION_MEMORY_BUDGET']):
        raise RuntimeError('Container memory limit is not enforced')
    if int((cgroup / 'pids.max').read_text()) > 4096:
        raise RuntimeError('Container process limit is not enforced')
    quota, period = map(int, (cgroup / 'cpu.max').read_text().split())
    if quota > int(os.environ['ISOLATION_CPU_BUDGET']) * period:
        raise RuntimeError('Container CPU limit is not enforced')
    if offline and {p.name for p in Path('/sys/class/net').iterdir()} != {'lo'}:
        raise RuntimeError('Offline stage has a network interface')
    for path in ('/var/run/docker.sock', '/run/podman/podman.sock'):
        if Path(path).exists():
            raise RuntimeError('Container daemon socket is visible')
    canary = os.environ.get('ISOLATION_HOST_CANARY_PATH')
    if not canary or Path(canary).exists():
        raise RuntimeError('Host filesystem canary is missing or visible')
    allowed_environment = {'PATH', 'HOSTNAME', 'HOME', 'ELAN_HOME', 'XDG_CACHE_HOME',
                           'TMPDIR', 'ISOLATION_HOST_CANARY_PATH', 'LC_CTYPE',
                           'ISOLATION_CPU_BUDGET', 'ISOLATION_MEMORY_BUDGET'}
    if set(os.environ) - allowed_environment:
        raise RuntimeError('Unexpected container environment keys: ' +
                           ', '.join(sorted(set(os.environ) - allowed_environment)))
    for key in ('SSH_AUTH_SOCK', 'GH_TOKEN', 'GITHUB_TOKEN', 'AWS_ACCESS_KEY_ID',
                'AWS_SECRET_ACCESS_KEY', 'OPENAI_API_KEY', 'PYTHONPATH', 'LD_PRELOAD'):
        if key in os.environ:
            raise RuntimeError('Unexpected inherited environment variable: ' + key)
    target = TOOLS / '.write-probe'
    try:
        target.write_text('probe')
    except OSError:
        pass
    else:
        target.unlink()
        raise RuntimeError('Image root filesystem is writable')
    for name in ('home', 'cache', 'tmp'):
        (WORK / name).mkdir(exist_ok=True)
    print('Isolation probes passed' + (' (offline).' if offline else ' (online preparation).'),
          file=sys.stderr, flush=True)


def extract_snapshot(stream, destination):
    """Extract inert regular files only; no symlinks, devices, or Git internals."""
    names, seen, total = [], set(), 0
    with tarfile.open(fileobj=stream, mode='r|') as archive:
        for member in archive:
            name = member.name.rstrip('/') if member.isdir() else member.name
            parts = name.split('/')
            if (not name or name.startswith('/') or any(p in ('', '.', '..', '.git') for p in parts)
                    or '\\' in name or '\x00' in name or name in seen):
                raise ValueError('Unsafe source archive path')
            seen.add(name)
            target = destination.joinpath(*PurePosixPath(name).parts)
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
                continue
            if not member.isreg() or member.issparse() or not 0 <= member.size <= 1024**3:
                raise ValueError('Source snapshot must contain ordinary files/directories')
            total += member.size
            if total > 32 * 1024**3:
                raise ValueError('Source archive exceeds the snapshot size budget')
            target.parent.mkdir(parents=True, exist_ok=True)
            with archive.extractfile(member) as source, target.open('xb') as output:
                shutil.copyfileobj(source, output)
            # Do not propagate setuid/setgid or executable bits from the submission.
            target.chmod(0o644)
            names.append(name)
    return names


def seed(commit):
    probe()
    if REPO.exists() or REPO.is_symlink():
        raise RuntimeError('Workspace is already seeded; do not overwrite it')
    REPO.mkdir()
    names = extract_snapshot(sys.stdin.buffer, REPO)
    run(['git', 'init', '--quiet'], cwd=REPO)
    run(['git', '--literal-pathspecs', 'add', '--force', '--pathspec-from-file=-',
         '--pathspec-file-nul'], cwd=REPO, input=b''.join(n.encode() + b'\0' for n in names))
    (WORK / 'snapshot.json').write_text(json.dumps({'commit': commit, 'files': len(names)}))
    print(f'Seeded {len(names)} tracked files into the private Docker volume.', flush=True)


def prepare():
    probe(offline=False)
    if not (WORK / 'snapshot.json').is_file():
        raise RuntimeError('Seed the workspace first')
    # Only official bootstrap tools and pinned mathlib are executed online.
    # The submission's lakefile, scripts, and Lean modules are never evaluated here.
    if not (WORK / 'elan/bin/elan').is_file():
        installer = WORK / 'tmp/elan-init.sh'
        run(['curl', '-fsSL', 'https://elan.lean-lang.org/elan-init.sh', '-o', str(installer)])
        run(['sh', str(installer), '-y', '--default-toolchain', 'none', '--no-modify-path'])
    run(['elan', 'toolchain', 'install', TOOLCHAIN])
    bootstrap = WORK / 'bootstrap'
    bootstrap.mkdir(exist_ok=True)
    (bootstrap / 'lean-toolchain').write_text(TOOLCHAIN + '\n')
    (bootstrap / 'lakefile.lean').write_text(
        'import Lake\nopen Lake DSL\npackage elevenSquare\n'
        'require mathlib from git\n'
        f'  "https://github.com/leanprover-community/mathlib4.git" @ "{MATHLIB}"\n')
    shutil.copyfile(TOOLS / 'lake-manifest.json', bootstrap / 'lake-manifest.json')
    run(['lake', 'exe', 'cache', 'get'], cwd=bootstrap)
    (REPO / '.lake').mkdir(exist_ok=True)
    packages = REPO / '.lake/packages'
    expected = bootstrap / '.lake/packages'
    if not packages.exists() and not packages.is_symlink():
        packages.symlink_to(expected, target_is_directory=True)
    elif not packages.is_symlink() or packages.readlink() != expected:
        raise RuntimeError('Unexpected dependency directory in submission')
    # This downloader is copied into the reviewed image, not imported from REPO.
    sys.path.insert(0, str(TOOLS / 'scripts'))
    import fetch_wand125_release as release
    cache = REPO / '.verification/wand125/releases'
    for unit in ('F', 'FCOMMON', 'U2G', 'U2P', 'U2R', 'U5'):
        for entry in release.release_plan(unit):
            release.fetch_release([entry], cache, REPO)
    (WORK / 'prepared.json').write_text(json.dumps({'toolchain': TOOLCHAIN, 'mathlib': MATHLIB}))
    print('Preparation complete; submission code has not been executed online.', flush=True)


def verify(parallel, jobs, memory_percent):
    probe()
    if not (WORK / 'prepared.json').is_file():
        raise RuntimeError('Complete preparation first')
    # Repository code is executed only here, with networking disabled by Docker.
    run(['python3', '-u', 'scripts/materialize_wand125.py'], cwd=REPO)
    run(['python3', '-u', 'scripts/verify.py', '--all', '--keep-going',
         '--max-parallel', str(parallel), '--jobs', str(jobs),
         '--memory-percent', str(memory_percent)], cwd=REPO)
    run(['python3', '-B', 'scripts/finalize_verification.py', '--write'], cwd=REPO)
    audit_path = REPO / 'verification/wand125-upgrade.json'
    audit = json.loads(audit_path.read_text())
    if (audit.get('status') != 'OPTIMALITY_PROVED'
            or audit.get('global_optimality_proved') is not True
            or audit.get('full_upgrade_verified') is not True):
        raise RuntimeError('Final audit did not report complete optimality')
    completion = {key: audit[key] for key in ('status', 'global_optimality_proved',
                  'full_upgrade_verified', 'checked_modules', 'lean_toolchain', 'mathlib_revision')}
    completion['audit_sha256'] = hashlib.sha256(audit_path.read_bytes()).hexdigest()
    (REPO / '.verification/completion.json').write_text(json.dumps(completion, indent=2) + '\n')
    print('Completed verification; reports remain in the private Docker volume.', flush=True)


REPORTS = {'completion.json': '.verification/completion.json',
           'result.json': '.verification/result.json',
           'incomplete-result.json': '.verification/incomplete-result.json',
           'wand125-upgrade.json': 'verification/wand125-upgrade.json',
           'source-check.json': 'verification/source-check.json',
           'MANIFEST.json': 'MANIFEST.json'}


def report(name):
    probe()
    path = REPO / REPORTS[name]
    # Never emit arbitrary files/symlinks or an unbounded attacker-controlled blob.
    if path.is_symlink() or not path.is_file() or path.stat().st_size > 128 * 1024**2:
        raise RuntimeError('Missing, nonregular, or oversized report')
    with path.open('rb') as source:
        shutil.copyfileobj(source, sys.stdout.buffer)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stage', choices=('seed', 'prepare', 'verify', 'probe', 'report'))
    parser.add_argument('--commit')
    parser.add_argument('--max-parallel', type=int, default=2)
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--memory-percent', type=int, default=85)
    parser.add_argument('--report', choices=REPORTS)
    args = parser.parse_args()
    if args.stage == 'seed':
        seed(args.commit)
    elif args.stage == 'prepare':
        prepare()
    elif args.stage == 'verify':
        verify(args.max_parallel, args.jobs, args.memory_percent)
    elif args.stage == 'report':
        if not args.report:
            parser.error('report stage requires --report')
        report(args.report)
    else:
        probe()


if __name__ == '__main__':
    main()
