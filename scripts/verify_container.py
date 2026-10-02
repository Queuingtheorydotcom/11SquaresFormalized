#!/usr/bin/env python3
"""Launch verification in rootless Docker; never bind-mount the host repository.

Run this reviewed host launcher with `python3 -I`. The image recipe, entrypoint,
release downloader, manifests, Docker runtime, and official dependencies form
the trusted bootstrap. All other repository code runs only in the offline stage.
"""
import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import io
import json
import os
from pathlib import Path
import re
import signal
import stat
import subprocess
import sys
import tarfile
import tempfile
import uuid

ROOT = Path(__file__).resolve().parents[1]
LABEL = 'org.elevensquare.isolation'


@contextmanager
def volume_lock(volume, directory=None):
    """Serialize the entire lifecycle in host storage inaccessible to the proof."""
    directory = directory or Path.home() / '.local/state/eleven-square-locks'
    directory.mkdir(mode=0o700, parents=True, exist_ok=True)
    info = directory.lstat()
    if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid() or info.st_mode & 0o077:
        raise ValueError('Volume lock directory must be private and owned by this user')
    descriptor = os.open(directory / (volume + '.lock'), os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
    try:
        info = os.fstat(descriptor)
        if not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid() or info.st_mode & 0o077:
            raise ValueError('Volume lock must be a private regular file')
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise ValueError('Another launcher owns this volume; wait for it to finish') from None
        yield
    finally:
        os.close(descriptor)


def output(argv, **kwargs):
    return subprocess.check_output(argv, text=True, **kwargs).strip()


def git(*args):
    return ['git', '-c', 'core.fsmonitor=false', '-c', 'core.hooksPath=/dev/null', *args]


def context(root):
    files = {
        'Dockerfile': root / 'scripts/container/Dockerfile',
        'runner.py': root / 'scripts/container/container_runner.py',
        'fetch_wand125_release.py': root / 'scripts/fetch_wand125_release.py',
        'lake-manifest.json': root / 'lake-manifest.json',
    }
    metadata = root / 'integrations/wand125/release'
    for name in ('MANIFEST_F.sha256', 'MANIFEST_FCOMMON.sha256', 'MANIFEST_U2G.sha256',
                 'MANIFEST_U2P.sha256', 'MANIFEST_U2R.sha256', 'MANIFEST_U5.sha256',
                 'SHA256SUMS_F', 'SHA256SUMS_U2G', 'SHA256SUMS_U2P', 'SHA256SUMS_U2R', 'SHA256SUMS_U5'):
        files['metadata/' + name] = metadata / name
    data = io.BytesIO()
    with tarfile.open(fileobj=data, mode='w') as archive:
        for name, path in sorted(files.items()):
            if path.is_symlink() or not path.is_file():
                raise ValueError('Image input must be a regular file: ' + name)
            raw = path.read_bytes()
            info = tarfile.TarInfo(name)
            info.size, info.mode = len(raw), 0o644
            archive.addfile(info, io.BytesIO(raw))
    return data.getvalue()


def check_engine():
    endpoint = (os.environ.get('DOCKER_HOST') if not os.environ.get('DOCKER_CONTEXT') else None)
    endpoint = endpoint or output(['docker', 'context', 'inspect', '--format={{.Endpoints.docker.Host}}'])
    if not endpoint.startswith('unix://'):
        raise ValueError('A local Docker daemon is required for host locks and allocation limits')
    info = json.loads(output(['docker', 'info', '--format', '{{json .}}']))
    if not any('rootless' in item for item in info.get('SecurityOptions', [])):
        raise ValueError('Rootless Docker is required; there is no unsandboxed fallback')
    if str(info.get('CgroupVersion')) != '2' or info.get('CgroupDriver') != 'systemd':
        raise ValueError('Rootless resource enforcement requires cgroup v2 and systemd')


def run_arguments(image, volume, stage, options, canary):
    cpuset = ','.join(str(cpu) for cpu in sorted(os.sched_getaffinity(0)))
    return ['docker', 'run', '--rm', '--init', '--pull=never', '--read-only',
            '--cap-drop=ALL', '--security-opt=no-new-privileges=true',
            '--security-opt=seccomp=builtin', '--user=10001:10001',
            '--network=' + ('bridge' if stage == 'prepare' else 'none'),
            '--cpus=' + str(options.cpus), '--cpuset-cpus=' + cpuset,
            '--memory=' + options.memory, '--memory-swap=' + options.memory,
            '--pids-limit=4096', '--stop-timeout=30',
            '--tmpfs=/tmp:rw,noexec,nosuid,nodev,size=1g',
            '--mount=type=volume,source=' + volume + ',target=/workspace',
            '--env=ISOLATION_HOST_CANARY_PATH=' + str(canary),
            '--env=ISOLATION_CPU_BUDGET=' + str(options.cpus),
            '--env=ISOLATION_MEMORY_BUDGET=' + str(int(options.memory[:-1]) *
                                                 (1024**3 if options.memory[-1].lower() == 'g' else 1024**2)),
            *(['--interactive'] if stage == 'seed' else []), image, stage]


def validate_options(args):
    if not re.fullmatch(r'[1-9][0-9]*[mMgG]', args.memory):
        raise ValueError('Use an explicit memory budget, e.g. 16g or 1300g')
    if min(args.cpus, args.max_parallel, args.jobs) < 1:
        raise ValueError('CPU/process/thread counts must be positive')
    if args.cpus > len(os.sched_getaffinity(0)):
        raise ValueError('Requested CPUs exceed this process allocation/affinity')
    if args.jobs * args.max_parallel > args.cpus:
        raise ValueError('Parallel compiler threads exceed the requested CPUs')
    if args.volume and not re.fullmatch(r'[a-zA-Z0-9][a-zA-Z0-9_.-]{0,127}', args.volume):
        raise ValueError('Invalid Docker volume name')


def stages_for(stage, existing):
    # Immutable daemon metadata, not a submission-writable marker, decides this.
    # Once a volume exists, never expose its contents to online execution again.
    if existing and stage == 'prepare':
        raise ValueError('Existing volumes cannot re-enter online preparation; use a new volume name')
    if stage == 'all':
        return ['verify'] if existing else ['prepare', 'verify']
    return [stage]


def execute_container(command, **kwargs):
    """Kill this container and its detached children if the launcher is stopped."""
    name = 'eleven-square-run-' + uuid.uuid4().hex
    command = command[:2] + ['--name=' + name] + command[2:]
    process = subprocess.Popen(command, **kwargs)
    try:
        code = process.wait()
        if code:
            raise subprocess.CalledProcessError(code, command)
    except BaseException:
        try:
            subprocess.run(['docker', 'rm', '--force', name], stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL, timeout=30)
        finally:
            if process.poll() is None:
                process.terminate()
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
        raise


def main(argv=None):
    default_cpus = min(4, len(os.sched_getaffinity(0)))
    default_jobs = min(2, default_cpus)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stage', nargs='?', default='all', choices=('all', 'prepare', 'verify', 'probe', 'report'))
    parser.add_argument('--cpus', type=int, default=default_cpus)
    parser.add_argument('--memory', default='16g')
    parser.add_argument('--max-parallel', type=int, default=max(1, default_cpus // default_jobs))
    parser.add_argument('--jobs', type=int, default=default_jobs)
    parser.add_argument('--memory-percent', type=int, choices=range(1, 96), default=85)
    parser.add_argument('--volume', help='Persistent private volume; defaults to the source commit.')
    parser.add_argument('--report', choices=('completion.json', 'result.json', 'incomplete-result.json',
                                           'wand125-upgrade.json', 'source-check.json', 'MANIFEST.json'),
                        default='completion.json')
    args = parser.parse_args(argv)
    validate_options(args)
    check_engine()
    if output(git('status', '--porcelain', '--untracked-files=normal'), cwd=ROOT):
        raise ValueError('Commit intended changes first; only a clean HEAD snapshot is verified')
    commit = output(git('rev-parse', '--verify', 'HEAD'), cwd=ROOT)
    volume = args.volume or 'eleven-square-' + commit[:16]
    with volume_lock(volume):
        lifecycle(args, commit, volume)


def lifecycle(args, commit, volume):
    raw = context(ROOT)
    recipe = hashlib.sha256(raw).hexdigest()
    tag = 'eleven-square-isolated:' + recipe[:16]
    # Images are built only from the explicit reviewed allowlist, not repo context.
    if subprocess.run(['docker', 'image', 'inspect', tag], stdout=subprocess.DEVNULL,
                      stderr=subprocess.DEVNULL).returncode:
        subprocess.run(['docker', 'build', '-t', tag, '-'], input=raw, check=True)
    image = output(['docker', 'image', 'inspect', '--format={{.Id}}', tag])
    found = subprocess.run(['docker', 'volume', 'inspect', volume], capture_output=True, text=True)
    labels = {LABEL: 'v1', LABEL + '.commit': commit, LABEL + '.image': image}
    if found.returncode:
        if args.stage not in ('all', 'prepare'):
            raise ValueError('No prepared volume exists; run prepare or all first')
        command = ['docker', 'volume', 'create']
        for key, value in labels.items():
            command.extend(['--label', key + '=' + value])
        output([*command, volume])
        seeded = False
    else:
        actual = json.loads(found.stdout)[0].get('Labels') or {}
        if any(actual.get(k) != v for k, v in labels.items()):
            raise ValueError('Volume belongs to a different snapshot or image; use a new volume name')
        seeded = True
    stages = stages_for(args.stage, seeded)
    print('Private Docker volume: ' + volume + '; image: ' + image, file=sys.stderr, flush=True)
    with tempfile.TemporaryDirectory(prefix='eleven-square-host-canary-') as directory:
        canary = Path(directory) / ('private-' + uuid.uuid4().hex)
        canary.write_text('This host file must not be visible inside the container.')

        def launch(stage, extra=()):
            execute_container([*run_arguments(image, volume, stage, args, canary), *extra])

        if not seeded:
            command = [*run_arguments(image, volume, 'seed', args, canary), '--commit', commit]
            archive = subprocess.Popen(git('archive', '--format=tar', 'HEAD'), cwd=ROOT, stdout=subprocess.PIPE)
            try:
                execute_container(command, stdin=archive.stdout)
            finally:
                archive.stdout.close()
                try:
                    archive.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    archive.terminate()
                    archive.wait(timeout=5)
            if archive.returncode:
                raise RuntimeError('Source snapshot export failed; use a new volume name')
        if 'prepare' in stages:
            launch('prepare')
        if 'verify' in stages:
            launch('verify', ['--max-parallel', str(args.max_parallel), '--jobs', str(args.jobs),
                             '--memory-percent', str(args.memory_percent)])
        if args.stage == 'probe':
            launch('probe')
        if args.stage == 'report':
            launch('report', ['--report', args.report])


if __name__ == '__main__':
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
    try:
        main()
    except KeyboardInterrupt:
        print('Interrupted; private volume retained for an offline resume.', file=sys.stderr)
        raise SystemExit(130)
    except (ValueError, RuntimeError, OSError, subprocess.CalledProcessError) as error:
        print('Container verification refused/failed: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
