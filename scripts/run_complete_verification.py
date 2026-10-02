#!/usr/bin/env python3
"""Resume all local proofs, then publish evidence only after the strict full audit.

No downloads, Git writes, automatic kills, or fresh rebuilds. Detailed diagnostics
stay in ignored .verification/run directories; terminal progress and summaries
contain only fixed statuses, counts, and validated local module identifiers.
"""
import argparse
from dataclasses import dataclass, field
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
import traceback
import uuid

sys.dont_write_bytecode = True
from check_sources import code_only, import_names
from verify_scheduler import CheckoutLock
from verify_support import (STANDARD_AXIOMS, audit_axioms, input_digest,
                            lean_arguments, positive_jobs, recorded_arguments)

ROOT = Path(__file__).resolve().parents[1]
MODULE = r'(?:ElevenSquare|Sqpack)(?:\.[A-Za-z0-9_]+)*'
PROGRESS = re.compile(r'^\[(\d+)/(\d+)\] (cached|accepted|failed|blocked|started|interrupted) (' + MODULE + r')$')
CONFIG = ('lean-toolchain', 'lakefile.lean', 'lake-manifest.json')


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(4 << 20), b''):
            digest.update(block)
    return digest.hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))


def save_json(path, data):
    temporary = path.with_name(path.name + '.checking')
    temporary.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')
    os.replace(temporary, path)


def valid_benchmark(root, path, workers, memory_percent):
    """Recheck matched scratch objects/logs and current cohort inputs before reuse."""
    try:
        report = read_json(path)
        if report.get('status') != 'MATCHED_BENCHMARK' or report.get('canonical_files_unchanged') is not True:
            return None
        order = report['order']
        if not order or len(set(order)) != len(order) or any(not re.fullmatch(MODULE, m) for m in order):
            return None
        context = {name: sha(root / name) for name in CONFIG}
        # Benchmark reuse is conditional on the current complete dependency
        # closure, not merely unchanged top-level sources or old receipt claims.
        records, visiting = {}, set()

        def validate(module):
            if module in records:
                return records[module]
            if module in visiting:
                raise ValueError('Benchmark dependency cycle')
            visiting.add(module)
            source = root.joinpath(*module.split('.')).with_suffix('.lean')
            code = code_only(source.read_text(encoding='utf-8'))
            receipt = read_json(root / '.verification' / (module + '.json'))
            dependencies = {name: validate(name) for name in import_names(code) if re.fullmatch(MODULE, name)}
            current = dict(source=sha(source), compiler=report['compiler'], build_context=context,
                arguments=recorded_arguments(module, receipt['inputs']['arguments']),
                local_dependency_objects={name: child['object_sha256'] for name, child in dependencies.items()},
                local_dependency_inputs={name: input_digest(child['inputs']) for name, child in dependencies.items()})
            obj = (root / '.lake/build/lib/lean').joinpath(*module.split('.')).with_suffix('.olean')
            if receipt.get('status') != 'accepted' or receipt['inputs'] != current or sha(obj) != receipt['object_sha256']:
                raise ValueError('Stale benchmark dependency')
            audit_axioms(code, (root / '.verification' / (module + '.log')).read_text(encoding='utf-8'), STANDARD_AXIOMS, set())
            records[module] = receipt
            visiting.remove(module)
            return receipt

        for module in order:
            validate(module)
        compiler = root / 'work/tooling/lean-4.34.1-windows/bin/lean.exe'
        if not report.get('compiler_sha256') or sha(compiler) != report['compiler_sha256']:
            return None
        modes = report['modes']
        expected_axioms, expected_objects = {}, {}
        for name, maximum in [('serial', 1), ('parallel2', 2)]:
            mode = modes[name]
            elapsed = mode['elapsed_seconds']
            if (mode.get('status') != 'MATCHED' or mode.get('max_parallel') != maximum
                    or mode.get('order') != order or mode['guard']['memory_percent'] != memory_percent
                    or type(elapsed) not in (int, float) or not math.isfinite(elapsed) or elapsed <= 0):
                return None
            last = {}
            for attempt in mode['attempts']:
                if attempt['module'] not in order:
                    return None
                last[attempt['module']] = attempt
            if set(last) != set(order):
                return None
            for module in order:
                attempt = last[module]
                if (attempt['status'] != 'MATCHED' or attempt['returncode'] != 0
                        or attempt['arguments'] != lean_arguments(module, workers)):
                    return None
                source = root.joinpath(*module.split('.')).with_suffix('.lean')
                receipt = read_json(root / '.verification' / (module + '.json'))
                obj = (root / '.lake/build/lib/lean').joinpath(*module.split('.')).with_suffix('.olean')
                if (receipt.get('status') != 'accepted' or receipt['inputs']['source'] != sha(source)
                        or report['source_sha256'][module] != sha(source)
                        or receipt['inputs']['build_context'] != context
                        or receipt['inputs']['compiler'] != report['compiler']
                        or receipt['object_sha256'] != attempt['output_sha256']
                        or sha(obj) != attempt['output_sha256']):
                    return None
                for key in ('output', 'log'):
                    if Path(attempt[key]).name != attempt[key] or '/' in attempt[key] or '\\' in attempt[key]:
                        return None
                scratch, log = path.parent / name / attempt['output'], path.parent / name / attempt['log']
                if sha(scratch) != attempt['output_sha256'] or sha(log) != attempt['log_sha256']:
                    return None
                axioms = audit_axioms(code_only(source.read_text(encoding='utf-8')),
                                     log.read_text(encoding='utf-8'), STANDARD_AXIOMS, set())
                if not axioms or axioms != attempt['axioms']:
                    return None
                if name == 'serial':
                    expected_axioms[module], expected_objects[module] = axioms, attempt['output_sha256']
                elif axioms != expected_axioms[module] or attempt['output_sha256'] != expected_objects[module]:
                    return None
        faster = modes['parallel2']['elapsed_seconds'] < modes['serial']['elapsed_seconds']
        observed = modes['parallel2']['memory']['concurrent_processes_peak'] >= 2
        return {'status': 'MATCHED_BENCHMARK', 'max_parallel': 2 if faster and observed else 1,
                'report': str(path.relative_to(root)).replace('\\', '/'),
                'speedup': modes['serial']['elapsed_seconds'] / modes['parallel2']['elapsed_seconds']}
    except (OSError, ValueError, KeyError, TypeError, AttributeError):
        return None


@dataclass
class StageResult:
    returncode: int
    accepted: set = field(default_factory=set)
    failed: set = field(default_factory=set)
    blocked: set = field(default_factory=set)


class StopControl:
    def __init__(self, path):
        self.path, self.signaled = path, False

    def signal(self, *_):
        self.signaled = True

    def requested(self):
        if self.signaled:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            self.path.touch(exist_ok=True)
        return self.signaled or self.path.exists()


def run_stage(root, name, command, folder, stop, wrapper):
    """Tee bytes privately; drain and reap on cancellation without killing a child."""
    result = StageResult(-1)
    errors = []
    print(name.capitalize() + ' started.', flush=True)
    wrapper.write(('\nSTAGE ' + name + '\n' + json.dumps(command) + '\n').encode()); wrapper.flush()
    env = os.environ.copy()
    env['PYTHONUTF8'] = env['PYTHONDONTWRITEBYTECODE'] = '1'
    options = {'creationflags': subprocess.CREATE_NEW_PROCESS_GROUP} if os.name == 'nt' else {'start_new_session': True}
    with (folder / (name + '.log')).open('ab') as log:
        child = subprocess.Popen(command, cwd=root, env=env, stdin=subprocess.DEVNULL,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT, **options)

        def pump():
            try:
                while True:
                    data = child.stdout.readline(1 << 20)
                    if not data:
                        break
                    if errors:
                        continue
                    try:
                        log.write(data); log.flush()
                        wrapper.write(data); wrapper.flush()
                        match = PROGRESS.fullmatch(data.decode('utf-8', errors='replace').strip())
                        if match:
                            _, _, status, module = match.groups()
                            if status in ('accepted', 'cached'):
                                result.accepted.add(module)
                            elif status == 'failed':
                                result.failed.add(module)
                            elif status == 'blocked':
                                result.blocked.add(module)
                            print(match.group(), flush=True)
                    except BaseException as error:
                        # Continue draining the pipe even if disk/console output
                        # fails, so the child can observe the stop file and exit.
                        errors.append(error)
                        stop.signaled = True
            except BaseException as error:
                errors.append(error)
                stop.signaled = True

        reader = threading.Thread(target=pump, name='private-log-reader')
        reader.start()
        stop_announced = False
        try:
            while child.poll() is None:
                if stop.requested() and not stop_announced:
                    print('Stop requested; finishing active checks. Keep this window open.', flush=True)
                    stop_announced = True
                try:
                    child.wait(timeout=0.25)
                except subprocess.TimeoutExpired:
                    pass
        except BaseException:
            stop.signaled = True
            stop.requested()
            # Deliberately no terminate/kill: the coordinator owns its Lean
            # children and must finish its own cleanup before we release locks.
            child.wait()
            raise
        finally:
            while reader.is_alive():
                reader.join(timeout=0.25)
                stop.requested()
            child.stdout.close()
        result.returncode = child.wait()
    if errors:
        raise OSError('Private log capture failed') from errors[0]
    return result


def archive_failures(root, folder, modules):
    """Preserve complete failed diagnostics before a later replay overwrites them."""
    for module in sorted(modules):
        if not re.fullmatch(MODULE, module):
            continue
        for suffix in ('.log', '.json'):
            source = root / '.verification' / (module + suffix)
            if source.is_file() and not source.is_symlink():
                destination = folder / 'failed-modules' / source.name
                destination.parent.mkdir(exist_ok=True)
                shutil.copyfile(source, destination)


def complete_state(root, *, finalized):
    result = read_json(root / '.verification/result.json')
    sites = read_json(root / 'verification/admissions.json')['sites']
    if (sites != [] or result.get('status') != 'OPTIMALITY_PROVED'
            or result.get('global_optimality_proved') is not True
            or type(result.get('checked_modules')) is not int or result['checked_modules'] <= 0):
        raise ValueError('Full proof completion was not established')
    if finalized:
        audit = read_json(root / 'verification/wand125-upgrade.json')
        source = read_json(root / 'verification/source-check.json')
        if (audit.get('status') != 'OPTIMALITY_PROVED' or audit.get('full_upgrade_verified') is not True
                or audit.get('global_optimality_proved') is not True
                or audit.get('explicit_native_admissions') != 0
                or audit.get('checked_modules') != result['checked_modules']
                or source.get('status') != 'SOURCE_ASSEMBLY_PASS'
                or source.get('explicit_admissions') != 0
                or source.get('local_modules') != result['checked_modules']
                or not (root / 'MANIFEST.json').is_file()):
            raise ValueError('Strict final publication did not establish completion')
    return result['checked_modules']


def summary_files(root, folder, summary):
    save_json(folder / 'summary.json', summary)
    lines = [summary['status'], 'Stage: ' + summary['stage'],
             'Complete: ' + str(summary['complete']).lower(),
             'Checked modules: ' + str(summary['checked_modules']),
             'Failed modules: ' + str(summary['failed_module_count']),
             'Blocked modules: ' + str(summary['blocked_module_count'])]
    lines.extend(summary['failed_modules'])
    (folder / 'summary.txt').write_text('\n'.join(lines) + '\n', encoding='utf-8')
    relative = folder.relative_to(root).as_posix()
    save_json(root / '.verification/run/latest.json', {
        'run_id': folder.name, 'directory': relative, 'summary': relative + '/summary.json',
        'status': summary['status'], 'complete': summary['complete']})


def benchmark_choice(root, folder, stop, wrapper, options, stage_runner):
    if options.skip_benchmark:
        return {'status': 'SKIPPED', 'max_parallel': 1}
    for path in sorted((root / '.verification/bench').glob('matched-*/report.json'), reverse=True):
        choice = valid_benchmark(root, path, options.workers, options.memory_percent)
        if choice is not None:
            return choice
    helper = root / '.verification/bench/matched_short_cohort.py'
    paths = [root / p for p in CONFIG] + [root / 'scripts' / name for name in
             ('verify.py', 'verify_scheduler.py', 'verify_resources.py', 'verify_support.py')]
    context = {'files': {p.relative_to(root).as_posix(): sha(p) for p in paths},
               'workers': options.workers, 'memory_percent': options.memory_percent,
               'helper': sha(helper) if helper.is_file() else None}
    attempted = root / '.verification/run/benchmark-attempt.json'
    if attempted.is_file() and read_json(attempted) == context:
        return {'status': 'NO_VALID_FASTER_BENCHMARK', 'max_parallel': 1}
    save_json(attempted, context)  # A cancelled/failed optional benchmark is not repeated silently.
    if not helper.is_file() or options.workers != 4 or options.memory_percent != 95:
        return {'status': 'UNAVAILABLE', 'max_parallel': 1}
    outcome = stage_runner(root, 'benchmark',
        [sys.executable, '-B', '-u', str(helper.relative_to(root)), '--run',
         ], folder, stop, wrapper)
    if outcome.returncode != 0 or stop.requested():
        return {'status': 'BENCHMARK_FAILED', 'max_parallel': 1}
    for path in sorted((root / '.verification/bench').glob('matched-*/report.json'), reverse=True):
        choice = valid_benchmark(root, path, options.workers, options.memory_percent)
        if choice is not None:
            return choice
    return {'status': 'NO_VALID_FASTER_BENCHMARK', 'max_parallel': 1}


def execute(root, options, *, stage_runner=run_stage):
    state = root / '.verification'
    runs = state / 'run'
    runs.mkdir(parents=True, exist_ok=True)
    with CheckoutLock(runs / 'complete-run.lock'):
        # This also refuses a directly launched modern verifier or benchmark.
        with CheckoutLock(state / 'verifier.lock'):
            pass
        default_stop = runs / 'stop-requested'
        stop_path = (options.stop_file or default_stop)
        if not stop_path.is_absolute():
            stop_path = root / stop_path
        stop_path = stop_path.resolve()
        if not stop_path.is_relative_to(state.resolve()) or stop_path == state.resolve():
            raise ValueError('The stop file must stay inside .verification')
        if options.resume_after_stop:
            if stop_path != default_stop.resolve():
                raise ValueError('Resume clearing is limited to the default stop file')
            stop_path.unlink(missing_ok=True)
        stop = StopControl(stop_path)
        folder = runs / (datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ-') + uuid.uuid4().hex[:8])
        folder.mkdir()
        for name in ('benchmark', 'verifier', 'finalizer'):
            (folder / (name + '.log')).touch()
        summary = dict(status='RUNNING', stage='startup', complete=False, checked_modules=0,
                       explicit_admissions=None, failed_module_count=0, blocked_module_count=0,
                       failed_modules=[], settings={'workers': options.workers,
                       'memory_percent': options.memory_percent, 'max_parallel': 1})
        summary_files(root, folder, summary)
        previous = {sig: signal.getsignal(sig) for sig in (signal.SIGINT, signal.SIGTERM)}
        for sig in previous:
            signal.signal(sig, stop.signal)
        code = 1
        with (folder / 'runner.log').open('ab') as wrapper:
            try:
                if stop.requested():
                    summary.update(status='STOPPED', stage='startup')
                    return 130
                summary['stage'] = 'benchmark'
                summary_files(root, folder, summary)
                choice = benchmark_choice(root, folder, stop, wrapper, options, stage_runner)
                wrapper.write(('BENCHMARK_SELECTION ' + json.dumps(choice) + '\n').encode()); wrapper.flush()
                summary['benchmark'] = {key: choice[key] for key in ('status', 'max_parallel', 'speedup') if key in choice}
                summary['settings']['max_parallel'] = choice['max_parallel']
                print('Using ' + str(choice['max_parallel']) + ' coordinated compiler process(es).', flush=True)
                if stop.requested():
                    summary['status'] = 'STOPPED'
                    return 130
                summary['stage'] = 'verification'
                summary_files(root, folder, summary)
                outcome = stage_runner(root, 'verifier', [sys.executable, '-B', '-u', 'scripts/verify.py',
                    '--all', '--keep-going', '--jobs', str(options.workers),
                    '--max-parallel', str(choice['max_parallel']), '--memory-percent', str(options.memory_percent),
                    '--stop-file', str(stop.path.relative_to(root))], folder, stop, wrapper)
                failed = sorted(m for m in outcome.failed if re.fullmatch(MODULE, m))
                blocked = {m for m in outcome.blocked if re.fullmatch(MODULE, m)}
                archive_failures(root, folder, failed)
                summary.update(checked_modules=len(outcome.accepted), failed_modules=failed[:50],
                               failed_module_count=len(failed), blocked_module_count=len(blocked))
                if stop.requested():
                    summary['status'] = 'STOPPED'
                    return 130
                if outcome.returncode != 0:
                    summary['status'] = 'VERIFICATION_FAILED'
                    return 1
                summary['checked_modules'] = complete_state(root, finalized=False)
                summary.update(stage='finalization', explicit_admissions=0)
                summary_files(root, folder, summary)
                with CheckoutLock(state / 'verifier.lock'):
                    outcome = stage_runner(root, 'finalizer',
                        [sys.executable, '-B', '-u', 'scripts/finalize_verification.py', '--write'],
                        folder, stop, wrapper)
                    if stop.requested():
                        summary['status'] = 'STOPPED'
                        return 130
                    if outcome.returncode != 0:
                        summary['status'] = 'FINALIZATION_FAILED'
                        return 1
                    summary['checked_modules'] = complete_state(root, finalized=True)
                summary.update(status='OPTIMALITY_PROVED', stage='complete', complete=True)
                code = 0
            except BaseException as error:
                # Full exceptions are useful for repair, and are private only.
                wrapper.write(traceback.format_exc().encode('utf-8', errors='replace')); wrapper.flush()
                summary.update(status='RUNNER_FAILED', error_type=type(error).__name__)
            finally:
                for sig, handler in previous.items():
                    signal.signal(sig, handler)
                summary_files(root, folder, summary)
                print(summary['status'] + '; summary: .verification/run/latest.json', flush=True)
        return code


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-benchmark', action='store_true', help='Use one compiler process without benchmarking.')
    parser.add_argument('--workers', type=positive_jobs, default=4)
    parser.add_argument('--memory-percent', type=int, choices=range(1, 96), default=95, metavar='1..95')
    parser.add_argument('--stop-file', type=Path, help='Optional stop file inside .verification; default: .verification/run/stop-requested.')
    parser.add_argument('--resume-after-stop', action='store_true', help='Explicitly remove the default stop request before resuming.')
    options = parser.parse_args(argv)
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, 'reconfigure'):
            stream.reconfigure(encoding='utf-8')
    try:
        return execute(ROOT, options)
    except (OSError, ValueError):
        try:
            log = ROOT / '.verification/run/runner-startup-error.log'
            log.parent.mkdir(parents=True, exist_ok=True)
            with log.open('a', encoding='utf-8') as stream:
                traceback.print_exc(file=stream)
        except OSError:
            pass
        print('STARTUP_REFUSED; private details: .verification/run/runner-startup-error.log', flush=True)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
