#!/usr/bin/env python3
"""Prepare and run one of 18 matching-platform proof workers, without uploading.

Workers 0 and 1 are machine-1 and machine-2; workers 2 through 17 are the hosted
workers. A selected worker result is a checkpoint, never a completed proof.
Only the final full-source replay and strict publication audit establish that.
"""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import platform
import re
import runpy
import shutil
import signal
import subprocess
import sys
import time
import traceback
import uuid

sys.dont_write_bytecode = True
import ci_plan
from run_complete_verification import (CONFIG, MODULE, StopControl, archive_failures,
                                       complete_state, read_json, run_stage, save_json, sha)
from verify_scheduler import CheckoutLock
from verify_support import input_digest, lean_arguments, positive_jobs, recorded_arguments

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = 'eleven-square-workers-v1'
PLATFORMS = ('windows-x86_64', 'linux-x86_64')
DEFAULT_PLAN = Path('verification/distributed-plan.json')
POLICY = 'exact-version-and-binary-sha256'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def platform_id():
    machine = platform.machine().lower()
    require(machine in {'amd64', 'x86_64'}, 'Unsupported compiler architecture')
    require(sys.platform == 'win32' or sys.platform.startswith('linux'), 'Unsupported compiler platform')
    return 'windows-x86_64' if sys.platform == 'win32' else 'linux-x86_64'


def compiler_identity(root, override=None):
    """Resolve the same pinned Lake environment as verify.py; never install it."""
    pin = (root / 'lean-toolchain').read_text(encoding='utf-8').strip()
    require(re.fullmatch(r'leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+', pin), 'Invalid pinned toolchain')
    env = os.environ.copy()
    elan_home = Path(env.get('ELAN_HOME', Path.home() / '.elan'))
    toolchain = elan_home / 'toolchains' / pin.replace('/', '--').replace(':', '---')
    suffix = '.exe' if os.name == 'nt' else ''
    installed = toolchain / 'bin' / ('lean' + suffix)
    require(installed.is_file(), 'Install the pinned toolchain before using workers')
    for package in read_json(root / 'lake-manifest.json')['packages']:
        name = package['name']
        require(re.fullmatch(r'[A-Za-z0-9_-]+', name) is not None
                and (root / '.lake/packages' / name).is_dir(), 'Pinned dependency checkout is missing')
    env['ELAN_TOOLCHAIN'] = pin
    env['PATH'] = str(elan_home / 'bin') + os.pathsep + env.get('PATH', '')
    lake = shutil.which('lake', path=env['PATH'])
    require(lake is not None, 'Pinned Lake environment is unavailable')
    resolved = subprocess.check_output([lake, 'env', sys.executable, '-B', '-c',
        "import shutil,json; print(json.dumps({'lean':shutil.which('lean')}))"],
        cwd=root, env=env, text=True, encoding='utf-8', stderr=subprocess.PIPE)
    executable = Path(json.loads(resolved)['lean']).resolve()
    require(executable.is_file() and executable.samefile(installed), 'Lake resolved a different compiler')
    if override is not None:
        supplied = override if override.is_absolute() else root / override
        require(supplied.resolve() == executable, 'Compiler override does not match pinned Lake environment')
    version = subprocess.check_output([str(executable), '--version'], cwd=root, env=env,
                                     text=True, encoding='utf-8', stderr=subprocess.PIPE).strip()
    require(re.fullmatch(r'[A-Za-z0-9_.,() +:\-]+', version) is not None,
            'Unexpected compiler identity text')
    parsed = re.search(r'\bversion ([0-9]+\.[0-9]+\.[0-9]+)\b', version)
    require(parsed is not None and parsed[1] == pin.rsplit(':v', 1)[1], 'Compiler/toolchain mismatch')
    target = platform_id()
    require(('windows' if target.startswith('windows') else 'linux') in version.lower(),
            'Compiler/platform mismatch')
    return {'version': version, 'binary_sha256': sha(executable), 'platform': target}


def accepted_jobs(root, graph, hashes, context, identity, default=4):
    """Capture actual accepted worker counts only for a current receipt closure."""
    jobs = {module: default for module in sorted(graph)}
    accepted, digests = {}, {}
    for module in ci_plan.dependency_order(graph):
        if any(dep not in accepted for dep in graph[module]):
            continue
        try:
            path = root / '.verification' / (module + '.json')
            receipt = read_json(path)
            inputs = receipt['inputs']
            arguments = recorded_arguments(module, inputs['arguments'])
            current = {'source': hashes[module], 'compiler': identity['version'], 'arguments': arguments,
                       'build_context': context,
                       'local_dependency_objects': {dep: accepted[dep] for dep in graph[module]},
                       'local_dependency_inputs': {dep: digests[dep] for dep in graph[module]}}
            obj = (root / '.lake/build/lib/lean').joinpath(*module.split('.')).with_suffix('.olean')
            if (receipt.get('status') != 'accepted' or inputs != current
                    or not (root / '.verification' / (module + '.log')).is_file()
                    or sha(obj) != receipt['object_sha256']):
                continue
            accepted[module], digests[module] = receipt['object_sha256'], input_digest(inputs)
            jobs[module] = positive_jobs(arguments[0][2:])
        except (OSError, ValueError, KeyError, TypeError):
            continue
    return jobs


def create_plan(root, identity, *, graph_data=None):
    expected = ci_plan.required_sources()
    graph, sizes, hashes = graph_data or ci_plan.read_graph(root, expected)
    plan = ci_plan.make_plan(graph, sizes, expected, hashes, shard_count=18)
    context = {name: sha(root / name) for name in CONFIG}
    plan.update(distribution_schema=SCHEMA,
                lean_toolchain=(root / 'lean-toolchain').read_text(encoding='utf-8').strip(),
                platform=identity['platform'], compiler_identity=identity,
                compiler_policy={'required_platform': identity['platform'], 'identity': POLICY},
                build_context_sha256=context,
                dependencies={m: sorted(graph[m]) for m in sorted(graph)},
                source_sha256=dict(sorted(hashes.items())), source_bytes=dict(sorted(sizes.items())),
                job_policy={'default_jobs': 4,
                            'module_jobs': accepted_jobs(root, graph, hashes, context, identity)})
    validate_structure(plan)
    return plan


def validate_structure(plan):
    require(plan.get('distribution_schema') == SCHEMA and plan.get('schema_version') == 1
            and plan.get('shard_count') == 18, 'Wrong distributed plan schema')
    require(plan.get('platform') in PLATFORMS, 'Unsupported planned compiler platform')
    identity = plan['compiler_identity']
    require(set(identity) == {'version', 'binary_sha256', 'platform'}
            and identity['platform'] == plan['platform']
            and re.fullmatch(r'[A-Za-z0-9_.,() +:\-]+', identity['version']) is not None
            and re.fullmatch(r'[0-9a-f]{64}', identity['binary_sha256']) is not None,
            'Invalid compiler identity')
    require(plan['compiler_policy'] == {'required_platform': plan['platform'], 'identity': POLICY},
            'Invalid compiler policy')
    graph = plan['dependencies']
    require(all(re.fullmatch(MODULE, module) is not None for module in graph), 'Invalid local module name')
    require(set(graph) == set(plan['source_sha256']) == set(plan['source_bytes'])
            == set(plan['job_policy']['module_jobs']), 'Incomplete plan source or jobs inventory')
    require(plan['job_policy']['default_jobs'] == 4, 'Invalid default worker count')
    for module, dependencies in graph.items():
        require(type(dependencies) is list and dependencies == sorted(set(dependencies))
                and set(dependencies) <= graph.keys(), 'Invalid dependency graph')
        require(type(plan['source_bytes'][module]) is int and plan['source_bytes'][module] >= 0
                and re.fullmatch(r'[0-9a-f]{64}', plan['source_sha256'][module]) is not None,
                'Invalid source fingerprint')
        lean_arguments(module, plan['job_policy']['module_jobs'][module])
    require(set(plan['build_context_sha256']) == set(CONFIG)
            and all(re.fullmatch(r'[0-9a-f]{64}', h) for h in plan['build_context_sha256'].values()),
            'Invalid configuration fingerprints')
    require(len(plan['shards']) == 18 and [s['index'] for s in plan['shards']] == list(range(18)),
            'Invalid worker assignment')
    assigned = []
    for shard in plan['shards']:
        require(shard['modules'] == sorted(set(shard['modules']))
                and set(shard['modules']) <= graph.keys(), 'Invalid worker targets')
        assigned.extend(shard['modules'])
    require(len(set(assigned)) == len(assigned), 'A target was assigned to multiple workers')
    ci_plan.dependency_order(graph)


def load_plan(root, path, *, current_sources=True):
    plan = read_json(path)
    validate_structure(plan)
    require(plan['lean_toolchain'] == (root / 'lean-toolchain').read_text(encoding='utf-8').strip()
            and plan['build_context_sha256'] == {name: sha(root / name) for name in CONFIG},
            'Stale planned configuration; explicitly regenerate the shared plan')
    if current_sources:
        expected = ci_plan.required_sources()
        graph, sizes, hashes = ci_plan.read_graph(root, expected)
        require(plan['dependencies'] == graph and plan['source_sha256'] == hashes
                and plan['source_bytes'] == sizes, 'Stale planned source graph; explicitly regenerate the shared plan')
        regenerated = ci_plan.make_plan(graph, sizes, expected, hashes, shard_count=18)
        require(all(plan.get(key) == value for key, value in regenerated.items()), 'Plan assignment or graph digest changed')
    return plan


def worker_closure(plan, worker):
    remaining = list(plan['shards'][worker]['modules'])
    closure = set()
    while remaining:
        module = remaining.pop()
        if module not in closure:
            closure.add(module)
            remaining.extend(plan['dependencies'][module])
    return closure


def private_path(root, path):
    result = (path if path.is_absolute() else root / path).resolve()
    state = (root / '.verification').resolve()
    require(state.is_relative_to(root.resolve()) and result != state and result.is_relative_to(state),
            'Private outputs must stay inside .verification')
    return result


def plan_path(root, path):
    result = (path if path.is_absolute() else root / path).resolve()
    require(result.is_relative_to(root.resolve())
            and any(result.is_relative_to((root / name).resolve()) for name in ('verification', '.verification')),
            'Plan must stay in verification or .verification')
    return result


class BudgetStop(StopControl):
    def __init__(self, path, seconds=None, clock=time.monotonic):
        super().__init__(path)
        self.clock = clock
        self.deadline = None if seconds is None else clock() + seconds

    def requested(self):
        if self.deadline is not None and self.clock() >= self.deadline:
            self.signaled = True
        return super().requested()


def child_verify(root, options):
    """Expand large target lists in-process, below the Windows command-line limit."""
    path = plan_path(root, options.plan)
    require(sha(path) == options.plan_sha256, 'Shared plan changed before worker startup')
    plan = load_plan(root, path, current_sources=False)
    os.environ['ELAN_TOOLCHAIN'] = plan['lean_toolchain']
    require(compiler_identity(root, options.compiler) == plan['compiler_identity'], 'Worker compiler identity differs')
    jobs = private_path(root, options.jobs_file)
    require(read_json(jobs) == plan['job_policy']['module_jobs'], 'Shared jobs file changed')
    targets = plan['shards'][options.worker]['modules']
    if not targets:
        print('EMPTY_WORKER: no selected targets.', flush=True)
        return 0
    argv = ['scripts/verify.py', '--keep-going', '--jobs', '4', '--jobs-file', str(jobs),
            '--max-parallel', str(options.max_parallel), '--memory-percent', str(options.memory_percent),
            '--stop-file', str(private_path(root, options.stop_file))]
    for module in targets:
        argv.extend(['--module', module])
    sys.argv = argv
    runpy.run_path(str(root / 'scripts/verify.py'), run_name='__main__')
    return 0


def run_checks(root, options, plan, path, *, stage_runner=run_stage):
    state = root / '.verification'
    name = 'final' if options.command == 'final' else f'worker-{options.worker:02d}'
    default_stop = state / 'distributed' / ('stop-' + name)
    stop_path = private_path(root, options.stop_file or default_stop)
    if options.resume_after_stop:
        require(stop_path == default_stop.resolve(), 'Only the exact default stop file can be cleared')
        stop_path.unlink(missing_ok=True)
    stop = BudgetStop(stop_path, options.budget_seconds)
    folder = state / 'distributed/runs' / (name + '-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ-') + uuid.uuid4().hex[:8])
    folder.mkdir(parents=True)
    summary = {'status': 'RUNNING', 'worker': None if name == 'final' else options.worker,
               'graph_sha256': plan['graph_sha256'], 'global_optimality_proved': False,
               'checked_modules': 0, 'failed_modules': [], 'blocked_module_count': 0}

    def publish():
        save_json(folder / 'summary.json', summary)
        save_json(state / 'distributed' / ('latest-' + name + '.json'),
                  {'directory': folder.relative_to(root).as_posix(), 'status': summary['status']})

    publish()
    previous = {sig: signal.getsignal(sig) for sig in (signal.SIGINT, signal.SIGTERM)}
    for sig in previous:
        signal.signal(sig, stop.signal)
    try:
        with (folder / 'runner.log').open('ab') as log:
            try:
                if stop.requested():
                    summary['status'] = 'STOPPED'
                    return 130
                jobs = state / 'distributed/jobs.json'
                save_json(jobs, plan['job_policy']['module_jobs'])
                if name == 'final':
                    command = [sys.executable, '-B', '-u', 'scripts/verify.py', '--all', '--keep-going',
                               '--jobs', '4', '--jobs-file', str(jobs.relative_to(root)),
                               '--max-parallel', str(options.max_parallel), '--memory-percent', str(options.memory_percent),
                               '--stop-file', str(stop_path.relative_to(root))]
                else:
                    command = [sys.executable, '-B', '-u', 'scripts/distributed_worker.py', '_verify',
                               '--plan', str(path.relative_to(root)), '--plan-sha256', sha(path),
                               '--worker', str(options.worker), '--jobs-file', str(jobs.relative_to(root)),
                               '--max-parallel', str(options.max_parallel), '--memory-percent', str(options.memory_percent),
                               '--stop-file', str(stop_path.relative_to(root))]
                    if options.compiler is not None:
                        command.extend(['--compiler', str(options.compiler)])
                outcome = stage_runner(root, 'verifier', command, folder, stop, log)
                failed = sorted(m for m in outcome.failed if re.fullmatch(MODULE, m))
                archive_failures(root, folder, failed)
                summary.update(checked_modules=len(outcome.accepted), failed_modules=failed,
                               blocked_module_count=len(outcome.blocked))
                if stop.requested():
                    summary['status'] = 'STOPPED'
                    return 130
                if outcome.returncode:
                    summary['status'] = 'VERIFICATION_FAILED'
                    return 1
                if name != 'final':
                    if plan['shards'][options.worker]['modules']:
                        selected = read_json(state / 'selected-result.json')
                        require(selected.get('status') == 'SELECTED_MODULES_COMPILE'
                                and selected.get('targets') == plan['shards'][options.worker]['modules']
                                and selected.get('checked_modules') == len(worker_closure(plan, options.worker)),
                                'Worker result does not match assigned closure')
                        summary['checked_modules'] = selected['checked_modules']
                    summary['status'] = 'WORKER_CHECKPOINT_ACCEPTED'
                    return 0
                summary['checked_modules'] = complete_state(root, finalized=False)
                with CheckoutLock(state / 'verifier.lock'):
                    outcome = stage_runner(root, 'finalizer',
                        [sys.executable, '-B', '-u', 'scripts/finalize_verification.py', '--write'], folder, stop, log)
                    if stop.requested():
                        summary['status'] = 'STOPPED'
                        return 130
                    require(outcome.returncode == 0, 'Strict finalizer failed')
                    summary['checked_modules'] = complete_state(root, finalized=True)
                summary.update(status='OPTIMALITY_PROVED', global_optimality_proved=True)
                return 0
            except BaseException:
                log.write(traceback.format_exc().encode('utf-8', errors='replace')); log.flush()
                summary['status'] = 'FAILED'
                return 1
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)
        publish()
        print(summary['status'] + '; private logs: .verification/distributed/runs/', flush=True)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True, metavar='{plan,run,final,export,import}')
    descriptions = {'plan': 'Create the shared 18-worker plan.', 'run': 'Check one assigned worker closure.',
                    'final': 'Replay all sources and run the strict final audit.',
                    'export': 'Write a sanitized private checkpoint.',
                    'import': 'Validate and merge matching private checkpoints.'}
    for name in ('plan', 'run', 'final', 'export', 'import', '_verify'):
        command = sub.add_parser(name, **({'help': descriptions[name]} if name in descriptions else {}))
        command.add_argument('--plan', type=Path, default=DEFAULT_PLAN)
        command.add_argument('--compiler', type=Path, help='Optional actual pinned Lean executable; its path is never stored in the plan.')
        if name == 'plan':
            command.add_argument('--platform', choices=PLATFORMS)
        if name in ('run', 'export', '_verify'):
            command.add_argument('--worker', type=int, choices=range(18), required=True, metavar='0..17')
        if name in ('run', 'final', '_verify'):
            command.add_argument('--max-parallel', type=positive_jobs, default=1)
            command.add_argument('--memory-percent', type=int, choices=range(1, 96), default=95, metavar='1..95')
            command.add_argument('--stop-file', type=Path, required=name == '_verify')
        if name in ('run', 'final'):
            command.add_argument('--resume-after-stop', action='store_true')
            command.add_argument('--budget-seconds', type=positive_jobs,
                                 help='Request a graceful drain after this budget; active proofs are not killed.')
        if name == '_verify':
            command.add_argument('--plan-sha256', required=True)
            command.add_argument('--jobs-file', type=Path, required=True)
        if name == 'export':
            command.add_argument('--output', type=Path)
        if name == 'import':
            command.add_argument('--archive', type=Path, action='append', required=True)
    options = parser.parse_args(argv)
    try:
        if options.command == '_verify':
            return child_verify(ROOT, options)
        path = plan_path(ROOT, options.plan)
        if options.command == 'plan':
            require(path == (ROOT / DEFAULT_PLAN).resolve()
                    or path.is_relative_to((ROOT / '.verification/distributed').resolve()),
                    'Plan output must be the shared distributed plan or private distributed directory')
            identity = compiler_identity(ROOT, options.compiler)
            require(options.platform is None or options.platform == identity['platform'], 'Planned platform differs from this compiler')
            plan = create_plan(ROOT, identity)
            path.parent.mkdir(parents=True, exist_ok=True)
            temporary = path.with_name(path.name + '.checking')
            temporary.write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n',
                                 encoding='utf-8', newline='\n')
            os.replace(temporary, path)
            print('PLANNED: 18 workers; exact compiler, source graph, and shared jobs policy recorded.', flush=True)
            return 0
        with CheckoutLock(ROOT / '.verification/run/complete-run.lock'):
            with CheckoutLock(ROOT / '.verification/verifier.lock'):
                plan = load_plan(ROOT, path)
                os.environ['ELAN_TOOLCHAIN'] = plan['lean_toolchain']
                identity = compiler_identity(ROOT, options.compiler)
                require(identity == plan['compiler_identity'], 'Exact compiler identity differs from shared plan')
                if options.command in ('export', 'import'):
                    from distributed_bundle import export_bundle, import_bundle
                    if options.command == 'export':
                        output = private_path(ROOT, options.output or Path(f'.verification/distributed/worker-{options.worker:02d}.tar.gz'))
                        result = export_bundle(ROOT, plan, options.worker, output, identity)
                    else:
                        result = [import_bundle(ROOT, plan, private_path(ROOT, p), identity) for p in options.archive]
                    print(json.dumps(result), flush=True)
                    return 0
            return run_checks(ROOT, options, plan, path)
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError):
        log = ROOT / '.verification/distributed/error.log'
        log.parent.mkdir(parents=True, exist_ok=True)
        with log.open('a', encoding='utf-8') as stream:
            traceback.print_exc(file=stream)
        print('REFUSED: see private .verification/distributed/error.log; no completion claimed.', flush=True)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
