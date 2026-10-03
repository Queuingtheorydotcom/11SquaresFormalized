#!/usr/bin/env python3
"""Coordinated Lean replay and axiom audit (one compiler process by default)."""
from pathlib import Path
import argparse
import atexit
import hashlib
import json
import os
import shutil
import signal
import subprocess
import sys
sys.dont_write_bytecode = True
# Redirected Windows streams otherwise use a legacy code page. Lean diagnostics
# and declaration names are UTF-8, including when a failed check is printed.
for stream in (sys.stdout, sys.stderr):
    stream.reconfigure(encoding='utf-8')
import time
from check_sources import ROOT, check, code_only, imports
from verify_support import (STANDARD_AXIOMS, admitted_targets, public_audit_status,
                            priority_order, input_digest, reusable_fingerprint, audit_axioms,
                            positive_jobs, lean_arguments)
from verify_scheduler import CheckoutLock, CheckFailed, CheckpointStop, schedule

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--setup', action='store_true', help='Install the pinned toolchain and dependency cache; keep tracked simplified sources.')
ap.add_argument('--all', action='store_true', help='Check every included local source module.')
ap.add_argument('--keep-going', action='store_true', help='Continue independent modules after a failure; never accepts an incomplete build.')
ap.add_argument('--fresh', action='store_true', help='Ignore this checkout\'s matching accepted receipts.')
ap.add_argument('--jobs', type=positive_jobs, default=1,
                help='Worker threads within each new Lean process (default: 1); matching receipts retain their recorded count.')
ap.add_argument('--jobs-file', type=Path,
                help='Optional shared module-to-thread-count JSON map; mapped modules must use exactly those recorded worker counts.')
ap.add_argument('--max-parallel', type=positive_jobs, default=1,
                help='Maximum independent compiler processes owned by this verifier (default: 1); parallel starts require measured resource headroom.')
ap.add_argument('--memory-percent', type=int, choices=range(1, 96), default=95,
                metavar='1..95', help='Physical/commit memory target for optional parallel scheduling (default: 95 percent).')
ap.add_argument('--stop-file', type=Path,
                help='If this file appears, finish active module checks and stop without starting more; remove it before resuming.')
ap.add_argument('--plan', action='store_true', help='Print dependency order without installing or compiling.')
ap.add_argument('--module', action='append', default=[], help='Check only this module and its dependencies (repeatable).')
args = ap.parse_args()
state = ROOT / '.verification'
state.mkdir(exist_ok=True)
if not args.plan:
    owner = CheckoutLock(state / 'verifier.lock')
    try:
        owner.acquire()
    except OSError as error:
        raise SystemExit('Another verifier owns this checkout; wait for it to finish.') from error
    atexit.register(owner.close)
if args.setup and not args.plan:
    print('Using tracked simplified sources; setup installs only Lean and dependency cache.', flush=True)
print(json.dumps(check(use_cache=not args.fresh)), flush=True)
admissions = json.loads((ROOT / 'verification/admissions.json').read_text(encoding='utf-8'))['sites']
try:
    unfinished = admitted_targets(admissions)
except ValueError as error:
    raise SystemExit(str(error)) from error
files = sorted((ROOT / 'ElevenSquare').rglob('*.lean')) + sorted((ROOT / 'Sqpack').rglob('*.lean')) + [ROOT / 'ElevenSquare.lean', ROOT / 'Sqpack.lean']
modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p for p in files}
job_overrides = {}
if args.jobs_file is not None:
    try:
        job_overrides = json.loads(args.jobs_file.read_text(encoding='utf-8'))
        if (not isinstance(job_overrides, dict)
                or any(m not in modules or type(n) is not int or not 0 < n < 2**32
                       for m, n in job_overrides.items())):
            raise ValueError('Expected known module names and positive UInt32 thread counts.')
    except (OSError, ValueError) as error:
        raise SystemExit('Invalid shared worker-count map.') from error
order = []; done = set()
def visit(m):
    if m in done or m not in modules: return
    for dep in imports(modules[m]): visit(dep)
    done.add(m); order.append(m)
if args.all:
    for m in sorted(modules):
        if m != 'ElevenSquare.Verification': visit(m)
if args.module:
    for m in args.module:
        if m not in modules: raise SystemExit('Unknown local module: ' + m)
        visit(m)
else:
    visit('ElevenSquare.Verification')
selected = set(order)
dependencies = {m: [d for d in imports(modules[m]) if d in selected] for m in selected}
order = priority_order(dependencies, {m: modules[m].stat().st_size for m in selected})
if args.plan:
    print('Dependency-ordered local module checks:', len(order))
    print('\n'.join(order))
    raise SystemExit(0)

child = None
signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
def run(command, **kwargs):
    global child
    child = subprocess.Popen(command, cwd=ROOT, **kwargs)
    try:
        code = child.wait()
    except BaseException:
        child.terminate()
        try: child.wait(timeout=3)
        except subprocess.TimeoutExpired:
            child.kill(); child.wait()
        raise
    finally:
        child = None
    if code: raise SystemExit(code)

bin_dir = Path(os.environ.get('ELAN_HOME', Path.home() / '.elan')) / 'bin'
env = os.environ.copy()
if bin_dir.is_dir(): env['PATH'] = str(bin_dir) + os.pathsep + env.get('PATH', '')
elan = shutil.which('elan', path=env['PATH'])
lake = shutil.which('lake', path=env['PATH'])
if not elan or not lake:
    raise SystemExit('Install elan and make its bin directory available, then retry.')
if args.setup:
    run([elan, 'toolchain', 'install', (ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip()], env=env)
    run([lake, 'exe', 'cache', 'get'], env=env)
# Read only the scoped Lean executable/path, not the full user environment.
runtime = json.loads(subprocess.check_output(
    [lake, 'env', sys.executable, '-c',
     "import os,shutil,json; print(json.dumps({'lean':shutil.which('lean'), 'path':os.environ.get('LEAN_PATH','')}))"],
    cwd=ROOT, env=env, text=True, encoding='utf-8'))
lean_env = env.copy(); lean_env['LEAN_PATH'] = runtime['path']
version = subprocess.check_output([runtime['lean'], '--version'], cwd=ROOT, env=lean_env,
                                  text=True, encoding='utf-8').strip()
if '4.34.1' not in version:
    raise SystemExit('Unexpected Lean version; use the pinned lean-toolchain.')

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda: f.read(4 << 20), b''): h.update(b)
    return h.hexdigest()

def object_path(m): return ROOT / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')

config_paths = [ROOT / p for p in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json']]
build_context = {p.name: sha(p) for p in config_paths}
config_modified_at = max(p.stat().st_mtime_ns for p in config_paths)
historical = json.loads((ROOT / 'verification/wand125-integration.json').read_text(encoding='utf-8'))
manifest = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))
legacy_baseline = (
    historical.get('lean_toolchain') == (ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip()
    and historical.get('mathlib_revision') == next(
        (p.get('rev') for p in manifest['packages'] if p['name'] == 'mathlib'), None))
input_ids = {}; checked_times = {}
indices = {m: i + 1 for i, m in enumerate(order)}

def progress(m, outcome):
    print(f'[{indices[m]}/{len(order)}] {outcome} {m}', flush=True)

def write_receipt(path, data):
    temporary = path.with_name(path.name + '.checking')
    try:
        temporary.write_text(json.dumps(data, indent=2)+'\n', encoding='utf-8')
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)

class ModuleCheck:
    def __init__(self, m, target, receipt, log, fingerprint, dependency_checked_at):
        self.module, self.target, self.receipt, self.log = m, target, receipt, log
        self.fingerprint = fingerprint
        self.dependency_checked_at = dependency_checked_at
        self.temporary = target.with_name(target.name + '.checking')
        self.process = None
        self.stream = None
        self.started = None

    def start(self):
        self.temporary.unlink(missing_ok=True)
        self.started = time.monotonic()
        # Lean writes UTF-8 bytes directly; never transcode its evidence logs.
        self.stream = self.log.open('wb')
        self.process = subprocess.Popen(
            [runtime['lean'], '--root=.', *self.fingerprint['arguments'],
             '-o', str(self.temporary.relative_to(ROOT)),
             str(modules[self.module].relative_to(ROOT))],
            cwd=ROOT, env=lean_env, stdout=self.stream, stderr=subprocess.STDOUT)

    def close_log(self):
        if self.stream is not None:
            self.stream.close()
            self.stream = None

    def accept(self):
        self.close_log()
        os.replace(self.temporary, self.target)
        checked_at = time.time_ns()
        write_receipt(self.receipt, {
            'module': self.module, 'status': 'accepted', 'inputs': self.fingerprint,
            'checked_at_ns': checked_at, 'object_sha256': sha(self.target),
            'elapsed_seconds': round(time.monotonic() - self.started, 2)})
        input_ids[self.module] = input_digest(self.fingerprint)
        checked_times[self.module] = max(checked_at, self.dependency_checked_at)
        progress(self.module, 'accepted')

    def reject(self, reason):
        self.close_log()
        self.temporary.unlink(missing_ok=True)
        write_receipt(self.receipt, {'module': self.module,
            'status': 'failed_or_interrupted', 'inputs': self.fingerprint})
        if self.log.is_file():
            # Interrupted output can end inside a UTF-8 code point. Replacement
            # is diagnostic-only: accepted evidence is audited strictly below.
            print(self.log.read_text(encoding='utf-8', errors='replace')[-4000:], file=sys.stderr, flush=True)
        progress(self.module, 'failed' if reason == 'compiler_failed' else 'interrupted')

def prepare(m):
    src = modules[m]; target = object_path(m)
    target.parent.mkdir(parents=True, exist_ok=True)
    receipt = state / (m + '.json'); log = state / (m + '.log')
    local_deps = [d for d in imports(src) if d in modules]
    deps = {d: sha(object_path(d)) for d in local_deps}
    fingerprint = {'source': sha(src), 'local_dependency_objects': deps, 'compiler': version,
                   'arguments': lean_arguments(m, job_overrides.get(m, args.jobs)),
                   'build_context': build_context,
                   'local_dependency_inputs': {d: input_ids[d] for d in local_deps}}
    old = json.loads(receipt.read_text(encoding='utf-8')) if receipt.is_file() else {}
    old_checked_at = old.get('checked_at_ns', receipt.stat().st_mtime_ns if receipt.is_file() else 0)
    dependency_checked_at = max([config_modified_at] + [checked_times[d] for d in local_deps])
    old_files_modified_at = max([dependency_checked_at] +
        [p.stat().st_mtime_ns for p in [target, log] if p.is_file()])
    cached_fingerprint = reusable_fingerprint(
        m, old.get('inputs'), fingerprint, legacy_baseline=legacy_baseline,
        checked_at=old_checked_at, newest_input=old_files_modified_at)
    if (m in job_overrides and cached_fingerprint is not None
            and cached_fingerprint['arguments'] != fingerprint['arguments']):
        # Distributed workers must agree on the actual provenance of shared
        # dependencies. Recheck with the chosen flags; never relabel a receipt.
        cached_fingerprint = None
    if (not args.fresh and target.is_file() and old.get('status') == 'accepted'
            and cached_fingerprint is not None
            and old.get('object_sha256') == sha(target)
            and log.is_file()):
        if old.get('inputs') != cached_fingerprint:
            old.update(inputs=cached_fingerprint, checked_at_ns=old_checked_at)
            write_receipt(receipt, old)
        input_ids[m] = input_digest(cached_fingerprint)
        checked_times[m] = max(old_checked_at, dependency_checked_at)
        progress(m, 'cached')
        return None
    return ModuleCheck(m, target, receipt, log, fingerprint, dependency_checked_at)

def scheduling_event(kind, module, detail):
    if kind == 'blocked':
        progress(module, 'blocked')
    elif kind == 'retry_exclusive':
        print(f'Retrying {module} alone after resource pressure: {detail}', flush=True)
    elif kind == 'waiting':
        print(f'Waiting for resource headroom: {detail}', flush=True)
    elif kind == 'started' and args.max_parallel > 1:
        progress(module, 'started')
    elif kind == 'draining':
        print('Stop requested; finishing active module checks before exiting.', flush=True)

guard = None
if args.max_parallel > 1:
    from verify_resources import ResourceGuard
    guard = ResourceGuard(memory_percent=args.memory_percent)
try:
    replay = schedule(order, dependencies, prepare, max_parallel=args.max_parallel,
                      keep_going=args.keep_going, guard=guard, event=scheduling_event,
                      stop_requested=lambda: args.stop_file is not None and args.stop_file.exists())
except CheckFailed as error:
    raise SystemExit(error.returncode) from error
except CheckpointStop:
    raise SystemExit('Stopped at a checkpoint; accepted receipts can be resumed.')
accepted = len(replay.accepted)
failed, blocked = replay.failed, replay.blocked

if failed or blocked:
    result = {'status': 'INCOMPLETE_BUILD', 'checked_modules': accepted,
              'failed_modules': failed, 'blocked_modules': blocked}
    (state / 'incomplete-result.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(f'Incomplete build: {len(failed)} failed, {len(blocked)} blocked, {accepted} accepted.', flush=True)
    raise SystemExit(1)

def audit(module):
    source = modules[module].read_text(encoding='utf-8')
    if '#print' not in source:
        return {}
    try:
        return audit_axioms(code_only(source),
                            (state / (module + '.log')).read_text(encoding='utf-8'), STANDARD_AXIOMS, unfinished)
    except ValueError as error:
        raise SystemExit(module + ': ' + str(error)) from error

axioms = {}
for m in order:
    axioms.update(audit(m))

if args.module:
    result = {'status': 'SELECTED_MODULES_COMPILE', 'checked_modules': accepted,
              'targets': args.module, 'axioms': axioms}
    (state / 'selected-result.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
    raise SystemExit(0)

try:
    status = public_audit_status(axioms, len(admissions))
except ValueError as error:
    raise SystemExit(str(error)) from error
result = dict(status, checked_modules=accepted,
              axioms={n: sorted(values) for n, values in axioms.items()})
(state / 'result.json').write_text(json.dumps(result,indent=2)+'\n', encoding='utf-8')
print(json.dumps(result,indent=2))
if result['global_optimality_proved']:
    print('Global optimality verified with no inventoried admissions and clean public axiom audits.')
else:
    print('Partial assembly accepted. See MISSING.md for the remaining proof obligations.')
