#!/usr/bin/env python3
"""One low-priority, bounded Lean check. Never runs lake build or launches agents."""
import fcntl
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
CONFIG = json.loads((ROOT / 'verification/LOW_RESOURCE_MODE.json').read_text())
CPU_SECONDS = int(CONFIG['cpu_seconds'])
WALL_SECONDS = int(CONFIG['wall_seconds'])
MEMORY_MB = int(CONFIG['lean_memory_mb'])
NICE_INCREMENT = int(CONFIG['nice_increment'])
assert CONFIG['max_concurrent_lean_checks'] == 1 and CONFIG['lean_threads'] == 1
source = Path(sys.argv[1]).resolve()
assert source.is_file() and source.suffix == '.lean'
assert source.is_relative_to(ROOT), 'Check a source inside this project.'
label = sys.argv[2] if len(sys.argv) > 2 else source.stem
assert all(c.isalnum() or c in '_-' for c in label)
emit = len(sys.argv) == 4 and sys.argv[3] == '--emit-olean'
assert len(sys.argv) <= 3 or emit, 'Optional third argument: --emit-olean'
olean = None
if emit:
    rel = source.relative_to(ROOT)
    assert rel.parts[0] == 'ElevenSquare', 'Only emit project module objects.'
    olean = (ROOT / '.lake/build/lib' / rel).with_suffix('.olean')
    olean.parent.mkdir(parents=True, exist_ok=True)
out = ROOT / 'verification/small-checks' / (label + '-' + time.strftime('%Y%m%dT%H%M%SZ', time.gmtime()))
out.mkdir(parents=True)
lock = (ROOT / 'verification/small-check.lock').open('w')
try:
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
except BlockingIOError:
    raise SystemExit('Another small check is running; no second worker started.')


def limits():
    os.nice(NICE_INCREMENT)
    resource.setrlimit(resource.RLIMIT_CPU, (CPU_SECONDS, CPU_SECONDS + 1))


proc = None


def interrupted(signum, frame):
    raise KeyboardInterrupt


signal.signal(signal.SIGTERM, interrupted)
signal.signal(signal.SIGINT, interrupted)
status = 'interrupted'
code = None
started = time.monotonic()
try:
    with (out / 'lean.log').open('w') as log:
        command = ['bash', 'scripts/lake.sh', 'env', 'lean',
            f'-M{MEMORY_MB}', '-j1', '-T200000']
        if olean is not None:
            command += ['-o', str(olean)]
        command += [str(source)]
        proc = subprocess.Popen(command, cwd=ROOT,
            stdout=log, stderr=subprocess.STDOUT, start_new_session=True,
            preexec_fn=limits)
        try:
            code = proc.wait(timeout=WALL_SECONDS)
            status = 'accepted' if code == 0 else 'failed_or_resource_limited'
        except subprocess.TimeoutExpired:
            status, code = 'wall_time_limit', None
except KeyboardInterrupt:
    code = None
finally:
    if proc is not None:
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
    report = {'status': status, 'source': str(source.relative_to(ROOT)),
              'exit_code': code, 'elapsed_seconds': round(time.monotonic()-started, 2),
              'lean_memory_limit_mb': MEMORY_MB, 'lean_threads': 1,
              'cpu_seconds_limit': CPU_SECONDS, 'wall_seconds_limit': WALL_SECONDS,
              'nice_increment': NICE_INCREMENT,
              'emitted_olean': str(olean.relative_to(ROOT)) if olean is not None and status == 'accepted' else None,
              'meaning': 'Elaboration check only; inspect axioms and admissions before marking a proof complete.'}
    (out / 'CHECK.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report), flush=True)
    print('Log:', out / 'lean.log', flush=True)
    print((out / 'lean.log').read_text()[-6000:], flush=True)
    fcntl.flock(lock, fcntl.LOCK_UN)
raise SystemExit(0 if status == 'accepted' else 1)
