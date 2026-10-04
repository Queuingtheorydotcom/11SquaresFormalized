#!/usr/bin/env python3
"""Serial, source-bound kernel benchmarks for T07 checker variants.

Defaults: three fixtures, four variants, original literals, two repetitions.
Every trial imports the SAME RuntimeCheck and CompactWitness modules and checks
one full real Sub using decide +kernel. No .olean output is requested, no build
or package manager is run, and at most one Lean process exists at a time.

Prepare the dependencies separately with scripts/verify.py, then run:
  python3 scripts/benchmark_t07.py
  python3 scripts/benchmark_t07.py --include-compact
  python3 scripts/benchmark_t07.py --cases Small --timeout 120

This is a component benchmark, not a prediction of whole-proof build time.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time
from collections import defaultdict

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'simplification/benchmarks/t07'
VARIANTS = ('original', 'fastSum', 'integerConvex', 'combined')
CASES = ('Small', 'Medium', 'Larger')
COMPONENTS = ('RuntimeCheck', 'FastComb', 'IntegerConvex', 'CompactWitness')
PREFIX = 'ElevenSquare.Tasks.T07.Ext.'
BASE_CONDITIONS = (
    ('original', 'original'), ('combined', 'compact'),
    ('fastSum', 'original'), ('integerConvex', 'compact'),
    ('integerConvex', 'original'), ('fastSum', 'compact'),
    ('combined', 'original'), ('original', 'compact'),
)
_current = None


def sha(data):
    return hashlib.sha256(data).hexdigest()


def stop_child():
    global _current
    if _current is not None and _current.poll() is None:
        _current.terminate()
        try:
            _current.communicate(timeout=3)
        except subprocess.TimeoutExpired:
            _current.kill()
            _current.communicate()
    _current = None


def interrupted(signum, frame):
    raise KeyboardInterrupt


def load_fixtures():
    manifest = json.loads((FIXTURES / 'manifest.json').read_text())
    result = {}
    for entry in manifest['fixtures']:
        path = ROOT / entry['output_file']
        data = path.read_bytes()
        if sha(data) != entry['output_sha256']:
            raise RuntimeError(f'Fixture hash differs: {entry["output_file"]}')
        # Frozen context and source identity remain recorded even if those sources
        # are later shortened; fixture bytes themselves must always match.
        result[entry['tag']] = (entry, data.decode())
    return result


def schedule(cases, variants, include_compact, repeats):
    conditions = [pair for pair in BASE_CONDITIONS
                  if pair[0] in variants and (include_compact or pair[1] == 'original')]
    result = []
    for repeat in range(repeats):
        # Mirror both condition and case order on alternate passes. This fixed
        # order interleaves variants rather than timing all baselines first.
        ordered = conditions if repeat % 2 == 0 else list(reversed(conditions))
        names = list(cases) if repeat % 2 == 0 else list(reversed(cases))
        for variant, value in ordered:
            for case in names:
                result.append({'repeat': repeat + 1, 'case': case,
                               'variant': variant, 'value': value})
    return result


def trial_source(entry, fixture, variant, value):
    imports = '\n'.join(line for line in fixture.splitlines() if line.startswith('import '))
    if imports != 'import ElevenSquare.Tasks.T07.Ext.CompactWitness':
        raise RuntimeError('Fixture imports changed; controlled import set needs review')
    return ('import ElevenSquare.Tasks.T07.Ext.RuntimeCheck\n' + fixture +
            '\nopen ElevenSquare.Tasks.T07.Ext\n' +
            f'open {entry["namespace"]}\n\n' +
            'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n' +
            'example : RuntimeCheck.subCheck RuntimeCheck.' + variant +
            f' state {entry["owner"]} outputRows (fun _ => []) inputRow ' +
            entry['namespace'] + '.' + value + ' = true := by\n  decide +kernel\n')


def component_provenance():
    result = {}
    for short in COMPONENTS:
        module = PREFIX + short
        source = Path(*module.split('.')).with_suffix('.lean')
        obj = Path('.lake/build/lib/lean') / Path(*module.split('.')).with_suffix('.olean')
        if not (ROOT / obj).is_file():
            raise RuntimeError(f'Missing compiled dependency {module}; run scripts/verify.py first')
        record = {'source_sha256': sha((ROOT / source).read_bytes()),
                  'object_sha256': sha((ROOT / obj).read_bytes())}
        receipt = ROOT / '.verification' / (module + '.json')
        if not receipt.is_file():
            raise RuntimeError(f'Missing verification receipt for {module}; run scripts/verify.py first')
        accepted = json.loads(receipt.read_text())
        if (accepted.get('status') != 'accepted' or
                accepted.get('inputs', {}).get('source') != record['source_sha256'] or
                accepted.get('object_sha256') != record['object_sha256']):
            raise RuntimeError(f'Stale/unaccepted dependency {module}; recheck it with scripts/verify.py')
        record['verification_status'] = 'accepted'
        result[module] = record
    return result


def lean_runtime(explicit):
    env = os.environ.copy()
    elan_home = Path(env.get('ELAN_HOME', str(Path.home() / '.elan')))
    bin_dir = elan_home / 'bin'
    env['PATH'] = str(bin_dir) + os.pathsep + env.get('PATH', '')
    if explicit:
        lean = Path(explicit).expanduser().resolve()
    else:
        elan = shutil.which('elan', path=env['PATH'])
        if not elan:
            raise RuntimeError('No elan found; pass --lean with the installed pinned Lean executable')
        # This resolves the already installed toolchain; it neither builds the
        # Lake configuration nor invokes a package/cache download.
        resolved = subprocess.run([elan, 'which', 'lean'], cwd=ROOT, env=env,
                                  capture_output=True, text=True, timeout=30)
        if resolved.returncode:
            raise RuntimeError('Pinned toolchain is not installed; set it up separately')
        lean = Path(resolved.stdout.strip())
    if not lean.is_file():
        raise RuntimeError('Resolved Lean executable does not exist')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    paths = [ROOT / '.lake/build/lib/lean']
    for package in manifest['packages']:
        paths.append(ROOT / '.lake/packages' / package['name'] / '.lake/build/lib/lean')
    env['LEAN_PATH'] = os.pathsep.join(str(p) for p in paths)
    version = subprocess.run([str(lean), '--version'], cwd=ROOT, env=env,
                             capture_output=True, text=True, timeout=30)
    if version.returncode:
        raise RuntimeError('Cannot query Lean version')
    pinned = (ROOT / 'lean-toolchain').read_text().strip()
    pin_version = pinned.rsplit(':v', 1)[-1]
    if f'version {pin_version},' not in version.stdout:
        raise RuntimeError('Lean executable does not match lean-toolchain')
    return str(lean), env, version.stdout.strip()


def write_report(path, report):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + '.tmp')
    tmp.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    tmp.replace(path)


def summarize(rows, required_repeats):
    groups = defaultdict(list)
    for row in rows:
        if row['status'] == 'accepted':
            groups[(row['case'], row['variant'], row['value'])].append(row)
    summaries = []
    for (case, variant, value), items in sorted(groups.items()):
        summaries.append({'case': case, 'variant': variant, 'value': value,
                          'accepted_repeats': len(items),
                          'enough_repeats': len(items) >= required_repeats,
                          'wall_median_seconds': statistics.median(x['wall_seconds'] for x in items),
                          'cpu_median_seconds': statistics.median(x['cpu_seconds'] for x in items),
                          'wall_min_seconds': min(x['wall_seconds'] for x in items),
                          'wall_max_seconds': max(x['wall_seconds'] for x in items)})
    controls = {(x['case'], x['value']): x for x in summaries if x['variant'] == 'original'}
    for summary in summaries:
        baseline = controls.get((summary['case'], summary['value']))
        if baseline and baseline['enough_repeats'] and summary['enough_repeats']:
            summary['wall_ratio_to_same_value_original'] = (
                summary['wall_median_seconds'] / baseline['wall_median_seconds'])
    return summaries


def main():
    global _current
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cases', choices=CASES, nargs='+', default=list(CASES))
    ap.add_argument('--variants', choices=VARIANTS, nargs='+', default=list(VARIANTS))
    ap.add_argument('--include-compact', action='store_true')
    ap.add_argument('--repeats', type=int, default=2)
    ap.add_argument('--timeout', type=float, default=180)
    ap.add_argument('--max-total-seconds', type=float, default=3600)
    ap.add_argument('--lean', help='Already installed pinned Lean executable; no setup is run')
    ap.add_argument('--output', type=Path, default=Path('.verification/t07-benchmark.json'))
    ap.add_argument('--keep-going', action='store_true', help='Continue after a failed or timed-out trial')
    ap.add_argument('--plan-only', action='store_true', help='Validate fixtures and print order without running Lean')
    args = ap.parse_args()
    if args.repeats < 2:
        ap.error('At least two repetitions are required')
    if args.timeout <= 0 or args.max_total_seconds <= 0:
        ap.error('Timeouts must be positive')
    if len(set(args.cases)) != len(args.cases) or len(set(args.variants)) != len(args.variants):
        ap.error('Cases and variants must not repeat')
    fixtures = load_fixtures()
    plan = schedule(args.cases, args.variants, args.include_compact, args.repeats)
    if args.plan_only:
        for trial in plan:
            entry, source = fixtures[trial['case']]
            trial_source(entry, source, trial['variant'], trial['value'])
        print(json.dumps({'trial_count': len(plan), 'schedule': plan}, indent=2))
        return 0
    components = component_provenance()
    lean, env, version = lean_runtime(args.lean)
    output = args.output if args.output.is_absolute() else ROOT / args.output
    work_parent = ROOT / '.verification'
    work_parent.mkdir(exist_ok=True)
    report = {'schema': 1, 'kind': 'controlled-serial-t07-kernel-benchmark',
              'compiler': version, 'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
              'lake_manifest_sha256': sha((ROOT / 'lake-manifest.json').read_bytes()),
              'script_sha256': sha(Path(__file__).read_bytes()),
              'manifest_sha256': sha((FIXTURES / 'manifest.json').read_bytes()),
              'components': components, 'fixture_sha256': {
                  case: fixtures[case][0]['output_sha256'] for case in args.cases},
              'imports': [PREFIX + 'RuntimeCheck', PREFIX + 'CompactWitness'],
              'lean_arguments': ['-j1', '-M0', '-s65536', '-DautoImplicit=false', '-DmaxHeartbeats=0'],
              'timeout_seconds': args.timeout, 'max_total_seconds': args.max_total_seconds,
              'repeats': args.repeats, 'schedule': plan, 'trials': [], 'complete': False,
              'notes': ['Each trial uses a fresh single-thread Lean process and identical imports/data declarations.',
                        'Wall time includes process startup, imports, parsing, elaboration and one kernel proof.',
                        'CPU time is the reaped child user+system CPU measured by Python resource.getrusage.',
                        'No compiler output object is requested; the script never runs Lake/build/cache setup.',
                        'These component timings do not establish a 2-3 hour whole-proof build time.']}
    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    start_all = time.monotonic()
    write_report(output, report)
    try:
        with tempfile.TemporaryDirectory(prefix='t07-runtime-', dir=work_parent) as work:
            path = Path(work) / 'check.lean'
            for number, trial in enumerate(plan, 1):
                remaining = args.max_total_seconds - (time.monotonic() - start_all)
                if remaining <= 0:
                    report['stopped_reason'] = 'total_time_bound'
                    break
                entry, source = fixtures[trial['case']]
                code = trial_source(entry, source, trial['variant'], trial['value'])
                path.write_text(code)
                command = [lean, *report['lean_arguments'], str(path.relative_to(ROOT))]
                usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
                start = time.perf_counter()
                _current = subprocess.Popen(command, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                            stderr=subprocess.STDOUT, text=True)
                status = 'accepted'
                try:
                    text, _ = _current.communicate(timeout=min(args.timeout, remaining))
                    code_return = _current.returncode
                    if code_return != 0:
                        status = 'failed'
                except subprocess.TimeoutExpired:
                    status = 'timeout'
                    stop_child()
                    text, code_return = 'Trial exceeded its time bound.', None
                elapsed = time.perf_counter() - start
                usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
                _current = None
                row = {**trial, 'number': number, 'status': status, 'returncode': code_return,
                       'input_sha256': sha(code.encode()), 'wall_seconds': elapsed,
                       'user_cpu_seconds': usage_after.ru_utime - usage_before.ru_utime,
                       'system_cpu_seconds': usage_after.ru_stime - usage_before.ru_stime,
                       'cpu_seconds': (usage_after.ru_utime + usage_after.ru_stime -
                                       usage_before.ru_utime - usage_before.ru_stime),
                       'diagnostic_tail': text[-5000:]}
                report['trials'].append(row)
                report['summaries'] = summarize(report['trials'], args.repeats)
                write_report(output, report)
                print(f'{number}/{len(plan)} {trial["case"]} {trial["variant"]}/{trial["value"]}: '
                      f'{status}, wall={elapsed:.3f}s cpu={row["cpu_seconds"]:.3f}s', flush=True)
                if status != 'accepted' and not args.keep_going:
                    report['stopped_reason'] = status
                    break
            report['complete'] = (len(report['trials']) == len(plan) and
                                  all(row['status'] == 'accepted' for row in report['trials']))
    except KeyboardInterrupt:
        report['stopped_reason'] = 'interrupted'
    finally:
        stop_child()
        report['total_wall_seconds'] = time.monotonic() - start_all
        report['summaries'] = summarize(report['trials'], args.repeats)
        write_report(output, report)
    return 0 if report['complete'] else 1


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (RuntimeError, ValueError, OSError, subprocess.SubprocessError) as exc:
        print(f'benchmark_t07: {exc}', file=sys.stderr)
        raise SystemExit(2)
