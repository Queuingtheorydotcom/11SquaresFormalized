#!/usr/bin/env python3
"""Serial full-stage T07 benchmarks, preserving the original five-block goal.

Runs literal/compact data with original/integerConvex checking, twice in a
mirrored order. Each trial uses identical imports and a fresh single-thread
Lean process, with no object output. Dependencies must already be verified.

  python3 scripts/benchmark_t07_stage.py --plan-only
  python3 scripts/benchmark_t07_stage.py
  python3 scripts/benchmark_t07_stage.py --lcm-only

This benchmarks one complete pruning step, not its history or promotion.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import resource
import signal
import subprocess
import sys
import tempfile
import time

import benchmark_t07 as common

ROOT = common.ROOT
FIXTURES = ROOT / 'simplification/benchmarks/t07/stage'
IMPORTS = (
    'ElevenSquare.Tasks.T07.Ext.RuntimeCheck',
    'ElevenSquare.Tasks.T07.Ext.CompactWitness',
    'ElevenSquare.Simplified.U5RowBlocks',
    'Mathlib.Tactic.IntervalCases',
)
ORIGINAL_TACTIC = '  interval_cases b <;> decide +kernel\n'
INTEGER_TACTIC = '''  interval_cases b
  all_goals
    unfold rowBlockB
    simp only [← RuntimeCheck.rowCheck_eq RuntimeCheck.integerConvex RuntimeCheck.integerConvex_agrees]
    decide +kernel
'''
CONDITIONS = (('original', 'literal'), ('integerConvex', 'compact'),
              ('integerConvex', 'literal'), ('original', 'compact'))
LCM_MODULE = 'ElevenSquare.Tasks.T07.Ext.IntegerConvexLcm'
LCM_CONFIG = '''namespace ElevenSquare.Tasks.T07.Ext.RuntimeCheck
def lcmConvexBenchmark : Components where
  empty := emptyB
  subset := subsetB
  convex := IntegerConvexLcm.convexLcmF

theorem lcmConvexBenchmark_agrees : Agrees lcmConvexBenchmark where
  empty_eq := fun _ _ => rfl
  subset_eq := fun _ _ _ => rfl
  convex_eq := IntegerConvexLcm.convexLcmF_eq_convexF
end ElevenSquare.Tasks.T07.Ext.RuntimeCheck

'''
LCM_TACTIC = INTEGER_TACTIC.replace('RuntimeCheck.integerConvex',
                                    'RuntimeCheck.lcmConvexBenchmark')


def load_fixtures():
    manifest = json.loads((FIXTURES / 'manifest.json').read_text())
    if (manifest['input_row_count'], manifest['cert_count'], manifest['subrow_count'],
            manifest['width'], manifest['blocks']) != (38, 38, 76, 8, 5):
        raise RuntimeError('Stage dimensions changed; benchmark requires review')
    result = {}
    for value in ('literal', 'compact'):
        entry = manifest['fixtures'][value.title()]
        path = ROOT / entry['path']
        data = path.read_bytes()
        if common.sha(data) != entry['sha256'] or len(data) != entry['bytes']:
            raise RuntimeError(f'Fixture hash/size differs: {entry["path"]}')
        source = data.decode()
        imports = tuple(line.removeprefix('import ') for line in source.splitlines()
                        if line.startswith('import '))
        if imports != IMPORTS:
            raise RuntimeError('Fixture imports changed; controlled import set needs review')
        if source.count(ORIGINAL_TACTIC) != 1:
            raise RuntimeError('Expected exactly one final original tactic')
        prefix, certificates = source.split('def cert0 ', 1)
        _, suffix = certificates.split('def certs :', 1)
        result[value] = (entry, source, prefix, suffix)
    if result['literal'][2:] != result['compact'][2:]:
        raise RuntimeError('Literal and compact context/theorem suffix differ')
    return manifest, result


def schedule(repeats, lcm_only=False):
    conditions = (('original', 'literal'), ('lcmConvex', 'literal')) if lcm_only else CONDITIONS
    return [{'repeat': repeat + 1, 'case': 'P2/S135', 'variant': variant, 'value': value}
            for repeat in range(repeats)
            for variant, value in (conditions if repeat % 2 == 0 else reversed(conditions))]


def trial_source(source, variant, lcm_only=False):
    if lcm_only:
        if variant not in ('original', 'lcmConvex'):
            raise RuntimeError('LCM comparison must use original or lcmConvex')
        marker = 'namespace ElevenSquare.Tasks.T07.Ext.T07StageS135\n'
        if source.count(marker) != 1:
            raise RuntimeError('Stage namespace changed; cannot insert shared configuration')
        # Both LCM-mode conditions elaborate the exact same import/configuration.
        source = 'import ' + LCM_MODULE + '\n' + source.replace(marker, LCM_CONFIG + marker, 1)
        if variant == 'lcmConvex':
            if source.count(ORIGINAL_TACTIC) != 1:
                raise RuntimeError('Expected exactly one final original tactic')
            changed = source.replace(ORIGINAL_TACTIC, LCM_TACTIC, 1)
            if changed.replace(LCM_TACTIC, ORIGINAL_TACTIC, 1) != source:
                raise RuntimeError('LCM tactic transformation did not round trip')
            return changed
    if variant == 'original':
        return source
    if variant != 'integerConvex' or source.count(ORIGINAL_TACTIC) != 1:
        raise RuntimeError('Unsupported tactic transformation')
    # Only the final tactic changes. The step_ok proposition, row count proof,
    # five-block decomposition, data definitions, and imports remain identical.
    changed = source.replace(ORIGINAL_TACTIC, INTEGER_TACTIC, 1)
    if changed.replace(INTEGER_TACTIC, ORIGINAL_TACTIC, 1) != source:
        raise RuntimeError('Tactic transformation did not round trip')
    return changed


def lcm_provenance():
    source = ROOT / Path(*LCM_MODULE.split('.')).with_suffix('.lean')
    obj = ROOT / '.lake/build/lib/lean' / Path(*LCM_MODULE.split('.')).with_suffix('.olean')
    receipt = ROOT / '.verification' / (LCM_MODULE + '.json')
    if not source.is_file() or not obj.is_file() or not receipt.is_file():
        raise RuntimeError('Missing LCM source, object, or receipt; verify IntegerConvexLcm first')
    result = {'source_sha256': common.sha(source.read_bytes()),
              'object_sha256': common.sha(obj.read_bytes())}
    accepted = json.loads(receipt.read_text())
    if (accepted.get('status') != 'accepted' or
            accepted.get('inputs', {}).get('source') != result['source_sha256'] or
            accepted.get('object_sha256') != result['object_sha256']):
        raise RuntimeError('Stale/unaccepted IntegerConvexLcm; recheck it with scripts/verify.py')
    result['verification_status'] = 'accepted'
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repeats', type=int, default=2, help='Default 2; use 1 only for an initial scout')
    ap.add_argument('--timeout', type=float, default=300)
    ap.add_argument('--max-total-seconds', type=float, default=2500)
    ap.add_argument('--lean', help='Already installed pinned Lean executable')
    ap.add_argument('--output', type=Path, help='Default report is separate for the optional LCM mode')
    ap.add_argument('--lcm-only', action='store_true', help='Literal original versus LCM checker only')
    ap.add_argument('--keep-going', action='store_true', help='Continue after failure or timeout')
    ap.add_argument('--plan-only', action='store_true', help='Validate and print order without Lean')
    args = ap.parse_args()
    if args.repeats < 1:
        ap.error('At least one repetition is required')
    if args.timeout <= 0 or args.max_total_seconds <= 0:
        ap.error('Timeouts must be positive')
    manifest, fixtures = load_fixtures()
    plan = schedule(args.repeats, args.lcm_only)
    for trial in plan:
        trial_source(fixtures[trial['value']][1], trial['variant'], args.lcm_only)
    if args.plan_only:
        print(json.dumps({'trial_count': len(plan), 'schedule': plan,
                          'timeout_seconds': args.timeout}, indent=2))
        return 0
    components = common.component_provenance()
    if args.lcm_only:
        components[LCM_MODULE] = lcm_provenance()
    lean, env, version = common.lean_runtime(args.lean)
    if args.output is None:
        args.output = Path('.verification/t07-stage-lcm-benchmark.json' if args.lcm_only else
                           '.verification/t07-stage-benchmark.json')
    output = args.output if args.output.is_absolute() else ROOT / args.output
    work_parent = ROOT / '.verification'
    work_parent.mkdir(exist_ok=True)
    report = {
        'schema': 1, 'kind': 'controlled-serial-t07-full-stage-kernel-benchmark',
        'compiler': version, 'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'lake_manifest_sha256': common.sha((ROOT / 'lake-manifest.json').read_bytes()),
        'script_sha256': common.sha(Path(__file__).read_bytes()),
        'shared_script_sha256': common.sha(Path(common.__file__).read_bytes()),
        'manifest_sha256': common.sha((FIXTURES / 'manifest.json').read_bytes()),
        'fixture_provenance': manifest, 'components': components,
        'imports': (LCM_MODULE, *IMPORTS) if args.lcm_only else IMPORTS,
        'lean_arguments': ['-j1', '-M0', '-s65536', '-DautoImplicit=false', '-DmaxHeartbeats=0'],
        'timeout_seconds': args.timeout, 'max_total_seconds': args.max_total_seconds,
        'repeats': args.repeats, 'scout_only': args.repeats < 2,
        'schedule': plan, 'trials': [], 'complete': False,
        'notes': [
            'Every condition imports the same four modules; only certificate data and the final tactic vary.',
            'The original step_ok goal, all 38 rows and 76 subrows, and all five blocks remain checked.',
            'Wall time includes startup, imports, parsing, elaboration and kernel checks.',
            'CPU is reaped child user+system time; no olean is written and no build command is run.',
            'Fixture acceptance is not a proof of stage history, promotion, or full-proof build time.',
        ],
    }
    if args.lcm_only:
        report['mode'] = 'literal-only-lcm-convexity'
        report['shared_lcm_configuration_sha256'] = common.sha(LCM_CONFIG.encode())
        report['notes'][0] = ('Both conditions import the same five modules and elaborate the same '
                              'configuration/equivalence lemma; only the final tactic varies.')
    signal.signal(signal.SIGTERM, common.interrupted)
    signal.signal(signal.SIGINT, common.interrupted)
    start_all = time.monotonic()
    common.write_report(output, report)
    try:
        with tempfile.TemporaryDirectory(prefix='t07-stage-runtime-', dir=work_parent) as work:
            path = Path(work) / 'check.lean'
            for number, trial in enumerate(plan, 1):
                remaining = args.max_total_seconds - (time.monotonic() - start_all)
                if remaining <= 0:
                    report['stopped_reason'] = 'total_time_bound'
                    break
                source = trial_source(fixtures[trial['value']][1], trial['variant'], args.lcm_only)
                path.write_text(source)
                command = [lean, *report['lean_arguments'], str(path.relative_to(ROOT))]
                usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
                start = time.perf_counter()
                common._current = subprocess.Popen(command, cwd=ROOT, env=env,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                status = 'accepted'
                try:
                    text, _ = common._current.communicate(timeout=min(args.timeout, remaining))
                    code_return = common._current.returncode
                    if code_return != 0:
                        status = 'failed'
                except subprocess.TimeoutExpired:
                    status = 'timeout'
                    common.stop_child()
                    text, code_return = 'Trial exceeded its time bound.', None
                elapsed = time.perf_counter() - start
                usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
                common._current = None
                row = {**trial, 'number': number, 'status': status, 'returncode': code_return,
                    'input_sha256': common.sha(source.encode()), 'wall_seconds': elapsed,
                    'user_cpu_seconds': usage_after.ru_utime - usage_before.ru_utime,
                    'system_cpu_seconds': usage_after.ru_stime - usage_before.ru_stime,
                    'cpu_seconds': (usage_after.ru_utime + usage_after.ru_stime -
                                    usage_before.ru_utime - usage_before.ru_stime),
                    'diagnostic_tail': text[-5000:]}
                report['trials'].append(row)
                report['summaries'] = common.summarize(report['trials'], args.repeats)
                common.write_report(output, report)
                print(f'{number}/{len(plan)} {trial["variant"]}/{trial["value"]}: '
                      f'{status}, wall={elapsed:.3f}s cpu={row["cpu_seconds"]:.3f}s', flush=True)
                if status != 'accepted' and not args.keep_going:
                    report['stopped_reason'] = status
                    break
            report['complete'] = (len(report['trials']) == len(plan) and
                                  all(row['status'] == 'accepted' for row in report['trials']))
    except KeyboardInterrupt:
        report['stopped_reason'] = 'interrupted'
    finally:
        common.stop_child()
        report['total_wall_seconds'] = time.monotonic() - start_all
        report['summaries'] = common.summarize(report['trials'], args.repeats)
        common.write_report(output, report)
    return 0 if report['complete'] else 1


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (RuntimeError, ValueError, OSError, subprocess.SubprocessError) as exc:
        print(f'benchmark_t07_stage: {exc}', file=sys.stderr)
        raise SystemExit(2)
