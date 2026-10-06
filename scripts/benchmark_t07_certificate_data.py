#!/usr/bin/env python3
"""Bounded, serial comparison of certificate data on the frozen S135 step.

The geometry, 38 input rows, 76 subrows and five blocks are identical. The
baseline and tail-trimmed condition use the unchanged production checker.
The optional direct condition uses a separately proved support-index checker.
No production files are changed and no compiler objects are written.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import resource
import shutil
import signal
import subprocess
import tempfile
import time

import benchmark_t07 as common
import benchmark_t07_stage as stage
from simplify_t07_witnesses import Parser, datum

ROOT = common.ROOT


def transform_direct(source):
    """Propose support indices; only the Lean checker can accept them."""
    changes = []
    counts = Counter()

    def supports(node):
        if node.kind != 'list':
            raise ValueError('Expected an explicit list of Farkas vectors')
        result = []
        for vector in node.args:
            weights = datum(vector)
            if not isinstance(weights, list):
                raise ValueError('Expected a literal Farkas vector')
            indices = [i for i, value in enumerate(weights) if value != 0]
            if any(value < 0 for value in weights) or len(indices) > 2:
                result.append('(.literal ' + vector.raw + ')')
                counts['literal_vectors'] += 1
            elif not indices:
                result.append('.zero')
                counts['zero_vectors'] += 1
            elif len(indices) == 1:
                result.append(f'(.one {indices[0]})')
                counts['one_vectors'] += 1
            else:
                result.append(f'(.two {indices[0]} {indices[1]})')
                counts['two_vectors'] += 1
        changes.append((node.start, node.end, '[' + ', '.join(result) + ']'))

    def tree(node):
        if node.kind == 'paren':
            tree(node.args[0])
        elif node.kind in ('keep', 'collide'):
            supports(node.args[1])
        elif node.kind == 'forbidHull':
            supports(node.args[2])
        elif node.kind == 'forbid':
            tri = node.args[1]
            if tri.kind != 'struct' or len(tri.args) != 4:
                raise ValueError('Unsupported triangle literal')
            supports(tri.args[3])
        elif node.kind == 'empty':
            counts['empty_leaves'] += 1
        elif node.kind == 'split':
            tree(node.args[1])
            tree(node.args[2])
        elif node.kind == 'chain':
            for cut in node.args[0].args:
                if cut.kind not in ('left', 'right'):
                    raise ValueError('Unsupported closed split')
                tree(cut.args[1])
            tree(node.args[1])
        else:
            raise ValueError('Unsupported tree: ' + node.kind)

    for match in re.finditer(r'^def cert\d+ : List Sub :=', source, re.M):
        cert = Parser(source, match.end()).val()
        if cert.kind != 'list':
            raise ValueError('Expected a literal certificate list')
        for sub in cert.args:
            if sub.kind != 'struct' or len(sub.args) != 8:
                raise ValueError('Unsupported Sub literal')
            tree(sub.args[7])
            counts['subrows'] += 1
        counts['rows'] += 1
    if counts['rows'] != 38 or counts['subrows'] != 76:
        raise ValueError('This pilot is bound to the complete frozen S135 step')
    changed = source
    for start, end, value in sorted(changes, reverse=True):
        changed = changed[:start] + value + changed[end:]
    changed = changed.replace('List Sub', 'List DirectSub')
    changed = changed.replace('CTreeChain.build', 'DirectChain.build')
    changed = changed.replace('stepB prev', 'directStepB prev')
    changed = changed.replace('apply stepB_of_row_blocks', 'apply directStepB_of_row_blocks')
    counts['bytes_before'] = len(source.encode())
    counts['bytes_after'] = len(changed.encode())
    return changed, dict(counts)


def direct_provenance():
    results = {}
    for short in ('DirectSupport', 'DirectTree'):
        module = common.PREFIX + short
        source = ROOT / Path(*module.split('.')).with_suffix('.lean')
        obj = ROOT / '.lake/build/lib/lean' / Path(*module.split('.')).with_suffix('.olean')
        receipt = ROOT / '.verification' / (module + '.json')
        if not all(p.is_file() for p in (source, obj, receipt)):
            raise RuntimeError(f'First verify {module} with scripts/verify.py')
        record = {'source_sha256': common.sha(source.read_bytes()),
                  'object_sha256': common.sha(obj.read_bytes())}
        accepted = json.loads(receipt.read_text())
        if (accepted.get('status') != 'accepted' or
                accepted.get('inputs', {}).get('source') != record['source_sha256'] or
                accepted.get('object_sha256') != record['object_sha256']):
            raise RuntimeError(f'Stale or unaccepted dependency: {module}')
        results[module] = record
    return results


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--variants', choices=('tail', 'tail_core', 'direct', 'direct_core'),
                    nargs='+', default=['tail'])
    ap.add_argument('--repeats', type=int, default=2)
    ap.add_argument('--timeout', type=float, default=180)
    ap.add_argument('--max-total-seconds', type=float, default=900)
    ap.add_argument('--memory-mib', type=int, default=3072)
    ap.add_argument('--min-free-gib', type=float, default=2)
    ap.add_argument('--output', type=Path, default=Path('.verification/t07-certificate-data-benchmark.json'))
    ap.add_argument('--plan-only', action='store_true')
    args = ap.parse_args()
    if min(args.repeats, args.timeout, args.max_total_seconds, args.memory_mib, args.min_free_gib) <= 0:
        ap.error('Resource bounds and repeat count must be positive')
    if len(set(args.variants)) != len(args.variants):
        ap.error('Variants must not repeat')
    _, fixtures = stage.load_fixtures()
    original = fixtures['literal'][1]
    closing = 'end ElevenSquare.Tasks.T07.Ext.T07StageS135\n'
    if original.count(closing) != 1:
        raise RuntimeError('Unexpected benchmark namespace boundary')
    original = original.replace(closing, '''theorem pruning : ExtStep prev (replaceRows prev 0 rs) :=
  stepB_sound (by intro j hj; simp [pcov] at hj) step_ok

''' + closing)
    sources, transformations = {'original': original}, {}
    if 'tail' in args.variants or 'tail_core' in args.variants:
        from trim_t07_zero_tails import transform_source
        for variant in ('tail', 'tail_core'):
            if variant in args.variants:
                sources[variant], transformations[variant] = transform_source(
                    original, clear_unused_cores=(variant == 'tail_core'))
    use_direct = any(variant in args.variants for variant in ('direct', 'direct_core'))
    if use_direct:
        for variant in ('direct', 'direct_core'):
            if variant not in args.variants:
                continue
            base = original
            if variant == 'direct_core':
                from trim_t07_zero_tails import transform_source
                base, core_metadata = transform_source(base, clear_unused_cores=True)
            sources[variant], transformations[variant] = transform_direct(base)
            if variant == 'direct_core':
                transformations[variant]['prior_trimming'] = core_metadata
            sources[variant] = sources[variant].replace(
                '  stepB_sound (by intro j hj;', '  directStepB_sound (by intro j hj;')
        # Equal imports for both sides of the comparison.
        sources = {name: 'import ElevenSquare.Tasks.T07.Ext.DirectTree\n' + text
                   for name, text in sources.items()}
    conditions = list(sources)
    schedule = [(repeat + 1, variant) for repeat in range(args.repeats)
                for variant in (conditions if repeat % 2 == 0 else list(reversed(conditions)))]
    report = {'schema': 1, 'kind': 'bounded-t07-certificate-data-comparison',
              'full_proof_verified': False, 'complete': False,
              'transformations': transformations,
              'source_hashes': {name: common.sha(text.encode()) for name, text in sources.items()},
              'schedule': schedule, 'trials': [], 'summaries': [],
              'limits': {'timeout_seconds': args.timeout, 'total_seconds': args.max_total_seconds,
                         'memory_mib': args.memory_mib, 'min_free_gib': args.min_free_gib},
              'script_sha256': common.sha(Path(__file__).read_bytes()),
              'notes': ['One frozen complete pruning step, not its history or promotion.',
                        'Fresh serial compiler processes; identical imports in each comparison.',
                        'Source bytes include all certificate data; no opaque proof oracle.',
                        'Single repetitions are scouts, not a reproducible speed claim.']}
    if args.plan_only:
        print(json.dumps({key: report[key] for key in ('source_hashes', 'schedule', 'limits')}, indent=2))
        return 0
    report['components'] = common.component_provenance()
    if use_direct:
        report['components'].update(direct_provenance())
    lean, env, report['compiler'] = common.lean_runtime(None)
    lean_args = ['-j1', f'-M{args.memory_mib}', '-s65536', '-DautoImplicit=false', '-DmaxHeartbeats=0']
    report['lean_arguments'] = lean_args
    output = args.output if args.output.is_absolute() else ROOT / args.output
    signal.signal(signal.SIGINT, common.interrupted)
    signal.signal(signal.SIGTERM, common.interrupted)
    start_all = time.monotonic()
    try:
        with tempfile.TemporaryDirectory(prefix='certificate-data-', dir=ROOT / '.verification') as scratch:
            for repeat, variant in schedule:
                if shutil.disk_usage(ROOT).free < args.min_free_gib * 1024**3:
                    report['stop_reason'] = 'free_disk_below_bound'
                    break
                remaining = args.max_total_seconds - (time.monotonic() - start_all)
                if remaining <= 0:
                    report['stop_reason'] = 'total_time_bound'
                    break
                path = Path(scratch) / 'Trial.lean'
                path.write_text(sources[variant])
                before = resource.getrusage(resource.RUSAGE_CHILDREN)
                start = time.monotonic()
                common._current = subprocess.Popen([lean, *lean_args, str(path)], cwd=ROOT,
                    env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                status, diagnostic, code = 'accepted', '', None
                while True:
                    if shutil.disk_usage(ROOT).free < args.min_free_gib * 1024**3:
                        status = 'disk_limit'
                        common.stop_child()
                        break
                    if time.monotonic() - start > min(args.timeout, remaining):
                        status = 'timeout'
                        common.stop_child()
                        break
                    try:
                        diagnostic, _ = common._current.communicate(timeout=1)
                        code = common._current.returncode
                        common._current = None
                        if code != 0:
                            status = 'failed'
                        break
                    except subprocess.TimeoutExpired:
                        pass
                after = resource.getrusage(resource.RUSAGE_CHILDREN)
                trial = {'repeat': repeat, 'case': 'P2/S135', 'variant': variant,
                         'value': 'data', 'status': status, 'returncode': code,
                         'wall_seconds': time.monotonic() - start,
                         'cpu_seconds': after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime,
                         'diagnostic_tail': diagnostic[-4000:]}
                report['trials'].append(trial)
                common.write_report(output, report)
                print(json.dumps(trial), flush=True)
                if status != 'accepted':
                    report['stop_reason'] = status
                    break
            else:
                report['complete'] = True
    except KeyboardInterrupt:
        report['stop_reason'] = 'interrupted'
    finally:
        common.stop_child()
        report['summaries'] = common.summarize(report['trials'], args.repeats)
        common.write_report(output, report)
    return 0 if report['complete'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
