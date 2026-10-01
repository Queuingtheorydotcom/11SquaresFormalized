"""Inspect all three actual supplied-checker outputs before deciding on batching."""
from pathlib import Path
import argparse,datetime, hashlib, json, re, zipfile

ap=argparse.ArgumentParser();ap.add_argument('--kit',required=True);ap.add_argument('--transport-dir');ap.add_argument('--output',default='multi-target-audit-probe-result-20261001.json');ap.add_argument('--max-workers',type=int,default=1)
a=ap.parse_args()
from retry_paths import kit_paths,low_priority_single_core,metadata_path
K,E,transport_root=kit_paths(a.kit,a.transport_dir);assert Path(a.output).name==a.output and a.output.endswith('.json') and 1<=a.max_workers<=6
low_priority_single_core()
record = E / a.output
assert not record.exists()
names = {
    'combined': 'library-case2069-node995-two-target-audit-probe-task.json',
    'first': 'library-case2069-node995-one-target-first-audit-probe-task.json',
    'second': 'library-case2069-node995-one-target-second-audit-probe-task.json',
}
observations = {}; source_manifest = None; configuration = None
for variant, task_name in names.items():
    task = json.loads((E / task_name).read_bytes())
    matches = []
    for prefix in ['primary','independent','helper','extra-a','library-b','library-c']:
        wrapper_path = E / (prefix + '-' + Path(task_name).stem + '.log')
        execution_path = wrapper_path.with_suffix('.json')
        if not execution_path.exists(): continue
        execution = json.loads(execution_path.read_bytes())
        if execution['exit_code'] != 0: continue
        wrapper_raw = wrapper_path.read_bytes(); wrapper = wrapper_raw.decode()
        assert wrapper.rstrip().endswith('PASS: target declarations have clean transitive axiom audits.')
        paths = re.findall(r'^Log: (\S+/handoff-HandoffAudit-\S+/lean\.log)$', wrapper, re.M)
        assert len(paths) == 1
        path = metadata_path(paths[0])
        audit_raw = path.read_bytes(); check_raw = path.with_name('CHECK.json').read_bytes(); check = json.loads(check_raw)
        assert check['status'] == 'accepted' and check['exit_code'] == 0
        found = {n:[x.strip() for x in axes.split(',') if x.strip()] for n,axes in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit_raw.decode(), re.S)}
        found.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms", audit_raw.decode())})
        assert set(found) == set(task['axiom_targets'])
        assert all(set(v) <= {'propext','Classical.choice','Quot.sound'} for v in found.values())
        settings = {k: execution['configuration'][k] for k in ['lean_threads','lean_memory_mb','runtime_compiler_sha256','runtime_lean_environment']}
        if configuration is None: configuration = settings
        else: assert settings == configuration
        matches.append(dict(task=task_name, worker=prefix, audit_seconds=check['elapsed_seconds'],
                            actual_audit=str(path), audit_log_sha256=hashlib.sha256(audit_raw).hexdigest(),
                            actual_CHECK_sha256=hashlib.sha256(check_raw).hexdigest(), targets=found,
                            transport_sha256=execution['transport_sha256'],
                            execution_sha256=hashlib.sha256(execution_path.read_bytes()).hexdigest()))
    assert len(matches) == 1, task_name
    observations[variant] = matches[0]
    archive = transport_root / ('.t03-runtime-sync-' + Path(task_name).stem + '.zip')
    digest = hashlib.sha256()
    with archive.open('rb') as source:
        while block := source.read(1024 * 1024): digest.update(block)
    assert digest.hexdigest() == matches[0]['transport_sha256']
    with zipfile.ZipFile(archive) as z:
        manifest = json.loads(z.read('source-sync-manifest.json'))
        selected = {n:h for n,h in manifest.items() if n == 'TASK.json' or n.startswith('project/')}
        for name, expected in selected.items(): assert hashlib.sha256(z.read(name)).hexdigest() == expected
        if source_manifest is None: source_manifest = selected
        else: assert selected == source_manifest
combined_targets = observations['combined']['targets']
assert combined_targets == (observations['first']['targets'] | observations['second']['targets'])
separate = observations['first']['audit_seconds'] + observations['second']['audit_seconds']
combined = observations['combined']['audit_seconds']
payload = dict(status='ALL_REAL_TARGET_AUDITS_ACCEPTED_IDENTICAL_SOURCE_FIXTURE',
               utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), observations=observations,
               separate_audit_seconds_sum=separate, combined_audit_seconds=combined,
               observed_audit_seconds_saved=separate-combined,
               measured_fixture_gain=combined < separate,
               timing_scope='Three sequential actual checks under the background six-slot pool; this observation does not establish a general compiler speedup.',
               source_manifest_sha256=hashlib.sha256(json.dumps(source_manifest, sort_keys=True).encode()).hexdigest(),
               source_members=len(source_manifest), source_bytes_and_numeric_data_unchanged=True,
               target_union_exactly_preserved=True, all_actual_axiom_targets_audited=True,
               maximum_global_compiler_checks=a.max_workers, full_case_acceptances=0,
               complete_case_and_original_public_target_audits_still_required=True)
record.write_text(json.dumps(payload, indent=2) + '\n')
print(json.dumps(payload), flush=True)
