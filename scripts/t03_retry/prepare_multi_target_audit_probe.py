"""Queue one real two-target audit of two already accepted, unchanged groups."""
from pathlib import Path
import argparse, ctypes, datetime, hashlib, json, os, re, zipfile

case = 2069
ap = argparse.ArgumentParser()
ap.add_argument('--variant', choices=['combined', 'first', 'second'], default='combined')
ap.add_argument('--kit',required=True);ap.add_argument('--transport-dir');ap.add_argument('--scratch-root',type=Path,required=True);ap.add_argument('--max-workers',type=int,default=1)
a=ap.parse_args();variant=a.variant
from retry_paths import kit_paths,low_priority_single_core,metadata_path
K,E,transport_root=kit_paths(a.kit,a.transport_dir);scratch=a.scratch_root.resolve();assert scratch.is_dir() and 1<=a.max_workers<=6
low_priority_single_core()
name = ('library-case2069-node995-two-target-audit-probe-task.json' if variant == 'combined'
        else f'library-case2069-node995-one-target-{variant}-audit-probe-task.json')
record = E / ('multi-target-audit-probe-preparation-20261001.json' if variant == 'combined'
              else f'multi-target-audit-probe-{variant}-preparation-20261001.json')
queue = E / 'library-case2069-node995-queue.json'
target = transport_root / ('.t03-runtime-sync-' + Path(name).stem + '.zip')
assert not any(p.exists() for p in [record, E / name, target])
previous_rows = []
if variant == 'combined': assert not queue.exists()
else:
    previous_queue = json.loads(queue.read_bytes())
    assert previous_queue['status'] == 'BOUNDED_REAL_TWO_TARGET_AUDIT_PROBE_ONLY'
    previous_rows = previous_queue['tasks']
    prerequisite = ('library-case2069-node995-two-target-audit-probe-task.json' if variant == 'first'
                    else 'library-case2069-node995-one-target-first-audit-probe-task.json')
    assert any(r['task'] == prerequisite for r in previous_rows)
    assert not any(r['task'] == name for r in previous_rows)
    matches = []
    for prefix in ['primary','independent','helper','extra-a','library-b','library-c']:
        wrapper = E / (prefix + '-' + Path(prerequisite).stem + '.log')
        execution_path = wrapper.with_suffix('.json')
        if not execution_path.exists(): continue
        execution = json.loads(execution_path.read_bytes())
        if execution['exit_code'] == 0:
            assert wrapper.read_text().rstrip().endswith('PASS: target declarations have clean transitive axiom audits.')
            matches.append(execution_path)
    assert len(matches) == 1, 'Prior real audit must finish successfully before the next sequential comparison.'
def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as source:
        while block := source.read(1024 * 1024): digest.update(block)
    return digest.hexdigest()

def win(value):return metadata_path(value)

contents = {}; baselines = []; modules = []; targets = []; base_task = None
for number in [0, 1]:
    original_name = f'library-case2069-node998-{number:03d}-task.json'
    original_task_raw = (E / original_name).read_bytes()
    original_task = json.loads(original_task_raw)
    assert len(original_task['modules']) == len(original_task['axiom_targets']) == 1
    if base_task is None: base_task = original_task
    else:
        assert {k:v for k,v in base_task.items() if k not in ['modules','axiom_targets']} == {k:v for k,v in original_task.items() if k not in ['modules','axiom_targets']}
    accepted = None
    for prefix in ['primary','independent','helper','extra-a','library-b','library-c']:
        wrapper = E / (prefix + '-' + Path(original_name).stem + '.log')
        execution_path = wrapper.with_suffix('.json')
        if not execution_path.exists(): continue
        execution = json.loads(execution_path.read_bytes())
        if execution['exit_code'] != 0: continue
        text = wrapper.read_text(encoding='utf8')
        assert text.rstrip().endswith('PASS: target declarations have clean transitive axiom audits.')
        paths = re.findall(r'^Log: (\S+/handoff-HandoffAudit-\S+/lean\.log)$', text, re.M)
        assert len(paths) == 1
        actual = win(paths[0]); check_raw = actual.with_name('CHECK.json').read_bytes()
        check = json.loads(check_raw); audit_raw = actual.read_bytes()
        assert check['status'] == 'accepted' and check['exit_code'] == 0
        found = {n:[x.strip() for x in axes.split(',') if x.strip()] for n,axes in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit_raw.decode(), re.S)}
        found.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms", audit_raw.decode())})
        assert set(found) == set(original_task['axiom_targets'])
        assert all(set(v) <= {'propext','Classical.choice','Quot.sound'} for v in found.values())
        accepted = dict(task=original_name, transport_sha256=execution['transport_sha256'],
                        audit_seconds=check['elapsed_seconds'], actual_audit=str(actual),
                        actual_audit_sha256=hashlib.sha256(audit_raw).hexdigest(),
                        actual_CHECK_sha256=hashlib.sha256(check_raw).hexdigest(), targets=found)
        break
    assert accepted, original_name
    archive = scratch/'case2069-parallel-packed-transports' / ('.t03-runtime-sync-' + Path(original_name).stem + '.zip')
    assert sha(archive) == accepted['transport_sha256']
    with zipfile.ZipFile(archive) as z:
        manifest = json.loads(z.read('source-sync-manifest.json'))
        assert z.read(original_name) == original_task_raw
        for member, expected in manifest.items():
            raw = z.read(member)
            assert hashlib.sha256(raw).hexdigest() == expected
            if member == original_name: continue
            assert member == 'TASK.json' or member.startswith('project/')
            assert not member.endswith(('.olean','.ilean')) and '/.lake/' not in member
            if member in contents: assert contents[member] == raw, member
            else: contents[member] = raw
    modules.extend(original_task['modules']); targets.extend(original_task['axiom_targets']); baselines.append(accepted)
task = dict(base_task, modules=list(dict.fromkeys(modules)), axiom_targets=list(dict.fromkeys(targets)))
assert len(task['modules']) == len(task['axiom_targets']) == 2
if variant != 'combined':
    number = 0 if variant == 'first' else 1
    task['modules'] = [task['modules'][number]]
    task['axiom_targets'] = [task['axiom_targets'][number]]
task_raw = (json.dumps(task, indent=2) + '\n').encode()
contents[name] = task_raw
manifest = {n:hashlib.sha256(raw).hexdigest() for n,raw in contents.items()}
staged = target.with_suffix('.preparing.zip'); assert not staged.exists()
with zipfile.ZipFile(staged, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=1) as out:
    for member, raw in sorted(contents.items()): out.writestr(member, raw)
    out.writestr('source-sync-manifest.json', json.dumps(manifest))
with zipfile.ZipFile(staged) as z:
    assert set(z.namelist()) == set(contents) | {'source-sync-manifest.json'}
    assert len(z.namelist()) == len(set(z.namelist()))
    for member, expected in manifest.items(): assert hashlib.sha256(z.read(member)).hexdigest() == expected
(E / name).write_bytes(task_raw)
assert staged.resolve().parent == target.resolve().parent == transport_root.resolve()
staged.replace(target)
queue_tmp = queue.with_suffix('.writing.json')
queue_tmp.write_text(json.dumps(dict(status='BOUNDED_REAL_TWO_TARGET_AUDIT_PROBE_ONLY', tasks=previous_rows+[dict(task=name, multi_target_audit_probe=True)]), indent=2) + '\n')
queue_tmp.replace(queue)
payload = dict(status='TWO_ALREADY_CHECKED_GROUPS_REAL_TARGET_AUDIT_PROBE_QUEUED_NOT_CASE_EVIDENCE',
               utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), task=name, variant=variant,
               transport_sha256=sha(target), modules=task['modules'], axiom_targets=task['axiom_targets'],
               baseline_actual_target_audits=baselines,
               separate_audits_seconds_sum=sum(r['audit_seconds'] for r in baselines),
               sources_changed=[], all_source_environment_and_checker_bytes_unchanged=True,
               maximum_global_compiler_checks=a.max_workers, acceptance_count_changed=False,
               original_case_and_final_public_target_audits_still_required=True)
record.write_text(json.dumps(payload, indent=2) + '\n')
print(json.dumps(payload), flush=True)
