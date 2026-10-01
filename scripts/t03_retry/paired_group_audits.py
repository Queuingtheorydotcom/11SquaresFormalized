"""Batch unchanged ready modules through the original multi-target checker.

This module creates no compiler receipt or synthetic individual execution.
Every accepted group is bound to the real batch CHECK/log and its own genuine
source/object receipt. Failed batches fall back to ordinary individual jobs.
"""
from pathlib import Path
import datetime, hashlib, json, re, shutil, zipfile
from retry_paths import metadata_path

class PairedGroupAudits:
    def __init__(self, *, evidence, kit, case, destination, rows, graph, keys,
                 manifest, read_module, read_member, full_task, extras,
                 publication_sha256, valid, event, enabled, transport_root, max_workers=1):
        self.E, self.K, self.case, self.destination = evidence, kit, case, destination
        self.rows = {r['module']:r for r in rows}
        self.index = {m:i for i,m in enumerate(sorted(self.rows))}
        self.graph, self.keys, self.manifest = graph, keys, manifest
        self.read_module, self.read_member = read_module, read_member
        self.full_task, self.extras = full_task, extras
        self.publication_sha256, self.valid, self.event = publication_sha256, valid, event
        self.enabled = enabled
        self.transport_root=Path(transport_root).resolve();self.max_workers=max_workers
        assert self.transport_root.is_dir() and 1<=max_workers<=6
        if enabled:
            probe = json.loads((self.E / 'multi-target-audit-probe-result-20261001.json').read_bytes())
            assert probe['measured_fixture_gain'] and probe['target_union_exactly_preserved']
            assert probe['all_actual_axiom_targets_audited'] and probe['source_bytes_and_numeric_data_unchanged']
        self.path = self.E / f'case{case}-paired-group-audit-bindings.json'
        self.queue = self.E / f'library-case{case}-node994-queue.json'
        self.marker = self.E / f'.paired-group-publication-case{case}.json'
        assert not self.marker.exists(), 'Inspect an interrupted publication before resuming.'
        self.jobs = json.loads(self.path.read_bytes())['jobs'] if self.path.exists() else []
        if self.path.exists(): assert json.loads(self.path.read_bytes())['case'] == case
        self.failed_modules = set()
        self.proof_cache = {}
        for job in self.jobs:
            assert len(job['modules']) == len(set(job['modules'])) == 2
            assert set(job['modules']) <= self.rows.keys()
            assert job['task'].startswith(f'library-case{case}-node994-pair-')
            task_raw = (self.E / job['task']).read_bytes()
            assert hashlib.sha256(task_raw).hexdigest() == job['task_sha256']
            task = json.loads(task_raw)
            assert task['modules'] == job['modules'] and task['axiom_targets'] == job['axiom_targets']
        if self.jobs: self.save_queue()

    @staticmethod
    def sha(path):
        digest = hashlib.sha256()
        with path.open('rb') as source:
            while block := source.read(1024 * 1024): digest.update(block)
        return digest.hexdigest()

    @staticmethod
    def atomic(path, payload):
        temp = path.with_suffix('.writing.json')
        temp.write_text(json.dumps(payload, indent=2) + '\n')
        temp.replace(path)

    def save(self):
        self.atomic(self.path, dict(status='ACTUAL_MULTI_TARGET_AUDITS_REQUIRED_FOR_EACH_GROUP',
                                   case=self.case, jobs=self.jobs,
                                   proof_sources_changed=False, synthetic_receipts_created=0,
                                   maximum_global_compiler_checks=self.max_workers))

    def save_queue(self):
        self.atomic(self.queue, dict(status='EXACT_SOURCE_PAIRED_GROUPS_AWAITING_ORIGINAL_CHECKER',
                                    tasks=[dict(task=j['task'], modules=j['modules'],
                                                axiom_targets=j['axiom_targets'],
                                                remaining_dependency_path_groups=j['remaining_dependency_path_groups'])
                                           for j in self.jobs]))

    def paths(self, job):
        name = '.t03-runtime-sync-' + Path(job['task']).stem + '.zip'
        return self.transport_root / name, self.destination / name

    def execution(self, job):
        if job['task'] in self.proof_cache: return self.proof_cache[job['task']]
        for prefix in ['primary','independent','helper','auxiliary','extra-a','extra-b','extra-c','extra-d','extra-e','extra-f','library-a','library-b','library-c','library-d','library-e','library-f']:
            wrapper = self.E / (prefix + '-' + Path(job['task']).stem + '.log')
            receipt = wrapper.with_suffix('.json')
            if not receipt.exists(): continue
            data = json.loads(receipt.read_bytes())
            assert data['task'] == job['task'] and data['transport_sha256'] == job['transport_sha256']
            if data['exit_code'] != 0:
                result = dict(status='failed', actual_execution=receipt.name,
                              execution_sha256=self.sha(receipt), exit_code=data['exit_code'])
                self.proof_cache[job['task']] = result
                return result
            text = wrapper.read_text(encoding='utf8')
            assert text.rstrip().endswith('PASS: target declarations have clean transitive axiom audits.')
            paths = re.findall(r'^Log: (\S+/handoff-HandoffAudit-\S+/lean\.log)$', text, re.M)
            assert len(paths) == 1
            value = paths[0]
            log = metadata_path(value)
            raw = log.read_bytes(); check_raw = log.with_name('CHECK.json').read_bytes()
            check = json.loads(check_raw)
            assert check['status'] == 'accepted' and check['exit_code'] == 0
            found = {n:[x.strip() for x in axes.split(',') if x.strip()] for n,axes in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", raw.decode(), re.S)}
            found.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms", raw.decode())})
            assert set(found) == set(job['axiom_targets'])
            assert all(set(v) <= {'propext','Classical.choice','Quot.sound'} for v in found.values())
            result = dict(status='accepted', actual_execution=receipt.name,
                          execution_sha256=self.sha(receipt), actual_audit=str(log),
                          actual_audit_sha256=hashlib.sha256(raw).hexdigest(),
                          actual_CHECK_sha256=hashlib.sha256(check_raw).hexdigest(),
                          audit_seconds=check['elapsed_seconds'], target_axioms=found)
            self.proof_cache[job['task']] = result
            return result
        return None

    def preserve(self, job):
        source, backup = self.paths(job)
        if backup.exists():
            assert self.sha(backup) == job['transport_sha256']
        else:
            assert source.exists() and self.sha(source) == job['transport_sha256']
            temporary = backup.with_suffix('.preserving.zip')
            assert not temporary.exists()
            shutil.copyfile(source, temporary)
            assert self.sha(temporary) == job['transport_sha256']
            assert temporary.resolve().parent == backup.resolve().parent == self.destination.resolve()
            temporary.replace(backup)
        if source.exists():
            assert source.resolve().parent == self.transport_root.resolve()
            assert self.sha(source) == job['transport_sha256']
            source.unlink()

    def poll(self, complete, published, preserved):
        for job in self.jobs:
            proof = self.execution(job)
            if proof and proof['status'] == 'failed':
                self.failed_modules.update(job['modules'])
                if job.get('actual_verification',{}).get('status') != 'failed':
                    self.preserve(job)
                    for module in job['modules']:
                        if module not in complete: published.discard(module)
                    job['actual_verification'] = proof
                    self.save()
                    self.event(status='PAIRED_GROUP_JOB_FAILED_ORDINARY_INDIVIDUAL_FALLBACK_ENABLED',
                               task=job['task'], modules=job['modules'], exit_code=proof['exit_code'])
                continue
            assert all(job['source_closure_sha256'][m] == self.keys[m] for m in job['modules']), 'An issued batch source closure changed.'
            published.update(job['modules'])
            if set(job['modules']) <= complete:
                if not set(job['modules']) <= preserved:
                    self.preserve(job); preserved.update(job['modules'])
                continue
            if not proof or not all(self.valid(m, self.keys[m]) for m in job['modules']): continue
            assert all(self.rows[m]['axiom_targets'][0] in proof['target_axioms'] for m in job['modules'])
            job['actual_verification'] = proof
            self.save()
            for module in job['modules']:
                if module in complete: continue
                complete.add(module)
                self.event(status='CHUNK_ACCEPTED_WITH_ACTUAL_TARGET_AUDIT_AND_GENUINE_RECEIPT',
                           module=module, completed=len(complete), total=len(self.rows),
                           verification_mode='ORIGINAL_CHECKER_REAL_MULTI_TARGET_AUDIT',
                           actual_task=job['task'], actual_audit_sha256=proof['actual_audit_sha256'])
            self.preserve(job); preserved.update(job['modules'])

    def eligible(self, first, second):
        return (first['module'] not in self.failed_modules and second['module'] not in self.failed_modules
                and abs(first['remaining_dependency_path_groups']-second['remaining_dependency_path_groups']) <= 1)

    def publish(self, first, second, complete, published):
        chosen = [first, second]
        modules = [r['module'] for r in chosen]
        assert len(set(modules)) == 2 and self.eligible(first, second)
        assert all(m not in published for m in modules)
        assert all(set(r['dependencies']) <= complete for r in chosen)
        numbers = sorted(self.index[m] for m in modules)
        name = f'library-case{self.case}-node994-pair-{numbers[0]:03d}-{numbers[1]:03d}-task.json'
        assert not any(j['task'] == name for j in self.jobs)
        task = dict(self.full_task, modules=modules,
                    axiom_targets=[t for r in chosen for t in r['axiom_targets']])
        assert len(set(task['axiom_targets'])) == 2
        task_raw = (json.dumps(task, indent=2)+'\n').encode()
        target_task = self.E / name
        source = self.transport_root / ('.t03-runtime-sync-' + Path(name).stem + '.zip')
        temporary = self.destination / ('.preparing-' + source.name)
        assert not any(p.exists() for p in [self.marker,target_task,source,temporary])
        self.marker.write_text(json.dumps(dict(case=self.case, task=name, status='EXACT_SOURCE_PUBLICATION_IN_PROGRESS')))
        selected = set()
        def visit(module):
            if module in selected: return
            for dep in self.graph[module]: visit(dep)
            selected.add(module)
        for module in modules: visit(module)
        members = {'project/'+m.replace('.','/')+'.lean' for m in selected} | set(self.extras)
        manifest = {}
        with zipfile.ZipFile(temporary,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=1) as out:
            for member in sorted(members):
                raw = self.read_module(member[8:-5].replace('/','.')) if member.startswith('project/ElevenSquare/') and member.endswith('.lean') else self.read_member(member)
                assert hashlib.sha256(raw).hexdigest() == self.manifest[member]
                manifest[member] = self.manifest[member]; out.writestr(member,raw)
            manifest[name] = hashlib.sha256(task_raw).hexdigest()
            out.writestr(name,task_raw); out.writestr('source-sync-manifest.json',json.dumps(manifest))
        with zipfile.ZipFile(temporary) as z:
            assert set(z.namelist()) == set(manifest) | {'source-sync-manifest.json'}
            assert len(z.namelist()) == len(set(z.namelist()))
            for member, expected in manifest.items(): assert hashlib.sha256(z.read(member)).hexdigest() == expected
        target_task.write_bytes(task_raw)
        staged = source.with_suffix('.preparing.zip'); assert not staged.exists()
        shutil.copyfile(temporary,staged)
        digest = self.sha(temporary)
        assert self.sha(staged) == digest and staged.resolve().parent == self.transport_root.resolve()
        staged.replace(source)
        job = dict(task=name, modules=modules, axiom_targets=task['axiom_targets'],
                   task_sha256=hashlib.sha256(task_raw).hexdigest(), transport_sha256=digest,
                   original_group_tasks={r['module']:r['task'] for r in chosen},
                   source_closure_sha256={m:self.keys[m] for m in modules},
                   prepared_from_master_sha256=self.publication_sha256,
                   remaining_dependency_path_groups=max(r['remaining_dependency_path_groups'] for r in chosen),
                   source_members=len(members), proof_sources_changed=False)
        self.jobs.append(job); self.save(); self.save_queue()
        assert temporary.resolve().parent == self.destination.resolve()
        temporary.unlink()
        assert self.marker.resolve().parent == self.E.resolve()
        self.marker.unlink()
        published.update(modules)
        self.event(status='READY_PAIRED_GROUP_TRANSPORT_PUBLISHED_ALL_TARGET_AUDITS_PENDING',
                   task=name, modules=modules, source_members=len(members), bytes=source.stat().st_size)
