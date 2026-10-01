"""Publish at most eight ready private chunk transports; keep Lean concurrency unchanged.

Actual supplied-checker PASS and genuine source/object receipts are both required
before releasing the full exact case task. Completed transports are preserved in the selected scratch directory,
keeping the live transport footprint bounded.
"""
from pathlib import Path
import argparse,collections,ctypes,datetime,functools,hashlib,json,os,re,shutil,time,zipfile
from retry_paths import kit_paths, low_priority_single_core
from zip_raw_copy import RawZipCopyUnsupported, copy_member_raw
ap=argparse.ArgumentParser();ap.add_argument('--resume',action='store_true')
ap.add_argument('--case',type=int,required=True);ap.add_argument('--publication');ap.add_argument('--preparation')
ap.add_argument('--kit',required=True);ap.add_argument('--transport-dir')
ap.add_argument('--scratch-root',required=True);ap.add_argument('--receipt-root',required=True)
ap.add_argument('--object-root',required=True);ap.add_argument('--max-workers',type=int,default=1)
ap.add_argument('--max-live-archives', '--max-live',type=int)
ap.add_argument('--raw-copy-transports',action='store_true')
args=ap.parse_args();case=args.case
K,E,transport_root=kit_paths(args.kit,args.transport_dir)
assert 1<=args.max_workers<=6
assert case in {r['case'] for r in json.loads((E/'forward-workload-inventory.json').read_text())['records']}
low_priority_single_core()
record=E/f'case{case}-parallel-packed-status.json'
previous=json.loads(record.read_text()) if args.resume else None
if args.max_live_archives is None:
 args.max_live_archives=previous.get('maximum_live_chunk_archives',8) if previous else 8
assert 1<=args.max_live_archives<=8
assert args.resume or not record.exists()
if previous:assert previous['case']==case
preparation_name=args.preparation or f'case{case}-packed-namespaced-publication.json'
assert Path(preparation_name).name==preparation_name and preparation_name.endswith('.json')
prep=json.loads((E/preparation_name).read_text())
publication_name=args.publication or f'case{case}-packed-canonical-publication.json'
assert Path(publication_name).name==publication_name and publication_name.endswith('.json')
publication=json.loads((E/publication_name).read_text())
assert publication['full_case_guard_retained_for_parallel_dependency_audits']
guard=E/f'.collision-bool-preparing-case{case}.json';assert guard.exists()
master=transport_root/('.t03-runtime-sync-'+Path(prep['task']).stem+'.zip')
scratch=Path(args.scratch_root).resolve();assert scratch.is_dir()
destination=scratch/f'case{case}-parallel-packed-transports'
assert destination.is_dir() if args.resume else not destination.exists()
if not args.resume:destination.mkdir()
receipt_root=Path(args.receipt_root).resolve();assert receipt_root.is_dir()
object_root=Path(args.object_root).resolve();assert object_root.is_dir()
prefixes=['primary','independent','helper','auxiliary','extra-a','extra-b','extra-c','extra-d','extra-e','extra-f','library-a','library-b','library-c','library-d','library-e','library-f']
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  while block:=f.read(1024*1024):h.update(block)
 return h.hexdigest()
assert sha(master)==publication['grouped_archive_sha256']
if previous and previous['source_archive_sha256']!=publication['grouped_archive_sha256']:
 transition=json.loads((E/publication.get('kernel_equality_refl_transition',f'case{case}-equality-refl-publication.json')).read_text())
 assert transition['status'] in ['UNPUBLISHED_GROUP_EQUALITY_PROOFS_CANONICALLY_PUBLISHED','FAILED_AND_UNPUBLISHED_GROUP_EQUALITY_PROOFS_CANONICALLY_PUBLISHED']
 assert previous['source_archive_sha256']==transition['previous_grouped_archive_sha256']
 assert publication['grouped_archive_sha256']==transition['new_grouped_archive_sha256']
 assert transition.get('published_and_running_group_source_closures_unchanged',False) or transition.get('all_unaffected_published_and_running_group_source_closures_unchanged',False)
task_aliases={}
transition_path=E/publication.get('kernel_equality_refl_transition',f'case{case}-equality-refl-publication.json')
if transition_path.exists():
 task_aliases=json.loads(transition_path.read_text()).get('group_task_aliases',{})
events=previous['events'] if previous else []
def event(**row):
 row['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();events.append(row)
 payload=dict(case=case,events=events[-1000:],maximum_live_chunk_archives=args.max_live_archives,maximum_parallel_lean_checks=args.max_workers,
              source_archive_sha256=publication['grouped_archive_sha256'],source_archive=str(master),
              destination=str(destination),full_case_guard=str(guard),full_case_and_final_audits_pending=True,
              raw_copy_transports=args.raw_copy_transports,
              scheduling='READY_GROUPS_WITH_LONGEST_REMAINING_DEPENDENCY_PATH_FIRST')
 temp=record.with_suffix('.writing.json');temp.write_text(json.dumps(payload,indent=2)+'\n');temp.replace(record)
 print(json.dumps(row),flush=True)
def last_declaration(raw):
 ns='';stack=[];last=None
 for line in raw.decode().splitlines():
  if m:=re.fullmatch(r'namespace ([A-Za-z_][A-Za-z_0-9.]*)',line):stack.append(('namespace',ns));ns=ns+'.'+m[1] if ns else m[1]
  elif re.match(r'^(?:noncomputable )?section\b',line):stack.append(('section',ns))
  elif re.match(r'^end(?:\s|$)',line):
   kind,previous=stack.pop()
   if kind=='namespace':ns=previous
  elif m:=re.match(r'^(?:noncomputable )?(?:theorem|def)\s+([A-Za-z_][A-Za-z_0-9]*)\b',line):last=ns+'.'+m[1]
 assert last and not stack
 return last
object_cache={}
def valid(module,key):
 try:
  receipt=json.loads((receipt_root/(module+'.json')).read_text())
  if receipt.get('source_closure_sha256')!=key:return False
  assert module.startswith('ElevenSquare.Tasks.T03.')
  obj=object_root/Path(*module.removeprefix('ElevenSquare.Tasks.T03.').split('.')).with_suffix('.olean')
  st=obj.stat();fingerprint=(st.st_size,st.st_mtime_ns)
  if obj not in object_cache or object_cache[obj][0]!=fingerprint:object_cache[obj]=(fingerprint,sha(obj))
  return object_cache[obj][1]==receipt.get('object_sha256')
 except (OSError,ValueError):return False
def passed(task):
 for prefix in prefixes:
  log=E/(prefix+'-'+Path(task).stem+'.log');execution=log.with_suffix('.json')
  if not log.exists() or not execution.exists():continue
  with log.open('rb') as f:f.seek(max(0,log.stat().st_size-1200));tail=f.read().decode(errors='replace')
  if tail.rstrip().endswith('PASS: target declarations have clean transitive axiom audits.'):
   data=json.loads(execution.read_text())
   if data['exit_code']==0:return data
 return None
with zipfile.ZipFile(master) as z:
 manifest=json.loads(z.read('source-sync-manifest.json'));environment=z.read('project/lake-manifest.json')+z.read('project/lean-toolchain')
 full_task=json.loads(z.read(prep['task']))
 group_prefix=prep.get('group_module_prefix')
 modules=sorted(n[8:-5].replace('/','.') for n in manifest if n.endswith('.lean') and
     (n[8:-5].replace('/','.').startswith(group_prefix) if group_prefix else '/PackedNamespaced/' in n))
 assert len(modules)==prep['groups']
 @functools.lru_cache(maxsize=32)
 def raw(module):
  name='project/'+module.replace('.','/')+'.lean';data=z.read(name);assert hashlib.sha256(data).hexdigest()==manifest[name];return data
 graph={};keys={};visiting=set()
 def visit(module):
  if module in keys:return keys[module]
  assert module not in visiting;visiting.add(module);data=raw(module);deps=[]
  for line in data.decode().splitlines():
   if line.startswith('import '):deps.extend(m for m in line[7:].split('--')[0].split() if m=='ElevenSquare' or m.startswith('ElevenSquare.'))
  graph[module]=deps;depkeys=[visit(m) for m in deps]
  keys[module]=hashlib.sha256(data+''.join(depkeys).encode()+environment).hexdigest();visiting.remove(module);return keys[module]
 visit(full_task['modules'][0]);assert set(modules)<=set(keys)
 rows=[];module_set=set(modules)
 for i,module in enumerate(modules):
  task_name=task_aliases.get(module,f'library-case{case}-node998-{i:03d}-task.json')
  task=dict(full_task);task['modules']=[module];task['axiom_targets']=[last_declaration(raw(module))]
  target=E/task_name;task_bytes=(json.dumps(task,indent=2)+'\n').encode()
  if args.resume:assert json.loads(target.read_bytes())==task
  else:assert not target.exists();target.write_bytes(task_bytes)
  rows.append(dict(task=task_name,module=module,axiom_targets=task['axiom_targets'],dependencies=[d for d in graph[module] if d in module_set]))
 # Dependency depth alone creates entire waves. Prioritize the longest path
 # remaining above each ready chunk so serial replay work can overlap leaves.
 users={m:[] for m in modules}
 for row in rows:
  for dep in row['dependencies']:users[dep].append(row['module'])
 remaining={}
 for module in reversed(modules):
  assert all(user in remaining for user in users[module])
  remaining[module]=1+max((remaining[user] for user in users[module]),default=0)
 rows.sort(key=lambda r:(-remaining[r['module']],-len(users[r['module']]),r['module']))
 for row in rows:row['remaining_dependency_path_groups']=remaining[row['module']]
 queue=E/f'library-case{case}-node998-queue.json'
 if args.resume:
  old=json.loads(queue.read_text());old_rows={r['task']:r for r in old['tasks']}
  assert len(old_rows)==len(rows)
  for row in rows:assert all(old_rows[row['task']][k]==row[k] for k in ['task','module','axiom_targets','dependencies'])
 else:assert not queue.exists()
 queue_tmp=queue.with_suffix('.writing.json')
 queue_tmp.write_text(json.dumps(dict(status='EXACT_SOURCE_GROUPS_AWAITING_SUPPLIED_CHECKER_AUDITS',tasks=rows,groups=len(rows),
                  scheduling='LONGEST_REMAINING_DEPENDENCY_PATH_FIRST'),indent=2)+'\n');queue_tmp.replace(queue)
 event(status='PARALLEL_PACKED_QUEUE_RESUMED_WITH_CRITICAL_PATH_PRIORITY' if args.resume else 'PARALLEL_PACKED_QUEUE_READY',
       groups=len(rows),independent_frontier=sum(not r['dependencies'] for r in rows),longest_remaining_path_groups=max(remaining.values()))
 extras=['TASK.json']+['project/'+n for n in ['lakefile.lean','lake-manifest.json','lean-toolchain','scripts/lake.sh','scripts/check_handoff.py','scripts/lean_small_check.py','verification/LOW_RESOURCE_MODE.json']]
 published=set();complete=set();preserved=set()
 if args.resume:
  for row in rows:
   module,task_name=row['module'],row['task']
   path=transport_root/('.t03-runtime-sync-'+Path(task_name).stem+'.zip');backup=destination/path.name
   if backup.exists():
    execution=passed(task_name);assert execution and valid(module,keys[module])
    assert sha(backup)==execution['transport_sha256'];complete.add(module);preserved.add(module);published.add(module)
   if path.exists():
    selected=set()
    def prior_closure(m):
     if m in selected:return
     for dep in graph[m]:prior_closure(dep)
     selected.add(m)
    prior_closure(module)
    expected_names={'project/'+m.replace('.','/')+'.lean' for m in selected}|set(extras)|{task_name}
    with zipfile.ZipFile(path) as prior:
     prior_manifest=json.loads(prior.read('source-sync-manifest.json'))
     assert set(prior_manifest)==expected_names and set(prior.namelist())==expected_names|{'source-sync-manifest.json'}
     for name in expected_names:
      expected=hashlib.sha256((E/task_name).read_bytes()).hexdigest() if name==task_name else manifest[name]
      assert prior_manifest[name]==expected==hashlib.sha256(prior.read(name)).hexdigest()
    published.add(module)
    if module in preserved:
     assert path.resolve().parent==transport_root.resolve() and sha(path)==sha(backup);path.unlink()
  event(status='EXACT_ARCHIVES_AND_GENUINE_RECEIPTS_RECOVERED',completed=len(complete),live_archives=len(published-complete),total=len(rows))
 while True:
  for row in rows:
   module,task_name=row['module'],row['task']
   if module in complete:continue
   execution=passed(task_name)
   if execution and valid(module,keys[module]):complete.add(module);event(status='CHUNK_ACCEPTED_WITH_ACTUAL_TARGET_AUDIT_AND_GENUINE_RECEIPT',module=module,completed=len(complete),total=len(rows))
  for row in rows:
   module,task_name=row['module'],row['task']
   if module not in complete or module in preserved:continue
   path=transport_root/('.t03-runtime-sync-'+Path(task_name).stem+'.zip');backup=destination/path.name
   execution=passed(task_name);assert path.resolve().parent==transport_root.resolve() and path.exists() and not backup.exists()
   assert sha(path)==execution['transport_sha256'];shutil.copyfile(path,backup);assert sha(backup)==execution['transport_sha256']
   path.unlink();preserved.add(module)
  if len(complete)==len(rows):
   assert guard.resolve().parent==E.resolve() and guard.name==f'.collision-bool-preparing-case{case}.json'
   guard.unlink();event(status='ALL_PACKED_DEPENDENCY_AUDITS_PASSED_EXACT_FULL_CASE_TASK_RELEASED',groups=len(rows));break
  live=len(published-complete)
  for row in rows:
   module,task_name=row['module'],row['task']
   if live>=args.max_live_archives:break
   if module in published or not set(row['dependencies'])<=complete:continue
   selected=set()
   def closure(m):
    if m in selected:return
    for dep in graph[m]:closure(dep)
    selected.add(m)
   closure(module)
   names={'project/'+m.replace('.','/')+'.lean' for m in selected}|set(extras)
   task_raw=(E/task_name).read_bytes();new_manifest={}
   target=transport_root/('.t03-runtime-sync-'+Path(task_name).stem+'.zip');assert not target.exists()
   temp=destination/('.preparing-'+target.name);assert not temp.exists()
   with zipfile.ZipFile(temp,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=1) as output:
    for name in sorted(names):
     if args.raw_copy_transports:
      try:
       copy_member_raw(z,output,name)
      except RawZipCopyUnsupported:
       data=raw(name[8:-5].replace('/','.')) if name.endswith('.lean') and name.startswith('project/ElevenSquare/') else z.read(name)
       assert hashlib.sha256(data).hexdigest()==manifest[name],name
       output.writestr(name,data)
     else:
      data=raw(name[8:-5].replace('/','.')) if name.endswith('.lean') and name.startswith('project/ElevenSquare/') else z.read(name)
      assert hashlib.sha256(data).hexdigest()==manifest[name],name
      output.writestr(name,data)
     new_manifest[name]=manifest[name]
    new_manifest[task_name]=hashlib.sha256(task_raw).hexdigest();output.writestr(task_name,task_raw)
    output.writestr('source-sync-manifest.json',json.dumps(new_manifest))
   with zipfile.ZipFile(temp) as check:
    assert len(check.namelist())==len(set(check.namelist()))
    for name,expected in new_manifest.items():assert hashlib.sha256(check.read(name)).hexdigest()==expected,name
   staged=target.with_suffix('.preparing.zip');assert not staged.exists();shutil.copyfile(temp,staged);assert sha(staged)==sha(temp);staged.replace(target)
   # Keep only the published archive and its later audited scratch copy.
   assert temp.resolve().parent==destination.resolve();temp.unlink()
   published.add(module);live+=1;event(status='READY_CHUNK_TRANSPORT_PUBLISHED',module=module,source_members=len(names),bytes=target.stat().st_size,live_archives=live)
  time.sleep(20)
