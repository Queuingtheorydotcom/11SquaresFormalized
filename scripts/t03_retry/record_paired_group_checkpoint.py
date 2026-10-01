"""Independently recheck actual paired audits, exact sources and genuine objects."""
from pathlib import Path
import argparse,datetime,functools,hashlib,json,re,zipfile
ap=argparse.ArgumentParser();ap.add_argument('--case',type=int,required=True);ap.add_argument('--kit',required=True);ap.add_argument('--transport-dir');ap.add_argument('--scratch-root',type=Path,required=True);ap.add_argument('--receipt-root',type=Path,required=True);ap.add_argument('--object-root',type=Path,required=True);ap.add_argument('--max-workers',type=int,default=1);ap.add_argument('--output')
a=ap.parse_args()
from retry_paths import kit_paths,low_priority_single_core,metadata_path
K,E,transport_root=kit_paths(a.kit,a.transport_dir);scratch=a.scratch_root.resolve();assert scratch.is_dir() and 1<=a.max_workers<=6
low_priority_single_core()
case=a.case
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024*1024):h.update(b)
 return h.hexdigest()
registry=E/f'case{case}-paired-group-audit-bindings.json'
jobs=json.loads(registry.read_bytes())['jobs']
accepted=[j for j in jobs if j.get('actual_verification',{}).get('status')=='accepted'];assert accepted
pub=json.loads((E/f'case{case}-packed-canonical-publication.json').read_bytes())
prep=json.loads((E/f'case{case}-packed-namespaced-publication.json').read_bytes())
master=transport_root/('.t03-runtime-sync-'+Path(prep['task']).stem+'.zip')
assert sha(master)==pub['grouped_archive_sha256']
receipts=a.receipt_root.resolve();objects=a.object_root.resolve();assert receipts.is_dir() and objects.is_dir();observations=[]
with zipfile.ZipFile(master) as source:
 manifest=json.loads(source.read('source-sync-manifest.json'))
 environment=source.read('project/lake-manifest.json')+source.read('project/lean-toolchain')
 @functools.lru_cache(None)
 def closure(module):
  raw=source.read('project/'+module.replace('.','/')+'.lean');dependencies=[]
  for line in raw.decode().splitlines():
   if line.startswith('import '):dependencies.extend(m for m in line[7:].split('--')[0].split() if m=='ElevenSquare' or m.startswith('ElevenSquare.'))
  return hashlib.sha256(raw+''.join(closure(m) for m in dependencies).encode()+environment).hexdigest()
 for job in accepted:
  task_raw=(E/job['task']).read_bytes();task=json.loads(task_raw)
  assert hashlib.sha256(task_raw).hexdigest()==job['task_sha256']
  assert task['modules']==job['modules'] and task['axiom_targets']==job['axiom_targets']
  proof=job['actual_verification'];execution=E/proof['actual_execution'];actual=json.loads(execution.read_bytes())
  assert sha(execution)==proof['execution_sha256'] and actual['exit_code']==0
  assert actual['task']==job['task'] and actual['transport_sha256']==job['transport_sha256']
  wrapper=execution.with_suffix('.log')
  assert wrapper.read_text(encoding='utf8').rstrip().endswith('PASS: target declarations have clean transitive axiom audits.')
  audit=metadata_path(proof['actual_audit']);check=audit.with_name('CHECK.json');audit_raw=audit.read_bytes()
  assert sha(audit)==proof['actual_audit_sha256'] and sha(check)==proof['actual_CHECK_sha256']
  c=json.loads(check.read_bytes());assert c['exit_code']==0 and c['status']=='accepted'
  targets={n:[x.strip() for x in axes.split(',') if x.strip()] for n,axes in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit_raw.decode(),re.S)}
  targets.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",audit_raw.decode())})
  assert set(targets)==set(task['axiom_targets'])
  assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in targets.values())
  archive=scratch/f'case{case}-parallel-packed-transports'/('.t03-runtime-sync-'+Path(job['task']).stem+'.zip')
  assert sha(archive)==job['transport_sha256']
  with zipfile.ZipFile(archive) as z:
   m=json.loads(z.read('source-sync-manifest.json'))
   assert set(z.namelist())==set(m)|{'source-sync-manifest.json'} and len(z.namelist())==len(set(z.namelist()))
   for name,digest in m.items():
    data=z.read(name);assert hashlib.sha256(data).hexdigest()==digest
    if name==job['task']:assert data==task_raw
    else:assert digest==manifest[name] and data==source.read(name)
  genuine=[]
  for module in job['modules']:
   key=closure(module);assert key==job['source_closure_sha256'][module]
   receipt=receipts/(module+'.json');r=json.loads(receipt.read_bytes())
   obj=objects/Path(*module.removeprefix('ElevenSquare.Tasks.T03.').split('.')).with_suffix('.olean')
   assert r['source_closure_sha256']==key and r['object_sha256']==sha(obj)
   genuine.append(dict(module=module,source_closure_sha256=key,actual_receipt=str(receipt),actual_receipt_sha256=sha(receipt),actual_object_sha256=r['object_sha256']))
  observations.append(dict(task=job['task'],task_sha256=job['task_sha256'],transport_sha256=job['transport_sha256'],
    actual_audit=str(audit),actual_audit_sha256=sha(audit),actual_CHECK_sha256=sha(check),
    actual_execution=execution.name,actual_execution_sha256=sha(execution),actual_target_axioms=targets,genuine_receipts=genuine))
output=a.output or f'case{case}-paired-group-actual-checkpoint-20261001.json'
assert Path(output).name==output and output.endswith('.json')
record=E/output
assert not record.exists()
payload=dict(status='ORIGINAL_CHECKER_MULTI_TARGET_AUDITS_AND_GENUINE_OBJECTS_REVERIFIED',case=case,
 utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),accepted_paired_jobs=len(observations),
 accepted_dependency_groups=2*len(observations),observations=observations,
 source_bytes_and_numeric_data_unchanged=True,synthetic_receipts_created=0,
 source_master_sha256=pub['grouped_archive_sha256'],maximum_global_compiler_checks=a.max_workers,
 full_case_acceptances=0,full_case_and_original_public_target_audits_still_required=True)
record.write_text(json.dumps(payload,indent=2)+'\n');print(json.dumps({k:v for k,v in payload.items() if k!='observations'}),flush=True)
