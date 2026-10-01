#!/usr/bin/env python3
"""Serial source-based check of a handoff's dependency closure and target axioms.
Use --plan without invoking Lean. Requires pinned mathlib dependency objects.
Resumes only from source/dependency AND object hashes produced by this script.
"""
import argparse,hashlib,json,re,subprocess,sys,signal
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
ap=argparse.ArgumentParser();ap.add_argument('--task',type=Path,default=ROOT.parent/'TASK.json');ap.add_argument('--plan',action='store_true');a=ap.parse_args()
task=json.loads(a.task.read_text());order=[];seen=set();keys={}
def visit(name):
 if name in seen:return
 p=ROOT/Path(*name.split('.')).with_suffix('.lean')
 if not p.exists():raise SystemExit('Missing source: '+str(p))
 seen.add(name);deps=[]
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split('--')[0].split():
    if dep=='ElevenSquare' or dep.startswith('ElevenSquare.'):
     visit(dep);deps.append(keys[dep])
 keys[name]=hashlib.sha256(p.read_bytes()+''.join(deps).encode()+(ROOT/'lake-manifest.json').read_bytes()+(ROOT/'lean-toolchain').read_bytes()).hexdigest();order.append((name,p))
for name in task['modules']:visit(name)
if a.plan:
 print(json.dumps({'task':task['id'],'modules_in_serial_order':[n for n,p in order],'axiom_targets':task['axiom_targets'],'open_deliverables':task.get('open_deliverables',[])},indent=2));raise SystemExit(0)
cache=ROOT/'verification/handoff-cache';cache.mkdir(parents=True,exist_ok=True);proc=None

def stop(signum,frame):raise KeyboardInterrupt
signal.signal(signal.SIGTERM,stop)
def check(p,emit):
 global proc
 cmd=[sys.executable,str(ROOT/'scripts/lean_small_check.py'),str(p),'handoff-'+p.stem]+(['--emit-olean'] if emit else [])
 proc=subprocess.Popen(cmd,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 text,_=proc.communicate();rc=proc.returncode;proc=None;print(text,flush=True)
 if rc:raise RuntimeError('Bounded check failed; split the module or inspect its log.')
 logs=re.findall(r'^Log: (.+)$',text,re.M)
 if logs:
  full=Path(logs[-1]).resolve()
  assert full.is_relative_to(ROOT/'verification'), 'Unexpected checker log path'
  return full.read_text()
 return text
try:
 for name,p in order:
  obj=ROOT/'.lake/build/lib'/p.relative_to(ROOT).with_suffix('.olean');receipt=cache/(name+'.json')
  old=json.loads(receipt.read_text()) if receipt.exists() else {}
  if old.get('source_closure_sha256')==keys[name] and obj.exists() and hashlib.sha256(obj.read_bytes()).hexdigest()==old.get('object_sha256'):continue
  check(p,True);receipt.write_text(json.dumps({'source_closure_sha256':keys[name],'object_sha256':hashlib.sha256(obj.read_bytes()).hexdigest()})+'\n')
 audit=ROOT/'verification/HandoffAudit.lean'
 audit.write_text('\n'.join('import '+m for m in task['modules'])+'\n'+'\n'.join('#print axioms '+t for t in task['axiom_targets'])+'\n')
 text=check(audit,False)
 found={n:[x.strip() for x in v.split(',') if x.strip()] for n,v in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text,re.S)}
 for n in re.findall(r"'([^']+)' does not depend on any axioms",text):found[n]=[]
 expected=set(task['axiom_targets']);assert expected and expected<=found.keys(),'Missing target audits'
 assert all(set(found[n])<={'propext','Classical.choice','Quot.sound'} for n in expected),'Unproved or nonstandard axiom in target'
 if task.get('open_deliverables'):raise RuntimeError('Helper checks passed, but task still has open deliverables: '+repr(task['open_deliverables']))
 print('PASS: target declarations have clean transitive axiom audits.')
except KeyboardInterrupt:
 if proc:
  proc.terminate()
  try:proc.wait(timeout=5)
  except subprocess.TimeoutExpired:pass
 raise SystemExit(130)
except Exception as e:raise SystemExit(str(e))
