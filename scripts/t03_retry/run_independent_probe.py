"""Run one explicitly allocated worker's supplied serial Lean checker.

Uses the unchanged supplied checkers in a separate runtime workspace. Paired library tasks retain every original module and axiom target. Shared
dependency objects are reused only through the supplied source/object hash
receipts. The pool dispatcher must exclude duplicate jobs and enforce its limit.
"""
from pathlib import Path,PurePosixPath
import os,zipfile,json,hashlib,sys,shutil,subprocess,argparse
from retry_paths import kit_paths, low_priority_single_core

ap=argparse.ArgumentParser()
ap.add_argument('archive');ap.add_argument('task');ap.add_argument('--worker',default='independent-probe')
ap.add_argument('--kit',required=True);ap.add_argument('--runtime-root',required=True)
ap.add_argument('--transport-dir');ap.add_argument('--scratch-root',required=True)
ap.add_argument('--source-workspace',choices=['scratch','runtime'],default='scratch')
ap.add_argument('--min-free-gib',type=int,default=20);ap.add_argument('--max-workers',type=int,default=1)
args=ap.parse_args()
assert sys.platform=='linux','Worker locks and checker launch require Linux'
import fcntl
K,_,transport_root=kit_paths(args.kit,args.transport_dir)
base=Path(args.runtime_root).resolve();assert base.is_dir()
worker=args.worker;archive_name,task_name=args.archive,args.task
assert worker in ['independent-probe','helper-probe','auxiliary-probe','primary','library-a','library-b','library-c','library-d','library-e','library-f','coarse-pilot','extra-a','extra-b','extra-c','extra-d','extra-e','extra-f']
assert Path(archive_name).name==archive_name and archive_name.startswith('.t03-runtime-sync-')
assert Path(task_name).name==task_name and task_name.endswith('.json')
assert 1<=args.max_workers<=6 and args.min_free_gib>=1
os.environ['T03_MAX_WORKERS']=str(args.max_workers)
low_priority_single_core()
main=base/'project';slot=base if worker=='primary' else base/worker
slot.mkdir(parents=True,exist_ok=True)
lock=(slot/'probe.lock').open('w');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
# The per-worker lock excludes another checker from this disposable source workspace.
scratch=Path(args.scratch_root).resolve();assert scratch.is_dir()
use_scratch=args.source_workspace=='scratch'
runtime=(scratch/'grouped-source-runtimes'/worker) if use_scratch else slot
if use_scratch:
    assert runtime.resolve().is_relative_to(scratch)
    assert shutil.disk_usage(scratch).free>args.min_free_gib*1024**3
runtime.mkdir(parents=True,exist_ok=True);project=runtime/'project'
assert project.resolve()!=(K/'eleven-square-lean').resolve()
with (transport_root/archive_name).open('rb') as transport_file, zipfile.ZipFile(transport_file) as z:
    # Keep the exact opened archive and its hash, without retaining the whole
    # compressed archive while Lean checks a potentially much larger closure.
    transport_stat=os.fstat(transport_file.fileno())
    transport_digest=hashlib.sha256()
    transport_file.seek(0)
    while block:=transport_file.read(1024*1024):transport_digest.update(block)
    manifest=json.loads(z.read('source-sync-manifest.json'))
    # Keep runtime source copies bounded as the full batch progresses. Only
    # remove an obsolete extracted Lean file when its bytes still match our
    # previous saved transport manifest. Source originals and archives remain.
    # The per-worker lock guarantees no checker still uses this workspace.
    copy_inventory=runtime/'last-extracted-source-manifest.json'
    if copy_inventory.exists():
        previous=json.loads(copy_inventory.read_text())
        source_root=(project/'ElevenSquare').resolve()
        for name,expected in previous.items():
            if name in manifest or not (name.startswith('project/ElevenSquare/') and name.endswith('.lean')):continue
            path=runtime/name
            assert path.resolve().is_relative_to(source_root),('Unexpected runtime source path',str(path))
            if path.is_file() and not path.is_symlink() and hashlib.sha256(path.read_bytes()).hexdigest()==expected:
                path.unlink()
    for name,sha in manifest.items():
        rel=PurePosixPath(name);assert not rel.is_absolute() and '..' not in rel.parts
        assert rel.parts[0]=='project' or len(rel.parts)==1
        content=z.read(name);assert hashlib.sha256(content).hexdigest()==sha
        path=runtime/str(rel);path.parent.mkdir(parents=True,exist_ok=True)
        if not path.exists() or path.read_bytes()!=content:path.write_bytes(content)
        assert path.read_bytes()==content
    saved_inventory=copy_inventory.with_suffix('.writing.json')
    saved_inventory.write_text(json.dumps(manifest)+'\n');saved_inventory.replace(copy_inventory)
    transport_after=os.fstat(transport_file.fileno())
    assert (transport_after.st_size,transport_after.st_mtime_ns)==(transport_stat.st_size,transport_stat.st_mtime_ns),'Transport changed while reading'
lake=project/'.lake'
if not lake.exists():lake.symlink_to(base/'lake',target_is_directory=True)
cache=project/'verification/handoff-cache';cache.mkdir(parents=True,exist_ok=True)
modules=[name[len('project/'):].removesuffix('.lean').replace('/','.') for name in manifest
    if name.startswith('project/ElevenSquare/') and name.endswith('.lean')]
for module in modules:
    receipt=main/'verification/handoff-cache'/(module+'.json')
    current=cache/(module+'.json')
    # These are genuine checker records, copied provisionally. The unchanged
    # check_handoff.py verifies BOTH source-closure and object hashes before
    # reusing any object. Hash here only when choosing between conflicting
    # records, preserving a newer worker receipt over an older main copy.
    if current.exists() and (not receipt.exists() or current.read_bytes()==receipt.read_bytes()):
        continue
    if not current.exists() and receipt.exists():
        shutil.copyfile(receipt,current)
        continue
    if not current.exists():
        continue
    obj=base/'lake/build/lib'/Path(*module.split('.')).with_suffix('.olean')
    object_sha=hashlib.sha256(obj.read_bytes()).hexdigest() if obj.exists() else None
    # Preserve a genuine local receipt for the current object. In particular,
    # do not overwrite freshly checked reduced data with an older main receipt.
    if current.exists() and json.loads(current.read_text()).get('object_sha256')==object_sha:
        continue
    if receipt.exists() and json.loads(receipt.read_text()).get('object_sha256')==object_sha:
        shutil.copyfile(receipt,current)
from configure_runtime import configure
library_job=worker.startswith('library-') or task_name.startswith('library-case')
config=configure(project,kit=K,threads=1,memory=8192,final_check=(task_name=='final-returned-target-task.json')) if library_job else (configure(project,kit=K,threads=1,memory=3072) if worker=='coarse-pilot' else configure(project,kit=K,threads=1))
if worker.startswith('extra-') and not library_job:config=configure(project,kit=K,threads=1,memory=4096)
task=json.loads((runtime/task_name).read_text())
prefix={'independent-probe':'independent','helper-probe':'helper','auxiliary-probe':'auxiliary','primary':'primary','library-a':'library-a','library-b':'library-b','library-c':'library-c','library-d':'library-d','library-e':'library-e','library-f':'library-f','coarse-pilot':'coarse-pilot','extra-a':'extra-a','extra-b':'extra-b','extra-c':'extra-c','extra-d':'extra-d','extra-e':'extra-e','extra-f':'extra-f'}[worker]
log_path=K/'agent-evidence'/(prefix+'-'+Path(task_name).stem+'.log')
command=['python3','scripts/check_handoff.py','--task',str(runtime/task_name)]
with log_path.open('a') as log:
    code=subprocess.call(command,cwd=project,stdout=log,stderr=subprocess.STDOUT)
if code==0:
    # Copy only genuine receipts created/validated by the unchanged supplied
    # checker. The main checker will independently recheck their source closure
    # and object hashes before reuse after its later source sync.
    for module in modules:
        receipt=cache/(module+'.json')
        destination=main/'verification/handoff-cache'/receipt.name
        if receipt.exists() and receipt!=destination:shutil.copyfile(receipt,destination)
record=dict(task=task_name,exit_code=code,project=str(project),actual_log=str(log_path),
    transport_sha256=transport_digest.hexdigest(),configuration=config,
    disposable_source_workspace_kind='scratch' if use_scratch else 'runtime',
    supplied_handoff_checker_unchanged=True,runtime_resource_adapter='configure_runtime.py',
    resource_scope='Single-thread checker in one explicitly allocated worker slot.')
(K/'agent-evidence'/(prefix+'-'+Path(task_name).stem+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
raise SystemExit(code)
