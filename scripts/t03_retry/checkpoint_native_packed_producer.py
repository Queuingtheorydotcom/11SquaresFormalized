"""Stop only an owned transport producer at a completed file-publication boundary."""
from pathlib import Path
import argparse, ctypes, datetime, hashlib, json, subprocess, time

from retry_paths import kit_paths
ap = argparse.ArgumentParser()
ap.add_argument('--case', type=int, required=True)
ap.add_argument('--pid', type=int, required=True)
ap.add_argument('--kit',required=True)
ap.add_argument('--transport-dir')
ap.add_argument('--scratch-root',required=True)
ap.add_argument('--producer-script',type=Path,required=True)
ap.add_argument('--revision', type=int, default=1)
ap.add_argument('--reason',default='Preserve issued source closures at a complete producer publication boundary.')
a = ap.parse_args()
K,E,transport_root=kit_paths(a.kit,a.transport_dir)
scratch=Path(a.scratch_root).resolve();assert scratch.is_dir()
assert a.producer_script.name=='parallel_packed_case_producer.py'
assert a.case in {r['case'] for r in json.loads((E/'forward-workload-inventory.json').read_text())['records']} and a.pid>0
assert 1 <= a.revision <= 99
revision_tag = '' if a.revision == 1 else f'-retry{a.revision:02d}'
record = E / f'case{a.case}-equality-repair-producer-checkpoint{revision_tag}.json'
assert not record.exists()
command = f"Get-CimInstance Win32_Process -Filter 'ProcessId={a.pid}' | Select-Object ProcessId,CommandLine,ExecutablePath | ConvertTo-Json -Compress"
identity = json.loads(subprocess.check_output(['powershell.exe', '-NoProfile', '-Command', command], text=True))
assert identity['ProcessId'] == a.pid
assert str(a.producer_script.resolve()).replace(chr(92),'/').lower() in identity['CommandLine'].replace(chr(92),'/').lower()
assert Path(identity['ExecutablePath']).name.lower() in ['python.exe','python3.exe']
assert f'--case {a.case}' in identity['CommandLine']
if '--publication' in identity['CommandLine']:
    assert f'case{a.case}-packed-parallel-publication.json' in identity['CommandLine']
    publication_name=f'case{a.case}-packed-parallel-publication.json'
else:publication_name=f'case{a.case}-packed-canonical-publication.json'
publication=json.loads((E/publication_name).read_text());prior_status=json.loads((E/f'case{a.case}-parallel-packed-status.json').read_text())
assert publication['case']==prior_status['case']==a.case and prior_status['source_archive_sha256']==publication['grouped_archive_sha256']
kernel = ctypes.WinDLL('kernel32', use_last_error=True)
kernel.OpenProcess.argtypes = (ctypes.c_ulong, ctypes.c_int, ctypes.c_ulong)
kernel.OpenProcess.restype = ctypes.c_void_p
kernel.TerminateProcess.argtypes = (ctypes.c_void_p, ctypes.c_uint)
kernel.WaitForSingleObject.argtypes = (ctypes.c_void_p, ctypes.c_ulong)
kernel.CloseHandle.argtypes = (ctypes.c_void_p,)
nt = ctypes.WinDLL('ntdll')
nt.NtSuspendProcess.argtypes = (ctypes.c_void_p,)
nt.NtResumeProcess.argtypes = (ctypes.c_void_p,)
handle = kernel.OpenProcess(0x0800 | 0x1000 | 0x0001 | 0x00100000, False, a.pid)
assert handle
destination = scratch/f'case{a.case}-parallel-packed-transports'
assert destination.resolve().parent == scratch

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as source:
        while block := source.read(1024 * 1024):
            h.update(block)
    return h.hexdigest()

suspended = False
terminated = False
try:
    deadline = time.monotonic() + 45
    while True:
        assert nt.NtSuspendProcess(handle) == 0
        suspended = True
        busy = list(destination.glob('.preparing-*'))
        busy += list(destination.glob('*.preserving.zip'))
        busy += list(E.glob(f'.paired-group-publication-case{a.case}.json'))
        busy += list(E.glob(f'case{a.case}-paired-group-audit-bindings.writing.json'))
        busy += list(E.glob(f'library-case{a.case}-node994-queue.writing.json'))
        busy += list(transport_root.glob(f'.t03-runtime-sync-library-case{a.case}-*.preparing.zip'))
        busy += list(E.glob(f'case{a.case}-parallel-packed-status.writing.json'))
        for live in transport_root.glob(f'.t03-runtime-sync-library-case{a.case}-node998-*-task.zip'):
            saved = destination / live.name
            if saved.exists() and (saved.stat().st_size != live.stat().st_size or sha(saved) != sha(live)):
                busy.append(saved)
        if not busy:
            break
        assert nt.NtResumeProcess(handle) == 0
        suspended = False
        assert time.monotonic() < deadline, ('Producer did not reach a file boundary', [str(p) for p in busy])
        time.sleep(1)
    snapshot = (E / f'case{a.case}-parallel-packed-status.json').read_bytes()
    prior = E / f'case{a.case}-parallel-packed-status-before-equality-repair{revision_tag}.json'
    with prior.open('xb') as output:
        output.write(snapshot)
    assert kernel.TerminateProcess(handle, 0)
    terminated = True
    assert kernel.WaitForSingleObject(handle, 2000) == 0
    p = dict(status='OWNED_NATIVE_PRODUCER_CHECKPOINTED_COMPILER_JOBS_UNTOUCHED',
        case=a.case, utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        old_pid=a.pid, verified_command_line=identity['CommandLine'],
        repair_revision=a.revision,
        stopped_at_complete_file_boundary=True, partial_transport_files=[],
        preserved_status=prior.name, preserved_status_sha256=hashlib.sha256(snapshot).hexdigest(),
        proof_processes_signalled=[], other_producers_untouched=True,
        reason=a.reason)
    record.write_text(json.dumps(p, indent=2) + '\n')
    print(json.dumps(p), flush=True)
finally:
    if suspended and not terminated:
        nt.NtResumeProcess(handle)
    kernel.CloseHandle(handle)
