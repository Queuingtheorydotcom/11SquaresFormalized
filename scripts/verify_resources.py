"""Read-only memory advice for one coordinated proof scheduler.

This helper never starts, signals, or reaps a process and never writes receipts.
Native Windows and Linux telemetry is supported; missing telemetry allows only
the serial slot. Admission estimates are conservative, not OS-enforced limits.
"""
from dataclasses import dataclass
import math
from pathlib import Path, PurePosixPath
import sys
import time

MiB = 1024 ** 2
GiB = 1024 ** 3


@dataclass(frozen=True)
class MemorySnapshot:
    total_physical: int
    available_physical: int
    available_commit: int


@dataclass(frozen=True)
class ProcessMemory:
    resident: int
    private: int
    peak_resident: int
    peak_private: int


@dataclass(frozen=True)
class GuardDecision:
    allow_start: bool
    terminate_module: str | None
    reason: str


def _kb_fields(text):
    values = {}
    for line in text.splitlines():
        key, separator, value = line.partition(':')
        pieces = value.split()
        if separator and pieces and pieces[0].isdigit():
            values[key] = int(pieces[0]) * (1024 if len(pieces) > 1 and pieces[1] == 'kB' else 1)
    return values


def _linux_memory():
    values = _kb_fields(Path('/proc/meminfo').read_text(encoding='ascii'))
    total, available = values['MemTotal'], values['MemAvailable']
    commit = max(0, values['CommitLimit'] - values['Committed_AS'])
    # Honor the process's own memory cgroup and every constrained ancestor,
    # rather than assuming the mounted root is the process's effective limit.
    # If the membership cannot be resolved at the standard mount, fail closed.
    memberships = Path('/proc/self/cgroup').read_text(encoding='ascii').splitlines()
    for line in memberships:
        _, controllers, group = line.split(':', 2)
        if controllers and 'memory' not in controllers.split(','):
            continue
        parts = PurePosixPath(group).parts
        if not parts or parts[0] != '/' or '..' in parts:
            raise ValueError('Unresolved memory cgroup')
        unified = not controllers
        mount = Path('/sys/fs/cgroup') if unified else Path('/sys/fs/cgroup/memory')
        current_group = mount.joinpath(*parts[1:])
        maximum = 'memory.max' if unified else 'memory.limit_in_bytes'
        usage = 'memory.current' if unified else 'memory.usage_in_bytes'
        if not (current_group / maximum).is_file():
            raise ValueError('Unresolved memory cgroup')
        while True:
            limit_file = current_group / maximum
            if limit_file.is_file():
                value = limit_file.read_text(encoding='ascii').strip()
                if value != 'max':
                    limit = int(value)
                    used = int((current_group / usage).read_text(encoding='ascii'))
                    total = min(total, limit)
                    available = min(available, max(0, limit - used))
            if current_group == mount:
                break
            current_group = current_group.parent
    return MemorySnapshot(total, available, commit)


def _windows_memory():
    import ctypes
    from ctypes import wintypes

    class Status(ctypes.Structure):
        _fields_ = [('length', wintypes.DWORD), ('load', wintypes.DWORD)] + [
            (name, ctypes.c_ulonglong) for name in
            ('total', 'available', 'commit_total', 'commit_available',
             'virtual_total', 'virtual_available', 'extended_available')]

    status = Status()
    status.length = ctypes.sizeof(status)
    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    kernel.GlobalMemoryStatusEx.argtypes = [ctypes.POINTER(Status)]
    kernel.GlobalMemoryStatusEx.restype = wintypes.BOOL
    if not kernel.GlobalMemoryStatusEx(ctypes.byref(status)):
        raise OSError('System memory telemetry unavailable')
    return MemorySnapshot(status.total, status.available, status.commit_available)


def read_system_memory():
    try:
        if sys.platform == 'win32':
            result = _windows_memory()
        elif sys.platform.startswith('linux'):
            result = _linux_memory()
        else:
            return None
        if (result.total_physical <= 0 or result.available_physical < 0
                or result.available_physical > result.total_physical
                or result.available_commit < 0):
            return None
        return result
    except (OSError, ValueError, KeyError):
        return None


def _windows_process(pid):
    import ctypes
    from ctypes import wintypes

    class Counters(ctypes.Structure):
        _fields_ = [('size', wintypes.DWORD), ('faults', wintypes.DWORD)] + [
            (name, ctypes.c_size_t) for name in
            ('peak_resident', 'resident', 'peak_paged_pool', 'paged_pool',
             'peak_nonpaged_pool', 'nonpaged_pool', 'pagefile',
             'peak_private', 'private')]

    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    psapi = ctypes.WinDLL('psapi', use_last_error=True)
    kernel.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    kernel.OpenProcess.restype = wintypes.HANDLE
    kernel.CloseHandle.argtypes = [wintypes.HANDLE]
    psapi.GetProcessMemoryInfo.argtypes = [wintypes.HANDLE, ctypes.POINTER(Counters), wintypes.DWORD]
    psapi.GetProcessMemoryInfo.restype = wintypes.BOOL
    handle = kernel.OpenProcess(0x1000, False, pid)  # QUERY_LIMITED_INFORMATION only.
    if not handle:
        raise OSError('Process memory telemetry unavailable')
    try:
        counters = Counters()
        counters.size = ctypes.sizeof(counters)
        if not psapi.GetProcessMemoryInfo(handle, ctypes.byref(counters), counters.size):
            raise OSError('Process memory telemetry unavailable')
        return ProcessMemory(counters.resident, counters.private,
                             counters.peak_resident, counters.peak_private)
    finally:
        kernel.CloseHandle(handle)


def read_process_memory(pid):
    try:
        if type(pid) is not int or pid <= 0:
            return None
        if sys.platform == 'win32':
            result = _windows_process(pid)
        elif sys.platform.startswith('linux'):
            values = _kb_fields(Path(f'/proc/{pid}/status').read_text(encoding='ascii'))
            resident = values['VmRSS']
            # Linux does not expose Windows-style private commit here. Reserve
            # at least RSS+swap and the data/stack virtual regions; the separate
            # system CommitLimit/Committed_AS gate stays conservative as well.
            private = max(resident + values.get('VmSwap', 0),
                          values.get('VmData', 0) + values.get('VmStk', 0))
            result = ProcessMemory(resident, private, values.get('VmHWM', resident), private)
        else:
            return None
        if min(result.resident, result.private, result.peak_resident, result.peak_private) < 0:
            return None
        return result
    except (OSError, ValueError, KeyError):
        return None


class ResourceGuard:
    """Advise on auxiliary admission and pressure; leave child ownership alone."""

    def __init__(self, memory_percent=95, reserve_bytes=512 * MiB,
                 warmup_seconds=5, minimum_process_bytes=GiB,
                 system_reader=read_system_memory, process_reader=read_process_memory,
                 clock=time.monotonic):
        if (not 0 < memory_percent <= 95 or reserve_bytes < 0
                or warmup_seconds < 0 or minimum_process_bytes <= 0):
            raise ValueError('Invalid memory guard configuration')
        self.memory_percent = memory_percent
        self.reserve_bytes = reserve_bytes
        self.warmup_seconds = warmup_seconds
        self.minimum_process_bytes = minimum_process_bytes
        self.system_reader, self.process_reader, self.clock = system_reader, process_reader, clock
        self.peak_resident = self.peak_private = 0

    def assess(self, active):
        # The first child is the existing serial behavior. No advice can kill the
        # sole primary; unavailable telemetry simply disables auxiliary work.
        if not active:
            # A completed heavy batch must not permanently serialize later light
            # work. Retain peaks until the entire active batch has drained.
            self.peak_resident = self.peak_private = 0
            return GuardDecision(True, None, 'serial_slot')
        ordered = sorted(active, key=lambda name: (active[name].started, name))
        auxiliary = ordered[-1] if len(ordered) > 1 else None
        system = self.system_reader()
        if system is None:
            return GuardDecision(False, auxiliary, 'system_memory_unavailable')
        reserve = max(self.reserve_bytes,
                      math.ceil(system.total_physical * (100 - self.memory_percent) / 100))
        if system.available_physical < reserve:
            return GuardDecision(False, auxiliary, 'physical_memory_pressure')
        if system.available_commit < reserve:
            return GuardDecision(False, auxiliary, 'commit_memory_pressure')
        memories = []
        for name in ordered:
            usage = self.process_reader(active[name].process.pid)
            if usage is None:
                return GuardDecision(False, auxiliary, 'process_memory_unavailable')
            self.peak_resident = max(self.peak_resident, usage.resident, usage.peak_resident)
            self.peak_private = max(self.peak_private, usage.private, usage.peak_private)
            memories.append(usage)
        # Serialize admissions through startup. A low first sample must not
        # immediately fill all slots before any compiler reaches its working set.
        if any(self.clock() - active[name].started < self.warmup_seconds for name in ordered):
            return GuardDecision(False, None, 'startup_warmup')
        resident_budget = max(self.minimum_process_bytes, math.ceil(self.peak_resident * 1.25))
        private_budget = max(self.minimum_process_bytes, math.ceil(self.peak_private * 1.25))
        resident_growth = sum(max(0, resident_budget - m.resident) for m in memories)
        private_growth = sum(max(0, private_budget - m.private) for m in memories)
        if system.available_physical < reserve + resident_growth + resident_budget:
            return GuardDecision(False, None, 'physical_admission_budget')
        if system.available_commit < reserve + private_growth + private_budget:
            return GuardDecision(False, None, 'commit_admission_budget')
        return GuardDecision(True, None, 'memory_available')
