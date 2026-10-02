"""Single-owner dependency scheduling; proof acceptance stays with the verifier.

All callbacks run on the main thread. ``prepare`` returns None for a validated
cache hit, or a job exposing process/started and start/accept/reject methods.
Only accept (or the cache callback) may publish a completed dependency. A guard
can delay starts or interrupt an auxiliary job for an exclusive retry; it never
accepts proofs or changes compiler arguments.
"""
from collections import deque
from contextlib import contextmanager
from dataclasses import dataclass
import heapq
import os
from pathlib import Path
import signal
import subprocess
import time


class CheckoutLock:
    """An OS-released advisory lock; never unlink the shared lock-file inode."""
    def __init__(self, path):
        self.path = Path(path)
        self.stream = None

    def acquire(self):
        if self.stream is not None:
            raise RuntimeError('Verifier lock is already held')
        self.path.parent.mkdir(parents=True, exist_ok=True)
        stream = self.path.open('a+b')
        try:
            stream.seek(0, os.SEEK_END)
            if stream.tell() == 0:
                stream.write(b'1'); stream.flush()
            stream.seek(0)
            if os.name == 'nt':
                import msvcrt
                msvcrt.locking(stream.fileno(), msvcrt.LK_NBLCK, 1)
            else:
                import fcntl
                fcntl.flock(stream.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BaseException:
            stream.close()
            raise
        self.stream = stream
        return self

    def close(self):
        if self.stream is not None:
            self.stream.close()
            self.stream = None

    def __enter__(self):
        return self.acquire()

    def __exit__(self, *_):
        self.close()


@contextmanager
def defer_interrupts():
    """Close the Popen/registration race without ignoring an interrupt."""
    pending = []
    previous = {}
    try:
        for sig in (signal.SIGINT, signal.SIGTERM):
            previous[sig] = signal.getsignal(sig)
            signal.signal(sig, lambda signum, _frame: pending.append(signum))
        yield
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)
        if pending:
            raise KeyboardInterrupt


def stop_processes(jobs, *, grace=3.0, kill_grace=3.0):
    """Signal all children before bounded waits, and reap every started child.

The subprocess is Lean itself, with no shell or compiler grandchildren. Both
phases have one common deadline, so cancellation is bounded independently of
the configured pool size and fits the CI wrapper's 45-second grace period.
"""
    processes = [job.process for job in jobs if job.process is not None]
    for process in processes:
        if process.poll() is None:
            try:
                process.terminate()
            except OSError:
                pass
    deadline = time.monotonic() + grace
    for process in processes:
        try:
            process.wait(timeout=max(0, deadline - time.monotonic()))
        except (OSError, subprocess.TimeoutExpired):
            pass
    for process in processes:
        if process.poll() is None:
            try:
                process.kill()
            except OSError:
                pass
    deadline = time.monotonic() + kill_grace
    errors = []
    for process in processes:
        try:
            process.wait(timeout=max(0, deadline - time.monotonic()))
        except (OSError, subprocess.TimeoutExpired) as error:
            errors.append(error)
    if errors:
        raise RuntimeError('Could not reap every compiler child') from errors[0]


class CheckFailed(RuntimeError):
    def __init__(self, module, returncode):
        super().__init__('Compiler failed: ' + module)
        self.module, self.returncode = module, returncode


class CheckpointStop(RuntimeError):
    """A requested drain finished; no incomplete result is accepted."""


@dataclass
class ScheduleResult:
    accepted: list
    failed: list
    blocked: dict


def schedule(order, dependencies, prepare, *, max_parallel=1, keep_going=False,
             guard=None, event=lambda *_: None, poll_seconds=0.1,
             final='ElevenSquare.Verification', stop_requested=lambda: False):
    """Run an exact, closed DAG once, publishing only after callback success.

The supplied order is also the deterministic result/audit order. Ready jobs are
selected by that priority, while the final audit module waits for every other
selected module to settle. A pressure-interrupted job is retried exclusively;
it is never counted as accepted or as an ordinary proof failure.
"""
    if type(max_parallel) is not int or max_parallel < 1:
        raise ValueError('max_parallel must be a positive integer')
    if max_parallel > 1 and guard is None:
        raise ValueError('Parallel checks require a resource guard')
    if len(order) != len(set(order)) or set(order) != set(dependencies):
        raise ValueError('Schedule must include each selected module exactly once')
    rank = {m: i for i, m in enumerate(order)}
    deps = {m: set(ds) for m, ds in dependencies.items()}
    users = {m: set() for m in order}
    for m, ds in deps.items():
        if not ds <= rank.keys():
            raise ValueError('Schedule omits a local dependency: ' + m)
        if any(rank[d] >= rank[m] for d in ds):
            raise ValueError('Schedule order is not topological: ' + m)
        for d in ds:
            users[d].add(m)
    if users.get(final):
        raise ValueError('The final audit module must not have local dependents')
    priority = lambda m: (m == final, rank[m], m)
    remaining = {m: len(ds) for m, ds in deps.items()}
    ready = [priority(m) for m in order if remaining[m] == 0]
    heapq.heapify(ready)
    status = {}
    pending = {}
    active = {}
    exclusive = set()
    waiting_reason = None
    draining = False

    def settle(module, outcome):
        queue = deque([(module, outcome)])
        while queue:
            m, outcome = queue.popleft()
            if m in status:
                raise RuntimeError('Module settled twice: ' + m)
            status[m] = outcome
            for user in sorted(users[m], key=rank.get):
                remaining[user] -= 1
                if remaining[user] == 0:
                    unavailable = [d for d in dependencies[user]
                                   if status[d] in {'failed', 'blocked'}]
                    if unavailable:
                        event('blocked', user, unavailable)
                        queue.append((user, 'blocked'))
                    else:
                        heapq.heappush(ready, priority(user))

    def cleanup(reason):
        # Ignore repeated Ctrl-C only while stopping/reaping; the first one is
        # still propagated after all interruption receipts have been written.
        errors = []
        with defer_interrupts():
            try:
                stop_processes(list(active.values()))
            except BaseException as error:
                errors.append(error)
            for module, job in list(active.items()):
                try:
                    job.reject(reason)
                except BaseException as error:
                    errors.append(error)
                active.pop(module)
        if errors:
            raise RuntimeError('Compiler cleanup failed') from errors[0]

    try:
        while len(status) < len(order):
            progressed = False
            for module, job in sorted(list(active.items()), key=lambda item: rank[item[0]]):
                code = job.process.poll()
                if code is None:
                    continue
                # Retain active ownership until object/receipt/digest publication
                # finishes, so an interrupted callback is rejected and cleaned.
                if code == 0:
                    # A handled signal after receipt publication must preserve
                    # that complete checkpoint. Callback errors still retain
                    # active ownership and therefore reject the attempt.
                    with defer_interrupts():
                        job.accept()
                        active.pop(module)
                        exclusive.discard(module)
                        settle(module, 'accepted')
                else:
                    job.reject('compiler_failed')
                    active.pop(module)
                    exclusive.discard(module)
                    settle(module, 'failed')
                    if not keep_going:
                        raise CheckFailed(module, code)
                progressed = True

            if stop_requested():
                if not draining:
                    event('draining', None, None)
                draining = True
            decision = guard.assess(active) if guard is not None else None
            victim = decision.terminate_module if decision is not None else None
            if victim is not None:
                if victim not in active or len(active) < 2:
                    raise ValueError('Resource guard selected an invalid auxiliary job')
                job = active[victim]
                with defer_interrupts():
                    stop_processes([job])
                    job.reject('resource_pressure')
                    active.pop(victim)
                if draining:
                    # A drain still enforces auxiliary memory backoff, but an
                    # interrupted attempt resumes only in the next invocation.
                    continue
                exclusive.add(victim)
                retry = prepare(victim)
                if retry is None:
                    exclusive.discard(victim)
                    settle(victim, 'accepted')
                else:
                    # Keep the retry even if the usual pending buffer is full;
                    # otherwise draining for an unprepared retry could deadlock.
                    pending[victim] = retry
                event('retry_exclusive', victim, decision.reason)
                progressed = True
                continue

            if draining:
                if not active:
                    raise CheckpointStop('Stopped after current compiler checks')
                time.sleep(poll_seconds)
                continue

            # A bounded pending queue keeps fingerprints close to launch time
            # and lets the guard run regularly even across many cached modules.
            while ready and len(pending) < max_parallel:
                module = heapq.heappop(ready)[-1]
                if module == final and len(status) < len(order) - 1:
                    heapq.heappush(ready, priority(module))
                    break
                job = prepare(module)
                if job is None:
                    settle(module, 'accepted')
                else:
                    pending[module] = job
                progressed = True
                # Re-poll active compilers and memory after each fingerprint.
                break

            retry_waiting = exclusive & pending.keys()
            if pending and len(active) < max_parallel:
                candidate = min(retry_waiting, key=rank.get) if retry_waiting else min(pending, key=priority)
                # Drain the pool before an exclusive retry; do not launch new
                # independent work while that retry is waiting to run alone.
                if candidate in pending and not (retry_waiting and active):
                    if not any(module in exclusive for module in active):
                        decision = guard.assess(active) if guard is not None else None
                        if decision is None or (decision.allow_start and decision.terminate_module is None):
                            if stop_requested():
                                continue
                            job = pending.pop(candidate)
                            with defer_interrupts():
                                active[candidate] = job
                                job.start()
                            event('started', candidate, None)
                            waiting_reason = None
                            progressed = True
                        elif decision.reason != waiting_reason:
                            event('waiting', candidate, decision.reason)
                            waiting_reason = decision.reason

            if not progressed:
                if not active and not pending and not ready and len(status) < len(order):
                    raise RuntimeError('Incomplete schedule without runnable modules')
                time.sleep(poll_seconds)
    except BaseException:
        cleanup('interrupted')
        raise
    return ScheduleResult(
        [m for m in order if status[m] == 'accepted'],
        [m for m in order if status[m] == 'failed'],
        {m: [d for d in dependencies[m] if status[d] in {'failed', 'blocked'}]
         for m in order if status[m] == 'blocked'})
