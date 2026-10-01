# Experimental T03 retry tools

These portable copies record operational retries for unfinished cases 1464
and 1465. The live originals produced the actual dependency-group audits in
`verification/t03-case1464-parallel-retry.json` and
`verification/t03-case1465-operational-retry.json`. Parameterized copies have
Python source validation; they have not been replayed in Lean. They do not add
a completed case or replace the repository's serial `scripts/verify.py`.

The tools require an existing T03 checker kit with `eleven-square-lean/` and
`agent-evidence/`, exact source transports, a compatible pool dispatcher, and
genuine source/object receipts. The pending cases 1464 and 1465 generated source
closures
are not included in this Git checkpoint. These scripts alone cannot reproduce
their complete proofs.

| Tool | Role |
| --- | --- |
| `regroup_packed_case_by_depth.py` | Regroup an existing exact cold-source plan by dependency depth, with up to 64 modules and 8 MiB of source per group. Preserve earlier plans; optionally retain an exact original helper with no grouped ancestor. |
| `queue_parallel_case_retry.py` | Hold the full-case retry, let the active compiler finish, retire its serial wrapper at a compiler boundary, and retain the original sources, transport and receipts. |
| `parallel_packed_case_producer.py` | Create bounded exact-source group transports, prioritize ready groups on the longest remaining dependency path, and release the full case only after all required group audits and genuine source/object receipts match. |
| `run_independent_probe.py` | Run one supplied serial checker in an allocated worker slot, with hash-verified source extraction into a separate scratch workspace. |
| `scheduling.py` | Pure full-case/fair-group priority and aggregate-refresh deferral policies; read-only dispatch-delay observation CLI. The caller must validate readiness, source reservations, worker ownership and its concurrency ceiling. |
| `queue_failed_binding_pilot.py` | Copy exact failed binding data into an isolated pilot and queue it through the supplied source packer and existing pool; diagnostic rational equality does not accept the proof. |
| `prepare_coordinate_binding_retry.py` | Require accepted exact-data pilot evidence, rewrite only those failed proof constructions, verify an immutable retry archive, then update the single canonical grouped source. |
| `publish_coordinate_binding_retry.py` | Verify the prepared immutable retry, preserve its old guard, and queue it through an existing Linux dispatcher with no active job for that case. |
| `configure_runtime.py` | Configure only a disposable runtime: pin the exact compiler/environment, use one Lean thread, and allocate unique check-log directories. |

Every machine path is supplied explicitly. `--kit` identifies the checker kit;
`--runtime-root` identifies its configured compiler/object runtime;
`--scratch-root` identifies an existing directory with space for disposable
source workspaces and preserved completed transports. `--transport-dir` defaults
to the kit's parent. The producer also requires `--receipt-root` and
`--object-root`. Its object root is the directory corresponding to
`ElevenSquare.Tasks.T03` in the shared object cache.

The queue transition, runtime configurator, and worker wrapper use Linux process
and file-lock APIs. The planner and producer support Windows or Linux. Python
3.10 or newer is required. Preparation uses low process priority and one
available CPU. The portable worker default is one; `--max-workers` can record
an already allocated pool ceiling up to six. The external dispatcher enforces
that ceiling and excludes duplicate jobs; these tools do not create a worker
pool. The producer defaults to at most eight live source transports.

`parallel_packed_case_producer.py --raw-copy-transports` enables an opt-in
transport fast path. Eligible `ZIP_STORED` and `ZIP_DEFLATED` members are copied
from the frozen master transport without decompressing and recompressing their
payloads; the per-group task and fresh source manifest are still written
normally. Unsupported ZIP/runtime conditions fall back to the existing
`read`/`writestr` path before writing that member. Corrupt or inconsistent ZIP
data is not treated as a fallback condition. The producer still reopens every
new transport and checks every recorded member SHA-256 before publication.
Run `python3 scripts/t03_retry/test_zip_raw_copy.py` for the source-only raw-copy
regressions. The option remains explicit because the resulting ZIP byte stream
and compressed sizes can differ from transports produced by recompression even
when all decompressed members are identical.

The worker defaults to a scratch source workspace. It retains the worker lock,
checks the exact opened transport digest, verifies every extracted member, and
copies genuine checker receipts provisionally. The supplied checker must
revalidate both the source closure and object hashes before reusing a proof
object. Obsolete disposable Lean copies are removed only when their bytes match
the saved prior manifest. Canonical source files and input archives remain.

`configure_runtime.py` defaults to one compiler thread and a 4096 MiB per-check
ceiling; library groups use 8192 MiB through the wrapper. These are limits, not
memory reservations. It captures the unchanged pinned Lake environment once,
checks the exact compiler binary hash, and disables advisory linters in the
disposable runner. Mathematical kernel checking remains enabled. The target
HandoffAudit must still pass with the standard allowed axioms.

For arguments without starting a job, use `python3 TOOL.py --help`. Configure
paths and an existing compatible dispatcher before a transition. Runtime
manifests, process state, transport archives, logs and build caches are local
working data; retain them outside Git. Repository assembly checks remain:

```sh
python3 scripts/check_sources.py
python3 scripts/verify.py --setup
```

The actual first group passed in a disposable scratch workspace. The proposed
extra manual test found the automatic checker already running and started no
extra compiler or borrowed worker slot. Full case1464 and both public returned
target audits remain pending. This operational snapshot had 155/173 published
complete cases; subsequent accepted case supplements are tracked in T03_PROGRESS.md.

The latest operational update keeps the full published count at **156/173**.
Case1465 has two independently inspected group audits and a retained exact
original `DistanceCollision` import; neither grouped case is fully accepted.
Use repeatable `--preserve-original-module MODULE` on the depth planner to
retain such a helper. It rejects helpers that import a grouped ancestor and
preserves the preceding plan before regrouping.

The public scheduling module contains policy functions rather than a pool
controller. Integrate its priority only after the caller's ordinary readiness
and receipt checks. Its aggregate-refresh predicate defers only dispatcher
group-completion rescans while full cases remain unfinished; individual audit,
receipt and execution records must always be retained. The read-only CLI takes
`--events`, `--cut`, optional `--snapshot`, and `--window` (default 20). Its
observations describe scheduling and polling delays, not Lean compiler timing.

The latest case1372 checkpoint supplies an actually accepted two-binding pilot
and an immutable full retry, not a complete case certificate. The pilot tool
requires `--kit` and `--packer`, an existing compatible kit source packer that
accepts `TASK --named`. It creates a source/task/queue candidate; only the
unchanged supplied Lean checker can accept it. The packer must use that kit's
evidence and source directories. It is not included in these experimental tools.

The preparation tool requires `--kit` and `--scratch-root`; optionally supply
`--transport-dir` and `--failed-execution` (an existing execution-record filename).
It requires a matching actual accepted pilot record and the tested exact helper
hash. It preserves the old archive, changes only the checked failed proof
constructions plus the helper import, verifies every output member, and updates
the single canonical grouped source only after all validations. It refuses a
case with an active full-case or library job. This is a source preparation action,
not a proof acceptance step.

The queue publisher requires `--kit` and optionally `--transport-dir`,
`--dispatcher-name` and `--max-workers` (default one, maximum six, matching the
prepared record). It uses Linux process control to pause only the existing
controller while replacing the case's preserved reuse guard. It refuses active
jobs for that case, and resumes the controller in a `finally` block. It neither
creates a dispatcher nor launches a compiler. All three tools have Python
source/help validation and bounded fixtures, not a portable Lean/pool replay.

`rewrite_generated_rfl.py` is a source-only helper for these exact generated
proof files. Supply `--source`, its exact `--source-sha256`, and a fresh
`--output`. It performs the same lexical tactic replacement as the verified
49-module retry, adds the tested helper import, and preserves numeric tokens.
It is not a general Lean parser: use only reviewed generated source templates.
It refuses a wrong input hash, repeated rewriting and an existing output.
Every resulting declaration still requires the original kernel check.

`share_completed_receipts.py` is a Linux copier with explicit `--runtime-root`,
optional `--scratch-root`, `--destination`, `--object-root`, repeated `--worker`
and `--once` arguments. Defaults include the separate primary scratch donor.
It copies existing receipt bytes only when the current object hash matches;
the unchanged original checker must independently validate source closure
and objects before reuse. A process lock and atomic JSON replacement avoid
concurrent partial writes. No compiler or pool is created. Only isolated
Python fixtures were replayed for this portable copy, not the production service.


The generalized failed-group tools require explicit `--kit`, `--case`,
`--transport-dir` and `--scratch-root`. `prepare_failed_packed_equality_repairs.py`
accepts reviewed 1464/1465 generated source formats, preserves old archives and
issued closures, repairs failed/never-issued modules, and validates bytes
before publishing the immutable source version. `publish_failed_packed_equality_repairs.py`
retains the existing full-case guard, records distinct task aliases and resumes
only its identified controller in a `finally` block. Neither accepts a proof.
`checkpoint_native_packed_producer.py` additionally requires an explicit owned
`--pid` and `--producer-script`, checks executable/script identity and waits
for a complete publication boundary. Do not point it at a compiler. Publication
validated only parsing/help, with no process control or live pool replay.

`sync_native_runtime_sources.py` runs on Windows with explicit `--scratch-root`,
`--archive`, `--runtime` and `--expected-sha256`. The runtime must be an allowed
disposable child of `grouped-source-runtimes`; the caller must already hold its
ordinary runtime lock. Supply `--main-receipts`, `--object-root` and
`--other-object-root` for provisional genuine record copying. The original
checker must validate source/object closure before reuse. `--skip-receipts`
is restricted to isolated validation directories. No compiler or proof record
is created. It hashes the archive before/after and every extracted member.

`benchmark_native_source_sync.py` takes the same exact archive/hash plus
`--scratch-root`, `--native-python`, `--helper` and a fresh `--output`. Run it
from WSL with fresh disposable validation directories on a mounted drive.
It compares source synchronization, verifies repair of a corrupted fixture
and wrong-digest rejection. `record_native_source_sync_validation.py` uses
explicit `--record`, `--runtime`, `--main-receipts` and `--helper` to bind any
subsequent genuine record-copy fixture to byte-identical original records.
Parameterized publication copies had parsing/help checks only; the recorded
production measurements concern the exact original helper hash in the evidence.
The producer accepts `--max-live` as an alias of `--max-live-archives`, 1–8,
default 8. Changing preparation concurrency does not increase the Lean pool.


Failed-group tools accept `--revision` 1–99 (default 1); later revisions require
explicit preparation `--failed-group GROUP:WORKER` entries. Publication's
optional repeated `--failed-group` validates the prepared group set before
any publishing actions. Existing retry aliases accumulate through the named
latest transition; earlier revision records/archives remain preserved.

`apply_source_supplement.py` requires `--base`, `--supplement`, its exact
`--supplement-sha256` and a fresh `--output`. It verifies both ZIP digests,
safe members, changed-member bindings and the updated source manifest, then
streams unchanged base members plus the explicitly bound overlay to a fresh
source directory. Each source layer changes exactly one Lean module. Metadata changes are
explicitly listed. All proof/source/environment/task acceptance still belongs
to the unchanged original Lean checker. A small isolated fixture checked
byte preservation, manifest application, existing-output refusal and wrong
base/supplement digest rejection; no real bulk source extraction or Lean
build was performed for this publication.


For a stacked recipe, supply ordered repeated `--prior-supplement PATH` inputs.
Their required SHA256 values are bound by the current supplement's authenticated
recipe. The tool validates each predecessor chain, old/new source member hash
and refreshed manifest before creating the fresh output. The original base
ZIP stays unchanged, so no full ZIP repack is needed. Layered output is still
pending source, requiring the original full Lean check. The two-layer Python
fixture preserved both source changes and unchanged environment bytes and
rejected a missing/wrong predecessor before output creation.


`plan_remaining_packed_parallelism.py` takes explicit `--case`, `--prefix`,
`--worker`, `--kit`, `--scratch-root` and optional `--transport-dir`. It reads
actual failed-check evidence and accepted prefix CHECK/source bindings before
planning the dependency-depth remainder. `prepare_remaining_parallel_case.py`
implements the reviewed case1499/prefix26 source format, with explicit kit,
scratch and optional source/transport roots and WSL distribution. It preserves
prefix source bytes and the exact original target, rewrites only reviewed
generated equality constructs, and prepares source/task metadata. It does not
prove a case; the unchanged original checker still validates every new proof.

`create_private_packed_source_storage.py` creates only fresh Windows source
junctions under the chosen scratch root, with an explicit `--kit`, optional
`--source-root` and `--wsl-distro`. It refuses existing source/storage directories
and active/completed cases and checks both Windows and WSL access. The logical
source path stays unchanged while new generated sources use scratch storage.
`activate_prepared_local_case.py` requires explicit kit/scratch roots and preserves
the earlier hold record before leaving a full exact-target proof barrier in its
place. Neither accepts proofs, starts a compiler nor increases the pool.
These portable source-storage/activation actions were not executed during
publication; only parsing and help paths were checked.

The producer's `--preparation` argument must name a kit evidence JSON basename.
If it records `group_module_prefix`, only those new groups become queue rows;
checked prefix modules remain source dependencies. `--resume` preserves the
previous live-archive bound unless `--max-live` is explicitly supplied; a new
producer still defaults to eight. Preparation defaults to one core and the
portable global compiler ceiling defaults to one, with an explicit maximum six.

`scheduling.prioritize_ready_candidates` accepts optional `last_case_starts`.
Full cases retain priority; group ranking uses active count, oldest last
assignment and then longest dependency path. Recompute after every successful
assignment with current active jobs and timestamps so simultaneous free slots
rotate fairly. Isolated decision fixtures checked rotation and priority without
starting jobs. No audit timing probe is evidence of mathematical correctness.


`prepare_homogeneous_fan_probe.py` prepares only the reviewed abstract arithmetic
helper task, using explicit `--kit`, `--scratch-root`, optional source/transport
roots and a conservative `--max-workers` default of one. It preserves exact
reachable source/environment/checker bytes and refuses existing task/queue
paths. It starts no compiler and accepts no full case.

`prepare_homogeneous_fan_comparison.py` additionally requires `--polygon-source`
pointing to the reviewed generated source block format. The helper must already
have passed its actual supplied-checker audit. Exact rational literals produce
integer witnesses, while both comparison modules retain the same original
definitions and prove the original rational Boolean claim. Python arithmetic
checks only prepare data; ordinary Lean proofs and the original audit are still
required. It refuses existing fixture modules/tasks/queues. The included fixture
sources are the exact actually checked 56-vertex modules, not a claimed speedup.

`record_homogeneous_fan_helper_acceptance.py` reads actual wrapper/execution,
CHECK/log and source hashes with explicit kit/source roots, helper prefix and
an output basename. Optional `--include-group105` collects that specific group
audit with `--group-prefix`; it never counts it as a full case.
`--reported-accepted-cases` is caller-provided informational metadata, not a
proof count calculated by this collector. Portable tools had parsing/help
checks only; publication did not replay source generation, queue writes or
runtime checks. The independent published provenance contains the actual
accepted source-member and checker bindings.


## Local queue and readiness checkpoint

The current compact checkpoint records 159 full accepted cases; the 14 remaining
dependency queues and their actual first-group audits are partial work. See
`verification/t03-local-queues-checkpoint-20261001.json`. This does not publish
new large pending source closures or complete a family target.

`plan_packed_case.py`, `regroup_packed_case_by_depth.py` (optional `--plan`),
`packed_namespace_transform.py` and `prepare_namespaced_packed_case.py` preserve
the original statement/data and classify new source constructions as pending.
The last preparation tool supports `--all-equality-refl`, `--canonical` and a
distinct revision; all transformed proofs still need the original Lean checker.
Planning requires genuine source/object receipts in the compatible runtime.
Preparation requires the original kit's benchmark/precheck evidence. All paths
are explicit `--kit`, `--runtime-root`, `--transport-dir`, `--scratch-root` or
`--source-root` arguments as relevant. `publish_idle_rebalanced_case.py` refuses
active/already accepted cases; `restore_external_case_queue.py` restores only
the exact preserved queue under its full-case guard.

`pool_helpers.py` exposes the unchanged source-closure and object-hash predicates
without starting a pool. `run_unified_proof_pool_v7.py` reserves active exact
closures, prefers fewer active groups, rotates older waiting cases and then
chooses the longest remaining path. It defaults to four global slots, optionally
six, with one compiler thread per worker. Its ready-archive prefilter avoids
historical-log probes for source batches not yet published. The checked 15.761
to 1.547 second improvement concerns readiness selection only.

`restart_critical_path_dispatcher.py` requires an explicit owned controller PID
and exact controller/probe script paths. It pauses/replaces only that controller
and conservatively adopts live source reservations. It does not signal a Lean
job. Controller ownership tools require Linux and the original compatible kit,
worker schemas and supplied checker; their live actions were not replayed for
publication. Run `--help` for explicit arguments before using them.

`benchmark_ready_archive_prefilter.py` and
`record_ready_archive_prefilter_application.py` record eligibility and actual
event timings without starting a checker. Reversed timestamp pairs are retained
and flagged; they cannot establish a refill duration. `stage_verified_return.py`
and `write_verified_report.py` retain the full-173/both-target/frozen-protocol
guards and refuse partial completion. They were not executed for this snapshot.
