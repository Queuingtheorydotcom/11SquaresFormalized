# Eleven-square packing in Lean

This repository assembles a formalization of the optimal eleven-square packing.
**All former source admissions have proof bodies; full native verification is
still pending.** The admission inventory is empty. The complete baseline, prior,
returned, and case438 paths require compiler acceptance and clean transitive
axiom audits before global optimality can be claimed. See [MISSING.md](MISSING.md).

The target side length is the exact real number

\[
T = \frac{6u+4}{1+2u-u^2},
\]

where `u` is the unique root in `(9/25,37/100)` of

\[
5u^8-10u^7-2u^6+14u^5+12u^4-6u^3+2u^2+2u-1=0.
\]

The construction attains approximately `3.8770835900228141773`. The model allows
arbitrary orientations, legal boundary contact, and disjoint open interiors.

## Entry points

| File | Purpose |
| --- | --- |
| `ElevenSquare/Foundations.lean` | Geometry, the exact endpoint, attaining construction, closed-cell cover, and finite case reduction. |
| `ElevenSquare/Progress.lean` | Completed baseline groups, case1000 through two steps, and selected global capture helpers. |
| `ElevenSquare/Pending/` | Public interfaces and the later proof stages, with explicit remaining dependencies. |
| `ElevenSquare/Tasks/` | Returned certificate data, generic checkers, analytic lemmas, and concrete partial proofs. |
| `ElevenSquare/Optimality.lean` | Final unconditional theorem statements; complete dependency replay remains pending. |
| `ElevenSquare/ProofAudit.lean` | Focused final-theorem closure and component axiom queries. |
| `ElevenSquare/Verification.lean` | Public-target and progress-milestone axiom queries. |

## Verification

On this prepared Windows checkout, double-click `RUN_FORMALIZATION.cmd` to run
the complete resumable verification and final audit. The launcher reuses valid
checkpoints, selects parallel checking only when a matched benchmark is faster,
and limits additional compiler processes according to memory headroom. It does
not upload anything. Re-run the same launcher after an interruption or repair.
Private diagnostics and the latest run pointer are saved under
`.verification/run/latest.json`; each run has its own logs and `summary.txt`.
Per-module compiler logs and receipts remain under `.verification/`.

### Two Windows machines and sixteen hosted workers

The shared `verification/distributed-plan.json` assigns worker 0 to machine-1,
worker 1 to machine-2, and workers 2 through 17 to GitHub's Windows runners.
All participants must use this exact plan, source snapshot, pinned Windows
compiler binary, and recorded per-module thread counts. Linux objects cannot
be substituted. Shared dependencies may be checked by more than one worker.

On a second Windows checkout, install Git and Python 3.11 or newer, then run
this explicit prerequisite restoration from the repository directory:

```cmd
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\distributed_setup.ps1 -Install
```

This stores downloaded tools, temporary files, and diagnostics inside the
checkout. Setup refuses to run while another verifier holds the checkout locks.
After setup, run `RUN_MACHINE_1.cmd` on machine-1 or `RUN_MACHINE_2.cmd` on
machine-2. The first uses at most two simultaneous module checks; the second
starts conservatively with one. Both use a 95% memory guard. These launchers
neither upload files nor start hosted workers.

Before switching from the complete local launcher, request a graceful stop
with `type nul > .verification\run\stop-requested` in Command Prompt and wait
for that run to finish its active checks. Do not run both launchers together.
To stop a distributed worker, create `.verification/distributed/stop-worker-00`
or `stop-worker-01`, respectively. Re-running its launcher clears that worker's
stop request and resumes matching accepted checkpoints.

Private run pointers are `.verification/distributed/latest-worker-00.json`
and `latest-worker-01.json`. Their named directories contain the compiler logs,
runner log, and status. Launcher errors are retained in
`.verification/distributed/launcher-error.log`; setup errors are in `setup.log`.
Keep each computer awake until its worker stops. A worker checkpoint is never
reported as a completed formalization.

When a worker is idle, create its sanitized checkpoint in PowerShell:

```powershell
. ./scripts/distributed_env.ps1
$workerPython = Resolve-DistributedPython
& $workerPython -B scripts/distributed_worker.py export --worker 1
```

Use `--worker 0` on machine-1. Transfer only the resulting
`.verification/distributed/worker-01.tar.gz` (or `worker-00.tar.gz`), never raw
logs, the `.verification` directory, or personal tool installations. Archives
have normalized metadata, privacy-screened objects, whitelisted receipts, and
axiom evidence. Each archive is capped at 512 MiB; an oversized export fails
without replacing an earlier archive.

Place received archives in machine-1's `.verification/distributed/incoming/`.
Use only archives produced by this verifier at the agreed revision on the
participating machines or the approved Actions run. Matching hashes establish
integrity and compatibility; they do not authenticate who ran the compiler.
With all local verifiers idle, import each archive and eventually run the full
collector check from the same scoped PowerShell session:

```powershell
& $workerPython -B scripts/distributed_worker.py import --archive .verification/distributed/incoming/worker-01.tar.gz
& $workerPython -B scripts/distributed_worker.py final --max-parallel 2
```

Import validates the complete archive before publication and preserves backups
of any explicitly interrupted evidence it replaces. Accepted conflicting
evidence is refused. The collector reuses only current matching evidence,
checks all remaining modules, and runs the unchanged strict dependency and
axiom audit. Only its `OPTIMALITY_PROVED` status establishes completion.
Changes to source or configuration require an explicitly regenerated common
plan; do not independently regenerate it on each machine.

The separate `Explicit distributed Windows replay` workflow starts only from
an approved launch request. A change to `.github/distributed-launch.json` on
the designated handoff branch binds a pilot or fleet request to the exact
plan digest; ordinary tooling pushes do not launch it. The pilot runs one
hosted worker. Launching all sixteen requires a separate fleet request.
Hosted setup checks for sufficient disk space before downloading prerequisites.
Only sanitized archives are uploaded, with one-day retention and a maximum
of 512 MiB per worker (8 GiB for sixteen). Artifact storage can incur charges.
No launch request or GitHub upload is implied by local setup or verification.

Install Git, Python 3.11 or newer, and Lean's `elan` launcher. The project pins
Lean `v4.34.1` and
mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Keep `lake-manifest.json`; do not update dependencies while reproducing this
snapshot.

Restore the pinned generated certificate sources, set up the public dependencies,
then compile the main dependency chain serially and inspect its target axioms:

```sh
python3 scripts/verify.py --setup
```

`--setup` restores the pinned generated sources before checking imports. To
restore only those sources, use `python3 scripts/materialize_wand125.py`;
matching existing files require no download.

For every included source module, including progress outside the main chain:

```sh
python3 scripts/verify.py --setup --all
```

To check only the final theorem's dependency closure and its component axiom
queries, use the focused audit:

```sh
python3 scripts/verify.py --module ElevenSquare.ProofAudit --keep-going
```

This target has not yet earned complete native compiler and axiom acceptance.
A focused result does not establish that every optional legacy module builds,
and does not satisfy the full-source publication gate.

For a progress display and saved log, run `bash scripts/check_lean.sh`.
It checks all modules and continues through independent failures.

Once dependencies are installed, omit `--setup`. Accepted unchanged modules
can be resumed using the script's source/object/dependency fingerprints. The
checker prioritizes shared dependencies, records transitive input hashes,
and audits every included explicit axiom query. Optional `--max-parallel N`
coordinates independent modules under one checkout lock; `--memory-percent 95`
guards additional starts and retries memory-constrained work alone. Use
`--jobs N` to give each new Lean process `N` worker threads while retaining serial
module checks. Matching accepted receipts keep their actual original thread count
and fingerprints. Extra threads can require more memory; the default remains one.
Use
`--keep-going` to collect independent compatibility failures in one run; it
still rejects any incomplete build. Add
`--fresh` to rebuild every selected local module. These are substantial exact
certificate checks and can take a long time. They use ordinary Lean checking;
no packing search or external algebra system is required.

A source-only check, requiring only Python3, is:

```sh
python3 scripts/check_sources.py
```

`--plan` on the verifier prints the compilation order without running Lean.
Build logs and objects remain in ignored `.verification/` and `.lake/` folders.
The normal Lake entry point is also available via `lake build`.

An optional, manually triggered `Bounded wand125 replay` GitHub Actions workflow
is available. Integration checks currently run locally; pushing the branch does
not start this workflow. Sixteen public standard runners check independent module groups, then
a final job runs the same full verifier and completion audit. Bounded caches
preserve accepted work between runs; an interrupted or incomplete replay remains
a failed check. This workflow does not publish verification evidence or merge
the branch. Local verification remains available through the commands above.

With an empty admission inventory, every queried target may use only `propext`,
`Classical.choice`, and `Quot.sound`. Source restoration and an admission-free
source scan do not establish proof acceptance. Before publishing completion,
finish the full replay and validate every current receipt. Unchanged local
checkpoints are reused only after their fingerprints and compiled objects match:

```sh
python3 scripts/verify.py --all --keep-going
python3 scripts/finalize_verification.py
```

Use the finalizer's `--write` only after all final source and documentation edits
and the complete replay have passed. A selected-module result cannot satisfy it.
If the fresh replay is interrupted, resume with
`python3 scripts/verify.py --all --keep-going`, omitting `--fresh` so matching
accepted receipts can be reused. The verifier still checks their current source,
configuration, objects, and transitive dependency fingerprints; finalization
still requires the complete supported source tree and clean axiom evidence.

## Upstream proof integration

The source now wires wand125's 1,904 field and 27 generic exclusions into all
1,931 native baseline indices, all 76 prior exclusions, and all 173 returned
exclusions, including case1465. The returned family uses the separately pinned
upstream revision `8126ef4d5ce0ecc967d7223388bac65ee5ffce5e`. The integrated U5
extended traces supply the case438 certificate from the genuine closed-cell seed
through the far branches and final near-state inclusion. The public packing
definitions and theorem statements are preserved.

The complete F04 bundled pilot has now been reproduced: all 23 modules and
1,771 axiom queries passed, with an axiom map identical to the historical pilot.
Current source, object, configuration, and dependency receipts were checked;
the portable result is `verification/wand125-bundled-field04-reproduction.json`.
The baseline adapter and upstream axiom query now use the bundled field theorem.
Replay of the complete baseline/prior paths and final-theorem closure is next,
as described in [NEXT_COMPUTER.md](NEXT_COMPUTER.md).
Independent native group proofs remain available as optional progress.
**All complete-family and case438 paths remain compiler-unverified until full
replay and axiom auditing finish.** See the
[integration details](integrations/wand125/README.md) and
[pinned release restoration instructions](integrations/wand125/release/README.md).

The earlier four-field integration checked 247 additional baseline exclusions
and their disjointness from the completed native groups, with only the standard
axioms. Its focused 180-module replay is recorded in
`verification/wand125-integration.json`; that historical result does not certify
the expanded generated sources or full-project toolchain migration.

The expanded release's representative generic case220 and prior case221 passed
a 47-module replay, and the conditional family adapters passed a 62-module replay.
Their clean axiom audits are recorded in `verification/wand125-release-pilots.json`
and `verification/wand125-family-core.json`. These focused checks do not certify
the complete families.

Three admitted private T01 plan-construction claims were retired as an unused
alternative route. Their requirement types and all completed native group proofs
remain; the abandoned plan obligations were not proved.

## Assembly provenance

The source incorporates the baseline partial return, the checked prior-support
continuation, the local-packet return, the complete returned-family source wiring,
and the U5 case438 extension. It also
preserves the previously integrated fixes to the overlay and D4 bridge from the
earlier current-work return. The two-file near-state compatibility fix from
`1d3b648` is also integrated, preserving the existing theorem statements; its
current dependency closure still needs replay. Older unreferenced speculative
modules are omitted; all delivered Lean modules and their local source dependencies
are preserved.

`verification/source-inventory.json` records exact source hashes and which files
match supplied compiler inventories. `verification/imported-audits.json` retains
only mathematical declaration names and their reported axiom sets. It is
historical evidence, not a fresh combined compiler replay. In particular, a
reported inherited admission may have been removed by another merged return.

Earlier assembly checks and imported compiler inventories are historical
evidence. The current expanded source requires its own complete import-closure
check, compiler replay, and axiom audit. The numerical certificate collection is
supplied through pinned release restoration for that reproducible replay.

Only portable source, pinned public dependency metadata, mathematical audit
summaries, and fresh documentation are distributed. Original handoff archives,
conversation records, machine diagnostics, private project identifiers, and
historical machine-specific logs are omitted.
