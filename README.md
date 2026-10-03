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

See [the step-by-step RHEL 9.6 / Slurm guide](LEAN_VERIFICATION_RUNBOOK.md)
for setup from a fresh account, submission, monitoring, resuming, and outputs.
Verification runs directly under your account. See [SECURITY.md](SECURITY.md)
for the execution boundary. Python 3.11+, Git, curl and Lean's `elan` launcher
are required; there are no third-party Python packages. Lean `v4.34.1` and
mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` are pinned.
Keep `lean-toolchain` and `lake-manifest.json`; do not run `lake update`.

For a node with approximately 200 allocated CPUs and 1,400 GiB RAM:

```sh
mkdir -p .verification
export ELEVEN_SQUARE_PYTHON=python3.11
sbatch --account YOUR_ACCOUNT --partition YOUR_PARTITION scripts/run_single_node_verification.sbatch
```

The supplied job requests 200 CPUs, 1,300 GiB RAM and three days. It restores
pinned generated sources, installs the pinned Lean toolchain and dependency
cache, checks all local modules with up to 100 concurrent compiler processes
and two threads per new process, audits axioms, and finalizes evidence only
after full success. These resource settings are initial choices, not measured
requirements. The verifier's memory guard is advisory. Override concurrency
with `ELEVEN_SQUARE_MAX_PARALLEL`, `ELEVEN_SQUARE_JOBS` and
`ELEVEN_SQUARE_MEMORY_PERCENT`; adjust them if requesting a smaller allocation.

Outside Slurm, the equivalent replay command is:

```sh
python3.11 -u scripts/verify.py --setup --all --keep-going --max-parallel 100 --jobs 2 --memory-percent 85
```

`--setup` both prepares dependencies and starts verification. To restore only
original sources and derived baseline bundles, use
`python3.11 scripts/materialize_wand125.py`.

Progress appears as `[module-position/total] started|accepted|cached|failed|blocked`
lines. Parallel completions can arrive out of order; the position is not a
completed-module count. There is no graphical progress bar or reliable time
estimate. Compiler diagnostics are saved in `.verification/MODULE.log`.

Accepted modules are saved with source, object, compiler, configuration and
transitive local dependency fingerprints. To resume after interruption, retain
the same checkout including `.verification/` and `.lake/`, then resubmit with
`ELEVEN_SQUARE_SETUP=0` once setup has completed. Do not use `--fresh` on resume.
Unfinished modules restart from their beginnings; Lean does not checkpoint
within an individual module. The job uses `--stop-file .verification/STOP`:
create that file to stop launching new checks and finish active checks, then
remove it before resubmitting. A hard allocation cutoff still loses active
module work. Only one verifier may own a checkout at a time.

For a serial replay, use `python3.11 scripts/verify.py --setup --all --keep-going`.
The optional `scripts/check_lean.sh` serial wrapper requires a Python 3.11+
`python3` on PATH and saves a combined log. `--module ElevenSquare.ProofAudit`
checks only the final theorem's closure; selected-module acceptance does not
satisfy the full-source publication gate. `--plan` prints dependency order
without running Lean, and `scripts/check_sources.py` performs a source-only check.

Successful full verification writes `.verification/result.json`. The job then
runs `scripts/finalize_verification.py --write`, validates current receipts and
axiom logs, updates `verification/wand125-upgrade.json`,
`verification/source-check.json` and `MANIFEST.json`, and writes a compact
`.verification/completion-JOB_ID.json`. That receipt must report
`OPTIMALITY_PROVED`, with `global_optimality_proved` and
`full_upgrade_verified` true. It summarizes the audit and its hashes; it is not
a standalone proof certificate. The step-by-step guide includes a
machine-readable completion check and instructions for compilation failures.

An optional manually triggered `Bounded wand125 replay` GitHub Actions workflow
also exists. Pushing does not trigger it. Full native verification remains
pending until a complete replay and the finalizer pass. An admission-free
source scan alone does not establish proof acceptance. Use `--fresh` only when
intentionally discarding accepted local checkpoints for a new replay.

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
