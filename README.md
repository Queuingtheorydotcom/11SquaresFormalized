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

For untrusted inputs, use the reviewed host launcher, which automatically builds
and runs an isolated image through **local rootless Docker**. Python 3.11+, Git,
and an installed, cluster-approved Docker daemon with cgroup v2 and the systemd
cgroup driver are required on the host. The launcher installs Lean and other
proof dependencies inside its private volume; no host Lean or pip packages are
needed. Commit all intended changes first; the launcher verifies a clean HEAD
snapshot. For the 200-core, 1,400-GiB node:

```sh
python3 -I scripts/verify_container.py all --cpus 200 --memory 1300g --max-parallel 100 --jobs 2 --memory-percent 85
```

Preparation uses networking once, on a newly created volume, and executes only
the reviewed bootstrap and pinned official dependencies. Repository Python,
Lake configuration and Lean code execute only in the subsequent offline stage.
There are no host bind mounts or daemon sockets. Restrictions are probed before
each stage; a missing restriction is a failure, with no host execution fallback.
See [SECURITY.md](SECURITY.md) for the trust boundary and remaining limitations.
The Docker runtime has not yet been tested on the target cluster.

Rerunning `all` with the same snapshot resumes **offline**. A failed preparation
requires a fresh name, supplied with `--volume eleven-square-attempt2`; reuse
that name for later resumes and reports. The persistent private volume contains
all restored sources, dependencies, logs and objects. Export only a fixed report:

```sh
python3 -I scripts/verify_container.py report --report completion.json > ../completion.json
```

On Slurm, create the log directory before submission:

```sh
mkdir -p .verification
sbatch --account YOUR_ACCOUNT --partition YOUR_PARTITION scripts/run_single_node_verification.sbatch
```

The example runs the Docker launcher automatically. The site must permit rootless
Docker and account for its daemon/containers within the job allocation. A CPU
affinity restriction and explicit container limits supplement the Slurm request;
they do not configure site accounting. The concurrency ceiling is an initial
setting, not a measured optimum. Containers share the host kernel, and workspace
disk use is not capped. A disposable VM and dedicated storage offer a stronger
boundary. Review these bootstrap scripts before running them on a sensitive host.

The example requests three days of wall time and exports a compact JSON receipt
to `.verification/completion-JOB_ID.json` after success. On RHEL 9.6, use an
installed Python 3.11+ explicitly: export `ELEVEN_SQUARE_PYTHON=python3.11` before
submission. Export `ELEVEN_SQUARE_START_USER_DOCKER=1` only when your site permits
starting the installed systemd user Docker service on the allocated node; otherwise
the site's daemon startup must already be in place. The example selects the
`rootless` Docker context, or `ELEVEN_SQUARE_DOCKER_CONTEXT` if set. For a fresh
attempt or named resume, set `ELEVEN_SQUARE_VOLUME` before submission. A daemon-owned
preparation marker and leftover-container checks also protect interrupted launches.

The following raw verifier commands describe operation **inside an independently
isolated environment**. `scripts/verify.py` itself remains unsandboxed.

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
serial checker prioritizes shared dependencies, records transitive input hashes,
and audits every included explicit axiom query. Use
`--jobs N` to give each new Lean process `N` worker threads while retaining serial
module checks by default. For concurrent independent modules on one node, use
`--max-parallel N`; `--jobs` sets threads per compiler process. For a node with
about 200 allocated cores and 1,400 GiB RAM, an initial configuration is:

```sh
python3 scripts/verify.py --setup --all --keep-going --max-parallel 100 --jobs 2 --memory-percent 85
```

This is an initial concurrency ceiling, not a measured optimum. The scheduler
waits for accepted dependencies, checks memory headroom before launching extra
processes, and retries auxiliary checks alone after memory pressure. Its memory
guard is advisory rather than an enforced allocation limit. Measure throughput
and peak memory before increasing concurrency. One verifier owns the checkout;
no distributed sharding is required. The final axiom audit and result artifacts
remain part of the same run. Matching accepted receipts keep their actual original thread count
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
finish the full fresh replay and validate its current receipts:

```sh
python3 scripts/verify.py --all --fresh --keep-going
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
