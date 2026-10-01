# Eleven-square packing in Lean

This repository assembles the completed foundations and the available partial
formalizations of the optimal eleven-square packing. **Global optimality is
still unfinished.** Two explicit `sorry` sites remain in source. The newly wired
baseline and prior families still require full compiler and axiom validation;
the smaller source admission count is not a claim of verified proof completion.
See [MISSING.md](MISSING.md).

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
| `ElevenSquare/Optimality.lean` | Final unconditional theorem statements; their proofs currently inherit the listed admissions. |
| `ElevenSquare/Verification.lean` | Axiom queries for completed milestones and unfinished public targets. |

## Verification

Install Git and Lean's `elan` launcher. The project pins Lean `v4.34.1` and
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

For a progress display and saved log, run `bash scripts/check_lean.sh`.
It checks all modules and continues through independent failures.

Once dependencies are installed, omit `--setup`. Accepted unchanged modules
can be resumed using the script's source/object/dependency fingerprints. The
serial checker prioritizes shared dependencies, records transitive input hashes,
and audits every included explicit axiom query. Use
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

The verifier distinguishes clean milestones, which may use only `propext`,
`Classical.choice`, and `Quot.sound`, from the explicit unfinished targets.
Success with the two remaining source admissions is **partial assembly success**,
not a proof of optimality. The newly wired baseline and prior paths must also pass
fresh compiler and axiom checks. Closing the remaining admissions requires a
fresh final audit.

## Upstream proof integration

The source now wires wand125's 1,904 field and 27 generic exclusions into all
1,931 native baseline indices, and all 76 published prior exclusions into the
native prior interface. The public packing definitions and theorem statements
are preserved. **These complete-family dependency paths are compiler-unverified
until full replay and axiom auditing finish.** See the
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
continuation, the local-packet return, and the global partial handoff. It also
preserves the previously integrated fixes to the overlay and D4 bridge from the
earlier current-work return. Older unreferenced speculative modules are omitted;
all delivered Lean modules and their local source dependencies are preserved.

`verification/source-inventory.json` records exact source hashes and which files
match supplied compiler inventories. `verification/imported-audits.json` retains
only mathematical declaration names and their reported axiom sets. It is
historical evidence, not a fresh combined compiler replay. In particular, a
reported inherited admission may have been removed by another merged return.

The assembly was checked for a complete local import closure, exact admission
inventory, matching returned source hashes, and personal information. The small
final composition is checked separately against the existing shared interfaces.
The entire large numerical certificate collection is supplied for reproducible
replay rather than claimed freshly rebuilt during packaging.

Only portable source, pinned public dependency metadata, mathematical audit
summaries, and fresh documentation are distributed. Original handoff archives,
conversation records, machine diagnostics, private project identifiers, and
historical machine-specific logs are omitted.
