# Full-stage T07 benchmark

These frozen P2/S135 fixtures retain all 38 input rows, 74 output rows, 76
subrows, and the two owned hulls read by the complete pruning check. Each checks
the original `step_ok` proposition in its original five blocks of eight rows.
Literal and compact versions have identical context, imports, and theorem
suffixes; only certificate declarations differ. `manifest.json` preserves the
original source/context hashes and exact reconstruction counts.

After separately verifying the four checker helpers with `scripts/verify.py`
and preparing their imported dependencies, run from the repository root:

```sh
python3 scripts/benchmark_t07_stage.py --plan-only
python3 scripts/benchmark_t07_stage.py
```

The default is eight serial checks: literal and compact certificates with the
original and integer-convexity checkers, each repeated twice in mirrored order.
Every condition imports the same four modules. The integer variant changes only
the final tactic, using the proved `RuntimeCheck.rowCheck_eq` equivalence before
kernel checking. Each check is bounded to 300 seconds; the entire run is bounded
to 2,500 seconds. Use `--keep-going` to collect remaining conditions after a
timeout or failed check. There is no package setup, build, or object-file write.
For an initial four-check scout, use `--repeats 1`; a single observation per
condition is not evidence of a reproducible speedup.

Results, exact input hashes, wall time, child CPU time, compiler identity, and
helper verification receipts are recorded in
`.verification/t07-stage-benchmark.json`. Ctrl-C terminates and reaps the active
compiler and saves an incomplete report. Run this benchmark when other Lean
checks have finished to avoid memory pressure and timing interference.

This is one complete pruning step, not its promotion theorem or preceding state
history. The fixtures omit only state entries that the check cannot read; their
provenance records this scope. Acceptance and timings do not establish full-proof
verification or a two-to-three-hour build estimate.

## Optional least-common-denominator trial

After separately verifying `ElevenSquare.Tasks.T07.Ext.IntegerConvexLcm`, run:

```sh
python3 scripts/benchmark_t07_stage.py --lcm-only
```

This uses literal certificates only and compares the original checker with LCM
integer convexity in four serial, mirrored trials. Both conditions import the
same five modules and elaborate the same small checker configuration and its
equivalence proof. Only the final tactic changes. The mode checks the LCM
source/object verification receipt and writes a separate
`.verification/t07-stage-lcm-benchmark.json`; existing default benchmark results
are not overwritten. It remains an experiment, not an active-proof change.
