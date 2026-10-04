# T07 kernel runtime benchmarks

These three finite, real sub-rows compare checker implementations without
loading their full generated stage histories. Each fixture retains every
original context entry read by its check. Unused entries are empty placeholders.
`manifest.json` records the original certificate, source and context SHA-256
hashes, and the exact fixture hash.

The fixtures contain definitions only. The runner gives every timed trial the
same imports and data declarations, then asks Lean's kernel to check one full
sub-row using `RuntimeCheck.original`, `fastSum`, `integerConvex`, or `combined`.
The runtime variants have proved equality to the original checker.

Prepare the dependencies separately:

```sh
python3 scripts/verify.py \
  --module ElevenSquare.Tasks.T07.Ext.RuntimeCheck \
  --module ElevenSquare.Tasks.T07.Ext.CompactWitness --jobs 1
```

Run from the repository using Python 3 on macOS or Linux:

```sh
python3 scripts/benchmark_t07.py
```

The default is **24 trials**: three fixtures, four checker configurations and
two repetitions, using the original literal certificates. Conditions and
fixtures follow a fixed order that reverses on alternate repetitions. The
runner records each trial's wall time, child user/system CPU time, source hash,
result and compiler diagnostics. It reports medians only alongside the actual
accepted repetition count. Timings include fresh-process startup, identical
imports, data parsing/elaboration and the kernel check; operating-system caches
are not reset.

Useful options:

```sh
# Inspect all trial conditions without starting Lean.
python3 scripts/benchmark_t07.py --plan-only

# Compare both original literals and reconstructed witnesses: 48 trials.
python3 scripts/benchmark_t07.py --include-compact

# Start with only the smallest real fixture.
python3 scripts/benchmark_t07.py --cases Small --timeout 120
```

The default result is `.verification/t07-benchmark.json`. The runner verifies
compiled-helper receipts first. It runs one Lean process at a time, requests no
`.olean` output, performs no builds or downloads, enforces per-trial and total
time limits, and terminates/reaps its child on interruption. Failed or incomplete
runs are reported as such. Full proof replay remains separate: these timings do
**not** establish a two-to-three-hour build time for the complete proof.
