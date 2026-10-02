# Continuation checkpoint — replay pending

Handoff branch: `codex/stronger-computer-handoff-20261002`, originally based on
`e69ba84`. The local continuation now supplies proof bodies for both former
admissions: returned173 and U5 case438 capture. The admission inventory is empty.
**Full native compiler and axiom acceptance is still pending.** Continue toward
`ElevenSquare.ProofAudit`, preserving public statements and kernel checking.
The current F04 bundled pilot has passed, and the native baseline adapter now
uses the bundled field theorem. Complete baseline/prior replay is the next step.

## Start on the new machine

Install Git, Python 3.11 or newer, and Lean's `elan` launcher. Allow substantial
disk headroom for generated sources, dependencies, and compiler objects. From
the checkout containing this continuation, reproduce the scoped F04 checkpoint:

```sh
python3 scripts/verify.py --setup --module Sqpack.S11Opt.Bundled.F04.Final
```

Keep `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json` unchanged:
Lean **4.34.1**, mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612**.
Do not run `lake update` or migrate dependencies during reproduction.

`--setup` restores authenticated F, FCOMMON, U2G, U2P, U2R, and U5 sources,
generates baseline bundles, installs the pinned toolchain, fetches the dependency cache, and runs
the selected check. Source generation is not proof acceptance. For restoration
without compilation, use `python3 scripts/materialize_wand125.py`.
Restoration can be resumed; conflicting existing files are rejected.
Preserve LF source bytes as required by `.gitattributes`; do not relax pinned
hashes to accommodate line-ending changes.

Ignored `.lake`, `.verification`, generated sources, archives, and local receipts
are not pushed and are not needed from the old computer. Public pins regenerate
sources. New-machine compiler receipts must be earned again. Use one verifier
per checkout: the current scripts are serial, with shared output/receipt files.
More cores do not make concurrent verifiers in the same checkout safe.
Optional `--jobs N` gives each new Lean process `N` worker threads without
concurrent module checks. Matching accepted receipts retain their actual original
worker count and fingerprints, and every other compiler flag remains fixed.
The default is one; additional threads can require more memory. The worker-count
and receipt changes passed 34 focused Python tests and independent review, but
this does not measure their speed or replace Lean acceptance.

## Historical checkpoints and current acceptance

- Original baseline replay `v52` stopped safely at **128/2,985**, without a
  failure. Neither the full baseline nor full prior family has acceptance.
- Ordinary source-grouping pilots passed exact original proposition checks and
  standard-axiom checks: F37 took 162.53s versus 439.79s across originals; F04
  coverage took 67.62s versus 190.49s for its leaves (300.43s with aggregators).
  These small measurements do not predict the whole replay.
- **Historical production F04 pilot accepted: 23/23 modules and 1,771 axiom queries**, all
  using only the standard axioms. This includes all three ownership leaf bundles,
  the exact original registry-membership contract, and the complete F04 Final.
  The portable result is `verification/wand125-bundled-field04-pilot.json`.
  This historical result covers a complete field pilot, not the full baseline family.
- **The current F04 reproduction also passed: 23/23 modules and 1,771 axiom
  queries**, with exactly the historical axiom map. Current source, configuration,
  object, transitive dependency, and axiom evidence were revalidated. Its portable
  result is `verification/wand125-bundled-field04-reproduction.json`. It establishes
  the F04 pilot and shared ownership dependencies only; complete baseline and
  global theorem replay remain pending.
- **The historical bundle checkpoint passed 51 Python tests** (42 bundle tests,
  9 raw-source tests). The helpers
  authenticate inputs, preserve original declaration bodies, and add explicit
  contract checks. This does not replace Lean acceptance.
- The F01–F58 derivation produces **617 coverage modules / 89,336 declarations**,
  plus three
  ownership leaf batches covering **134 points**. F00 and original computational
  data remain unchanged. The assembly/ownership helpers and automatic setup
  integration are ready.

**Native Baseline now uses the bundled route.**
`ElevenSquare/Interop/Wand125/Families/Baseline.lean` imports
`Sqpack.S11Opt.Bundled.Split.UField`, and both field proof arguments use
`SquarePacking.S11Opt.Bundled.Split.field_excluded`.
`ElevenSquare/Verification.lean` queries that bundled theorem. Native certificate
and exclusion signatures and the generic-family argument remain unchanged.
These adapter changes still need current compiler and axiom acceptance.

Check baseline/prior first, then the final-theorem closure with the integrated
returned173 and U5 sources:

```sh
python3 scripts/verify.py --module ElevenSquare.Pending.S06_Baseline \
  --module ElevenSquare.Pending.S06_PriorSupport --keep-going
python3 scripts/verify.py --module ElevenSquare.ProofAudit --keep-going
```

Inspect actual failures and axiom reports. Do not claim success because source
generation, a pilot, or an admitted theorem compiles. Defer optional legacy
repairs unless needed by this closure; `--all` includes substantial extra work.

## T06 return integrated on October 2

T06 return `68818f523c83925f164be32ea3932bc60a7120d7` is included
on this handoff branch. It ports all 128 integer certificate shards, adds the
two public axiom queries in `ElevenSquare.Tasks.T06.LocalIsolationAudit`, and
preserves all 8,448 numerical checks and the original public statements.

The supplied Linux Lean 4.34.1 evidence reports an accepted 833-module packet
and 834-module public audit, with only the standard three axioms. At integration,
all 834 source hashes matched the supplied inventory; 18 preservation tests and
the full T06 preservation checker passed. The reported compiler run was resumed
with validated fingerprints, not a single fresh replay. See
`verification/t06-local-isolation.md`, its JSON evidence, and
`verification/t06-local-isolation-integration.json` for provenance.

After setup on the new machine, reproduce this selected closure:

```sh
python3 -m unittest discover -s scripts -p 'test_check_t06_preservation.py' -v
python3 scripts/check_t06_preservation.py
python3 scripts/verify.py --module ElevenSquare.Tasks.T06.LocalIsolationAudit --keep-going
```

The returned `CertificateInteger087.lean` supersedes the older unverified draft
saved in `dbf2eef`; that draft remains in Git history. This scoped T06 result
does not complete baseline/prior replay or the global theorem.

## Integrated sources and remaining acceptance

`Pending/S06_Returned.lean` now uses the complete returned family at
`8126ef4d5ce0ecc967d7223388bac65ee5ffce5e`, including case1465. U2R metadata is
pinned separately from the original field/generic/prior release snapshot.
`Tasks/T07/UnfinishedCapture.lean` now uses the U5 extension from
`2b539e977c9e5daf2a68cb896c2acc1a21d49e39`, including the genuine seed ancestry,
far branches, and near-state inclusion. Do not restore either admitted body or
the old 172-case exception. All complete native dependency paths still require
compiler and transitive axiom acceptance.

The two-file near-state compatibility fix from `1d3b648` is integrated exactly
in `LocalAnglePacket.lean` and `NearStateBridge.lean`. It handles contradictory
owner cases explicitly and simplifies the near-field box instances while
preserving theorem statements. Its current 77-module dependency closure passed
compiler checking and 47 standard-axiom queries. The independent current-receipt
audit is `verification/near-state-bridge-reproduction.json`. The subsequent
`NearStateRectangle` handoff also passed its 78-module closure, recorded in
`verification/near-state-rectangle-reproduction.json`. Complete case438 capture
and final-theorem acceptance remain pending.

Existing native T03 progress remains preserved. The three retired private T01
alternative-plan existence claims remain requirement types; they were not
proved. Historical snapshots and partial progress retain their identities.

Commit `dbf2eef` preserves roughly 240 older, unverified compatibility drafts,
separate from the bundling work. Review actual diffs and coordinate ownership;
do not blindly merge them over collaborators' work. Keep original pinned proof
sources and verified progress. No invented proofs, admissions, custom axioms,
or unchecked computational shortcuts.

After all final source and documentation edits, complete the full fresh replay:

```sh
python3 scripts/verify.py --all --fresh --keep-going
python3 scripts/finalize_verification.py
```

If the fresh replay is interrupted, resume it with
`python3 scripts/verify.py --all --keep-going`, without `--fresh`. Matching
accepted receipts retain their recorded compiler arguments and must still pass
current source, configuration, object, and transitive dependency checks. A new
`--fresh` run deliberately rebuilds accepted work; an interruption alone does
not require that restart. The full-source and axiom gates remain unchanged.

Every queried target must use only `propext`, `Classical.choice`, and
`Quot.sound`, including `global_lower_bound`, `optimal_side_lower_bound`, and
`optimality`. Publish evidence with the finalizer's `--write` only after it
validates current complete receipts. A focused pilot does not satisfy the full
supported-source publication gate.

Run checks locally. GitHub writes, workflow dispatch, and merging require
explicit user approval. Do not force-push. Keep machine-specific logs and
private information outside tracked source and documentation.
