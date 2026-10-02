# Stronger-computer handoff — WIP

Handoff branch: `codex/stronger-computer-handoff-20261002`, based on `e69ba84`.
This saves unfinished work; it does **not** establish the packing theorem or a
completed Lean upgrade. Continue toward the native `ElevenSquare.ProofAudit`
goal, preserving its public statements and ordinary kernel checking.

## Start on the new machine

Install Git, Python 3.11 or newer, and Lean's `elan` launcher. Allow generous
disk headroom: the old checkout already occupied about 9.6 GB before all bundles
and remaining collaborator certificates were installed; 30 GB free is a useful
starting budget, not a measured upper bound. Then:

```sh
git clone --branch codex/stronger-computer-handoff-20261002 https://github.com/Queuingtheorydotcom/11SquaresFormalized.git
cd 11SquaresFormalized
python3 scripts/verify.py --setup --module Sqpack.S11Opt.Bundled.F04.Final
```

Keep `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json` unchanged:
Lean **4.34.1**, mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612**.
Do not run `lake update` or migrate dependencies during reproduction.

`--setup` restores authenticated public release sources, generates all baseline
bundles, installs the pinned toolchain, fetches the dependency cache, and runs
the selected check. Source generation is not proof acceptance. For restoration
without compilation, use `python3 scripts/materialize_wand125.py`.
Restoration can be resumed; conflicting existing files are rejected.

Ignored `.lake`, `.verification`, generated sources, archives, and local receipts
are not pushed and are not needed from the old computer. Public pins regenerate
sources. New-machine compiler receipts must be earned again. Use one verifier
per checkout: the current scripts are serial, with shared output/receipt files.
More cores do not make concurrent verifiers in the same checkout safe.

## Checkpoints and first integration step

- Original baseline replay `v52` stopped safely at **128/2,985**, without a
  failure. Neither the full baseline nor full prior family has acceptance.
- Ordinary source-grouping pilots passed exact original proposition checks and
  standard-axiom checks: F37 took 162.53s versus 439.79s across originals; F04
  coverage took 67.62s versus 190.49s for its leaves (300.43s with aggregators).
  These small measurements do not predict the whole replay.
- **Production F04 pilot accepted: 23/23 modules and 1,771 axiom queries**, all
  using only the standard axioms. This includes all three ownership leaf bundles,
  the exact original registry-membership contract, and the complete F04 Final.
  The portable result is `verification/wand125-bundled-field04-pilot.json`.
  The old-machine run exited successfully; no compiler or continuation remains
  running. This is a complete field pilot, not the full baseline family.
- **51 Python tests passed** (42 bundle tests, 9 raw-source tests). The helpers
  authenticate inputs, preserve original declaration bodies, and add explicit
  contract checks. This does not replace Lean acceptance.
- All F01–F58 derived coverage sources have **not** been materialized locally.
  Planned output: **617 coverage modules / 89,336 declarations**, plus three
  ownership leaf batches covering **134 points**. F00 and original computational
  data remain unchanged. The assembly/ownership helpers and automatic setup
  integration are ready.

**Native Baseline has not been switched to the bundled route.** First reproduce
`Sqpack.S11Opt.Bundled.F04.Final`, including its ownership dependencies and
contract/axiom checks. Then make only these initial adapter changes:

1. In `ElevenSquare/Interop/Wand125/Families/Baseline.lean`, change the UField
   import to `Sqpack.S11Opt.Bundled.Split.UField` and both field proof arguments
   to `SquarePacking.S11Opt.Bundled.Split.field_excluded`.
2. In `ElevenSquare/Verification.lean`, change the corresponding upstream
   `#print axioms` query to that bundled theorem. Preserve all native certificate
   and exclusion signatures and the generic-family argument.
3. Check the main agent's baseline/prior work first, then the final-theorem
   closure as collaborators' changes arrive:

```sh
python3 scripts/verify.py --module ElevenSquare.Pending.S06_Baseline \
  --module ElevenSquare.Pending.S06_PriorSupport --keep-going
python3 scripts/verify.py --module ElevenSquare.ProofAudit --keep-going
```

Inspect actual failures and axiom reports. Do not claim success because source
generation, a pilot, or an admitted theorem compiles. Defer optional legacy
repairs unless needed by this closure; `--all` includes substantial extra work.

## Remaining obligations and ownership

Two source admissions remain: `Pending/S06_Returned.lean` and
`Tasks/T07/UnfinishedCapture.lean` under `ElevenSquare/`. Baseline/prior source
wiring also still requires complete kernel replay. The three retired private
T01 alternative-plan existence claims were replaced by explicit requirement
types; they were **not proved**.

T03 is untouched. Its latest checkpoint is `16cebf4`: case-1465 prefix-40 audits
on old Lean 4.10 and 172/173 individual certificates, not a complete case-1465
proof or an accepted aggregate on the current toolchain. A separate human owns
returned-172 work. Dot 1 owns U5/PR4 integration; Dot 2 has T06 reserved.
Tiny/Little ownership mapping is unknown: resolve it before overlapping edits.

Commit `dbf2eef` preserves roughly 240 older, unverified compatibility drafts,
separate from the bundling work. Review actual diffs and coordinate ownership;
do not blindly merge them over collaborators' work. Keep original pinned proof
sources and verified progress. No invented proofs, admissions, custom axioms,
or unchecked computational shortcuts.

Run checks locally; do not start GitHub Actions or browser automation. Keep this
checkpoint on its branch. Final completion requires no source admissions and
clean transitive axiom reports for `global_lower_bound`,
`optimal_side_lower_bound`, and `optimality`. Preserve the full supported-source
replay and `scripts/finalize_verification.py` publication requirements before
merging to `main`; a focused pilot does not satisfy them. Do not force-push.
This handoff ends work on the old machine.
