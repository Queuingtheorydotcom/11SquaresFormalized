# Further simplification from the n=11 review

Reference: [jlevy/squares issue 317](https://github.com/jlevy/squares/issues/317).
This branch remains an **unverified assembled source candidate**. The full final
verification target has not been run on this checkpoint.

The refreshed closure is **365,392 lines in 4,257 modules**, compared with the
prior 394,204 lines / 6,326 modules: **28,812 lines and 2,069 modules removed**.
The 300,000-line target has not been reached.

## Implemented reductions

- Four collision pairs use exact rational coordinate boxes. Thirty-two
  nonnegative combinations of original closed-cell halfplanes establish those
  boxes; a shared distance lemma yields the same strict distance bounds. The
  finite assignment checker and public conclusions are retained.
- Label, view and mask data are separated from historical overlay vertices and
  banned-pair tables. Existing historical modules reexport moved declarations.
- The common local cone shares indexed fixed-row and parallel-row proofs. Its
  40 rows and 66 dual certificates are unchanged.
- Conditional coverage uses indexed triangle/target tables across 267 cases,
  retaining every original literal and checking all consumer indices. This saves
  14,991 lines; removing 652 redundant root aliases saves another 1,304 while
  preserving public propositions and certificate proof bodies.
- Bundled field certificates share option-disjunction and checked-majority
  arguments. All 187 cover calls and 147 majority certificates retain their
  geometric premises and finite checks.
- Module bundling removes **1,301 T07 modules and 731 Sqpack modules** from the
  final theorem closure. All 26,033 moved T07 declaration blocks remain intact.
  Exact inverse ledgers preserve earlier source audits across these moves.
  Compatibility reexports retain the old import paths. A cold theorem replay
  avoids **2,032 module launches**; the remaining net module reduction comes from
  dependency pruning. The optional `--all` audit still includes the reexports.

## Excluded T07 witness experiment

Compact recipes reconstruct planar multiplier vectors from one or two supporting
facets, but this experiment is **not in the active proof**. The complete S135
scout measured 54.126 CPU seconds for original literals and 132.407 for compact
recipes. These are single observations, not a general speed ratio. S137's
original literal certificate and consumer inputs were restored, and all module
mergers remain.

The prior compact-certificate receipt is preserved as historical experimental
evidence. The new bundling ledger records its exclusion and reconstructs the
active literal sources exactly. All four conditions in the S135 pruning
benchmark fixtures passed Lean. Runtime-checker helper lemmas and the LCM helper
have focused acceptance, but the LCM runtime comparison was not run and the
prototype is not enabled. No complete-build runtime or 2–3 hour completion claim
follows from these experiments.

## Scope of verification

The common cone, branch cone, collision helpers and bundled adapters have focused
Lean evidence. The selected `P2.S0` / `P2.S1` replay was stopped cleanly because of
low disk space and heavy swapping. Dependencies through `S1D` passed; `S0` was
not accepted and `S1` was not attempted. No complete merged-stage kernel pass is
claimed. Source audits pass, and verifier/compiler processes are stopped. Further
Lean work belongs on the larger computer; the S135 fixture results do not certify
the assembled production stage or complete theorem.

Run `python3 scripts/verify.py --jobs 1` to check `ElevenSquare.Verification`,
its dependency closure and the final public axiom audit. The broader `--all`
plus finalizer workflow is an **optional entire-repository audit**; it retains
historical-module startup costs. See [PC_RESUME.md](../PC_RESUME.md).

Physical counts include every local source in the `ElevenSquare.Optimality`
import closure, including certificate data, and exclude fixed Lean/Mathlib
sources. Reproduce them with `python3 scripts/simplification_census.py`.

## Existing mathematical structure retained

The active route already uses 44 selected fields, the majority/ten-hull capacity
argument, the weighted-residual local estimate and the smaller endpoint
polynomial argument. It retains the reduced system of 66 dual certificates.

The current closed-interval checker tests both ends of a covering interval,
including the lower end for a singleton target. The pose-state transitions retain
both closed split branches. These source comparisons do not replace replay, and
no new Taylor-bound proposal is part of this checkpoint.
