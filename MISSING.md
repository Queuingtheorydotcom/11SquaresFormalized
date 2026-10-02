# Remaining verification work

All former source admissions now have proof bodies, and
`verification/admissions.json` has an empty `sites` list. The complete baseline,
prior, returned, and case438 paths are **compiler-unverified pending full
dependency replay and axiom audits**. An empty admission inventory, generated
sources, and successful Python checks do not establish proof completion.

## 1. Baseline source wiring; replay pending

The baseline dispatcher now uses the published 1,904 field and 27 generic
exclusions for all 1,931 native baseline indices. The final dispatcher uses this complete family directly. The previously
completed imported-field and native G003/G004/G007 proofs remain in their own
modules as optional progress. The public `baseline_certificate_exists` and `baseline_excluded` statements are
unchanged, as are the packing, closed cells, masks, and trace semantics.

The adapter now imports `Sqpack.S11Opt.Bundled.Split.UField` and uses
`SquarePacking.S11Opt.Bundled.Split.field_excluded`; the corresponding upstream
axiom query follows that theorem. The prerequisite F04 pilot has been reproduced:
23 modules and 1,771 axiom queries passed with the exact historical axiom map,
and its current source/object/dependency receipts were validated. See
`verification/wand125-bundled-field04-reproduction.json`. This establishes only
the complete F04 pilot and shared ownership dependencies. The bundled dispatcher
and complete native baseline path still require replay and axiom acceptance.

The three old private plan obligations in `PlanData.lean`,
`ProgramCalculations.lean`, and `LeafCalculations.lean` were retired as an unused
alternative construction route. Their files now express the corresponding
requirements as types and predicates, with no supplied inhabitants. Those
obligations were **not proved**; the source instead delegates exclusion to the
independent published family. No completed native proof was deleted.

The native source retains all 188 shared owned-point proofs, uniform wall and
core lemmas, shared Bernstein sign certificates, finished parts of G005, and
partial G070 transitions. Its G003/G004/G007 certificates cover 1,132 cases; the
earlier four-field integration checked 247 additional disjoint cases. These
historical milestones do not validate the expanded complete-family sources.
The optional native G005/G070 route still has unfinished links, preserved as
source progress rather than claimed complete group exclusions.

## 2. Prior-support source wiring; replay pending

`ElevenSquare/Pending/S06_PriorSupport.lean:prior_certificate_exists` now uses
all 76 published owned-hull exclusion sources through
`ElevenSquare/Interop/Wand125/Families/Prior.lean`. Its initialized `VerifiedTrace`
and `Terminal` contract, including the original baseline-exclusion premise, is
unchanged. The imported proof does not use that premise, the final symmetry
bridge, or optimality. Full native compiler and axiom acceptance remains pending.

The native case1000 progress through archived steps0 and1 remains preserved.
That continuation establishes predecessor/self-cut implications, all 64 closed
rows in step1, normalized integer coverage, strict ownership promotion,
preservation of the owner permutation, and transport to the archived outer state.
Its optional archived route still lacks nonterminal steps2–11, linkage of terminal
step12, and the final contradiction. Those missing native steps were not proved;
the new source path uses the independent imported owned-hull construction.

## 3. Returned-family source wiring; replay pending

`ElevenSquare/Pending/S06_Returned.lean:returned_certificate_exists` now uses
`Interop/Wand125/Families/Returned.lean` and the complete upstream dispatcher at
`8126ef4d5ce0ecc967d7223388bac65ee5ffce5e`. The separately pinned U2R metadata
includes all 173 cases, including case1465. The public initialized-terminal-trace
contract and exclusion signature are unchanged. Existing native T03 progress
remains preserved. Full native compiler and axiom acceptance is still pending.

## 4. Case438 capture source wiring; replay pending

`ElevenSquare/Tasks/T07/UnfinishedCapture.lean:case438_near_certificate` now uses
the U5 extension from `2b539e977c9e5daf2a68cb896c2acc1a21d49e39`. Its type remains
the existing `Case438NearCertificate` interface: every centered case438 packing
of side at most `T` admits a representation in the focused local rectangle at
the same physical side length. The public `global_lower_bound` composition and
the unconditional optimality statements are unchanged.

The extended traces begin at `siteSeedFor roleCell`, supply phase 2 and root
ancestry, justify owned-point promotions, eliminate the far branches, and check
final near-row inclusion. Their soundness uses actual packing containment and
disjoint open interiors. The existing strict ownership and closed boundary
semantics remain. All generated U5 nodes and the native composition still need
compiler replay and clean transitive axiom reports.

The two-file near-state compatibility fix from `1d3b648` is integrated in
`LocalAnglePacket.lean` and `NearStateBridge.lean`. It changes proof tactics while
preserving their statements. Its complete 77-module `NearStateBridge` closure
has passed current compiler checking and all 47 axiom queries use only the
standard axioms. The current source, object, configuration, and dependency
receipts were independently revalidated; see
`verification/near-state-bridge-reproduction.json`. This scoped acceptance does
not establish the complete case438 capture or global theorem.
The subsequent `NearStateRectangle` handoff also passed its 78-module closure;
`verification/near-state-rectangle-reproduction.json` records the checked
rectangle representation and preservation of the original physical side bound.

Earlier counterexamples to direct promotion from mere closed-cell occupancy and
simple rowwise near inclusion remain valid obstructions to those shortcuts.
The new extension supplies explicit traces and checked inclusion instead.

## Completed stages to preserve

- Exact construction, geometric foundations, closed-cell cover, and finite case
  reduction.
- Generic owned-hull, core, residual-cover, trace, and local analytic arguments.
- The finite case inventory, overlay, strict distance bans, finite search, and
  conditional D4 bridge, including the previously checked integration fixes.
- The T01 groups and the initialized two-step T02 milestone described above.
- **T06:** `exact_local_packet_exists` and `construction_locally_isolated` have
  complete returned proofs. They cover the actual nonlinear gap aliases,
  derivatives, Taylor bounds, excluded features, branch cover, and 128 exact dual
  branches. The return reports clean audits with only the three standard axioms.

## Closing the proof

Restore F, FCOMMON, U2G, U2P, U2R, and U5 with
`python3 scripts/materialize_wand125.py`, then check the final-theorem closure
using `python3 scripts/verify.py --module ElevenSquare.ProofAudit --keep-going`.
Use one serial verifier per checkout. Resolve failures while preserving the
packing definitions, public statements, strict ownership, and boundary contact.
Optional `--jobs N` changes the worker count inside each new Lean process,
not the serial module schedule. Reused receipts retain their actual original
worker count and fingerprints; additional threads can require more memory.

After all final source and documentation edits, run:

```sh
python3 scripts/verify.py --all --fresh --keep-going
python3 scripts/finalize_verification.py
```

If the fresh replay is interrupted, resume with
`python3 scripts/verify.py --all --keep-going` without `--fresh`. Matching
accepted receipts remain reusable only under the verifier's current source,
configuration, object, and transitive dependency checks. Repeating `--fresh`
would deliberately discard that reuse; it is not required merely to resume.

The final `global_lower_bound`, `optimal_side_lower_bound`, and `optimality`, and
every other queried target, must use only `propext`, `Classical.choice`, and
`Quot.sound`. With no inventoried admissions, `sorryAx` is rejected everywhere.
The finalizer must accept current source, configuration, object, dependency, and
axiom-log evidence for every supported module before `--write` publishes it.
A focused result cannot satisfy this full-source gate.
