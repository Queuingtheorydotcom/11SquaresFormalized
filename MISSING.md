# Remaining proof obligations

Six explicit `sorry` sites remain. The exact files and line numbers are recorded
in `verification/admissions.json` and checked by `scripts/check_sources.py`.
They are intentional placeholders, not certified conclusions.

## 1. Complete the baseline case family

Three sites under `ElevenSquare/Tasks/T01/Handoff/` remain:

- `PlanData.lean:planData`: provide the full finite ancestry and branch plans.
- `ProgramCalculations.lean:program_calculations`: check cores, walls, coverage,
  ownership, interval coverage, and exact predecessor links for those plans.
- `LeafCalculations.lean:leaf_calculations`: prove every terminal leaf closes.

The reduced inventory covers all 1,931 baseline indices with 71 selected groups.
Groups G003, G004, and G007 are already integrated into the dispatcher; their
completed certificates cover 1,132 distinct required cases. The other 799 cases
remain outside that completed union. The number of cases is not an estimate of
remaining computational effort.

The return also includes all 188 shared owned-point proofs, uniform wall and core
lemmas, shared Bernstein sign certificates, finished parts of G005, and partial
G070 transitions. Conditional transitions do not complete an initialized program.
In particular, G005's completed cells and G070's terminal certificates cannot be
used to assert a whole group exclusion before their remaining links are proved.

The public `baseline_certificate_exists` and `baseline_excluded` preserve their
original statements and inherit the three private admissions. Their definitions
of the packing, closed cells, masks, and trace semantics are unchanged.

## 2. Complete the prior-support family

`ElevenSquare/Pending/S06_PriorSupport.lean:prior_certificate_exists` remains
admitted. It requires an initialized `VerifiedTrace` ending in `Terminal` for
all 76 prior indices. Its original baseline-exclusion premise is deliberate.
Early D4 cuts must use that premise, without appealing circularly to the final
symmetry or optimality result.

Case1000 is proved through archived steps0 and1. The checked continuation
establishes genuine predecessor/self-cut implications, all 64 closed rows in
step1, normalized integer coverage, strict ownership promotion, preservation of
the owner permutation, and transport to the exact archived outer state.

For the straightforward full case1000 chain, nonterminal steps2–11, linkage of
terminal step12, and the final contradiction still remain. The other cases also
need their full ancestry, refined intervals, branch coverage, and special
collision/support mechanisms. Existing conditional terminal-row results are
useful components, not a complete case exclusion.

## 3. Complete the returned-exclusion family

`ElevenSquare/Pending/S06_Returned.lean:returned_certificate_exists` remains
admitted for the 173 returned indices. The generic terminal-trace wrapper and
checked common geometry/checker tools are present. Case2135's complete certificate
source closure is also included; the other 172 assigned indices still need their
complete source proofs integrated before the public family theorem can close.

The checkpoints are documented in [T03_PROGRESS.md](T03_PROGRESS.md). The
[partial T03 release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-audited-151-20260930) supplies a standalone exact source collection
for 151 independently audited case certificates. Their actual target audits have
only the three standard axioms. A standalone source supplement adds the fully
audited case1484 and case2122 closures. The accepted grouped case1646 source
closure and the audited case2047 and case1848 closures are also published as
standalone supplements, with later accepted 1311, 1372 and 1731 checkpoints:
**167 published original-project full certificate audits** in total, now including
accepted imported cases1823,1849,1887,1891,2051,2068,2069 and2070. Upstream separately supplies 172 case-proof archives;
only case1465 is absent there. All 13 prepared import source closures are
published in the prepared source release, with exact accepted Combined and
DirectTrees source closures for2068/2069/2070,1891,1887,1823 and1849. The other five imported full-target audits
remain pending. See T03_PROGRESS.md for exact source/audit bindings.
The Git source tree contains case2135 directly; the full generated source
collections are distributed as release assets.

The other six cases and assembly of all 173 certificates into the exact public
family theorem remain unfinished. Its clean combined target audit and the final
return package are also pending. No fresh merged repository Lean replay or
completed T03 case-family return is claimed; the public admission remains open.

## 4. Complete case438 capture into the local rectangle

`ElevenSquare/Tasks/T07/UnfinishedCapture.lean:case438_near_certificate` remains
admitted. Its type is the existing `Case438NearCertificate` interface: every
centered case438 packing of side at most `T` must admit a representation in the
focused local rectangle at the same physical side length.

This named obligation replaces the old opaque `sorry` body of the public
`global_lower_bound`. The public theorem now uses the returned, checked
`global_lower_bound_of_case438_certificate` composition. The three unfinished
exclusion families remain upstream dependencies of that composition.

The T07 return supplies occupied-cell seed geometry, role and chart transport,
physical field conversion, far-row collisions, terminal polygon/triangle checks,
strict core fits, and conditional near-box/rigidity interfaces. It does not
supply the complete trace from the genuine occupied seed to the stronger
archived root and branch states.

Remaining work includes the phase 2/root ancestry, both promoted terminal partner
hulls' actual ownership, all required far-branch eliminations, and final near-row
inclusion. The returned counterexamples rule out direct promotion from mere
closed-cell occupancy and a simple rowwise near inclusion. They are obstructions
to proposed shortcuts, not counterexamples to the optimality theorem.

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

Discharge the six sites while preserving their semantics, then run the full
fresh source build and axiom audit. The final `global_lower_bound`,
`optimal_side_lower_bound`, and `optimality` must have no `sorryAx` or custom
computational axiom in their transitive dependency sets. A successful build of
this admitted snapshot alone does not satisfy that requirement.
