# Remaining proof obligations

One explicit `sorry` site remains in source. Its exact file and line number
are recorded in `verification/admissions.json` and checked by
`scripts/check_sources.py`. It is an intentional placeholder, not a certified
conclusion. The newly wired baseline and prior families are **compiler-unverified
pending full dependency replay and axiom audits**. A smaller source admission
count does not establish verified proof completion.

## 1. Baseline source wiring; replay pending

The baseline dispatcher now uses the published 1,904 field and 27 generic
exclusions for all 1,931 native baseline indices. Its previously completed
imported-field branch and native G003/G004/G007 branches remain intact. The
public `baseline_certificate_exists` and `baseline_excluded` statements are
unchanged, as are the packing, closed cells, masks, and trace semantics.

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

## 3. Complete the returned-exclusion family

`ElevenSquare/Pending/S06_Returned.lean:returned_certificate_exists` remains
admitted for the 173 returned indices. The published wand125 release supplies
individual proof sources for 172 of these indices and lacks case1465. Their
partial-family integration is a separate collaborator task. T03 progress remains
preserved on its own branch; this integration does not modify its sources or
replace that work. The active public theorem still needs accepted certificates
for all 173 indices.

## 4. Case438 capture into the local rectangle

`ElevenSquare/Tasks/T07/UnfinishedCapture.lean:case438_near_certificate` is no
longer admitted. It is `Ext.case438_near_certificate'`, obtained from
`Ext.role_near_box_state` by the existing `role_near_box_to_case438_certificate`.

`role_near_box_state` (in `ElevenSquare/Tasks/T07/Ext/Case438.lean`) states that
every charted packing in the `coverCap` container whose centres lie in the closed
cells `roleCell` satisfies the near outer state. Its proof is a chain of extended
trace steps (`ExtStep`: the `VerifiedStep` rules plus a posewise prune by the
square's own hull, the container, forbidden centres, and collisions with every
admissible pose of a partner) from `siteSeedFor roleCell` through the archived
phase 2 (`mask438-adaptive`, 14 rounds, after a round that promotes the seed's
wall points) and the archived capture tree (`root-self-240` with the closed cuts
`y₁₅ ≤ 5/4`, `t₁₃ < 147/512` and `t₂ < 183/512`, whose far branches end in
terminal states), followed by a row-by-row inclusion of the final state in the
frozen near packet (`Ext/Near.lean`). It was compiled with Lean 4.34.1 and depends
on `propext`, `Classical.choice` and `Quot.sound` only.

The generated node modules `ElevenSquare/Tasks/T07/Ext/Gen/` are the release unit
U5 (one `n11-u5-<node>.tar.xz` per node), materialized and checked against
`integrations/wand125/release/MANIFEST_U5.sha256`. The generator
`scripts/wand125_u5/` regenerates them byte for byte from the archived capture data.

The near outer state is checked against a verbatim copy in `Ext/Near.lean`
(`extNearOuterState`). `Ext/Case438Global.lean` identifies the copy with
`nearOuterState` by `rfl` and derives `case438_near_certificate'`; that file and
`role_near_box_to_case438_certificate` inherit the compiler status of the
`NearStateBridge` and `ConditionalGlobal` import closures.

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

Discharge the remaining source site while preserving its semantics, and
validate the newly wired baseline and prior paths. Then run the full fresh source
build and axiom audit. The final `global_lower_bound`,
`optimal_side_lower_bound`, and `optimality` must have no `sorryAx` or custom
computational axiom in their transitive dependency sets. A successful build of
this admitted snapshot alone does not satisfy that requirement.
