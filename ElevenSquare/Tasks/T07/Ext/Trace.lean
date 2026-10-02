import ElevenSquare.Pending.S05_Trace

/-! Extended trace steps for the case-438 capture.

The archived capture prunes a pose row using, besides the owned hulls of the
*other* squares, two further necessary conditions on the square itself:

* its own owned hull lies in its open square (`OwnsHulls`, as in
  `VerifiedStep.promoteOwned`), and
* the closed square lies in the container of side `coverCap`
  (`Packing.contained`).

Besides the disjuncts of `prunePosewise`, a pose may be dropped when it meets
every possible pose of another square (a universal collision).

`ExtStep.pruneOwned` makes both available to a posewise prune.  Every
`VerifiedStep` is an `ExtStep`.  Soundness holds for packings in the container
of side `coverCap`, the frame in which the case-438 composition works. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

inductive ExtStep : PoseState → PoseState → Prop
  | base {a b : PoseState} (h : VerifiedStep a b) : ExtStep a b
  /-- A posewise prune that may also use the square's own owned hull and the
  container.  The second disjunct is exactly that of `prunePosewise`. -/
  | pruneOwned (s : PoseState) (i : Owner) (rs : List PoseRow)
      (hcover : ∀ q, RowsContain (s.rows i) q →
        rationalHull (s.owned i) ⊆ {p | OpenSquare q p} →
        (∀ p, ClosedSquare q p → InContainer coverCap p) →
        RowsContain rs q ∨
          (∃ j : Owner, i ≠ j ∧ ∃ Q : Set Point,
            CoreFits Q q ∧ q.center ∈ forbiddenCenters (rationalHull (s.owned j)) Q) ∨
          (∃ j : Owner, i ≠ j ∧ ∀ r : UnitSquare, RowsContain (s.rows j) r →
            rationalHull (s.owned j) ⊆ {p | OpenSquare r p} →
            (∀ p, ClosedSquare r p → InContainer coverCap p) →
            ∃ p, OpenSquare q p ∧ OpenSquare r p)) :
      ExtStep s (replaceRows s i rs)

inductive ExtTrace : PoseState → PoseState → Prop
  | refl (s : PoseState) : ExtTrace s s
  | cons {a b c : PoseState} : ExtStep a b → ExtTrace b c → ExtTrace a c

theorem ext_step_sound (P : Packing 11 coverCap) {a b : PoseState}
    (hs : StateHolds P a) (h : ExtStep a b) : StateHolds P b := by
  cases h with
  | base h => exact verified_step_sound P hs h
  | pruneOwned i rs hcover =>
    have hkeep : RowsContain rs (P.squares i) := by
      rcases hcover (P.squares i) (hs.1 i) (hs.2 i) (P.contained i) with
        hrow | ⟨j, hij, Q, hQ, hc⟩ | ⟨j, hij, hcol⟩
      · exact hrow
      · obtain ⟨p, hp⟩ := forbidden_center_implies_overlap
          (P.squares i) (P.squares j) (rationalHull (a.owned j)) Q (hs.2 j) hQ hc
        exact False.elim (P.interior_disjoint i j hij p hp)
      · obtain ⟨p, hp⟩ := hcol (P.squares j) (hs.1 j) (hs.2 j) (P.contained j)
        exact False.elim (P.interior_disjoint i j hij p hp)
    refine ⟨?_, hs.2⟩
    intro k
    by_cases hki : k = i
    · subst k
      simpa only [replaceRows, Function.update_self] using hkeep
    · simpa only [replaceRows, Function.update_of_ne hki] using hs.1 k

theorem ext_trace_sound (P : Packing 11 coverCap) {a b : PoseState}
    (hs : StateHolds P a) (h : ExtTrace a b) : StateHolds P b := by
  induction h with
  | refl s => exact hs
  | cons step _ ih => exact ih (ext_step_sound P hs step)

theorem ExtTrace.of_verified {a b : PoseState} (h : VerifiedTrace a b) : ExtTrace a b := by
  induction h with
  | refl s => exact ExtTrace.refl s
  | cons step _ ih => exact ExtTrace.cons (ExtStep.base step) ih

theorem ExtTrace.trans {a b c : PoseState} (hab : ExtTrace a b) (hbc : ExtTrace b c) :
    ExtTrace a c := by
  induction hab with
  | refl _ => exact hbc
  | cons step _ ih => exact ExtTrace.cons step (ih hbc)

theorem ext_terminal_refutes (P : Packing 11 coverCap) {a b : PoseState}
    (ha : StateHolds P a) (hab : ExtTrace a b) (hb : Terminal b) : False :=
  terminal_contradiction P b (ext_trace_sound P ha hab) hb

end
end ElevenSquare.Tasks.T07
