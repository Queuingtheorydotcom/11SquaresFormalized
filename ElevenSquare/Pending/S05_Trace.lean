import ElevenSquare.Pending.S05_Minkowski
import ElevenSquare.Pending.S05_OwnedHull

/-! Semantic trace soundness. Concrete certificate initialization remains separate. -/

namespace ElevenSquare.Pending
noncomputable section

-- Each constructor stores geometric obligations to be discharged from rational certificate data.
-- There is no Boolean acceptance flag and no constructor accepting an arbitrary semantic implication.
inductive VerifiedStep : PoseState → PoseState → Prop
  | outerEquivalent (s : PoseState) (i : Owner) (rs : List PoseRow)
      (h : ∀ q, RowsContain (s.rows i) q ↔ RowsContain rs q) :
      VerifiedStep s (replaceRows s i rs)
  | prune (s : PoseState) (i j : Owner) (hij : i ≠ j)
      (Q : Set Point) (rs : List PoseRow)
      (hcore : ∀ q, RowsContain (s.rows i) q → CoreFits Q q)
      (hcover : ∀ q, RowsContain (s.rows i) q →
        RowsContain rs q ∨ q.center ∈ forbiddenCenters (rationalHull (s.owned j)) Q) :
      VerifiedStep s (replaceRows s i rs)
  /-- Each discarded pose has its own valid strict core and distinct partner.
  This supports row-dependent angular cores without a false uniform-core premise. -/
  | prunePosewise (s : PoseState) (i : Owner) (rs : List PoseRow)
      (hcover : ∀ q, RowsContain (s.rows i) q → RowsContain rs q ∨
        ∃ j : Owner, i ≠ j ∧ ∃ Q : Set Point,
          CoreFits Q q ∧ q.center ∈ forbiddenCenters (rationalHull (s.owned j)) Q) :
      VerifiedStep s (replaceRows s i rs)
  | universalCollision (s : PoseState) (i j : Owner) (hij : i ≠ j)
      (F : Set Point) (rs : List PoseRow)
      (hcollision : ∀ q r, RowsContain (s.rows i) q → RowsContain (s.rows j) r →
        q.center ∈ F → ∃ p, OpenSquare q p ∧ OpenSquare r p)
      (hcover : ∀ q, RowsContain (s.rows i) q → RowsContain rs q ∨ q.center ∈ F) :
      VerifiedStep s (replaceRows s i rs)

  | promote (s : PoseState) (i : Owner) (vs : List QPoint)
      (hvertices : ∀ q, RowsContain (s.rows i) q → ∀ v ∈ vs, OpenSquare q (realPoint v)) :
      VerifiedStep s (replaceHull s i vs)

  /-- Ownership-aware promotion: the old hull premise is supplied by StateHolds,
  not by assuming ownership for every square in an outer pose cover. -/
  | promoteOwned (s : PoseState) (i : Owner) (vs : List QPoint)
      (hvertices : ∀ q, RowsContain (s.rows i) q →
        (rationalHull (s.owned i) ⊆ {p | OpenSquare q p}) →
        ∀ v ∈ vs, OpenSquare q (realPoint v)) :
      VerifiedStep s (replaceHull s i vs)

inductive VerifiedTrace : PoseState → PoseState → Prop
  | refl (s : PoseState) : VerifiedTrace s s
  | cons {a b c : PoseState} : VerifiedStep a b → VerifiedTrace b c → VerifiedTrace a c

def Terminal (s : PoseState) : Prop :=
  (∃ i, s.rows i = []) ∨
  ∃ i j, i ≠ j ∧ ∃ p, p ∈ rationalHull (s.owned i) ∧ p ∈ rationalHull (s.owned j)

theorem verified_step_sound {S : ℝ} (P : Packing 11 S) {a b : PoseState}
    (hs : StateHolds P a) (h : VerifiedStep a b) : StateHolds P b := by
  cases h with
  | outerEquivalent i rs heq =>
    refine ⟨?_, hs.2⟩
    intro k
    by_cases hki : k = i
    · subst k
      simpa only [replaceRows, Function.update_self] using (heq (P.squares i)).mp (hs.1 i)
    · simpa only [replaceRows, Function.update_of_ne hki] using hs.1 k
  | prune i j hij Q rs hcore hcover =>
    exact prune_rows_sound P a i j hij Q rs hcore hcover hs
  | prunePosewise i rs hcover =>
    have hkeep : RowsContain rs (P.squares i) := by
      rcases hcover (P.squares i) (hs.1 i) with hrow | ⟨j, hij, Q, hQ, hc⟩
      · exact hrow
      · obtain ⟨p, hp⟩ := forbidden_center_implies_overlap
          (P.squares i) (P.squares j) (rationalHull (a.owned j)) Q (hs.2 j) hQ hc
        exact False.elim (P.interior_disjoint i j hij p hp)
    refine ⟨?_, hs.2⟩
    intro k
    by_cases hki : k = i
    · subst k
      simpa only [replaceRows, Function.update_self] using hkeep
    · simpa only [replaceRows, Function.update_of_ne hki] using hs.1 k
  | universalCollision i j hij F rs hcollision hcover =>
    exact universal_collision_prune P a i j hij F rs hcollision hcover hs
  | promote i vs hvertices =>
    refine ⟨hs.1, ?_⟩
    intro k
    by_cases hki : k = i
    · subst k
      simpa only [replaceHull, Function.update_self] using
        hull_owned_of_vertices (P.squares i) vs (hvertices (P.squares i) (hs.1 i))
    · simpa only [replaceHull, Function.update_of_ne hki] using hs.2 k
  | promoteOwned i vs hvertices =>
    refine ⟨hs.1, ?_⟩
    intro k
    by_cases hki : k = i
    · subst k
      simpa only [replaceHull, Function.update_self] using
        hull_owned_of_vertices (P.squares i) vs
          (hvertices (P.squares i) (hs.1 i) (hs.2 i))
    · simpa only [replaceHull, Function.update_of_ne hki] using hs.2 k

theorem verified_trace_sound {S : ℝ} (P : Packing 11 S) {a b : PoseState}
    (hs : StateHolds P a) (h : VerifiedTrace a b) : StateHolds P b := by
  induction h with
  | refl s => exact hs
  | cons step trace ih => exact ih (verified_step_sound P hs step)

theorem terminal_contradiction {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (hs : StateHolds P s) (ht : Terminal s) : False := by
  rcases ht with ⟨i, hi⟩ | ⟨i, j, hij, p, hpi, hpj⟩
  · have hc := hs.1 i
    simp [RowsContain, hi] at hc
  · exact P.interior_disjoint i j hij p ⟨hs.2 i hpi, hs.2 j hpj⟩


end
end ElevenSquare.Pending

#print axioms ElevenSquare.Pending.verified_step_sound
#print axioms ElevenSquare.Pending.verified_trace_sound
#print axioms ElevenSquare.Pending.terminal_contradiction
