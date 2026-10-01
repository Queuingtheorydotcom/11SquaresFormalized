import ElevenSquare.Pending.Types

/-!
# Sound center pruning

A Minkowski witness yields a common strict interior point. Both pruning
lemmas preserve the actual packing's outer cover and all owned hulls.
The public statements and the imported geometric definitions are unchanged.

Verification checkpoint: docs/FORMALIZATION_PROGRESS.md.
-/

namespace ElevenSquare.Pending
noncomputable section

-- A CLOSED Minkowski region is safely forbidden because BOTH witnesses are strict interior points.
theorem forbidden_center_implies_overlap
    (q r : UnitSquare) (K Q : Set Point)
    (hK : K ⊆ {p | OpenSquare r p}) (hQ : CoreFits Q q)
    (hc : q.center ∈ forbiddenCenters K Q) :
    ∃ p, OpenSquare q p ∧ OpenSquare r p := by
  rcases hc with ⟨k, hk, v, hv, hcenter⟩
  refine ⟨k, ?_, hK hk⟩
  have hq : OpenSquare q (q.center + v) := hQ v hv
  simpa only [hcenter, sub_add_cancel] using hq

theorem prune_rows_sound {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (i j : Owner) (hij : i ≠ j) (Q : Set Point) (rs : List PoseRow)
    (hcore : ∀ q, RowsContain (s.rows i) q → CoreFits Q q)
    (hcover : ∀ q, RowsContain (s.rows i) q →
      RowsContain rs q ∨ q.center ∈ forbiddenCenters (rationalHull (s.owned j)) Q)
    (hs : StateHolds P s) : StateHolds P (replaceRows s i rs) := by
  -- The actual square cannot occupy a forbidden center: it would overlap
  -- the distinct owner j, contradicting the packing invariant.
  have hkeep : RowsContain rs (P.squares i) := by
    rcases hcover (P.squares i) (hs.1 i) with hrow | hforbidden
    · exact hrow
    · rcases forbidden_center_implies_overlap
        (P.squares i) (P.squares j) (rationalHull (s.owned j)) Q
        (hs.2 j) (hcore (P.squares i) (hs.1 i)) hforbidden with ⟨p, hp⟩
      exact False.elim (P.interior_disjoint i j hij p hp)
  -- Only i's rows change; all strict owned-hull assertions are unchanged.
  refine ⟨?_, hs.2⟩
  intro k
  by_cases hki : k = i
  · subst k
    simpa only [replaceRows, Function.update_same] using hkeep
  · simpa only [replaceRows, Function.update_noteq hki] using hs.1 k

-- A universal collision kernel uses ALL poses of the partner. This antecedent
-- cannot be justified from only one representative orientation or center.
theorem universal_collision_prune {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (i j : Owner) (hij : i ≠ j) (F : Set Point) (rs : List PoseRow)
    (hcollision : ∀ q r, RowsContain (s.rows i) q → RowsContain (s.rows j) r →
      q.center ∈ F → ∃ p, OpenSquare q p ∧ OpenSquare r p)
    (hcover : ∀ q, RowsContain (s.rows i) q → RowsContain rs q ∨ q.center ∈ F)
    (hs : StateHolds P s) : StateHolds P (replaceRows s i rs) := by
  -- Instantiate the universal collision hypothesis with BOTH actual poses.
  -- In particular, hs.1 j supplies a genuine partner-row witness, so an
  -- empty partner cover cannot be used as a vacuous collision certificate.
  have hkeep : RowsContain rs (P.squares i) := by
    rcases hcover (P.squares i) (hs.1 i) with hrow | hforbidden
    · exact hrow
    · rcases hcollision (P.squares i) (P.squares j)
        (hs.1 i) (hs.1 j) hforbidden with ⟨p, hp⟩
      exact False.elim (P.interior_disjoint i j hij p hp)
  refine ⟨?_, hs.2⟩
  intro k
  by_cases hki : k = i
  · subst k
    simpa only [replaceRows, Function.update_same] using hkeep
  · simpa only [replaceRows, Function.update_noteq hki] using hs.1 k


end
end ElevenSquare.Pending
