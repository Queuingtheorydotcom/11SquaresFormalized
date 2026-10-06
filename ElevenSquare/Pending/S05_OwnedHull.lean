import ElevenSquare.Pending.Types
import ElevenSquare.BasicGeometry

/-! Strict ownership of convex hulls. Checkpoint: docs/FORMALIZATION_PROGRESS.md. -/

namespace ElevenSquare.Pending
noncomputable section

theorem openSquare_convex (q : UnitSquare) : Convex ℝ {p | OpenSquare q p} := by
  have hlin (v : Point) : IsLinearMap ℝ (fun p : Point => dot p v) := by
    constructor
    · intro x y
      dsimp [dot]
      ring
    · intro a x
      dsimp [dot]
      ring
  have strip (v : Point) : Convex ℝ {p : Point | |dot p v| < 1/2} := by
    simpa only [abs_lt, Set.setOf_and] using
      (convex_halfSpace_gt (hlin v) (-(1/2 : ℝ))).inter
        (convex_halfSpace_lt (hlin v) (1/2 : ℝ))
  have h := ((strip q.axis).inter (strip (perp q.axis))).translate_preimage_left
    (-q.center)
  simpa only [Set.preimage_inter, Set.preimage_setOf_eq, ← Set.setOf_and,
    OpenSquare, localX, localY, sub_eq_add_neg] using h

theorem hull_owned_of_vertices (q : UnitSquare) (vs : List QPoint)
    (hv : ∀ v ∈ vs, OpenSquare q (realPoint v)) :
    rationalHull vs ⊆ {p | OpenSquare q p} := by
  apply convexHull_min _ (openSquare_convex q)
  rintro p ⟨v, hmem, rfl⟩
  exact hv v hmem

-- The strict disk margin is essential: equality may only give boundary contact.
theorem owned_vertex_of_disk (q : UnitSquare) (v : Point)
    (hv : normSq (v-q.center) < 1/4) : OpenSquare q v := by
  exact open_of_normSq_lt q v hv

theorem common_core_hull (Q : List QPoint) (q : UnitSquare)
    (hv : ∀ v ∈ Q, OpenSquare q (q.center + realPoint v)) :
    CoreFits (rationalHull Q) q := by
  have hconv : Convex ℝ {v : Point | OpenSquare q (q.center + v)} :=
    (openSquare_convex q).translate_preimage_right q.center
  apply convexHull_min _ hconv
  rintro p ⟨v, hmem, rfl⟩
  exact hv v hmem


end
end ElevenSquare.Pending
