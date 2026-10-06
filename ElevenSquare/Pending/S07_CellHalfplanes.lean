import ElevenSquare.Cover
import ElevenSquare.Pending.Types
import Mathlib.Tactic.Ring

/-! Continuous-to-linear reduction for closed nearest-site cells. All boundaries
remain non-strict. The later overlay certificate must still establish the
recorded intersection and its exact vertex hull. -/
namespace ElevenSquare.Pending
noncomputable section

-- The quadratic terms in the query point cancel from a nearest-site comparison.
theorem distance_comparison_linear (p a b : Point) :
    coordinateDistanceSq p a ≤ coordinateDistanceSq p b ↔
    2*(b.1-a.1)*p.1 + 2*(b.2-a.2)*p.2 ≤
      b.1^2+b.2^2-a.1^2-a.2^2 := by
  unfold coordinateDistanceSq
  constructor <;> intro h <;> nlinarith

theorem closedCell_linear (i : Fin 16) (p : Point) :
    ClosedCell i p ↔ InUnitBox p ∧ ∀ j : Fin 16,
      2*((coverSite j).1-(coverSite i).1)*p.1 +
      2*((coverSite j).2-(coverSite i).2)*p.2 ≤
      (coverSite j).1^2+(coverSite j).2^2-
      (coverSite i).1^2-(coverSite i).2^2 := by
  simp only [ClosedCell, distance_comparison_linear]

theorem halfplane_convex (l : Halfplane) : Convex ℝ {p : Point | l.contains p} := by
  have hlin : IsLinearMap ℝ (fun p : Point => (l.a : ℝ)*p.1 + (l.b : ℝ)*p.2) := by
    constructor
    · intro x y
      dsimp
      ring
    · intro a x
      dsimp
      ring
  exact convex_halfSpace_le hlin (l.c : ℝ)

theorem polygon_convex (P : Polygon) : Convex ℝ P.carrier := by
  intro x hx y hy a b ha hb hab l hl
  exact halfplane_convex l (hx l hl) (hy l hl) ha hb hab

theorem rationalHull_in_polygon (P : Polygon) (vs : List QPoint)
    (hv : ∀ v ∈ vs, realPoint v ∈ P.carrier) : rationalHull vs ⊆ P.carrier := by
  apply convexHull_min _ (polygon_convex P)
  rintro p ⟨v, hmem, rfl⟩
  exact hv v hmem

end
end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.distance_comparison_linear
#print axioms ElevenSquare.Pending.closedCell_linear
#print axioms ElevenSquare.Pending.rationalHull_in_polygon
