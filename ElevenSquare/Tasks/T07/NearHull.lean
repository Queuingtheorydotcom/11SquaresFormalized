import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

/-! Closed rectangle transport for the residual center polygons in the
case-438 near leaf. The vertices of a polygon suffice: the certificate
consumer never assumes that only the listed vertices are feasible centers. -/
namespace ElevenSquare.Tasks.T07

def inRect (lx hx ly hy : ℝ) (p : ℝ × ℝ) : Prop :=
  lx ≤ p.1 ∧ p.1 ≤ hx ∧ ly ≤ p.2 ∧ p.2 ≤ hy

theorem rect_convex (lx hx ly hy : ℝ) :
    Convex ℝ {p : ℝ × ℝ | inRect lx hx ly hy p} := by
  have hs : {p : ℝ × ℝ | inRect lx hx ly hy p} =
      (Set.Icc lx hx ×ˢ Set.Icc ly hy) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc, inRect]
    tauto
  rw [hs]
  exact (convex_Icc lx hx).prod (convex_Icc ly hy)

theorem hull_in_rect {v : Set (ℝ × ℝ)} {lx hx ly hy : ℝ}
    (hv : ∀ p ∈ v, inRect lx hx ly hy p) :
    ∀ p ∈ convexHull ℝ v, inRect lx hx ly hy p := by
  exact convexHull_min hv (rect_convex lx hx ly hy)

theorem listed_vertices_in_rect {v : List (ℝ × ℝ)} {lx hx ly hy : ℝ}
    (hv : ∀ p ∈ v, inRect lx hx ly hy p) :
    ∀ p ∈ convexHull ℝ {q : ℝ × ℝ | q ∈ v}, inRect lx hx ly hy p := by
  exact hull_in_rect hv

theorem interval_deviation {x lo hi c r : ℝ}
    (hlo : lo ≤ x) (hhi : x ≤ hi)
    (hleft : c-r ≤ lo) (hright : hi ≤ c+r) : |x-c| ≤ r := by
  apply abs_le.mpr
  constructor <;> linarith

theorem affine_interval_deviation {x lo hi c r a b : ℝ}
    (ha : 0 < a) (hlo : lo ≤ x) (hhi : x ≤ hi)
    (hleft : c-r ≤ a*lo+b) (hright : a*hi+b ≤ c+r) :
    |(a*x+b)-c| ≤ r := by
  apply interval_deviation (lo := a*lo+b) (hi := a*hi+b)
    (c := c) (r := r) (by nlinarith) (by nlinarith) hleft hright

end ElevenSquare.Tasks.T07
