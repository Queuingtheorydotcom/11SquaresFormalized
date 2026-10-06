import ElevenSquare.Pending.S07_HullDistance

/-! Exact integer-grid certificates for vertex distance bounds. -/
namespace ElevenSquare.Pending.GridDistance

abbrev GridPoint := ℤ × ℤ
def scale : ℕ := 1048576

def Contains (g : GridPoint) (p : Point) : Prop :=
  (g.1 : ℝ) ≤ scale*p.1 ∧ scale*p.1 ≤ (g.1 : ℝ)+1 ∧
  (g.2 : ℝ) ≤ scale*p.2 ∧ scale*p.2 ≤ (g.2 : ℝ)+1

def delta (a b : ℤ) : ℤ := max (a+1-b) (b+1-a)

def Close (a b : GridPoint) : Prop :=
  2500 * ((delta a.1 b.1)^2 + (delta a.2 b.2)^2) ≤ 301 * (scale : ℤ)^2

theorem coordinate_bound (a b : ℤ) (x y : ℝ)
    (hx : (a : ℝ) ≤ scale*x ∧ scale*x ≤ (a : ℝ)+1)
    (hy : (b : ℝ) ≤ scale*y ∧ scale*y ≤ (b : ℝ)+1) :
    (scale*x-scale*y)^2 ≤ (delta a b : ℝ)^2 := by
  have hleft : (a : ℝ)+1-b ≤ (delta a b : ℝ) := by
    exact_mod_cast (le_max_left (a+1-b) (b+1-a))
  have hright : (b : ℝ)+1-a ≤ (delta a b : ℝ) := by
    exact_mod_cast (le_max_right (a+1-b) (b+1-a))
  have hprod : 0 ≤ ((delta a b : ℝ)-(scale*x-scale*y))*
      ((delta a b : ℝ)+(scale*x-scale*y)) :=
    mul_nonneg (by linarith only [hleft, hx.2, hy.1])
      (by linarith only [hright, hy.2, hx.1])
  nlinarith only [hprod]

theorem close_bounds_points (a b : GridPoint) (p q : Point)
    (hp : Contains a p) (hq : Contains b q) (h : Close a b) :
    normSq (p-q) ≤ (301/2500 : ℝ) := by
  have hx := coordinate_bound a.1 b.1 p.1 q.1 ⟨hp.1, hp.2.1⟩ ⟨hq.1, hq.2.1⟩
  have hy := coordinate_bound a.2 b.2 p.2 q.2 hp.2.2 hq.2.2
  have hc : (2500 : ℝ)*((delta a.1 b.1 : ℝ)^2+(delta a.2 b.2 : ℝ)^2)
      ≤ 301*(scale : ℝ)^2 := by
    exact_mod_cast h
  have hid : (scale : ℝ)^2*normSq (p-q) =
      (scale*p.1-scale*q.1)^2+(scale*p.2-scale*q.2)^2 := by
    dsimp [normSq, dot]
    ring
  have hs := mul_le_mul_of_nonneg_left (add_le_add hx hy) (by norm_num : (0 : ℝ) ≤ 2500)
  rw [← hid] at hs
  have hb := hs.trans hc
  apply (mul_le_mul_iff_of_pos_left (by norm_num [scale] : (0 : ℝ) < 2500*(scale : ℝ)^2)).mp
  calc
    (2500*(scale : ℝ)^2)*normSq (p-q) ≤ 301*(scale : ℝ)^2 := by
      simpa only [mul_assoc] using hb
    _ = (2500*(scale : ℝ)^2)*(301/2500 : ℝ) := by ring

theorem cap_strict : (coverCap-1)^2 * (301/2500 : ℝ) < 1 := by
  norm_num [coverCap]

theorem hulls_strict (A B : List QPoint)
    (h : ∀ a ∈ A, ∀ b ∈ B, normSq (realPoint a-realPoint b) ≤ (301/2500 : ℝ)) :
    ∀ p ∈ rationalHull A, ∀ q ∈ rationalHull B,
      (coverCap-1)^2 * normSq (p-q) < 1 := by
  intro p hp q hq
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
    (squared_distance_on_hulls A B (301/2500) h p hp q hq) (sq_nonneg _)) cap_strict

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.close_bounds_points
#print axioms ElevenSquare.Pending.GridDistance.hulls_strict
