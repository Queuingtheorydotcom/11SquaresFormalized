import ElevenSquare.Pending.Types
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Generic vertical-slice witnesses for planar convex-hull certificates.
No recorded overlay geometry is assumed or checked in this module. -/
namespace ElevenSquare.Pending
noncomputable section

theorem convex_vertical_between {C : Set Point} (hc : Convex ℝ C)
    (x lo hi y : ℝ) (hlo : (x,lo) ∈ C) (hhi : (x,hi) ∈ C)
    (hylo : lo ≤ y) (hyhi : y ≤ hi) : (x,y) ∈ C := by
  by_cases he : lo = hi
  · have hy : y = lo := by linarith
    simpa [hy] using hlo
  have hd : 0 < hi-lo := sub_pos.mpr (lt_of_le_of_ne (le_trans hylo hyhi) he)
  let t := (y-lo)/(hi-lo)
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hylo) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith)
  have h := hc hlo hhi (sub_nonneg.mpr ht1) ht (by ring : 1-t+t=1)
  convert h using 1
  ext <;> dsimp [t] <;> field_simp [ne_of_gt hd] <;> ring

theorem convex_trapezoid {C : Set Point} (hc : Convex ℝ C)
    (left right loLeft loRight hiLeft hiRight x y : ℝ)
    (hwidth : left < right)
    (hll : (left,loLeft) ∈ C) (hlr : (right,loRight) ∈ C)
    (hul : (left,hiLeft) ∈ C) (hur : (right,hiRight) ∈ C)
    (hx0 : left ≤ x) (hx1 : x ≤ right)
    (hlo : (right-x)*loLeft+(x-left)*loRight ≤ (right-left)*y)
    (hhi : (right-left)*y ≤ (right-x)*hiLeft+(x-left)*hiRight) :
    (x,y) ∈ C := by
  have hd : 0 < right-left := sub_pos.mpr hwidth
  let t := (x-left)/(right-left)
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx0) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hx : (1-t)*left+t*right = x := by
    dsimp [t]
    field_simp [ne_of_gt hd] <;> ring
  have lower : (x,(1-t)*loLeft+t*loRight) ∈ C := by
    convert hc hll hlr (sub_nonneg.mpr ht1) ht (by ring : 1-t+t=1) using 1
    ext <;> dsimp
    · exact hx.symm
  have upper : (x,(1-t)*hiLeft+t*hiRight) ∈ C := by
    convert hc hul hur (sub_nonneg.mpr ht1) ht (by ring : 1-t+t=1) using 1
    ext <;> dsimp
    · exact hx.symm
  apply convex_vertical_between hc x _ _ y lower upper
  · apply (mul_le_mul_iff_of_pos_left hd).mp
    have he : (right-left)*((1-t)*loLeft+t*loRight) =
        (right-x)*loLeft+(x-left)*loRight := by
      dsimp [t]
      field_simp [ne_of_gt hd] <;> ring
    rw [he]
    exact hlo
  · apply (mul_le_mul_iff_of_pos_left hd).mp
    have he : (right-left)*((1-t)*hiLeft+t*hiRight) =
        (right-x)*hiLeft+(x-left)*hiRight := by
      dsimp [t]
      field_simp [ne_of_gt hd] <;> ring
    rw [he]
    exact hhi

end
end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.convex_vertical_between
#print axioms ElevenSquare.Pending.convex_trapezoid
