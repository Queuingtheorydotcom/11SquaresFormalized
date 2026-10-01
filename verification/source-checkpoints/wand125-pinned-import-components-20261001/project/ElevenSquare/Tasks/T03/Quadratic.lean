import ElevenSquare.Pending.S05_OwnedHull
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ElevenSquare.Pending.T03
noncomputable section

/-- A closed-interval Bernstein certificate. All three inequalities are weak;
the certified lower bound can itself be strictly positive. -/
theorem quadratic_lower_bound (A B C lo hi eps t : ℝ)
    (hab : lo < hi) (hta : lo ≤ t) (htb : t ≤ hi)
    (ha : 0 ≤ A*lo^2+B*lo+C-eps)
    (hm : 0 ≤ 2*(A*lo^2+B*lo+C-eps)+(hi-lo)*(2*A*lo+B))
    (hb : 0 ≤ A*hi^2+B*hi+C-eps) :
    eps ≤ A*t^2+B*t+C := by
  have h0 := mul_nonneg ha (sq_nonneg (hi-t))
  have h1 := mul_nonneg hm (mul_nonneg (sub_nonneg.mpr hta) (sub_nonneg.mpr htb))
  have h2 := mul_nonneg hb (sq_nonneg (t-lo))
  have hid :
      (A*lo^2+B*lo+C-eps)*(hi-t)^2 +
      (2*(A*lo^2+B*lo+C-eps)+(hi-lo)*(2*A*lo+B))*(t-lo)*(hi-t) +
      (A*hi^2+B*hi+C-eps)*(t-lo)^2 =
      (hi-lo)^2*(A*t^2+B*t+C-eps) := by ring
  have hmul : 0 ≤ (hi-lo)^2*(A*t^2+B*t+C-eps) := by
    rw [← hid]
    nlinarith only [h0, h1, h2]
  have hd : 0 < (hi-lo)^2 := sq_pos_of_pos (sub_pos.mpr hab)
  have h := nonneg_of_mul_nonneg_right hmul hd
  linarith

/-- A positive discriminant margin certifies a convex quadratic on all of ℝ. -/
theorem quadratic_pos_of_discriminant (A B C t : ℝ)
    (hA : 0 < A) (hd : 0 < 4*A*C-B^2) :
    0 < A*t^2+B*t+C := by
  have he : 4*A*(A*t^2+B*t+C) = (2*A*t+B)^2 + (4*A*C-B^2) := by ring
  by_contra hn
  have hmul := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ 4*A by positivity) (le_of_not_gt hn)
  nlinarith only [hmul, he, sq_nonneg (2*A*t+B), hd]

/-- The four strict quadratic inequalities retain both angular endpoints. -/
theorem openSquare_of_chart_quadratics (q : UnitSquare) (v : Point) (t : ℝ)
    (hq : q.axis = chartAxis t)
    (hxplus : 0 < (1/2 + v.1)*t^2 + (-2*v.2)*t + (1/2-v.1))
    (hxminus : 0 < (1/2 - v.1)*t^2 + (2*v.2)*t + (1/2+v.1))
    (hyplus : 0 < (1/2 + v.2)*t^2 + (2*v.1)*t + (1/2-v.2))
    (hyminus : 0 < (1/2 - v.2)*t^2 + (-2*v.1)*t + (1/2+v.2)) :
    OpenSquare q (q.center + v) := by
  have hd : 0 < 1+t^2 := by positivity
  have hx : localX q (q.center+v) = (v.1*(1-t^2)+2*v.2*t)/(1+t^2) := by
    dsimp [localX, dot]
    rw [hq]
    dsimp [chartAxis]
    field_simp [ne_of_gt hd]
    <;> ring
  have hy : localY q (q.center+v) = (v.2*(1-t^2)-2*v.1*t)/(1+t^2) := by
    dsimp [localY, dot, perp]
    rw [hq]
    dsimp [chartAxis]
    field_simp [ne_of_gt hd]
    <;> ring
  rw [OpenSquare, hx, hy, abs_lt, abs_lt]
  constructor
  · constructor
    · apply (lt_div_iff hd).2
      nlinarith only [hxminus]
    · apply (div_lt_iff hd).2
      nlinarith only [hxplus]
  · constructor
    · apply (lt_div_iff hd).2
      nlinarith only [hyminus]
    · apply (div_lt_iff hd).2
      nlinarith only [hyplus]

end
end ElevenSquare.Pending.T03
