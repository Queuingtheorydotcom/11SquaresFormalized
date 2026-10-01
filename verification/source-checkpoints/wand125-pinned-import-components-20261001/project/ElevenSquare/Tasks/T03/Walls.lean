import ElevenSquare.Tasks.T03.Quadratic

namespace ElevenSquare.Pending.T03
noncomputable section

/-- Body coordinates on the closed square include its corners and edges. -/
theorem closedSquare_body (q : UnitSquare) (a b : ℝ)
    (ha : |a| ≤ 1/2) (hb : |b| ≤ 1/2) :
    ClosedSquare q (q.center + a • q.axis + b • perp q.axis) := by
  have hu : q.axis.1*q.axis.1 + q.axis.2*q.axis.2 = 1 := q.axis_unit
  have hx : localX q (q.center + a • q.axis + b • perp q.axis) = a := by
    dsimp [localX, dot, perp]
    nlinarith [congrArg (fun z : ℝ => a*z) hu]
  have hy : localY q (q.center + a • q.axis + b • perp q.axis) = b := by
    dsimp [localY, dot, perp]
    nlinarith [congrArg (fun z : ℝ => b*z) hu]
  exact ⟨by rw [hx]; exact ha, by rw [hy]; exact hb⟩

/-- Necessary wall bounds follow from containment of four actual corners. -/
theorem contained_signed_width (q : UnitSquare) (S : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer S p) :
    (q.axis.1+q.axis.2)/2 ≤ q.center.1 ∧
    q.center.1+(q.axis.1+q.axis.2)/2 ≤ S ∧
    (q.axis.1+q.axis.2)/2 ≤ q.center.2 ∧
    q.center.2+(q.axis.1+q.axis.2)/2 ≤ S := by
  have hr := hc _ (closedSquare_body q (1/2) (-1/2) (by norm_num [abs_le]) (by norm_num [abs_le]))
  have hl := hc _ (closedSquare_body q (-1/2) (1/2) (by norm_num [abs_le]) (by norm_num [abs_le]))
  have ht := hc _ (closedSquare_body q (1/2) (1/2) (by norm_num [abs_le]) (by norm_num [abs_le]))
  have hb := hc _ (closedSquare_body q (-1/2) (-1/2) (by norm_num [abs_le]) (by norm_num [abs_le]))
  dsimp [InContainer, perp] at hr hl ht hb
  exact ⟨by linarith [hl.1], by linarith [hr.2.1],
    by linarith [hb.2.2.1], by linarith [ht.2.2.2]⟩

/-- Concavity makes closed endpoint tests sufficient for a weak lower bound. -/
theorem concave_quadratic_nonneg (A B C lo hi t : ℝ)
    (hA : A ≤ 0) (hab : lo < hi) (hta : lo ≤ t) (htb : t ≤ hi)
    (ha : 0 ≤ A*lo^2+B*lo+C) (hb : 0 ≤ A*hi^2+B*hi+C) :
    0 ≤ A*t^2+B*t+C := by
  have hmul : A*(hi-lo)^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hA (sq_nonneg _)
  have hm : 0 ≤ 2*(A*lo^2+B*lo+C)+(hi-lo)*(2*A*lo+B) := by
    nlinarith only [ha, hb, hmul]
  exact quadratic_lower_bound A B C lo hi 0 t hab hta htb
    (by simpa using ha) (by simpa using hm) (by simpa using hb)

/-- A uniform wall envelope over a closed chart interval, with exact endpoint
checks. No midpoint sampling or omitted angular seam is used. -/
theorem chart_width_lower_bound (lo hi w t : ℝ)
    (hw : 0 ≤ w) (hab : lo < hi) (hta : lo ≤ t) (htb : t ≤ hi)
    (ha : 0 ≤ 1-w+2*lo-(1+w)*lo^2)
    (hb : 0 ≤ 1-w+2*hi-(1+w)*hi^2) :
    w ≤ (chartAxis t).1 + (chartAxis t).2 := by
  have h := concave_quadratic_nonneg (-(1+w)) 2 (1-w) lo hi t
    (by linarith) hab hta htb (by nlinarith only [ha]) (by nlinarith only [hb])
  have hd : 0 < 1+t^2 := by positivity
  dsimp [chartAxis]
  rw [← add_div]
  apply (le_div_iff hd).2
  nlinarith only [h]

theorem contained_interval_wall_bounds (q : UnitSquare) (S lo hi w t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer S p) (hq : q.axis = chartAxis t)
    (hw : 0 ≤ w) (hab : lo < hi) (hta : lo ≤ t) (htb : t ≤ hi)
    (ha : 0 ≤ 1-w+2*lo-(1+w)*lo^2)
    (hb : 0 ≤ 1-w+2*hi-(1+w)*hi^2) :
    w/2 ≤ q.center.1 ∧ q.center.1+w/2 ≤ S ∧
    w/2 ≤ q.center.2 ∧ q.center.2+w/2 ≤ S := by
  have hbds := contained_signed_width q S hc
  have hwidth := chart_width_lower_bound lo hi w t hw hab hta htb ha hb
  rw [← hq] at hwidth
  exact ⟨by linarith [hbds.1], by linarith [hbds.2.1],
    by linarith [hbds.2.2.1], by linarith [hbds.2.2.2]⟩

end
end ElevenSquare.Pending.T03
