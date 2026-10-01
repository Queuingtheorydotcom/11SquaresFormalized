import ElevenSquare.Tasks.T03.Walls

namespace ElevenSquare.Pending.T03
noncomputable section

theorem chart_x_antitone (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (chartAxis b).1 ≤ (chartAxis a).1 := by
  have hda : 0 < 1+a^2 := by positivity
  have hdb : 0 < 1+b^2 := by positivity
  dsimp [chartAxis]
  apply (div_le_div_iff hdb hda).2
  have hm := mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ b+a by linarith)
  nlinarith only [hm]

theorem chart_y_monotone (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (chartAxis a).2 ≤ (chartAxis b).2 := by
  have hda : 0 < 1+a^2 := by positivity
  have hdb : 0 < 1+b^2 := by positivity
  have hab1 : a*b ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hb) ha]
  have hm := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hab1)
  dsimp [chartAxis]
  apply (div_le_div_iff hda hdb).2
  nlinarith only [hm]

theorem chart_interval_bounds (a b t : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hta : a ≤ t) (htb : t ≤ b) :
    (chartAxis b).1 ≤ (chartAxis t).1 ∧ (chartAxis t).1 ≤ (chartAxis a).1 ∧
    (chartAxis a).2 ≤ (chartAxis t).2 ∧ (chartAxis t).2 ≤ (chartAxis b).2 := by
  exact ⟨chart_x_antitone t b (by linarith) htb, chart_x_antitone a t ha hta,
    chart_y_monotone a t ha hta (by linarith),
    chart_y_monotone t b (by linarith) htb hb⟩

/-- Four strict corner tests bound a linear expression throughout a closed
coefficient rectangle. No sign assumption on the center displacement is used. -/
theorem rectangle_linear_lt (x y cl ch sl sh c s h : ℝ)
    (hc0 : cl ≤ c) (hc1 : c ≤ ch) (hs0 : sl ≤ s) (hs1 : s ≤ sh)
    (h00 : x*cl+y*sl < h) (h01 : x*cl+y*sh < h)
    (h10 : x*ch+y*sl < h) (h11 : x*ch+y*sh < h) : x*c+y*s < h := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · exact lt_of_le_of_lt (add_le_add (mul_le_mul_of_nonneg_left hc1 hx)
      (mul_le_mul_of_nonneg_left hs1 hy)) h11
  · exact lt_of_le_of_lt (add_le_add (mul_le_mul_of_nonneg_left hc1 hx)
      (mul_le_mul_of_nonpos_left hs0 (le_of_not_ge hy))) h10
  · exact lt_of_le_of_lt (add_le_add (mul_le_mul_of_nonpos_left hc0 (le_of_not_ge hx))
      (mul_le_mul_of_nonneg_left hs1 hy)) h01
  · exact lt_of_le_of_lt (add_le_add (mul_le_mul_of_nonpos_left hc0 (le_of_not_ge hx))
      (mul_le_mul_of_nonpos_left hs0 (le_of_not_ge hy))) h00

end
end ElevenSquare.Pending.T03
