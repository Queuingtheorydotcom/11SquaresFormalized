import ElevenSquare.Pending.Types
import ElevenSquare.Construction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact angle conversion from the trace's half-angle chart to the radian
displacement chart used by the focused local packet. -/

namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem chartAxis_trig (t : ℝ) :
    chartAxis t = (Real.cos (2 * Real.arctan t), Real.sin (2 * Real.arctan t)) := by
  have hd : 1 + t^2 ≠ 0 := by positivity
  have hs : Real.sqrt (1 + t^2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by positivity))
  apply Prod.ext
  · dsimp [chartAxis]
    rw [Real.cos_two_mul, Real.cos_sq_arctan]
    field_simp [hd] <;> ring
  · dsimp [chartAxis]
    rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    field_simp [hd, hs]
    ring_nf
    rw [Real.sq_sqrt (by positivity : 0 ≤ 1 + t^2)]
    ring

theorem construction_axis_chart (i : Owner) :
    (constructionSquare i).axis = chartAxis (if i.val < 6 then 0 else u) := by
  by_cases hi : i.val < 6
  · have hn : ¬ 6 ≤ i.val := Nat.not_le.mpr hi
    simp [constructionSquare, constructionAxis, chartAxis, hi, hn]
  · have hg : 6 ≤ i.val := Nat.le_of_not_lt hi
    simp only [if_neg hi]
    simp [constructionSquare, constructionAxis, hg, chartAxis,
      construction_cos_halfAngle, construction_sin_halfAngle]

/-- An angle interval of width `d` in the half-angle parameter has radian
width at most `2*d`. This also applies at both closed chart endpoints. -/
theorem arctan_lipschitz (x y : ℝ) :
    |Real.arctan x - Real.arctan y| ≤ |x-y| := by
  have ordered (a b : ℝ) (hab : a ≤ b) :
      |Real.arctan a - Real.arctan b| ≤ |a-b| := by
    have hd (z : ℝ) : |(1 : ℝ) / (1 + z^2)| ≤ 1 := by
      have hp : 0 < 1 + z^2 := by positivity
      rw [abs_of_pos (div_pos (by norm_num) hp)]
      exact (div_le_iff₀ hp).mpr (by nlinarith [sq_nonneg z])
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (a := a) (b := b) (f := Real.arctan)
      (f' := fun z => 1 / (1 + z^2)) (C := 1)
      (fun z _ => (Real.hasDerivAt_arctan z).hasDerivWithinAt)
      (fun z _ => by simpa only [Real.norm_eq_abs] using hd z)
      b ⟨hab, le_rfl⟩
    calc
      |Real.arctan a - Real.arctan b| ≤ b-a := by
        simpa only [Real.norm_eq_abs, one_mul, abs_sub_comm] using h
      _ = |a-b| := by rw [abs_of_nonpos (sub_nonpos.mpr hab)]; ring
  rcases le_total x y with h | h
  · exact ordered x y h
  · simpa only [abs_sub_comm] using ordered y x h

/-- On the nonnegative ray above `m`, the derivative is bounded by
`1/(1+m²)`. The closed endpoints are included. -/
theorem arctan_lipschitz_above (m x y : ℝ)
    (hm : 0 ≤ m) (hx : m ≤ x) (hy : m ≤ y) :
    |Real.arctan x - Real.arctan y| ≤ |x-y| / (1+m^2) := by
  have ordered (a b : ℝ) (ha : m ≤ a) (hab : a ≤ b) :
      |Real.arctan a - Real.arctan b| ≤ |a-b| / (1+m^2) := by
    have hpM : 0 < 1+m^2 := by positivity
    have hd (z : ℝ) (hz : a ≤ z) :
        |(1 : ℝ) / (1+z^2)| ≤ 1/(1+m^2) := by
      have hpZ : 0 < 1+z^2 := by positivity
      have hmz : m ≤ z := ha.trans hz
      have hsq : m^2 ≤ z^2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hmz)
          (add_nonneg hm (hm.trans (ha.trans hz)))]
      rw [abs_of_pos (div_pos (by norm_num) hpZ)]
      exact (div_le_div_iff₀ hpZ hpM).mpr (by nlinarith)
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (a := a) (b := b) (f := Real.arctan)
      (f' := fun z => 1 / (1+z^2)) (C := 1/(1+m^2))
      (fun z _ => (Real.hasDerivAt_arctan z).hasDerivWithinAt)
      (fun z hz => by
        simpa only [Real.norm_eq_abs] using hd z hz.1)
      b ⟨hab, le_rfl⟩
    calc
      |Real.arctan a - Real.arctan b| ≤ (1/(1+m^2))*(b-a) := by
        simpa only [Real.norm_eq_abs, abs_sub_comm] using h
      _ = |a-b|/(1+m^2) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hab)]
        ring
  rcases le_total x y with h | h
  · exact ordered x y hx h
  · simpa only [abs_sub_comm] using ordered y x hy h

theorem angle_near_zero {t hi R : ℝ}
    (ht : 0 ≤ t) (hhi : t ≤ hi) (hR : 2*hi ≤ R) :
    |2 * Real.arctan t| ≤ R := by
  have h := arctan_lipschitz t 0
  simp only [Real.arctan_zero, sub_zero, abs_of_nonneg ht] at h
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  linarith

theorem angle_near_quarter {lo t R : ℝ}
    (hlo : 0 ≤ lo) (hlt : lo ≤ t) (ht : t ≤ 1)
    (hR : 2*(1-lo)/(1+lo^2) ≤ R) :
    |2 * Real.arctan t - Real.pi/2| ≤ R := by
  have h := arctan_lipschitz_above lo t 1 hlo hlt (by linarith)
  have hd : 0 < 1+lo^2 := by positivity
  have hdifference : (1-t)/(1+lo^2) ≤ (1-lo)/(1+lo^2) :=
    (div_le_div_iff₀ hd hd).mpr (by nlinarith)
  rw [abs_of_nonpos (sub_nonpos.mpr ht)] at h
  have h' : |Real.arctan t-Real.arctan 1| ≤ (1-t)/(1+lo^2) := by
    convert h using 1; ring
  have hR' : 2*((1-lo)/(1+lo^2)) ≤ R := by
    convert hR using 1; ring
  have hangle : 2 * Real.arctan t - Real.pi/2 =
      2*(Real.arctan t-Real.arctan 1) := by rw [Real.arctan_one]; ring
  rw [hangle, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  linarith

theorem angle_near_tilted {lo hi αlo αhi t α R : ℝ}
    (hlo0 : 0 ≤ lo) (hαlo0 : 0 ≤ αlo)
    (hlo : lo ≤ t) (hhi : t ≤ hi)
    (hαlo : αlo ≤ α) (hαhi : α ≤ αhi)
    (hleft : 2*(αhi-lo)/(1+lo^2) ≤ R)
    (hright : 2*(hi-αlo)/(1+αlo^2) ≤ R) :
    |2 * Real.arctan t - 2 * Real.arctan α| ≤ R := by
  have hangle : |2 * Real.arctan t - 2 * Real.arctan α| =
      2*|Real.arctan t-Real.arctan α| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [hangle]
  rcases le_total t α with h | h
  · have hd : 0 < 1+lo^2 := by positivity
    have hderiv := arctan_lipschitz_above lo t α hlo0 hlo (hlo.trans h)
    rw [abs_of_nonpos (sub_nonpos.mpr h)] at hderiv
    have hderiv' : |Real.arctan t-Real.arctan α| ≤ (α-t)/(1+lo^2) := by
      convert hderiv using 1; ring
    have hfraction : (α-t)/(1+lo^2) ≤ (αhi-lo)/(1+lo^2) :=
      (div_le_div_iff₀ hd hd).mpr (by nlinarith)
    have hleft' : 2*((αhi-lo)/(1+lo^2)) ≤ R := by
      convert hleft using 1; ring
    linarith
  · have hd : 0 < 1+αlo^2 := by positivity
    have hderiv := arctan_lipschitz_above αlo t α hαlo0
      (hαlo.trans h) hαlo
    rw [abs_of_nonneg (sub_nonneg.mpr h)] at hderiv
    have hfraction : (t-α)/(1+αlo^2) ≤ (hi-αlo)/(1+αlo^2) :=
      (div_le_div_iff₀ hd hd).mpr (by nlinarith)
    have hright' : 2*((hi-αlo)/(1+αlo^2)) ≤ R := by
      convert hright using 1; ring
    linarith

/-- The relative radian angle rotates one half-angle chart axis to another. -/
theorem chartAxis_rotate (base t : ℝ) :
    let θ := 2 * Real.arctan t - 2 * Real.arctan base
    (Real.cos θ * (chartAxis base).1 - Real.sin θ * (chartAxis base).2,
     Real.sin θ * (chartAxis base).1 + Real.cos θ * (chartAxis base).2) = chartAxis t := by
  dsimp
  rw [chartAxis_trig base, chartAxis_trig t]
  have hunit := Real.sin_sq_add_cos_sq (2 * Real.arctan base)
  apply Prod.ext
  · dsimp
    rw [Real.cos_sub, Real.sin_sub]
    nlinarith [congrArg (fun z : ℝ => Real.cos (2 * Real.arctan t) * z) hunit]
  · dsimp
    rw [Real.cos_sub, Real.sin_sub]
    nlinarith [congrArg (fun z : ℝ => Real.sin (2 * Real.arctan t) * z) hunit]

end
end ElevenSquare.Tasks.T07
