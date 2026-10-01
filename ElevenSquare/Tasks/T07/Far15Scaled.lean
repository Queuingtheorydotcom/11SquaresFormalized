import ElevenSquare.Tasks.T07.Far15FamilyData
import ElevenSquare.Tasks.T07.CoordinateBridge

/-! Correct field-to-physical collision certificate. The source vertices are
in a field where unit physical squares have side `fieldScale`; their centers
and owned points are divided by this scale before applying `OpenSquare`. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def far15PhysicalWitness : Point :=
  ((far15Owner9Witness.1 : ℝ)/fieldScale,
   (far15Owner9Witness.2 : ℝ)/fieldScale)

private theorem fieldScale_gt_983 : (983/1000 : ℝ) < fieldScale := by
  norm_num [fieldScale, coverCap]

theorem far15_scaled_box_collision (q : UnitSquare) (pField : Point)
    (hcenter : q.center = (pField.1/fieldScale,pField.2/fieldScale))
    (hbox : (1/2 : ℝ) ≤ pField.1 ∧ pField.1 ≤ 557/1000 ∧
      (2466/1000 : ℝ) ≤ pField.2 ∧ pField.2 ≤ 2573/1000)
    (ha : ∃ t : ℝ, (233/256 : ℝ) ≤ t ∧ t ≤ 63/64 ∧
      q.axis = chartAxis t) : OpenSquare q far15PhysicalWitness := by
  obtain ⟨t, htlo, hthi, haxis⟩ := ha
  let dx : ℝ := (far15Owner9Witness.1 : ℝ) - pField.1
  let d : ℝ := pField.2 - (far15Owner9Witness.2 : ℝ)
  let c : ℝ := (chartAxis t).1
  let s : ℝ := (chartAxis t).2
  have hden : 0 < 1+t^2 := by positivity
  have htloSq : (233/256 : ℝ)^2 ≤ t^2 := by
    nlinarith [mul_nonneg (show 0 ≤ t-233/256 by linarith)
      (show 0 ≤ t+233/256 by linarith)]
  have hthiSq : t^2 ≤ (63/64 : ℝ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 63/64-t by linarith)
      (show 0 ≤ 63/64+t by linarith)]
  have hc0 : 0 ≤ c := by
    dsimp [c, chartAxis]
    exact div_nonneg (by nlinarith) (le_of_lt hden)
  have hcLo : (1/70 : ℝ) ≤ c := by
    dsimp [c, chartAxis]
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hcHi : c ≤ 1/10 := by
    dsimp [c, chartAxis]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hs0 : 0 ≤ s := by
    dsimp [s, chartAxis]
    exact div_nonneg (by linarith) (le_of_lt hden)
  have hsHi : s ≤ 1 := by
    dsimp [s, chartAxis]
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg (t-1)]
  have hdx : (9/25 : ℝ) ≤ dx ∧ dx ≤ 43/100 := by
    dsimp [dx, far15Owner9Witness]
    norm_num at hbox ⊢
    constructor <;> linarith
  have hd : 0 ≤ d ∧ d ≤ 496/1000 := by
    dsimp [d, far15Owner9Witness]
    norm_num at hbox ⊢
    constructor <;> linarith
  have hdx0 : 0 ≤ dx := le_trans (by norm_num) hdx.1
  have hxcLo : (9/25 : ℝ)*(1/70) ≤ dx*c := by
    calc
      _ ≤ dx*(1/70) := mul_le_mul_of_nonneg_right hdx.1 (by norm_num)
      _ ≤ dx*c := mul_le_mul_of_nonneg_left hcLo hdx0
  have hxcHi : dx*c ≤ (43/100 : ℝ)*(1/10) :=
    mul_le_mul hdx.2 hcHi hc0 (by norm_num)
  have hds0 : 0 ≤ d*s := mul_nonneg hd.1 hs0
  have hdsHi : d*s ≤ (496/1000 : ℝ)*1 :=
    mul_le_mul hd.2 hsHi hs0 (by norm_num)
  have hxs0 : 0 ≤ dx*s := mul_nonneg hdx0 hs0
  have hxsHi : dx*s ≤ (43/100 : ℝ)*1 :=
    mul_le_mul hdx.2 hsHi hs0 (by norm_num)
  have hdc0 : 0 ≤ d*c := mul_nonneg hd.1 hc0
  have hdcHi : d*c ≤ (496/1000 : ℝ)*(1/10) :=
    mul_le_mul hd.2 hcHi hc0 (by norm_num)
  have hx : |dx*c-d*s| < fieldScale/2 := by
    apply abs_lt.mpr
    have hlo : -(fieldScale/2) < (9/25)*(1/70)-(496/1000) := by
      have h := fieldScale_gt_983
      norm_num at h ⊢
      linarith
    have hbound : (9/25 : ℝ)*(1/70)-(496/1000) ≤ dx*c-d*s := by
      apply sub_le_sub hxcLo
      simpa using hdsHi
    have hright : dx*c-d*s ≤ dx*c := by
      simpa only [sub_eq_add_neg, add_zero] using
        (add_le_add le_rfl (neg_nonpos.mpr hds0))
    refine ⟨lt_of_lt_of_le hlo hbound, lt_of_le_of_lt hright ?_⟩
    exact lt_of_le_of_lt hxcHi (by linarith [fieldScale_gt_983])
  have hy : |dx*(-s)-d*c| < fieldScale/2 := by
    have hsum0 : 0 ≤ dx*s+d*c := add_nonneg hxs0 hdc0
    have hsum : dx*s+d*c < fieldScale/2 :=
      lt_of_le_of_lt (add_le_add hxsHi hdcHi)
        (by linarith [fieldScale_gt_983])
    calc
      |dx*(-s)-d*c| = |-(dx*s+d*c)| := by congr 1; ring
      _ = |dx*s+d*c| := abs_neg _
      _ < fieldScale/2 := by rwa [abs_of_nonneg hsum0]
  have hlocalX : localX q far15PhysicalWitness =
      (dx*c-d*s)/fieldScale := by
    dsimp [localX, dot, far15PhysicalWitness]
    rw [hcenter, haxis]
    dsimp [dx, d, c, s]
    field_simp [fieldScale_ne_zero] <;> ring
  have hlocalY : localY q far15PhysicalWitness =
      (dx*(-s)-d*c)/fieldScale := by
    dsimp [localY, dot, perp, far15PhysicalWitness]
    rw [hcenter, haxis]
    dsimp [dx, d, c, s]
    field_simp [fieldScale_ne_zero] <;> ring
  rw [OpenSquare, hlocalX, hlocalY]
  constructor
  · rw [abs_div, abs_of_pos fieldScale_pos]
    exact (div_lt_iff₀ fieldScale_pos).mpr (by linarith [hx])
  · rw [abs_div, abs_of_pos fieldScale_pos]
    exact (div_lt_iff₀ fieldScale_pos).mpr (by linarith [hy])

end
end ElevenSquare.Tasks.T07
