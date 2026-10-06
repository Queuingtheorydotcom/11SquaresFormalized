import ElevenSquare.Simplified.LocalCommonData
import ElevenSquare.Tasks.T06.GradientsPolynomial
import Mathlib.Tactic.Positivity

/-! Convexification of the five parallel contacts, using the actual exact
source gradient polynomials. The 128 owner choices share the same forty
necessary first-order rows, with common upper curvature bounds. -/
namespace ElevenSquare.Simplified.LocalCommon
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06 ElevenSquare.Tasks.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def weightPolynomial : Fin 7 → Fin 8 → ℚ :=
  ![![(0), (0), (0), (0), (0), (0), (0), (0)],
    ![(11/10), (-31/40), (31/10), (-139/40), (-5), (-41/40), (5), (-17/8)],
    ![(39/40), (-81/40), (-71/40), (81/40), (13/8), (-31/40), (-5/8), (3/8)],
    ![(1/40), (81/40), (71/40), (-81/40), (-13/8), (31/40), (5/8), (-3/8)],
    ![(1), (0), (0), (0), (0), (0), (0), (0)],
    ![(39/40), (-21/40), (49/40), (-159/40), (-43/8), (9/40), (35/8), (-17/8)],
    ![(1/40), (21/40), (-49/40), (159/40), (43/8), (-9/40), (-35/8), (17/8)]]

def weightClass : Fin 20 → Fin 7 := ![0, 1, 1, 0, 0, 2, 3, 4, 0, 2, 3, 4, 0, 1, 1, 0, 4, 5, 6, 0]
def comboTarget : Fin 20 → Fin 56 := ![33, 33, 53, 53, 35, 35, 54, 54, 37, 37, 50, 50, 39, 39, 49, 49, 40, 40, 47, 47]
def comboFirst : Fin 20 → Fin 56 := ![32, 52, 32, 52, 34, 54, 34, 54, 36, 50, 36, 50, 38, 48, 38, 48, 40, 46, 40, 46]
def comboSecond : Fin 20 → Fin 56 := ![33, 53, 33, 53, 35, 55, 35, 55, 37, 51, 37, 51, 39, 49, 39, 49, 41, 47, 41, 47]
def comboCurvatureNumerator : Fin 20 → ℕ := ![101981296, 101981296, 101981296, 101981296, 79086693, 79086693, 79086693, 79086693, 115699695, 115699695, 115699695, 115699695, 88123140, 88123140, 88123140, 88123140, 289103692, 289103692, 289103692, 289103692]

def comboWeight (q : Fin 20) : ℝ := polyEval (weightPolynomial (weightClass q)) u

def comboCurvature (q : Fin 20) : ℚ :=
  (comboCurvatureNumerator q : ℚ)/1000000000000

private theorem root_window : ((3657/10000 : ℚ) : ℝ) ≤ u ∧
    u ≤ ((3658/10000 : ℚ) : ℝ) := by
  rcases u_bounds with ⟨hlo,hhi⟩
  dsimp only [rootLo,rootHi] at hlo hhi
  norm_num only [Rat.cast_div,Rat.cast_ofNat]
  constructor <;> linarith

private theorem polynomial_weight_bounds : ∀ q : Fin 7,
    0≤polyLower (weightPolynomial q) (3657/10000) (3658/10000) ∧
    polyUpper (weightPolynomial q) (3657/10000) (3658/10000)≤1 := by decide +kernel

theorem combo_weight_bounds (q : Fin 20) : 0≤comboWeight q ∧ comboWeight q≤1 := by
  obtain ⟨hl,hh⟩ := poly_enclosure (weightPolynomial (weightClass q))
    (3657/10000) (3658/10000) u (by norm_num) root_window.1 root_window.2
  have hb := polynomial_weight_bounds (weightClass q)
  have hlo : (0 : ℝ) ≤ (polyLower (weightPolynomial (weightClass q))
      (3657/10000) (3658/10000) : ℚ) := by exact_mod_cast hb.1
  have hhi : ((polyUpper (weightPolynomial (weightClass q))
      (3657/10000) (3658/10000) : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hb.2
  exact ⟨hlo.trans hl,hh.trans hhi⟩

private theorem scalar_identity_00 :
    polyEval (gradientCoefficients 2) u =
      polyEval (weightPolynomial 1) u * polyEval (gradientCoefficients 18) u +
      (1-polyEval (weightPolynomial 1) u) * polyEval (gradientCoefficients 16) u := by
  simp only [polyEval_expand]
  norm_num [weightPolynomial,gradientCoefficients] <;> ring

private theorem scalar_identity_01 :
    polyEval (gradientCoefficients 16) u =
      polyEval (weightPolynomial 1) u * polyEval (gradientCoefficients 3) u +
      (1-polyEval (weightPolynomial 1) u) * polyEval (gradientCoefficients 2) u := by
  simp only [polyEval_expand]
  norm_num [weightPolynomial,gradientCoefficients] <;> ring

private theorem scalar_identity_02 :
    polyEval (gradientCoefficients 2) u =
      polyEval (weightPolynomial 2) u * polyEval (gradientCoefficients 20) u +
      (1-polyEval (weightPolynomial 2) u) * polyEval (gradientCoefficients 19) u := by
  simp only [polyEval_expand]
  norm_num [weightPolynomial,gradientCoefficients] <;> ring

private theorem scalar_identity_03 :
    polyEval (gradientCoefficients 20) u =
      polyEval (weightPolynomial 2) u * polyEval (gradientCoefficients 2) u +
      (1-polyEval (weightPolynomial 2) u) * polyEval (gradientCoefficients 3) u := by
  simp only [polyEval_expand]
  norm_num [weightPolynomial,gradientCoefficients] <;> ring

private theorem scalar_identity_04 :
    polyEval (gradientCoefficients 2) u =
      polyEval (weightPolynomial 3) u * polyEval (gradientCoefficients 19) u +
      (1-polyEval (weightPolynomial 3) u) * polyEval (gradientCoefficients 20) u := by
  simp only [polyEval_expand]
  norm_num [weightPolynomial,gradientCoefficients] <;> ring

private theorem scalar_identity_05 :
    polyEval (gradientCoefficients 20) u =
      polyEval (weightPolynomial 3) u * polyEval (gradientCoefficients 3) u +
      (1-polyEval (weightPolynomial 3) u) * polyEval (gradientCoefficients 2) u := by
  simp only [polyEval_expand]
  norm_num [weightPolynomial,gradientCoefficients] <;> ring

private theorem scalar_identity_06 :
    polyEval (gradientCoefficients 2) u =
      polyEval (weightPolynomial 5) u * polyEval (gradientCoefficients 22) u +
      (1-polyEval (weightPolynomial 5) u) * polyEval (gradientCoefficients 21) u := by
  simp only [polyEval_expand]
  norm_num [weightPolynomial,gradientCoefficients] <;> ring

private theorem scalar_identity_07 :
    polyEval (gradientCoefficients 21) u =
      polyEval (weightPolynomial 5) u * polyEval (gradientCoefficients 3) u +
      (1-polyEval (weightPolynomial 5) u) * polyEval (gradientCoefficients 2) u := by
  simp only [polyEval_expand]
  norm_num [weightPolynomial,gradientCoefficients] <;> ring

private theorem scalar_identity_08 :
    polyEval (gradientCoefficients 2) u =
      polyEval (weightPolynomial 6) u * polyEval (gradientCoefficients 21) u +
      (1-polyEval (weightPolynomial 6) u) * polyEval (gradientCoefficients 22) u := by
  simp only [polyEval_expand]
  norm_num [weightPolynomial,gradientCoefficients] <;> ring

private theorem scalar_identity_09 :
    polyEval (gradientCoefficients 21) u =
      polyEval (weightPolynomial 6) u * polyEval (gradientCoefficients 2) u +
      (1-polyEval (weightPolynomial 6) u) * polyEval (gradientCoefficients 3) u := by
  simp only [polyEval_expand]
  norm_num [weightPolynomial,gradientCoefficients] <;> ring

/-- Owner changes affect only two angular coefficients. Equal coefficients,
zero weights and unit weights are automatic; ten scalar patterns remain. -/
private def ScalarPattern (w : Fin 7) (t a b : Fin 24) : Prop :=
  (t=a ∧ a=b) ∨ (w=0 ∧ t=b) ∨ (w=4 ∧ t=a) ∨
  (w=1 ∧ t=2 ∧ a=18 ∧ b=16) ∨
  (w=1 ∧ t=16 ∧ a=3 ∧ b=2) ∨
  (w=2 ∧ t=2 ∧ a=20 ∧ b=19) ∨
  (w=2 ∧ t=20 ∧ a=2 ∧ b=3) ∨
  (w=3 ∧ t=2 ∧ a=19 ∧ b=20) ∨
  (w=3 ∧ t=20 ∧ a=3 ∧ b=2) ∨
  (w=5 ∧ t=2 ∧ a=22 ∧ b=21) ∨
  (w=5 ∧ t=21 ∧ a=3 ∧ b=2) ∨
  (w=6 ∧ t=2 ∧ a=21 ∧ b=22) ∨
  (w=6 ∧ t=21 ∧ a=2 ∧ b=3)

private theorem all_scalar_patterns : ∀ (q : Fin 20) (k : Fin 33),
    ScalarPattern (weightClass q) (gradientClass (comboTarget q) k)
      (gradientClass (comboFirst q) k) (gradientClass (comboSecond q) k) := by
  unfold ScalarPattern
  decide

private theorem scalar_identity (w : Fin 7) (t a b : Fin 24)
    (hp : ScalarPattern w t a b) :
    polyEval (gradientCoefficients t) u =
      polyEval (weightPolynomial w) u * polyEval (gradientCoefficients a) u +
      (1-polyEval (weightPolynomial w) u) * polyEval (gradientCoefficients b) u := by
  have hz : polyEval (weightPolynomial 0) u = 0 := by
    simp only [polyEval_expand]
    norm_num [weightPolynomial]
  have ho : polyEval (weightPolynomial 4) u = 1 := by
    simp only [polyEval_expand]
    norm_num [weightPolynomial]
  rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩
  · ring
  · rw [hz]; ring
  · rw [ho]; ring
  · exact scalar_identity_00
  · exact scalar_identity_01
  · exact scalar_identity_02
  · exact scalar_identity_03
  · exact scalar_identity_04
  · exact scalar_identity_05
  · exact scalar_identity_06
  · exact scalar_identity_07
  · exact scalar_identity_08
  · exact scalar_identity_09

theorem combo_identity (q : Fin 20) (k : Fin 33) :
    polynomialGradient (comboTarget q) k =
      comboWeight q*polynomialGradient (comboFirst q) k +
      (1-comboWeight q)*polynomialGradient (comboSecond q) k := by
  exact scalar_identity (weightClass q) _ _ _ (all_scalar_patterns q k)

private theorem curvature_bounds : ∀ q : Fin 20,
    rowCurvatures (comboFirst q)≤comboCurvature q ∧
    rowCurvatures (comboSecond q)≤comboCurvature q := by decide +kernel

/-- Either owner's selected rows imply the common row, retaining the original
Taylor error through convexity and the larger of the owner curvatures. -/
theorem combo_lower (q : Fin 20) (τ : ℝ) (h : Fin 33 → ℝ)
    (ha : -(τ^2*(rowCurvatures (comboFirst q) : ℝ)/2) ≤
      dot (polynomialGradient (comboFirst q)) h)
    (hb : -(τ^2*(rowCurvatures (comboSecond q) : ℝ)/2) ≤
      dot (polynomialGradient (comboSecond q)) h) :
    -(τ^2*(comboCurvature q : ℝ)/2) ≤
      dot (polynomialGradient (comboTarget q)) h := by
  have hka : (rowCurvatures (comboFirst q) : ℝ)≤(comboCurvature q : ℝ) := by
    exact_mod_cast (curvature_bounds q).1
  have hkb : (rowCurvatures (comboSecond q) : ℝ)≤(comboCurvature q : ℝ) := by
    exact_mod_cast (curvature_bounds q).2
  have ha' : -(τ^2*(comboCurvature q : ℝ)/2) ≤
      dot (polynomialGradient (comboFirst q)) h := by
    linarith [mul_le_mul_of_nonneg_left hka (sq_nonneg τ)]
  have hb' : -(τ^2*(comboCurvature q : ℝ)/2) ≤
      dot (polynomialGradient (comboSecond q)) h := by
    linarith [mul_le_mul_of_nonneg_left hkb (sq_nonneg τ)]
  have hid : dot (polynomialGradient (comboTarget q)) h =
      comboWeight q*dot (polynomialGradient (comboFirst q)) h +
      (1-comboWeight q)*dot (polynomialGradient (comboSecond q)) h := by
    unfold dot
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [combo_identity]
    ring
  have hw := combo_weight_bounds q
  rw [hid]
  calc
    _ = comboWeight q*(-(τ^2*(comboCurvature q : ℝ)/2)) +
        (1-comboWeight q)*(-(τ^2*(comboCurvature q : ℝ)/2)) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left ha' hw.1)
      (mul_le_mul_of_nonneg_left hb' (sub_nonneg.mpr hw.2))

end
end ElevenSquare.Simplified.LocalCommon

#print axioms ElevenSquare.Simplified.LocalCommon.combo_weight_bounds
#print axioms ElevenSquare.Simplified.LocalCommon.combo_identity
#print axioms ElevenSquare.Simplified.LocalCommon.combo_lower
