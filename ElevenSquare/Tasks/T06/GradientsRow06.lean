import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row06_alias0_zero : gapValue T constructionSquare (Gap.wall 1 0 2) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.wall 1 0 2) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (((1 / 2)) + (-1 / 2)*(0) + (-1 / 2)*(1)) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row06_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.wall 1 0 2) 3 = polynomialGradient 6 3 := by
  calc
    gapGradient T constructionSquare (Gap.wall 1 0 2) 3 = wallGradientFormula constructionSquare 1 0 2 3 := gapGradient_wall T constructionSquare 1 0 2 3
    _ = (0 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 6 3 := rfl

theorem row06_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.wall 1 0 2) 4 = polynomialGradient 6 4 := by
  calc
    gapGradient T constructionSquare (Gap.wall 1 0 2) 4 = wallGradientFormula constructionSquare 1 0 2 4 := gapGradient_wall T constructionSquare 1 0 2 4
    _ = (1 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))) := rfl
    _ = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 6 4 := rfl

theorem row06_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.wall 1 0 2) 5 = polynomialGradient 6 5 := by
  calc
    gapGradient T constructionSquare (Gap.wall 1 0 2) 5 = wallGradientFormula constructionSquare 1 0 2 5 := gapGradient_wall T constructionSquare 1 0 2 5
    _ = (0 + (-1 / 2)*(((1)*1)) + (-1 / 2)*((-(0)*1))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 6 5 := rfl

theorem row06_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.wall 1 0 2) 0 = polynomialGradient 6 0 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.wall 1 0 2) 1 = polynomialGradient 6 1 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.wall 1 0 2) 2 = polynomialGradient 6 2 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.wall 1 0 2) 6 = polynomialGradient 6 6 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.wall 1 0 2) 7 = polynomialGradient 6 7 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.wall 1 0 2) 8 = polynomialGradient 6 8 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.wall 1 0 2) 9 = polynomialGradient 6 9 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.wall 1 0 2) 10 = polynomialGradient 6 10 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.wall 1 0 2) 11 = polynomialGradient 6 11 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.wall 1 0 2) 12 = polynomialGradient 6 12 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.wall 1 0 2) 13 = polynomialGradient 6 13 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.wall 1 0 2) 14 = polynomialGradient 6 14 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.wall 1 0 2) 15 = polynomialGradient 6 15 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.wall 1 0 2) 16 = polynomialGradient 6 16 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.wall 1 0 2) 17 = polynomialGradient 6 17 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.wall 1 0 2) 18 = polynomialGradient 6 18 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.wall 1 0 2) 19 = polynomialGradient 6 19 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.wall 1 0 2) 20 = polynomialGradient 6 20 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.wall 1 0 2) 21 = polynomialGradient 6 21 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.wall 1 0 2) 22 = polynomialGradient 6 22 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.wall 1 0 2) 23 = polynomialGradient 6 23 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.wall 1 0 2) 24 = polynomialGradient 6 24 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.wall 1 0 2) 25 = polynomialGradient 6 25 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.wall 1 0 2) 26 = polynomialGradient 6 26 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.wall 1 0 2) 27 = polynomialGradient 6 27 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.wall 1 0 2) 28 = polynomialGradient 6 28 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.wall 1 0 2) 29 = polynomialGradient 6 29 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.wall 1 0 2) 30 = polynomialGradient 6 30 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.wall 1 0 2) 31 = polynomialGradient 6 31 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.wall 1 0 2) 32 = polynomialGradient 6 32 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row06_alias0_gradient : gapGradient T constructionSquare (Gap.wall 1 0 2) = polynomialGradient 6 := by
  funext j
  fin_cases j
  · exact row06_alias0_coordinate_00
  · exact row06_alias0_coordinate_01
  · exact row06_alias0_coordinate_02
  · exact row06_alias0_coordinate_03
  · exact row06_alias0_coordinate_04
  · exact row06_alias0_coordinate_05
  · exact row06_alias0_coordinate_06
  · exact row06_alias0_coordinate_07
  · exact row06_alias0_coordinate_08
  · exact row06_alias0_coordinate_09
  · exact row06_alias0_coordinate_10
  · exact row06_alias0_coordinate_11
  · exact row06_alias0_coordinate_12
  · exact row06_alias0_coordinate_13
  · exact row06_alias0_coordinate_14
  · exact row06_alias0_coordinate_15
  · exact row06_alias0_coordinate_16
  · exact row06_alias0_coordinate_17
  · exact row06_alias0_coordinate_18
  · exact row06_alias0_coordinate_19
  · exact row06_alias0_coordinate_20
  · exact row06_alias0_coordinate_21
  · exact row06_alias0_coordinate_22
  · exact row06_alias0_coordinate_23
  · exact row06_alias0_coordinate_24
  · exact row06_alias0_coordinate_25
  · exact row06_alias0_coordinate_26
  · exact row06_alias0_coordinate_27
  · exact row06_alias0_coordinate_28
  · exact row06_alias0_coordinate_29
  · exact row06_alias0_coordinate_30
  · exact row06_alias0_coordinate_31
  · exact row06_alias0_coordinate_32

theorem row06_aliases_tied (g : Gap) (hg : g ∈ rowAliases 6) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 6 := by
  change g ∈ [Gap.wall 1 0 2] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row06_alias0_zero, row06_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
