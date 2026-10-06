import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row16_alias0_zero : gapValue T constructionSquare (Gap.wall 5 0 0) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.wall 5 0 0) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (((1 / 2)) + (-1 / 2)*(1) + (-1 / 2)*(-(0))) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row16_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.wall 5 0 0) 15 = polynomialGradient 16 15 := by
  calc
    gapGradient T constructionSquare (Gap.wall 5 0 0) 15 = wallGradientFormula constructionSquare 5 0 0 15 := gapGradient_wall T constructionSquare 5 0 0 15
    _ = (1 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))) := rfl
    _ = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 16 15 := rfl

theorem row16_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.wall 5 0 0) 16 = polynomialGradient 16 16 := by
  calc
    gapGradient T constructionSquare (Gap.wall 5 0 0) 16 = wallGradientFormula constructionSquare 5 0 0 16 := gapGradient_wall T constructionSquare 5 0 0 16
    _ = (0 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 16 16 := rfl

theorem row16_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.wall 5 0 0) 17 = polynomialGradient 16 17 := by
  calc
    gapGradient T constructionSquare (Gap.wall 5 0 0) 17 = wallGradientFormula constructionSquare 5 0 0 17 := gapGradient_wall T constructionSquare 5 0 0 17
    _ = (0 + (-1 / 2)*((-(0)*1)) + (-1 / 2)*(-(((1)*1)))) := rfl
    _ = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 16 17 := rfl

theorem row16_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.wall 5 0 0) 0 = polynomialGradient 16 0 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.wall 5 0 0) 1 = polynomialGradient 16 1 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.wall 5 0 0) 2 = polynomialGradient 16 2 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.wall 5 0 0) 3 = polynomialGradient 16 3 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.wall 5 0 0) 4 = polynomialGradient 16 4 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.wall 5 0 0) 5 = polynomialGradient 16 5 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.wall 5 0 0) 6 = polynomialGradient 16 6 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.wall 5 0 0) 7 = polynomialGradient 16 7 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.wall 5 0 0) 8 = polynomialGradient 16 8 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.wall 5 0 0) 9 = polynomialGradient 16 9 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.wall 5 0 0) 10 = polynomialGradient 16 10 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.wall 5 0 0) 11 = polynomialGradient 16 11 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.wall 5 0 0) 12 = polynomialGradient 16 12 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.wall 5 0 0) 13 = polynomialGradient 16 13 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.wall 5 0 0) 14 = polynomialGradient 16 14 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.wall 5 0 0) 18 = polynomialGradient 16 18 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.wall 5 0 0) 19 = polynomialGradient 16 19 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.wall 5 0 0) 20 = polynomialGradient 16 20 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.wall 5 0 0) 21 = polynomialGradient 16 21 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.wall 5 0 0) 22 = polynomialGradient 16 22 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.wall 5 0 0) 23 = polynomialGradient 16 23 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.wall 5 0 0) 24 = polynomialGradient 16 24 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.wall 5 0 0) 25 = polynomialGradient 16 25 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.wall 5 0 0) 26 = polynomialGradient 16 26 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.wall 5 0 0) 27 = polynomialGradient 16 27 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.wall 5 0 0) 28 = polynomialGradient 16 28 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.wall 5 0 0) 29 = polynomialGradient 16 29 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.wall 5 0 0) 30 = polynomialGradient 16 30 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.wall 5 0 0) 31 = polynomialGradient 16 31 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.wall 5 0 0) 32 = polynomialGradient 16 32 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row16_alias0_gradient : gapGradient T constructionSquare (Gap.wall 5 0 0) = polynomialGradient 16 := by
  funext j
  fin_cases j
  · exact row16_alias0_coordinate_00
  · exact row16_alias0_coordinate_01
  · exact row16_alias0_coordinate_02
  · exact row16_alias0_coordinate_03
  · exact row16_alias0_coordinate_04
  · exact row16_alias0_coordinate_05
  · exact row16_alias0_coordinate_06
  · exact row16_alias0_coordinate_07
  · exact row16_alias0_coordinate_08
  · exact row16_alias0_coordinate_09
  · exact row16_alias0_coordinate_10
  · exact row16_alias0_coordinate_11
  · exact row16_alias0_coordinate_12
  · exact row16_alias0_coordinate_13
  · exact row16_alias0_coordinate_14
  · exact row16_alias0_coordinate_15
  · exact row16_alias0_coordinate_16
  · exact row16_alias0_coordinate_17
  · exact row16_alias0_coordinate_18
  · exact row16_alias0_coordinate_19
  · exact row16_alias0_coordinate_20
  · exact row16_alias0_coordinate_21
  · exact row16_alias0_coordinate_22
  · exact row16_alias0_coordinate_23
  · exact row16_alias0_coordinate_24
  · exact row16_alias0_coordinate_25
  · exact row16_alias0_coordinate_26
  · exact row16_alias0_coordinate_27
  · exact row16_alias0_coordinate_28
  · exact row16_alias0_coordinate_29
  · exact row16_alias0_coordinate_30
  · exact row16_alias0_coordinate_31
  · exact row16_alias0_coordinate_32

theorem row16_aliases_tied (g : Gap) (hg : g ∈ rowAliases 16) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 16 := by
  change g ∈ [Gap.wall 5 0 0] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row16_alias0_zero, row16_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
