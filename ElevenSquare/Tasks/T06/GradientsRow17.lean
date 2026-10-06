import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row17_alias0_zero : gapValue T constructionSquare (Gap.wall 5 3 0) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.wall 5 3 0) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (((1 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row17_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.wall 5 3 0) 15 = polynomialGradient 17 15 := by
  calc
    gapGradient T constructionSquare (Gap.wall 5 3 0) 15 = wallGradientFormula constructionSquare 5 3 0 15 := gapGradient_wall T constructionSquare 5 3 0 15
    _ = (1 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))) := rfl
    _ = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 17 15 := rfl

theorem row17_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.wall 5 3 0) 16 = polynomialGradient 17 16 := by
  calc
    gapGradient T constructionSquare (Gap.wall 5 3 0) 16 = wallGradientFormula constructionSquare 5 3 0 16 := gapGradient_wall T constructionSquare 5 3 0 16
    _ = (0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 17 16 := rfl

theorem row17_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.wall 5 3 0) 17 = polynomialGradient 17 17 := by
  calc
    gapGradient T constructionSquare (Gap.wall 5 3 0) 17 = wallGradientFormula constructionSquare 5 3 0 17 := gapGradient_wall T constructionSquare 5 3 0 17
    _ = (0 + (-1 / 2)*((-(0)*1)) + (1 / 2)*(-(((1)*1)))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 17 17 := rfl

theorem row17_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.wall 5 3 0) 0 = polynomialGradient 17 0 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.wall 5 3 0) 1 = polynomialGradient 17 1 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.wall 5 3 0) 2 = polynomialGradient 17 2 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.wall 5 3 0) 3 = polynomialGradient 17 3 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.wall 5 3 0) 4 = polynomialGradient 17 4 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.wall 5 3 0) 5 = polynomialGradient 17 5 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.wall 5 3 0) 6 = polynomialGradient 17 6 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.wall 5 3 0) 7 = polynomialGradient 17 7 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.wall 5 3 0) 8 = polynomialGradient 17 8 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.wall 5 3 0) 9 = polynomialGradient 17 9 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.wall 5 3 0) 10 = polynomialGradient 17 10 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.wall 5 3 0) 11 = polynomialGradient 17 11 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.wall 5 3 0) 12 = polynomialGradient 17 12 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.wall 5 3 0) 13 = polynomialGradient 17 13 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.wall 5 3 0) 14 = polynomialGradient 17 14 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.wall 5 3 0) 18 = polynomialGradient 17 18 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.wall 5 3 0) 19 = polynomialGradient 17 19 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.wall 5 3 0) 20 = polynomialGradient 17 20 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.wall 5 3 0) 21 = polynomialGradient 17 21 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.wall 5 3 0) 22 = polynomialGradient 17 22 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.wall 5 3 0) 23 = polynomialGradient 17 23 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.wall 5 3 0) 24 = polynomialGradient 17 24 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.wall 5 3 0) 25 = polynomialGradient 17 25 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.wall 5 3 0) 26 = polynomialGradient 17 26 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.wall 5 3 0) 27 = polynomialGradient 17 27 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.wall 5 3 0) 28 = polynomialGradient 17 28 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.wall 5 3 0) 29 = polynomialGradient 17 29 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.wall 5 3 0) 30 = polynomialGradient 17 30 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.wall 5 3 0) 31 = polynomialGradient 17 31 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.wall 5 3 0) 32 = polynomialGradient 17 32 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row17_alias0_gradient : gapGradient T constructionSquare (Gap.wall 5 3 0) = polynomialGradient 17 := by
  funext j
  fin_cases j
  · exact row17_alias0_coordinate_00
  · exact row17_alias0_coordinate_01
  · exact row17_alias0_coordinate_02
  · exact row17_alias0_coordinate_03
  · exact row17_alias0_coordinate_04
  · exact row17_alias0_coordinate_05
  · exact row17_alias0_coordinate_06
  · exact row17_alias0_coordinate_07
  · exact row17_alias0_coordinate_08
  · exact row17_alias0_coordinate_09
  · exact row17_alias0_coordinate_10
  · exact row17_alias0_coordinate_11
  · exact row17_alias0_coordinate_12
  · exact row17_alias0_coordinate_13
  · exact row17_alias0_coordinate_14
  · exact row17_alias0_coordinate_15
  · exact row17_alias0_coordinate_16
  · exact row17_alias0_coordinate_17
  · exact row17_alias0_coordinate_18
  · exact row17_alias0_coordinate_19
  · exact row17_alias0_coordinate_20
  · exact row17_alias0_coordinate_21
  · exact row17_alias0_coordinate_22
  · exact row17_alias0_coordinate_23
  · exact row17_alias0_coordinate_24
  · exact row17_alias0_coordinate_25
  · exact row17_alias0_coordinate_26
  · exact row17_alias0_coordinate_27
  · exact row17_alias0_coordinate_28
  · exact row17_alias0_coordinate_29
  · exact row17_alias0_coordinate_30
  · exact row17_alias0_coordinate_31
  · exact row17_alias0_coordinate_32

theorem row17_aliases_tied (g : Gap) (hg : g ∈ rowAliases 17) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 17 := by
  change g ∈ [Gap.wall 5 3 0] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row17_alias0_zero, row17_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
