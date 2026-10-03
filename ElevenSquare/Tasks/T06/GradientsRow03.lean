import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row03_alias0_zero : gapValue T constructionSquare (Gap.wall 0 1 2) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.wall 0 1 2) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (((1 / 2)) + (1 / 2)*(0) + (-1 / 2)*(1)) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row03_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.wall 0 1 2) 0 = polynomialGradient 3 0 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 1 2) 0 = wallGradientFormula constructionSquare 0 1 2 0 := gapGradient_wall T constructionSquare 0 1 2 0
    _ = (0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 3 0 := rfl

theorem row03_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.wall 0 1 2) 1 = polynomialGradient 3 1 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 1 2) 1 = wallGradientFormula constructionSquare 0 1 2 1 := gapGradient_wall T constructionSquare 0 1 2 1
    _ = (1 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))) := rfl
    _ = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 3 1 := rfl

theorem row03_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.wall 0 1 2) 2 = polynomialGradient 3 2 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 1 2) 2 = wallGradientFormula constructionSquare 0 1 2 2 := gapGradient_wall T constructionSquare 0 1 2 2
    _ = (0 + (1 / 2)*(((1)*1)) + (-1 / 2)*((-(0)*1))) := rfl
    _ = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 3 2 := rfl

theorem row03_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.wall 0 1 2) 3 = polynomialGradient 3 3 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.wall 0 1 2) 4 = polynomialGradient 3 4 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.wall 0 1 2) 5 = polynomialGradient 3 5 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.wall 0 1 2) 6 = polynomialGradient 3 6 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.wall 0 1 2) 7 = polynomialGradient 3 7 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.wall 0 1 2) 8 = polynomialGradient 3 8 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.wall 0 1 2) 9 = polynomialGradient 3 9 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.wall 0 1 2) 10 = polynomialGradient 3 10 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.wall 0 1 2) 11 = polynomialGradient 3 11 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.wall 0 1 2) 12 = polynomialGradient 3 12 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.wall 0 1 2) 13 = polynomialGradient 3 13 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.wall 0 1 2) 14 = polynomialGradient 3 14 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.wall 0 1 2) 15 = polynomialGradient 3 15 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.wall 0 1 2) 16 = polynomialGradient 3 16 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.wall 0 1 2) 17 = polynomialGradient 3 17 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.wall 0 1 2) 18 = polynomialGradient 3 18 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.wall 0 1 2) 19 = polynomialGradient 3 19 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.wall 0 1 2) 20 = polynomialGradient 3 20 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.wall 0 1 2) 21 = polynomialGradient 3 21 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.wall 0 1 2) 22 = polynomialGradient 3 22 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.wall 0 1 2) 23 = polynomialGradient 3 23 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.wall 0 1 2) 24 = polynomialGradient 3 24 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.wall 0 1 2) 25 = polynomialGradient 3 25 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.wall 0 1 2) 26 = polynomialGradient 3 26 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.wall 0 1 2) 27 = polynomialGradient 3 27 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.wall 0 1 2) 28 = polynomialGradient 3 28 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.wall 0 1 2) 29 = polynomialGradient 3 29 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.wall 0 1 2) 30 = polynomialGradient 3 30 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.wall 0 1 2) 31 = polynomialGradient 3 31 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.wall 0 1 2) 32 = polynomialGradient 3 32 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row03_alias0_gradient : gapGradient T constructionSquare (Gap.wall 0 1 2) = polynomialGradient 3 := by
  funext j
  fin_cases j
  · exact row03_alias0_coordinate_00
  · exact row03_alias0_coordinate_01
  · exact row03_alias0_coordinate_02
  · exact row03_alias0_coordinate_03
  · exact row03_alias0_coordinate_04
  · exact row03_alias0_coordinate_05
  · exact row03_alias0_coordinate_06
  · exact row03_alias0_coordinate_07
  · exact row03_alias0_coordinate_08
  · exact row03_alias0_coordinate_09
  · exact row03_alias0_coordinate_10
  · exact row03_alias0_coordinate_11
  · exact row03_alias0_coordinate_12
  · exact row03_alias0_coordinate_13
  · exact row03_alias0_coordinate_14
  · exact row03_alias0_coordinate_15
  · exact row03_alias0_coordinate_16
  · exact row03_alias0_coordinate_17
  · exact row03_alias0_coordinate_18
  · exact row03_alias0_coordinate_19
  · exact row03_alias0_coordinate_20
  · exact row03_alias0_coordinate_21
  · exact row03_alias0_coordinate_22
  · exact row03_alias0_coordinate_23
  · exact row03_alias0_coordinate_24
  · exact row03_alias0_coordinate_25
  · exact row03_alias0_coordinate_26
  · exact row03_alias0_coordinate_27
  · exact row03_alias0_coordinate_28
  · exact row03_alias0_coordinate_29
  · exact row03_alias0_coordinate_30
  · exact row03_alias0_coordinate_31
  · exact row03_alias0_coordinate_32

theorem row03_aliases_tied (g : Gap) (hg : g ∈ rowAliases 3) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 3 := by
  change g ∈ [Gap.wall 0 1 2] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row03_alias0_zero, row03_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
