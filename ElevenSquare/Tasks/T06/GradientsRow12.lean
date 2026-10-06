import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row12_alias0_zero : gapValue T constructionSquare (Gap.wall 3 2 3) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.wall 3 2 3) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (constructionSide-((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (1 / 2)*(1)))) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row12_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.wall 3 2 3) 9 = polynomialGradient 12 9 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 2 3) 9 = wallGradientFormula constructionSquare 3 2 3 9 := gapGradient_wall T constructionSquare 3 2 3 9
    _ = (-((0 + (1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 12 9 := rfl

theorem row12_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.wall 3 2 3) 10 = polynomialGradient 12 10 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 2 3) 10 = wallGradientFormula constructionSquare 3 2 3 10 := gapGradient_wall T constructionSquare 3 2 3 10
    _ = (-((1 + (1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))) := rfl
    _ = polyEval ![-1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 12 10 := rfl

theorem row12_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.wall 3 2 3) 11 = polynomialGradient 12 11 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 2 3) 11 = wallGradientFormula constructionSquare 3 2 3 11 := gapGradient_wall T constructionSquare 3 2 3 11
    _ = (-((0 + (1 / 2)*(((1)*1)) + (1 / 2)*((-(0)*1))))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 12 11 := rfl

theorem row12_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.wall 3 2 3) 0 = polynomialGradient 12 0 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.wall 3 2 3) 1 = polynomialGradient 12 1 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.wall 3 2 3) 2 = polynomialGradient 12 2 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.wall 3 2 3) 3 = polynomialGradient 12 3 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.wall 3 2 3) 4 = polynomialGradient 12 4 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.wall 3 2 3) 5 = polynomialGradient 12 5 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.wall 3 2 3) 6 = polynomialGradient 12 6 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.wall 3 2 3) 7 = polynomialGradient 12 7 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.wall 3 2 3) 8 = polynomialGradient 12 8 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.wall 3 2 3) 12 = polynomialGradient 12 12 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.wall 3 2 3) 13 = polynomialGradient 12 13 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.wall 3 2 3) 14 = polynomialGradient 12 14 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.wall 3 2 3) 15 = polynomialGradient 12 15 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.wall 3 2 3) 16 = polynomialGradient 12 16 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.wall 3 2 3) 17 = polynomialGradient 12 17 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.wall 3 2 3) 18 = polynomialGradient 12 18 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.wall 3 2 3) 19 = polynomialGradient 12 19 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.wall 3 2 3) 20 = polynomialGradient 12 20 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.wall 3 2 3) 21 = polynomialGradient 12 21 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.wall 3 2 3) 22 = polynomialGradient 12 22 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.wall 3 2 3) 23 = polynomialGradient 12 23 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.wall 3 2 3) 24 = polynomialGradient 12 24 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.wall 3 2 3) 25 = polynomialGradient 12 25 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.wall 3 2 3) 26 = polynomialGradient 12 26 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.wall 3 2 3) 27 = polynomialGradient 12 27 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.wall 3 2 3) 28 = polynomialGradient 12 28 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.wall 3 2 3) 29 = polynomialGradient 12 29 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.wall 3 2 3) 30 = polynomialGradient 12 30 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.wall 3 2 3) 31 = polynomialGradient 12 31 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.wall 3 2 3) 32 = polynomialGradient 12 32 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row12_alias0_gradient : gapGradient T constructionSquare (Gap.wall 3 2 3) = polynomialGradient 12 := by
  funext j
  fin_cases j
  · exact row12_alias0_coordinate_00
  · exact row12_alias0_coordinate_01
  · exact row12_alias0_coordinate_02
  · exact row12_alias0_coordinate_03
  · exact row12_alias0_coordinate_04
  · exact row12_alias0_coordinate_05
  · exact row12_alias0_coordinate_06
  · exact row12_alias0_coordinate_07
  · exact row12_alias0_coordinate_08
  · exact row12_alias0_coordinate_09
  · exact row12_alias0_coordinate_10
  · exact row12_alias0_coordinate_11
  · exact row12_alias0_coordinate_12
  · exact row12_alias0_coordinate_13
  · exact row12_alias0_coordinate_14
  · exact row12_alias0_coordinate_15
  · exact row12_alias0_coordinate_16
  · exact row12_alias0_coordinate_17
  · exact row12_alias0_coordinate_18
  · exact row12_alias0_coordinate_19
  · exact row12_alias0_coordinate_20
  · exact row12_alias0_coordinate_21
  · exact row12_alias0_coordinate_22
  · exact row12_alias0_coordinate_23
  · exact row12_alias0_coordinate_24
  · exact row12_alias0_coordinate_25
  · exact row12_alias0_coordinate_26
  · exact row12_alias0_coordinate_27
  · exact row12_alias0_coordinate_28
  · exact row12_alias0_coordinate_29
  · exact row12_alias0_coordinate_30
  · exact row12_alias0_coordinate_31
  · exact row12_alias0_coordinate_32

theorem row12_aliases_tied (g : Gap) (hg : g ∈ rowAliases 12) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 12 := by
  change g ∈ [Gap.wall 3 2 3] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row12_alias0_zero, row12_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
