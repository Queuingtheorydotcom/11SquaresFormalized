import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row18_alias0_zero : gapValue T constructionSquare (Gap.wall 7 0 2) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.wall 7 0 2) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (-1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)) = 0 * endpointPolynomial u
        dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row18_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.wall 7 0 2) 21 = polynomialGradient 18 21 := by
  calc
    gapGradient T constructionSquare (Gap.wall 7 0 2) 21 = wallGradientFormula constructionSquare 7 0 2 21 := gapGradient_wall T constructionSquare 7 0 2 21
    _ = (0 + (-1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 18 21 := rfl

theorem row18_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.wall 7 0 2) 22 = polynomialGradient 18 22 := by
  calc
    gapGradient T constructionSquare (Gap.wall 7 0 2) 22 = wallGradientFormula constructionSquare 7 0 2 22 := gapGradient_wall T constructionSquare 7 0 2 22
    _ = (1 + (-1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))) := rfl
    _ = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 18 22 := rfl

theorem row18_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.wall 7 0 2) 23 = polynomialGradient 18 23 := by
  calc
    gapGradient T constructionSquare (Gap.wall 7 0 2) 23 = wallGradientFormula constructionSquare 7 0 2 23 := gapGradient_wall T constructionSquare 7 0 2 23
    _ = (0 + (-1 / 2)*(((constructionCos)*1)) + (-1 / 2)*((-(constructionSin)*1))) := rfl
    _ = polyEval ![(-39 / 80), (81 / 80), (71 / 80), (-81 / 80), (-13 / 16), (31 / 80), (5 / 16), (-3 / 16)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 18 23 := rfl

theorem row18_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.wall 7 0 2) 0 = polynomialGradient 18 0 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.wall 7 0 2) 1 = polynomialGradient 18 1 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.wall 7 0 2) 2 = polynomialGradient 18 2 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.wall 7 0 2) 3 = polynomialGradient 18 3 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.wall 7 0 2) 4 = polynomialGradient 18 4 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.wall 7 0 2) 5 = polynomialGradient 18 5 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.wall 7 0 2) 6 = polynomialGradient 18 6 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.wall 7 0 2) 7 = polynomialGradient 18 7 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.wall 7 0 2) 8 = polynomialGradient 18 8 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.wall 7 0 2) 9 = polynomialGradient 18 9 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.wall 7 0 2) 10 = polynomialGradient 18 10 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.wall 7 0 2) 11 = polynomialGradient 18 11 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.wall 7 0 2) 12 = polynomialGradient 18 12 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.wall 7 0 2) 13 = polynomialGradient 18 13 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.wall 7 0 2) 14 = polynomialGradient 18 14 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.wall 7 0 2) 15 = polynomialGradient 18 15 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.wall 7 0 2) 16 = polynomialGradient 18 16 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.wall 7 0 2) 17 = polynomialGradient 18 17 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.wall 7 0 2) 18 = polynomialGradient 18 18 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.wall 7 0 2) 19 = polynomialGradient 18 19 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.wall 7 0 2) 20 = polynomialGradient 18 20 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.wall 7 0 2) 24 = polynomialGradient 18 24 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.wall 7 0 2) 25 = polynomialGradient 18 25 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.wall 7 0 2) 26 = polynomialGradient 18 26 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.wall 7 0 2) 27 = polynomialGradient 18 27 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.wall 7 0 2) 28 = polynomialGradient 18 28 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.wall 7 0 2) 29 = polynomialGradient 18 29 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.wall 7 0 2) 30 = polynomialGradient 18 30 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.wall 7 0 2) 31 = polynomialGradient 18 31 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.wall 7 0 2) 32 = polynomialGradient 18 32 := by
  apply wallGradient_polynomial_zero <;> decide

theorem row18_alias0_gradient : gapGradient T constructionSquare (Gap.wall 7 0 2) = polynomialGradient 18 := by
  funext j
  fin_cases j
  · exact row18_alias0_coordinate_00
  · exact row18_alias0_coordinate_01
  · exact row18_alias0_coordinate_02
  · exact row18_alias0_coordinate_03
  · exact row18_alias0_coordinate_04
  · exact row18_alias0_coordinate_05
  · exact row18_alias0_coordinate_06
  · exact row18_alias0_coordinate_07
  · exact row18_alias0_coordinate_08
  · exact row18_alias0_coordinate_09
  · exact row18_alias0_coordinate_10
  · exact row18_alias0_coordinate_11
  · exact row18_alias0_coordinate_12
  · exact row18_alias0_coordinate_13
  · exact row18_alias0_coordinate_14
  · exact row18_alias0_coordinate_15
  · exact row18_alias0_coordinate_16
  · exact row18_alias0_coordinate_17
  · exact row18_alias0_coordinate_18
  · exact row18_alias0_coordinate_19
  · exact row18_alias0_coordinate_20
  · exact row18_alias0_coordinate_21
  · exact row18_alias0_coordinate_22
  · exact row18_alias0_coordinate_23
  · exact row18_alias0_coordinate_24
  · exact row18_alias0_coordinate_25
  · exact row18_alias0_coordinate_26
  · exact row18_alias0_coordinate_27
  · exact row18_alias0_coordinate_28
  · exact row18_alias0_coordinate_29
  · exact row18_alias0_coordinate_30
  · exact row18_alias0_coordinate_31
  · exact row18_alias0_coordinate_32

theorem row18_aliases_tied (g : Gap) (hg : g ∈ rowAliases 18) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 18 := by
  change g ∈ [Gap.wall 7 0 2] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row18_alias0_zero, row18_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
