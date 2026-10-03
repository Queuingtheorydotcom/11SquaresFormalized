import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row42_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (1*((((((3 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(0))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1))*(1)) - 1/2) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row42_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 12 = polynomialGradient 42 12 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 12 = pairGradientFormula constructionSquare ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 12 := gapGradient_pair T constructionSquare ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 12
    _ = (1*(((((1 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(0))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(1)) + ((((((3 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1))*((-(0)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 42 12 := rfl

theorem row42_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 13 = polynomialGradient 42 13 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 13 = pairGradientFormula constructionSquare ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 13 := gapGradient_pair T constructionSquare ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 13
    _ = (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(0))) + (((1 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(1)) + ((((((3 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1))*((-(0)*0))))) := rfl
    _ = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 42 13 := rfl

theorem row42_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 14 = polynomialGradient 42 14 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 14 = pairGradientFormula constructionSquare ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 14 := gapGradient_pair T constructionSquare ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 14
    _ = (1*(((((0 + (1 / 2)*((-(0)*1)) + (-1 / 2)*(-(((1)*1)))))-(0))*((-(0))) + (((0 + (1 / 2)*(((1)*1)) + (-1 / 2)*((-(0)*1))))-(0))*(1)) + ((((((3 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1))*((-(0)*0))))) := rfl
    _ = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 42 14 := rfl

theorem row42_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 15 = polynomialGradient 42 15 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 15 = pairGradientFormula constructionSquare ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 15 := gapGradient_pair T constructionSquare ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 15
    _ = (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(1))*((-(0))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(1)) + ((((((3 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1))*((-(0)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 42 15 := rfl

theorem row42_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 16 = polynomialGradient 42 16 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 16 = pairGradientFormula constructionSquare ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 16 := gapGradient_pair T constructionSquare ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 16
    _ = (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(0))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(1))*(1)) + ((((((3 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1))*((-(0)*0))))) := rfl
    _ = polyEval ![-1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 42 16 := rfl

theorem row42_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 17 = polynomialGradient 42 17 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 17 = pairGradientFormula constructionSquare ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 17 := gapGradient_pair T constructionSquare ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 17
    _ = (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(0))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(1)) + ((((((3 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*1)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1))*((-(0)*1))))) := rfl
    _ = polyEval ![(-3 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 42 17 := rfl

theorem row42_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 0 = polynomialGradient 42 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 1 = polynomialGradient 42 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 2 = polynomialGradient 42 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 3 = polynomialGradient 42 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 4 = polynomialGradient 42 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 5 = polynomialGradient 42 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 6 = polynomialGradient 42 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 7 = polynomialGradient 42 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 8 = polynomialGradient 42 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 9 = polynomialGradient 42 9 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 10 = polynomialGradient 42 10 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 11 = polynomialGradient 42 11 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 18 = polynomialGradient 42 18 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 19 = polynomialGradient 42 19 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 20 = polynomialGradient 42 20 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 21 = polynomialGradient 42 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 22 = polynomialGradient 42 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 23 = polynomialGradient 42 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 24 = polynomialGradient 42 24 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 25 = polynomialGradient 42 25 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 26 = polynomialGradient 42 26 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 27 = polynomialGradient 42 27 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 28 = polynomialGradient 42 28 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 29 = polynomialGradient 42 29 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 30 = polynomialGradient 42 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 31 = polynomialGradient 42 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 32 = polynomialGradient 42 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row42_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) = polynomialGradient 42 := by
  funext j
  fin_cases j
  · exact row42_alias0_coordinate_00
  · exact row42_alias0_coordinate_01
  · exact row42_alias0_coordinate_02
  · exact row42_alias0_coordinate_03
  · exact row42_alias0_coordinate_04
  · exact row42_alias0_coordinate_05
  · exact row42_alias0_coordinate_06
  · exact row42_alias0_coordinate_07
  · exact row42_alias0_coordinate_08
  · exact row42_alias0_coordinate_09
  · exact row42_alias0_coordinate_10
  · exact row42_alias0_coordinate_11
  · exact row42_alias0_coordinate_12
  · exact row42_alias0_coordinate_13
  · exact row42_alias0_coordinate_14
  · exact row42_alias0_coordinate_15
  · exact row42_alias0_coordinate_16
  · exact row42_alias0_coordinate_17
  · exact row42_alias0_coordinate_18
  · exact row42_alias0_coordinate_19
  · exact row42_alias0_coordinate_20
  · exact row42_alias0_coordinate_21
  · exact row42_alias0_coordinate_22
  · exact row42_alias0_coordinate_23
  · exact row42_alias0_coordinate_24
  · exact row42_alias0_coordinate_25
  · exact row42_alias0_coordinate_26
  · exact row42_alias0_coordinate_27
  · exact row42_alias0_coordinate_28
  · exact row42_alias0_coordinate_29
  · exact row42_alias0_coordinate_30
  · exact row42_alias0_coordinate_31
  · exact row42_alias0_coordinate_32

theorem row42_aliases_tied (g : Gap) (hg : g ∈ rowAliases 42) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 42 := by
  change g ∈ [Gap.pair ({ owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row42_alias0_zero, row42_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
