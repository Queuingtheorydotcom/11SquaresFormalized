import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row29_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (-1*((((((1 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((3 / 2)))*((-(0))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(1)) - 1/2) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row29_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 12 = polynomialGradient 29 12 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 12 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 12 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 12
    _ = (-1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(1))*((-(0))) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((3 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*((-(0)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 29 12 := rfl

theorem row29_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 13 = polynomialGradient 29 13 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 13 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 13 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 13
    _ = (-1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*((-(0))) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(1))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((3 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*((-(0)*0))))) := rfl
    _ = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 29 13 := rfl

theorem row29_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 14 = polynomialGradient 29 14 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 14 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 14 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 14
    _ = (-1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*((-(0))) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((3 / 2)))*((-(((1)*1)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*((-(0)*1))))) := rfl
    _ = polyEval ![(-3 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 29 14 := rfl

theorem row29_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 15 = polynomialGradient 29 15 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 15 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 15 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 15
    _ = (-1*(((((1 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*((-(0))) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((3 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*((-(0)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 29 15 := rfl

theorem row29_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 16 = polynomialGradient 29 16 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 16 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 16 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 16
    _ = (-1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*((-(0))) + (((1 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((3 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*((-(0)*0))))) := rfl
    _ = polyEval ![-1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 29 16 := rfl

theorem row29_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 17 = polynomialGradient 29 17 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 17 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 17 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 17
    _ = (-1*(((((0 + (-1 / 2)*((-(0)*1)) + (1 / 2)*(-(((1)*1)))))-(0))*((-(0))) + (((0 + (-1 / 2)*(((1)*1)) + (1 / 2)*((-(0)*1))))-(0))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((3 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*((-(0)*0))))) := rfl
    _ = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 29 17 := rfl

theorem row29_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 0 = polynomialGradient 29 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 1 = polynomialGradient 29 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 2 = polynomialGradient 29 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 3 = polynomialGradient 29 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 4 = polynomialGradient 29 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 5 = polynomialGradient 29 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 6 = polynomialGradient 29 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 7 = polynomialGradient 29 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 8 = polynomialGradient 29 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 9 = polynomialGradient 29 9 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 10 = polynomialGradient 29 10 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 11 = polynomialGradient 29 11 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 18 = polynomialGradient 29 18 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 19 = polynomialGradient 29 19 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 20 = polynomialGradient 29 20 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 21 = polynomialGradient 29 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 22 = polynomialGradient 29 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 23 = polynomialGradient 29 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 24 = polynomialGradient 29 24 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 25 = polynomialGradient 29 25 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 26 = polynomialGradient 29 26 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 27 = polynomialGradient 29 27 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 28 = polynomialGradient 29 28 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 29 = polynomialGradient 29 29 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 30 = polynomialGradient 29 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 31 = polynomialGradient 29 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 32 = polynomialGradient 29 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row29_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) = polynomialGradient 29 := by
  funext j
  fin_cases j
  · exact row29_alias0_coordinate_00
  · exact row29_alias0_coordinate_01
  · exact row29_alias0_coordinate_02
  · exact row29_alias0_coordinate_03
  · exact row29_alias0_coordinate_04
  · exact row29_alias0_coordinate_05
  · exact row29_alias0_coordinate_06
  · exact row29_alias0_coordinate_07
  · exact row29_alias0_coordinate_08
  · exact row29_alias0_coordinate_09
  · exact row29_alias0_coordinate_10
  · exact row29_alias0_coordinate_11
  · exact row29_alias0_coordinate_12
  · exact row29_alias0_coordinate_13
  · exact row29_alias0_coordinate_14
  · exact row29_alias0_coordinate_15
  · exact row29_alias0_coordinate_16
  · exact row29_alias0_coordinate_17
  · exact row29_alias0_coordinate_18
  · exact row29_alias0_coordinate_19
  · exact row29_alias0_coordinate_20
  · exact row29_alias0_coordinate_21
  · exact row29_alias0_coordinate_22
  · exact row29_alias0_coordinate_23
  · exact row29_alias0_coordinate_24
  · exact row29_alias0_coordinate_25
  · exact row29_alias0_coordinate_26
  · exact row29_alias0_coordinate_27
  · exact row29_alias0_coordinate_28
  · exact row29_alias0_coordinate_29
  · exact row29_alias0_coordinate_30
  · exact row29_alias0_coordinate_31
  · exact row29_alias0_coordinate_32

theorem row29_aliases_tied (g : Gap) (hg : g ∈ rowAliases 29) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 29 := by
  change g ∈ [Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row29_alias0_zero, row29_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
