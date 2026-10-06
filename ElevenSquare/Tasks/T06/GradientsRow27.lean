import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row27_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (-1*((((((1 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((1 / 2)))*((-(0))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(1)) - 1/2) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row27_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 9 = polynomialGradient 27 9 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 9 = pairGradientFormula constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 9 := gapGradient_pair T constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 9
    _ = (-1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(1))*((-(0))) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*((-(0)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 27 9 := rfl

theorem row27_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 10 = polynomialGradient 27 10 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 10 = pairGradientFormula constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 10 := gapGradient_pair T constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 10
    _ = (-1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*((-(0))) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(1))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*((-(0)*0))))) := rfl
    _ = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 27 10 := rfl

theorem row27_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 11 = polynomialGradient 27 11 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 11 = pairGradientFormula constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 11 := gapGradient_pair T constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 11
    _ = (-1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*((-(0))) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*1)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*((-(0)*1))))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 27 11 := rfl

theorem row27_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 15 = polynomialGradient 27 15 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 15 = pairGradientFormula constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 15 := gapGradient_pair T constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 15
    _ = (-1*(((((1 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*((-(0))) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*((-(0)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 27 15 := rfl

theorem row27_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 16 = polynomialGradient 27 16 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 16 = pairGradientFormula constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 16 := gapGradient_pair T constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 16
    _ = (-1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*((-(0))) + (((1 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*((-(0)*0))))) := rfl
    _ = polyEval ![-1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 27 16 := rfl

theorem row27_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 17 = polynomialGradient 27 17 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 17 = pairGradientFormula constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 17 := gapGradient_pair T constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 17
    _ = (-1*(((((0 + (-1 / 2)*((-(0)*1)) + (1 / 2)*(-(((1)*1)))))-(0))*((-(0))) + (((0 + (-1 / 2)*(((1)*1)) + (1 / 2)*((-(0)*1))))-(0))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*((-(0)*0))))) := rfl
    _ = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 27 17 := rfl

theorem row27_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 0 = polynomialGradient 27 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 1 = polynomialGradient 27 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 2 = polynomialGradient 27 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 3 = polynomialGradient 27 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 4 = polynomialGradient 27 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 5 = polynomialGradient 27 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 6 = polynomialGradient 27 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 7 = polynomialGradient 27 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 8 = polynomialGradient 27 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 12 = polynomialGradient 27 12 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 13 = polynomialGradient 27 13 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 14 = polynomialGradient 27 14 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 18 = polynomialGradient 27 18 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 19 = polynomialGradient 27 19 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 20 = polynomialGradient 27 20 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 21 = polynomialGradient 27 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 22 = polynomialGradient 27 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 23 = polynomialGradient 27 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 24 = polynomialGradient 27 24 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 25 = polynomialGradient 27 25 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 26 = polynomialGradient 27 26 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 27 = polynomialGradient 27 27 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 28 = polynomialGradient 27 28 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 29 = polynomialGradient 27 29 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 30 = polynomialGradient 27 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 31 = polynomialGradient 27 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 32 = polynomialGradient 27 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) = polynomialGradient 27 := by
  funext j
  fin_cases j
  · exact row27_alias0_coordinate_00
  · exact row27_alias0_coordinate_01
  · exact row27_alias0_coordinate_02
  · exact row27_alias0_coordinate_03
  · exact row27_alias0_coordinate_04
  · exact row27_alias0_coordinate_05
  · exact row27_alias0_coordinate_06
  · exact row27_alias0_coordinate_07
  · exact row27_alias0_coordinate_08
  · exact row27_alias0_coordinate_09
  · exact row27_alias0_coordinate_10
  · exact row27_alias0_coordinate_11
  · exact row27_alias0_coordinate_12
  · exact row27_alias0_coordinate_13
  · exact row27_alias0_coordinate_14
  · exact row27_alias0_coordinate_15
  · exact row27_alias0_coordinate_16
  · exact row27_alias0_coordinate_17
  · exact row27_alias0_coordinate_18
  · exact row27_alias0_coordinate_19
  · exact row27_alias0_coordinate_20
  · exact row27_alias0_coordinate_21
  · exact row27_alias0_coordinate_22
  · exact row27_alias0_coordinate_23
  · exact row27_alias0_coordinate_24
  · exact row27_alias0_coordinate_25
  · exact row27_alias0_coordinate_26
  · exact row27_alias0_coordinate_27
  · exact row27_alias0_coordinate_28
  · exact row27_alias0_coordinate_29
  · exact row27_alias0_coordinate_30
  · exact row27_alias0_coordinate_31
  · exact row27_alias0_coordinate_32

theorem row27_alias1_zero : gapValue T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (1*((((((1 / 2)) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(0))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1))*(1)) - 1/2) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row27_alias1_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 9 = polynomialGradient 27 9 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 9 = pairGradientFormula constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0 9 := gapGradient_pair T constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0 9
    _ = (1*(((((1 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(0))) + (((0 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1))*((-(0)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 27 9 := rfl

theorem row27_alias1_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 10 = polynomialGradient 27 10 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 10 = pairGradientFormula constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0 10 := gapGradient_pair T constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0 10
    _ = (1*(((((0 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(0))) + (((1 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1))*((-(0)*0))))) := rfl
    _ = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 27 10 := rfl

theorem row27_alias1_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 11 = polynomialGradient 27 11 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 11 = pairGradientFormula constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0 11 := gapGradient_pair T constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0 11
    _ = (1*(((((0 + (-1 / 2)*((-(0)*1)) + (-1 / 2)*(-(((1)*1)))))-(0))*((-(0))) + (((0 + (-1 / 2)*(((1)*1)) + (-1 / 2)*((-(0)*1))))-(0))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1))*((-(0)*0))))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 27 11 := rfl

theorem row27_alias1_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 15 = polynomialGradient 27 15 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 15 = pairGradientFormula constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0 15 := gapGradient_pair T constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0 15
    _ = (1*(((((0 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(1))*((-(0))) + (((0 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1))*((-(0)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 27 15 := rfl

theorem row27_alias1_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 16 = polynomialGradient 27 16 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 16 = pairGradientFormula constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0 16 := gapGradient_pair T constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0 16
    _ = (1*(((((0 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(0))) + (((0 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(1))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1))*((-(0)*0))))) := rfl
    _ = polyEval ![-1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 27 16 := rfl

theorem row27_alias1_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 17 = polynomialGradient 27 17 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 17 = pairGradientFormula constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0 17 := gapGradient_pair T constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0 17
    _ = (1*(((((0 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(0))) + (((0 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(1)) + ((((((1 / 2)) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(((1)*1)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1))*((-(0)*1))))) := rfl
    _ = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 27 17 := rfl

theorem row27_alias1_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 0 = polynomialGradient 27 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 1 = polynomialGradient 27 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 2 = polynomialGradient 27 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 3 = polynomialGradient 27 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 4 = polynomialGradient 27 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 5 = polynomialGradient 27 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 6 = polynomialGradient 27 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 7 = polynomialGradient 27 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 8 = polynomialGradient 27 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 12 = polynomialGradient 27 12 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 13 = polynomialGradient 27 13 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 14 = polynomialGradient 27 14 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 18 = polynomialGradient 27 18 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 19 = polynomialGradient 27 19 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 20 = polynomialGradient 27 20 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 21 = polynomialGradient 27 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 22 = polynomialGradient 27 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 23 = polynomialGradient 27 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 24 = polynomialGradient 27 24 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 25 = polynomialGradient 27 25 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 26 = polynomialGradient 27 26 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 27 = polynomialGradient 27 27 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 28 = polynomialGradient 27 28 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 29 = polynomialGradient 27 29 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 30 = polynomialGradient 27 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 31 = polynomialGradient 27 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) 32 = polynomialGradient 27 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row27_alias1_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0) = polynomialGradient 27 := by
  funext j
  fin_cases j
  · exact row27_alias1_coordinate_00
  · exact row27_alias1_coordinate_01
  · exact row27_alias1_coordinate_02
  · exact row27_alias1_coordinate_03
  · exact row27_alias1_coordinate_04
  · exact row27_alias1_coordinate_05
  · exact row27_alias1_coordinate_06
  · exact row27_alias1_coordinate_07
  · exact row27_alias1_coordinate_08
  · exact row27_alias1_coordinate_09
  · exact row27_alias1_coordinate_10
  · exact row27_alias1_coordinate_11
  · exact row27_alias1_coordinate_12
  · exact row27_alias1_coordinate_13
  · exact row27_alias1_coordinate_14
  · exact row27_alias1_coordinate_15
  · exact row27_alias1_coordinate_16
  · exact row27_alias1_coordinate_17
  · exact row27_alias1_coordinate_18
  · exact row27_alias1_coordinate_19
  · exact row27_alias1_coordinate_20
  · exact row27_alias1_coordinate_21
  · exact row27_alias1_coordinate_22
  · exact row27_alias1_coordinate_23
  · exact row27_alias1_coordinate_24
  · exact row27_alias1_coordinate_25
  · exact row27_alias1_coordinate_26
  · exact row27_alias1_coordinate_27
  · exact row27_alias1_coordinate_28
  · exact row27_alias1_coordinate_29
  · exact row27_alias1_coordinate_30
  · exact row27_alias1_coordinate_31
  · exact row27_alias1_coordinate_32

theorem row27_aliases_tied (g : Gap) (hg : g ∈ rowAliases 27) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 27 := by
  change g ∈ [Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3, Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 0] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ⟨row27_alias0_zero, row27_alias0_gradient⟩
  · exact ⟨row27_alias1_zero, row27_alias1_gradient⟩

end
end ElevenSquare.Tasks.T06
