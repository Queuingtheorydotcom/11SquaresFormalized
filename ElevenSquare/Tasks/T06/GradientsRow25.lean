import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row25_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (1*((((((3 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((1 / 2)))*(1) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(0)) - 1/2) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row25_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 9 = polynomialGradient 25 9 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 9 = pairGradientFormula constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3 9 := gapGradient_pair T constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3 9
    _ = (1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(1))*(1) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((3 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((1 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![-1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 25 9 := rfl

theorem row25_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 10 = polynomialGradient 25 10 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 10 = pairGradientFormula constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3 10 := gapGradient_pair T constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3 10
    _ = (1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*(1) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(1))*(0)) + ((((((3 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((1 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 25 10 := rfl

theorem row25_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 11 = polynomialGradient 25 11 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 11 = pairGradientFormula constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3 11 := gapGradient_pair T constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3 11
    _ = (1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*(1) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((3 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((1 / 2)))*((-(0)*1)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*1))))) := rfl
    _ = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 25 11 := rfl

theorem row25_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 12 = polynomialGradient 25 12 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 12 = pairGradientFormula constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3 12 := gapGradient_pair T constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3 12
    _ = (1*(((((1 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*(1) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((3 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((1 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 25 12 := rfl

theorem row25_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 13 = polynomialGradient 25 13 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 13 = pairGradientFormula constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3 13 := gapGradient_pair T constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3 13
    _ = (1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*(1) + (((1 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((3 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((1 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 25 13 := rfl

theorem row25_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 14 = polynomialGradient 25 14 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 14 = pairGradientFormula constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3 14 := gapGradient_pair T constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3 14
    _ = (1*(((((0 + (-1 / 2)*((-(0)*1)) + (1 / 2)*(-(((1)*1)))))-(0))*(1) + (((0 + (-1 / 2)*(((1)*1)) + (1 / 2)*((-(0)*1))))-(0))*(0)) + ((((((3 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((1 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 25 14 := rfl

theorem row25_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 0 = polynomialGradient 25 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 1 = polynomialGradient 25 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 2 = polynomialGradient 25 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 3 = polynomialGradient 25 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 4 = polynomialGradient 25 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 5 = polynomialGradient 25 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 6 = polynomialGradient 25 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 7 = polynomialGradient 25 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 8 = polynomialGradient 25 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 15 = polynomialGradient 25 15 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 16 = polynomialGradient 25 16 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 17 = polynomialGradient 25 17 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 18 = polynomialGradient 25 18 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 19 = polynomialGradient 25 19 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 20 = polynomialGradient 25 20 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 21 = polynomialGradient 25 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 22 = polynomialGradient 25 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 23 = polynomialGradient 25 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 24 = polynomialGradient 25 24 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 25 = polynomialGradient 25 25 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 26 = polynomialGradient 25 26 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 27 = polynomialGradient 25 27 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 28 = polynomialGradient 25 28 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 29 = polynomialGradient 25 29 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 30 = polynomialGradient 25 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 31 = polynomialGradient 25 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) 32 = polynomialGradient 25 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3) = polynomialGradient 25 := by
  funext j
  fin_cases j
  · exact row25_alias0_coordinate_00
  · exact row25_alias0_coordinate_01
  · exact row25_alias0_coordinate_02
  · exact row25_alias0_coordinate_03
  · exact row25_alias0_coordinate_04
  · exact row25_alias0_coordinate_05
  · exact row25_alias0_coordinate_06
  · exact row25_alias0_coordinate_07
  · exact row25_alias0_coordinate_08
  · exact row25_alias0_coordinate_09
  · exact row25_alias0_coordinate_10
  · exact row25_alias0_coordinate_11
  · exact row25_alias0_coordinate_12
  · exact row25_alias0_coordinate_13
  · exact row25_alias0_coordinate_14
  · exact row25_alias0_coordinate_15
  · exact row25_alias0_coordinate_16
  · exact row25_alias0_coordinate_17
  · exact row25_alias0_coordinate_18
  · exact row25_alias0_coordinate_19
  · exact row25_alias0_coordinate_20
  · exact row25_alias0_coordinate_21
  · exact row25_alias0_coordinate_22
  · exact row25_alias0_coordinate_23
  · exact row25_alias0_coordinate_24
  · exact row25_alias0_coordinate_25
  · exact row25_alias0_coordinate_26
  · exact row25_alias0_coordinate_27
  · exact row25_alias0_coordinate_28
  · exact row25_alias0_coordinate_29
  · exact row25_alias0_coordinate_30
  · exact row25_alias0_coordinate_31
  · exact row25_alias0_coordinate_32

theorem row25_alias1_zero : gapValue T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (-1*((((((1 / 2)) + (1 / 2)*(1) + (1 / 2)*(-(0))))-((3 / 2)))*(1) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(0)) - 1/2) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row25_alias1_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 9 = polynomialGradient 25 9 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 9 = pairGradientFormula constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2 9 := gapGradient_pair T constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2 9
    _ = (-1*(((((1 + (1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*(1) + (((0 + (1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (1 / 2)*(-(0))))-((3 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![-1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 25 9 := rfl

theorem row25_alias1_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 10 = polynomialGradient 25 10 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 10 = pairGradientFormula constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2 10 := gapGradient_pair T constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2 10
    _ = (-1*(((((0 + (1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*(1) + (((1 + (1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (1 / 2)*(-(0))))-((3 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 25 10 := rfl

theorem row25_alias1_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 11 = polynomialGradient 25 11 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 11 = pairGradientFormula constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2 11 := gapGradient_pair T constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2 11
    _ = (-1*(((((0 + (1 / 2)*((-(0)*1)) + (1 / 2)*(-(((1)*1)))))-(0))*(1) + (((0 + (1 / 2)*(((1)*1)) + (1 / 2)*((-(0)*1))))-(0))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (1 / 2)*(-(0))))-((3 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 25 11 := rfl

theorem row25_alias1_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 12 = polynomialGradient 25 12 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 12 = pairGradientFormula constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2 12 := gapGradient_pair T constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2 12
    _ = (-1*(((((0 + (1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(1))*(1) + (((0 + (1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (1 / 2)*(-(0))))-((3 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 25 12 := rfl

theorem row25_alias1_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 13 = polynomialGradient 25 13 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 13 = pairGradientFormula constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2 13 := gapGradient_pair T constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2 13
    _ = (-1*(((((0 + (1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*(1) + (((0 + (1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(1))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (1 / 2)*(-(0))))-((3 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 25 13 := rfl

theorem row25_alias1_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 14 = polynomialGradient 25 14 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 14 = pairGradientFormula constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2 14 := gapGradient_pair T constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2 14
    _ = (-1*(((((0 + (1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*(1) + (((0 + (1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (1 / 2)*(-(0))))-((3 / 2)))*((-(0)*1)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*1))))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 25 14 := rfl

theorem row25_alias1_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 = polynomialGradient 25 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 1 = polynomialGradient 25 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 2 = polynomialGradient 25 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 3 = polynomialGradient 25 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 4 = polynomialGradient 25 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 5 = polynomialGradient 25 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 6 = polynomialGradient 25 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 7 = polynomialGradient 25 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 8 = polynomialGradient 25 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 15 = polynomialGradient 25 15 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 16 = polynomialGradient 25 16 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 17 = polynomialGradient 25 17 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 18 = polynomialGradient 25 18 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 19 = polynomialGradient 25 19 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 20 = polynomialGradient 25 20 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 21 = polynomialGradient 25 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 22 = polynomialGradient 25 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 23 = polynomialGradient 25 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 24 = polynomialGradient 25 24 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 25 = polynomialGradient 25 25 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 26 = polynomialGradient 25 26 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 27 = polynomialGradient 25 27 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 28 = polynomialGradient 25 28 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 29 = polynomialGradient 25 29 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 30 = polynomialGradient 25 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 31 = polynomialGradient 25 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) 32 = polynomialGradient 25 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row25_alias1_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2) = polynomialGradient 25 := by
  funext j
  fin_cases j
  · exact row25_alias1_coordinate_00
  · exact row25_alias1_coordinate_01
  · exact row25_alias1_coordinate_02
  · exact row25_alias1_coordinate_03
  · exact row25_alias1_coordinate_04
  · exact row25_alias1_coordinate_05
  · exact row25_alias1_coordinate_06
  · exact row25_alias1_coordinate_07
  · exact row25_alias1_coordinate_08
  · exact row25_alias1_coordinate_09
  · exact row25_alias1_coordinate_10
  · exact row25_alias1_coordinate_11
  · exact row25_alias1_coordinate_12
  · exact row25_alias1_coordinate_13
  · exact row25_alias1_coordinate_14
  · exact row25_alias1_coordinate_15
  · exact row25_alias1_coordinate_16
  · exact row25_alias1_coordinate_17
  · exact row25_alias1_coordinate_18
  · exact row25_alias1_coordinate_19
  · exact row25_alias1_coordinate_20
  · exact row25_alias1_coordinate_21
  · exact row25_alias1_coordinate_22
  · exact row25_alias1_coordinate_23
  · exact row25_alias1_coordinate_24
  · exact row25_alias1_coordinate_25
  · exact row25_alias1_coordinate_26
  · exact row25_alias1_coordinate_27
  · exact row25_alias1_coordinate_28
  · exact row25_alias1_coordinate_29
  · exact row25_alias1_coordinate_30
  · exact row25_alias1_coordinate_31
  · exact row25_alias1_coordinate_32

theorem row25_aliases_tied (g : Gap) (hg : g ∈ rowAliases 25) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 25 := by
  change g ∈ [Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 3, Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 2] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ⟨row25_alias0_zero, row25_alias0_gradient⟩
  · exact ⟨row25_alias1_zero, row25_alias1_gradient⟩

end
end ElevenSquare.Tasks.T06
