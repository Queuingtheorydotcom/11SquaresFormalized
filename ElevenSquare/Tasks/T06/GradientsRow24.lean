import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row24_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (1*((((((3 / 2)) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*(1) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(0)) - 1/2) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row24_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 9 = polynomialGradient 24 9 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 9 = pairGradientFormula constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0 9 := gapGradient_pair T constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0 9
    _ = (1*(((((0 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(1))*(1) + (((0 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((3 / 2)) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![-1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 24 9 := rfl

theorem row24_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 10 = polynomialGradient 24 10 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 10 = pairGradientFormula constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0 10 := gapGradient_pair T constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0 10
    _ = (1*(((((0 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(1) + (((0 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(1))*(0)) + ((((((3 / 2)) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 24 10 := rfl

theorem row24_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 11 = polynomialGradient 24 11 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 11 = pairGradientFormula constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0 11 := gapGradient_pair T constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0 11
    _ = (1*(((((0 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(1) + (((0 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((3 / 2)) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(0)*1)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*1))))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 24 11 := rfl

theorem row24_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 12 = polynomialGradient 24 12 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 12 = pairGradientFormula constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0 12 := gapGradient_pair T constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0 12
    _ = (1*(((((1 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(1) + (((0 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((3 / 2)) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 24 12 := rfl

theorem row24_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 13 = polynomialGradient 24 13 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 13 = pairGradientFormula constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0 13 := gapGradient_pair T constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0 13
    _ = (1*(((((0 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(1) + (((1 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((3 / 2)) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 24 13 := rfl

theorem row24_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 14 = polynomialGradient 24 14 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 14 = pairGradientFormula constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0 14 := gapGradient_pair T constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0 14
    _ = (1*(((((0 + (-1 / 2)*((-(0)*1)) + (-1 / 2)*(-(((1)*1)))))-(0))*(1) + (((0 + (-1 / 2)*(((1)*1)) + (-1 / 2)*((-(0)*1))))-(0))*(0)) + ((((((3 / 2)) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((1 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 24 14 := rfl

theorem row24_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 = polynomialGradient 24 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 1 = polynomialGradient 24 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 2 = polynomialGradient 24 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 3 = polynomialGradient 24 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 4 = polynomialGradient 24 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 5 = polynomialGradient 24 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 6 = polynomialGradient 24 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 7 = polynomialGradient 24 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 8 = polynomialGradient 24 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 15 = polynomialGradient 24 15 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 16 = polynomialGradient 24 16 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 17 = polynomialGradient 24 17 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 18 = polynomialGradient 24 18 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 19 = polynomialGradient 24 19 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 20 = polynomialGradient 24 20 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 21 = polynomialGradient 24 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 22 = polynomialGradient 24 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 23 = polynomialGradient 24 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 24 = polynomialGradient 24 24 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 25 = polynomialGradient 24 25 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 26 = polynomialGradient 24 26 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 27 = polynomialGradient 24 27 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 28 = polynomialGradient 24 28 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 29 = polynomialGradient 24 29 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 30 = polynomialGradient 24 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 31 = polynomialGradient 24 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 32 = polynomialGradient 24 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) = polynomialGradient 24 := by
  funext j
  fin_cases j
  · exact row24_alias0_coordinate_00
  · exact row24_alias0_coordinate_01
  · exact row24_alias0_coordinate_02
  · exact row24_alias0_coordinate_03
  · exact row24_alias0_coordinate_04
  · exact row24_alias0_coordinate_05
  · exact row24_alias0_coordinate_06
  · exact row24_alias0_coordinate_07
  · exact row24_alias0_coordinate_08
  · exact row24_alias0_coordinate_09
  · exact row24_alias0_coordinate_10
  · exact row24_alias0_coordinate_11
  · exact row24_alias0_coordinate_12
  · exact row24_alias0_coordinate_13
  · exact row24_alias0_coordinate_14
  · exact row24_alias0_coordinate_15
  · exact row24_alias0_coordinate_16
  · exact row24_alias0_coordinate_17
  · exact row24_alias0_coordinate_18
  · exact row24_alias0_coordinate_19
  · exact row24_alias0_coordinate_20
  · exact row24_alias0_coordinate_21
  · exact row24_alias0_coordinate_22
  · exact row24_alias0_coordinate_23
  · exact row24_alias0_coordinate_24
  · exact row24_alias0_coordinate_25
  · exact row24_alias0_coordinate_26
  · exact row24_alias0_coordinate_27
  · exact row24_alias0_coordinate_28
  · exact row24_alias0_coordinate_29
  · exact row24_alias0_coordinate_30
  · exact row24_alias0_coordinate_31
  · exact row24_alias0_coordinate_32

theorem row24_alias1_zero : gapValue T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (-1*((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((3 / 2)))*(1) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(0)) - 1/2) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row24_alias1_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 9 = polynomialGradient 24 9 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 9 = pairGradientFormula constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1 9 := gapGradient_pair T constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1 9
    _ = (-1*(((((1 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(1) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((3 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![-1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 24 9 := rfl

theorem row24_alias1_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 10 = polynomialGradient 24 10 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 10 = pairGradientFormula constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1 10 := gapGradient_pair T constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1 10
    _ = (-1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(1) + (((1 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((3 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 24 10 := rfl

theorem row24_alias1_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 11 = polynomialGradient 24 11 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 11 = pairGradientFormula constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1 11 := gapGradient_pair T constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1 11
    _ = (-1*(((((0 + (1 / 2)*((-(0)*1)) + (-1 / 2)*(-(((1)*1)))))-(0))*(1) + (((0 + (1 / 2)*(((1)*1)) + (-1 / 2)*((-(0)*1))))-(0))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((3 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 24 11 := rfl

theorem row24_alias1_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 12 = polynomialGradient 24 12 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 12 = pairGradientFormula constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1 12 := gapGradient_pair T constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1 12
    _ = (-1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(1))*(1) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((3 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 24 12 := rfl

theorem row24_alias1_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 13 = polynomialGradient 24 13 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 13 = pairGradientFormula constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1 13 := gapGradient_pair T constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1 13
    _ = (-1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(1) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(1))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((3 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 24 13 := rfl

theorem row24_alias1_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 14 = polynomialGradient 24 14 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 14 = pairGradientFormula constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1 14 := gapGradient_pair T constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1 14
    _ = (-1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(1) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((3 / 2)))*((-(0)*1)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*1))))) := rfl
    _ = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 24 14 := rfl

theorem row24_alias1_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 = polynomialGradient 24 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 1 = polynomialGradient 24 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 2 = polynomialGradient 24 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 3 = polynomialGradient 24 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 4 = polynomialGradient 24 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 5 = polynomialGradient 24 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 6 = polynomialGradient 24 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 7 = polynomialGradient 24 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 8 = polynomialGradient 24 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 15 = polynomialGradient 24 15 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 16 = polynomialGradient 24 16 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 17 = polynomialGradient 24 17 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 18 = polynomialGradient 24 18 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 19 = polynomialGradient 24 19 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 20 = polynomialGradient 24 20 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 21 = polynomialGradient 24 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 22 = polynomialGradient 24 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 23 = polynomialGradient 24 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 24 = polynomialGradient 24 24 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 25 = polynomialGradient 24 25 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 26 = polynomialGradient 24 26 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 27 = polynomialGradient 24 27 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 28 = polynomialGradient 24 28 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 29 = polynomialGradient 24 29 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 30 = polynomialGradient 24 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 31 = polynomialGradient 24 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 32 = polynomialGradient 24 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row24_alias1_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) = polynomialGradient 24 := by
  funext j
  fin_cases j
  · exact row24_alias1_coordinate_00
  · exact row24_alias1_coordinate_01
  · exact row24_alias1_coordinate_02
  · exact row24_alias1_coordinate_03
  · exact row24_alias1_coordinate_04
  · exact row24_alias1_coordinate_05
  · exact row24_alias1_coordinate_06
  · exact row24_alias1_coordinate_07
  · exact row24_alias1_coordinate_08
  · exact row24_alias1_coordinate_09
  · exact row24_alias1_coordinate_10
  · exact row24_alias1_coordinate_11
  · exact row24_alias1_coordinate_12
  · exact row24_alias1_coordinate_13
  · exact row24_alias1_coordinate_14
  · exact row24_alias1_coordinate_15
  · exact row24_alias1_coordinate_16
  · exact row24_alias1_coordinate_17
  · exact row24_alias1_coordinate_18
  · exact row24_alias1_coordinate_19
  · exact row24_alias1_coordinate_20
  · exact row24_alias1_coordinate_21
  · exact row24_alias1_coordinate_22
  · exact row24_alias1_coordinate_23
  · exact row24_alias1_coordinate_24
  · exact row24_alias1_coordinate_25
  · exact row24_alias1_coordinate_26
  · exact row24_alias1_coordinate_27
  · exact row24_alias1_coordinate_28
  · exact row24_alias1_coordinate_29
  · exact row24_alias1_coordinate_30
  · exact row24_alias1_coordinate_31
  · exact row24_alias1_coordinate_32

theorem row24_aliases_tied (g : Gap) (hg : g ∈ rowAliases 24) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 24 := by
  change g ∈ [Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0, Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ⟨row24_alias0_zero, row24_alias0_gradient⟩
  · exact ⟨row24_alias1_zero, row24_alias1_gradient⟩

end
end ElevenSquare.Tasks.T06
