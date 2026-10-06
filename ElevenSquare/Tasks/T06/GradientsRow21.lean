import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row21_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 0 =
      ((219 / 3200) + (-63 / 160) * u + (357 / 3200) * u^2 + (263 / 800) * u^3 + (-151 / 3200) * u^4 + (-3 / 20) * u^5 + (43 / 640) * u^6) * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (-1*((((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin))) + (((((1 / 2)) + (-1 / 2)*(0) + (1 / 2)*(1)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(constructionCos)) - 1/2) = ((219 / 3200) + (-63 / 160) * u + (357 / 3200) * u^2 + (263 / 800) * u^3 + (-151 / 3200) * u^4 + (-3 / 20) * u^5 + (43 / 640) * u^6) * endpointPolynomial u
        dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row21_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 3 = polynomialGradient 21 3 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 3 = pairGradientFormula constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3 3 := gapGradient_pair T constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3 3
    _ = (-1*(((((1 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(((constructionCos)*0)))) + (((((1 / 2)) + (-1 / 2)*(0) + (1 / 2)*(1)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 21 3 := rfl

theorem row21_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 4 = polynomialGradient 21 4 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 4 = pairGradientFormula constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3 4 := gapGradient_pair T constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3 4
    _ = (-1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((1 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(((constructionCos)*0)))) + (((((1 / 2)) + (-1 / 2)*(0) + (1 / 2)*(1)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 21 4 := rfl

theorem row21_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 5 = polynomialGradient 21 5 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 5 = pairGradientFormula constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3 5 := gapGradient_pair T constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3 5
    _ = (-1*(((((0 + (-1 / 2)*((-(0)*1)) + (1 / 2)*(-(((1)*1)))))-(0))*((-(constructionSin))) + (((0 + (-1 / 2)*(((1)*1)) + (1 / 2)*((-(0)*1))))-(0))*(constructionCos)) + ((((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(((constructionCos)*0)))) + (((((1 / 2)) + (-1 / 2)*(0) + (1 / 2)*(1)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(39 / 80), (-81 / 80), (-71 / 80), (81 / 80), (13 / 16), (-31 / 80), (-5 / 16), (3 / 16)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 21 5 := rfl

theorem row21_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 27 = polynomialGradient 21 27 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 27 = pairGradientFormula constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3 27 := gapGradient_pair T constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3 27
    _ = (-1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(1))*((-(constructionSin))) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(((constructionCos)*0)))) + (((((1 / 2)) + (-1 / 2)*(0) + (1 / 2)*(1)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 21 27 := rfl

theorem row21_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 28 = polynomialGradient 21 28 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 28 = pairGradientFormula constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3 28 := gapGradient_pair T constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3 28
    _ = (-1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(1))*(constructionCos)) + ((((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(((constructionCos)*0)))) + (((((1 / 2)) + (-1 / 2)*(0) + (1 / 2)*(1)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 21 28 := rfl

theorem row21_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 29 = polynomialGradient 21 29 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 29 = pairGradientFormula constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3 29 := gapGradient_pair T constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3 29
    _ = (-1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(((constructionCos)*1)))) + (((((1 / 2)) + (-1 / 2)*(0) + (1 / 2)*(1)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*((-(constructionSin)*1))))) := rfl
    _ = polyEval ![(-17 / 40), (73 / 40), (-87 / 40), (-53 / 40), (9 / 8), (23 / 40), (-5 / 8), (1 / 8)] u := by
      apply sub_eq_zero.mp
      calc
        (-1*(((((0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(1) + (1 / 2)*(-(0))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(((constructionCos)*1)))) + (((((1 / 2)) + (-1 / 2)*(0) + (1 / 2)*(1)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*((-(constructionSin)*1))))) - polyEval ![(-17 / 40), (73 / 40), (-87 / 40), (-53 / 40), (9 / 8), (23 / 40), (-5 / 8), (1 / 8)] u = ((-857 / 3200) + (-7 / 80) * u + (809 / 3200) * u^2 + (131 / 800) * u^3 + (-267 / 3200) * u^4 + (-13 / 160) * u^5 + (31 / 640) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 21 29 := rfl

theorem row21_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 0 = polynomialGradient 21 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 1 = polynomialGradient 21 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 2 = polynomialGradient 21 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 6 = polynomialGradient 21 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 7 = polynomialGradient 21 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 8 = polynomialGradient 21 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 9 = polynomialGradient 21 9 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 10 = polynomialGradient 21 10 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 11 = polynomialGradient 21 11 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 12 = polynomialGradient 21 12 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 13 = polynomialGradient 21 13 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 14 = polynomialGradient 21 14 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 15 = polynomialGradient 21 15 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 16 = polynomialGradient 21 16 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 17 = polynomialGradient 21 17 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 18 = polynomialGradient 21 18 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 19 = polynomialGradient 21 19 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 20 = polynomialGradient 21 20 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 21 = polynomialGradient 21 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 22 = polynomialGradient 21 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 23 = polynomialGradient 21 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 24 = polynomialGradient 21 24 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 25 = polynomialGradient 21 25 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 26 = polynomialGradient 21 26 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 30 = polynomialGradient 21 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 31 = polynomialGradient 21 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) 32 = polynomialGradient 21 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row21_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) = polynomialGradient 21 := by
  funext j
  fin_cases j
  · exact row21_alias0_coordinate_00
  · exact row21_alias0_coordinate_01
  · exact row21_alias0_coordinate_02
  · exact row21_alias0_coordinate_03
  · exact row21_alias0_coordinate_04
  · exact row21_alias0_coordinate_05
  · exact row21_alias0_coordinate_06
  · exact row21_alias0_coordinate_07
  · exact row21_alias0_coordinate_08
  · exact row21_alias0_coordinate_09
  · exact row21_alias0_coordinate_10
  · exact row21_alias0_coordinate_11
  · exact row21_alias0_coordinate_12
  · exact row21_alias0_coordinate_13
  · exact row21_alias0_coordinate_14
  · exact row21_alias0_coordinate_15
  · exact row21_alias0_coordinate_16
  · exact row21_alias0_coordinate_17
  · exact row21_alias0_coordinate_18
  · exact row21_alias0_coordinate_19
  · exact row21_alias0_coordinate_20
  · exact row21_alias0_coordinate_21
  · exact row21_alias0_coordinate_22
  · exact row21_alias0_coordinate_23
  · exact row21_alias0_coordinate_24
  · exact row21_alias0_coordinate_25
  · exact row21_alias0_coordinate_26
  · exact row21_alias0_coordinate_27
  · exact row21_alias0_coordinate_28
  · exact row21_alias0_coordinate_29
  · exact row21_alias0_coordinate_30
  · exact row21_alias0_coordinate_31
  · exact row21_alias0_coordinate_32

theorem row21_aliases_tied (g : Gap) (hg : g ∈ rowAliases 21) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 21 := by
  change g ∈ [Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row21_alias0_zero, row21_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
