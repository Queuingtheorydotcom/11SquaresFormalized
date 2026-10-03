import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row22_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 =
      ((1789 / 3200) + (-61 / 160) * u + (-1383 / 3200) * u^2 + (99 / 400) * u^3 + (639 / 3200) * u^4 + (-29 / 160) * u^5 + (23 / 640) * u^6) * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (1*((((((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*(constructionCos) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(constructionSin)) - 1/2) = ((1789 / 3200) + (-61 / 160) * u + (-1383 / 3200) * u^2 + (99 / 400) * u^3 + (639 / 3200) * u^4 + (-29 / 160) * u^5 + (23 / 640) * u^6) * endpointPolynomial u
        dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row22_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 6 = polynomialGradient 22 6 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 6 = pairGradientFormula constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0 6 := gapGradient_pair T constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0 6
    _ = (1*(((((1 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionSin)) + ((((((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 22 6 := rfl

theorem row22_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 7 = polynomialGradient 22 7 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 7 = pairGradientFormula constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0 7 := gapGradient_pair T constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0 7
    _ = (1*(((((0 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(constructionCos) + (((1 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionSin)) + ((((((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 22 7 := rfl

theorem row22_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 8 = polynomialGradient 22 8 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 8 = pairGradientFormula constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0 8 := gapGradient_pair T constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0 8
    _ = (1*(((((0 + (-1 / 2)*((-(0)*1)) + (-1 / 2)*(-(((1)*1)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((1)*1)) + (-1 / 2)*((-(0)*1))))-(0))*(constructionSin)) + ((((((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(39 / 80), (-81 / 80), (-71 / 80), (81 / 80), (13 / 16), (-31 / 80), (-5 / 16), (3 / 16)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 22 8 := rfl

theorem row22_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 24 = polynomialGradient 22 24 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 24 = pairGradientFormula constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0 24 := gapGradient_pair T constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0 24
    _ = (1*(((((0 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(1))*(constructionCos) + (((0 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionSin)) + ((((((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 22 24 := rfl

theorem row22_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 25 = polynomialGradient 22 25 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 25 = pairGradientFormula constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0 25 := gapGradient_pair T constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0 25
    _ = (1*(((((0 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(1))*(constructionSin)) + ((((((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 22 25 := rfl

theorem row22_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 26 = polynomialGradient 22 26 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 26 = pairGradientFormula constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0 26 := gapGradient_pair T constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0 26
    _ = (1*(((((0 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionSin)) + ((((((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin)*1)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(((constructionCos)*1))))) := rfl
    _ = polyEval ![(-17 / 40), (49 / 20), (-57 / 40), (23 / 10), (41 / 8), (9 / 20), (-35 / 8), 2] u := by
      apply sub_eq_zero.mp
      calc
        (1*(((((0 + (-1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionSin)) + ((((((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2) + (-1 / 2)*(1) + (-1 / 2)*(-(0))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin)*1)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (-1 / 2)*(1)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(((constructionCos)*1))))) - polyEval ![(-17 / 40), (49 / 20), (-57 / 40), (23 / 10), (41 / 8), (9 / 20), (-35 / 8), 2] u = ((-687 / 3200) + (-171 / 320) * u + (619 / 3200) * u^2 + (281 / 800) * u^3 + (-137 / 3200) * u^4 + (-51 / 320) * u^5 + (41 / 640) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 22 26 := rfl

theorem row22_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 = polynomialGradient 22 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 1 = polynomialGradient 22 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 2 = polynomialGradient 22 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 3 = polynomialGradient 22 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 4 = polynomialGradient 22 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 5 = polynomialGradient 22 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 9 = polynomialGradient 22 9 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 10 = polynomialGradient 22 10 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 11 = polynomialGradient 22 11 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 12 = polynomialGradient 22 12 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 13 = polynomialGradient 22 13 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 14 = polynomialGradient 22 14 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 15 = polynomialGradient 22 15 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 16 = polynomialGradient 22 16 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 17 = polynomialGradient 22 17 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 18 = polynomialGradient 22 18 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 19 = polynomialGradient 22 19 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 20 = polynomialGradient 22 20 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 21 = polynomialGradient 22 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 22 = polynomialGradient 22 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 23 = polynomialGradient 22 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 27 = polynomialGradient 22 27 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 28 = polynomialGradient 22 28 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 29 = polynomialGradient 22 29 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 30 = polynomialGradient 22 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 31 = polynomialGradient 22 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 32 = polynomialGradient 22 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row22_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) = polynomialGradient 22 := by
  funext j
  fin_cases j
  · exact row22_alias0_coordinate_00
  · exact row22_alias0_coordinate_01
  · exact row22_alias0_coordinate_02
  · exact row22_alias0_coordinate_03
  · exact row22_alias0_coordinate_04
  · exact row22_alias0_coordinate_05
  · exact row22_alias0_coordinate_06
  · exact row22_alias0_coordinate_07
  · exact row22_alias0_coordinate_08
  · exact row22_alias0_coordinate_09
  · exact row22_alias0_coordinate_10
  · exact row22_alias0_coordinate_11
  · exact row22_alias0_coordinate_12
  · exact row22_alias0_coordinate_13
  · exact row22_alias0_coordinate_14
  · exact row22_alias0_coordinate_15
  · exact row22_alias0_coordinate_16
  · exact row22_alias0_coordinate_17
  · exact row22_alias0_coordinate_18
  · exact row22_alias0_coordinate_19
  · exact row22_alias0_coordinate_20
  · exact row22_alias0_coordinate_21
  · exact row22_alias0_coordinate_22
  · exact row22_alias0_coordinate_23
  · exact row22_alias0_coordinate_24
  · exact row22_alias0_coordinate_25
  · exact row22_alias0_coordinate_26
  · exact row22_alias0_coordinate_27
  · exact row22_alias0_coordinate_28
  · exact row22_alias0_coordinate_29
  · exact row22_alias0_coordinate_30
  · exact row22_alias0_coordinate_31
  · exact row22_alias0_coordinate_32

theorem row22_aliases_tied (g : Gap) (hg : g ∈ rowAliases 22) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 22 := by
  change g ∈ [Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row22_alias0_zero, row22_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
