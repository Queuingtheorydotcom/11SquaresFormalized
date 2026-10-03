import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row30_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 0 =
      ((2353 / 3200) + (-79 / 320) * u + (-1861 / 3200) * u^2 + (23 / 400) * u^3 + (943 / 3200) * u^4 + (-41 / 320) * u^5 + (1 / 640) * u^6) * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (1*((((((3 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(constructionCos)) - 1/2) = ((2353 / 3200) + (-79 / 320) * u + (-1861 / 3200) * u^2 + (23 / 400) * u^3 + (943 / 3200) * u^4 + (-41 / 320) * u^5 + (1 / 640) * u^6) * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row30_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 12 = polynomialGradient 30 12 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 12 = pairGradientFormula constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 12 := gapGradient_pair T constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 12
    _ = (1*(((((1 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((3 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(((constructionCos)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 30 12 := rfl

theorem row30_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 13 = polynomialGradient 30 13 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 13 = pairGradientFormula constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 13 := gapGradient_pair T constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 13
    _ = (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((1 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((3 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(((constructionCos)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 30 13 := rfl

theorem row30_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 14 = polynomialGradient 30 14 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 14 = pairGradientFormula constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 14 := gapGradient_pair T constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 14
    _ = (1*(((((0 + (1 / 2)*((-(0)*1)) + (-1 / 2)*(-(((1)*1)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*1)) + (-1 / 2)*((-(0)*1))))-(0))*(constructionCos)) + ((((((3 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(((constructionCos)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(39 / 80), (-81 / 80), (-71 / 80), (81 / 80), (13 / 16), (-31 / 80), (-5 / 16), (3 / 16)] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 30 14 := rfl

theorem row30_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 24 = polynomialGradient 30 24 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 24 = pairGradientFormula constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 24 := gapGradient_pair T constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 24
    _ = (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(1))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((3 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(((constructionCos)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 30 24 := rfl

theorem row30_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 25 = polynomialGradient 30 25 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 25 = pairGradientFormula constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 25 := gapGradient_pair T constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 25
    _ = (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(1))*(constructionCos)) + ((((((3 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(((constructionCos)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 30 25 := rfl

theorem row30_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 26 = polynomialGradient 30 26 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 26 = pairGradientFormula constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 26 := gapGradient_pair T constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 26
    _ = (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((3 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(((constructionCos)*1)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*((-(constructionSin)*1))))) := rfl
    _ = polyEval ![(-3 / 5), (31 / 40), (-31 / 10), (139 / 40), 5, (41 / 40), -5, (17 / 8)] u := by
      apply sub_eq_zero.mp
      calc
        (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((3 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(((constructionCos)*1)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*((-(constructionSin)*1))))) - polyEval ![(-3 / 5), (31 / 40), (-31 / 10), (139 / 40), 5, (41 / 40), -5, (17 / 8)] u = ((-469 / 3200) + (-101 / 160) * u + (843 / 3200) * u^2 + (93 / 200) * u^3 + (-299 / 3200) * u^4 + (-31 / 160) * u^5 + (57 / 640) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 30 26 := rfl

theorem row30_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 0 = polynomialGradient 30 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 1 = polynomialGradient 30 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 2 = polynomialGradient 30 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 3 = polynomialGradient 30 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 4 = polynomialGradient 30 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 5 = polynomialGradient 30 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 6 = polynomialGradient 30 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 7 = polynomialGradient 30 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 8 = polynomialGradient 30 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 9 = polynomialGradient 30 9 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 10 = polynomialGradient 30 10 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 11 = polynomialGradient 30 11 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 15 = polynomialGradient 30 15 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 16 = polynomialGradient 30 16 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 17 = polynomialGradient 30 17 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 18 = polynomialGradient 30 18 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 19 = polynomialGradient 30 19 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 20 = polynomialGradient 30 20 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 21 = polynomialGradient 30 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 22 = polynomialGradient 30 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 23 = polynomialGradient 30 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 27 = polynomialGradient 30 27 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 28 = polynomialGradient 30 28 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 29 = polynomialGradient 30 29 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 30 = polynomialGradient 30 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 31 = polynomialGradient 30 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) 32 = polynomialGradient 30 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row30_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) = polynomialGradient 30 := by
  funext j
  fin_cases j
  · exact row30_alias0_coordinate_00
  · exact row30_alias0_coordinate_01
  · exact row30_alias0_coordinate_02
  · exact row30_alias0_coordinate_03
  · exact row30_alias0_coordinate_04
  · exact row30_alias0_coordinate_05
  · exact row30_alias0_coordinate_06
  · exact row30_alias0_coordinate_07
  · exact row30_alias0_coordinate_08
  · exact row30_alias0_coordinate_09
  · exact row30_alias0_coordinate_10
  · exact row30_alias0_coordinate_11
  · exact row30_alias0_coordinate_12
  · exact row30_alias0_coordinate_13
  · exact row30_alias0_coordinate_14
  · exact row30_alias0_coordinate_15
  · exact row30_alias0_coordinate_16
  · exact row30_alias0_coordinate_17
  · exact row30_alias0_coordinate_18
  · exact row30_alias0_coordinate_19
  · exact row30_alias0_coordinate_20
  · exact row30_alias0_coordinate_21
  · exact row30_alias0_coordinate_22
  · exact row30_alias0_coordinate_23
  · exact row30_alias0_coordinate_24
  · exact row30_alias0_coordinate_25
  · exact row30_alias0_coordinate_26
  · exact row30_alias0_coordinate_27
  · exact row30_alias0_coordinate_28
  · exact row30_alias0_coordinate_29
  · exact row30_alias0_coordinate_30
  · exact row30_alias0_coordinate_31
  · exact row30_alias0_coordinate_32

theorem row30_aliases_tied (g : Gap) (hg : g ∈ rowAliases 30) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 30 := by
  change g ∈ [Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row30_alias0_zero, row30_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
