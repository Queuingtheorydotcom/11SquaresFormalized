import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row31_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 0 =
      ((2657 / 3200) + (-19 / 32) * u + (-1599 / 3200) * u^2 + (279 / 800) * u^3 + (827 / 3200) * u^4 + (-21 / 80) * u^5 + (39 / 640) * u^6) * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (1*((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(constructionSin))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (1 / 2)*(0) + (-1 / 2)*(1)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*(constructionCos)) - 1/2) = ((2657 / 3200) + (-19 / 32) * u + (-1599 / 3200) * u^2 + (279 / 800) * u^3 + (827 / 3200) * u^4 + (-21 / 80) * u^5 + (39 / 640) * u^6) * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row31_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 15 = polynomialGradient 31 15 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 15 = pairGradientFormula constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1 15 := gapGradient_pair T constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1 15
    _ = (1*(((((1 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(((constructionCos)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (1 / 2)*(0) + (-1 / 2)*(1)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 31 15 := rfl

theorem row31_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 16 = polynomialGradient 31 16 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 16 = pairGradientFormula constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1 16 := gapGradient_pair T constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1 16
    _ = (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((1 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(((constructionCos)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (1 / 2)*(0) + (-1 / 2)*(1)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 31 16 := rfl

theorem row31_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 17 = polynomialGradient 31 17 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 17 = pairGradientFormula constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1 17 := gapGradient_pair T constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1 17
    _ = (1*(((((0 + (1 / 2)*((-(0)*1)) + (-1 / 2)*(-(((1)*1)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*1)) + (-1 / 2)*((-(0)*1))))-(0))*(constructionCos)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(((constructionCos)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (1 / 2)*(0) + (-1 / 2)*(1)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(39 / 80), (-81 / 80), (-71 / 80), (81 / 80), (13 / 16), (-31 / 80), (-5 / 16), (3 / 16)] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 31 17 := rfl

theorem row31_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 18 = polynomialGradient 31 18 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 18 = pairGradientFormula constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1 18 := gapGradient_pair T constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1 18
    _ = (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(1))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(((constructionCos)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (1 / 2)*(0) + (-1 / 2)*(1)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 31 18 := rfl

theorem row31_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 19 = polynomialGradient 31 19 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 19 = pairGradientFormula constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1 19 := gapGradient_pair T constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1 19
    _ = (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(1))*(constructionCos)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(((constructionCos)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (1 / 2)*(0) + (-1 / 2)*(1)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 31 19 := rfl

theorem row31_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 20 = polynomialGradient 31 20 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 20 = pairGradientFormula constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1 20 := gapGradient_pair T constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1 20
    _ = (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(((constructionCos)*1)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (1 / 2)*(0) + (-1 / 2)*(1)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*((-(constructionSin)*1))))) := rfl
    _ = polyEval ![(-21 / 40), (13 / 5), (-211 / 40), (43 / 20), (49 / 8), (8 / 5), (-45 / 8), (9 / 4)] u := by
      apply sub_eq_zero.mp
      calc
        (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(((constructionCos)*1)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (1 / 2)*(0) + (-1 / 2)*(1)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*((-(constructionSin)*1))))) - polyEval ![(-21 / 40), (13 / 5), (-211 / 40), (43 / 20), (49 / 8), (8 / 5), (-45 / 8), (9 / 4)] u = ((-1411 / 3200) + (-49 / 64) * u + (1747 / 3200) * u^2 + (533 / 800) * u^3 + (-601 / 3200) * u^4 + (-93 / 320) * u^5 + (93 / 640) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 31 20 := rfl

theorem row31_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 0 = polynomialGradient 31 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 1 = polynomialGradient 31 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 2 = polynomialGradient 31 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 3 = polynomialGradient 31 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 4 = polynomialGradient 31 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 5 = polynomialGradient 31 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 6 = polynomialGradient 31 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 7 = polynomialGradient 31 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 8 = polynomialGradient 31 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 9 = polynomialGradient 31 9 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 10 = polynomialGradient 31 10 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 11 = polynomialGradient 31 11 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 12 = polynomialGradient 31 12 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 13 = polynomialGradient 31 13 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 14 = polynomialGradient 31 14 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 21 = polynomialGradient 31 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 22 = polynomialGradient 31 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 23 = polynomialGradient 31 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 24 = polynomialGradient 31 24 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 25 = polynomialGradient 31 25 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 26 = polynomialGradient 31 26 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 27 = polynomialGradient 31 27 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 28 = polynomialGradient 31 28 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 29 = polynomialGradient 31 29 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 30 = polynomialGradient 31 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 31 = polynomialGradient 31 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) 32 = polynomialGradient 31 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row31_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1) = polynomialGradient 31 := by
  funext j
  fin_cases j
  · exact row31_alias0_coordinate_00
  · exact row31_alias0_coordinate_01
  · exact row31_alias0_coordinate_02
  · exact row31_alias0_coordinate_03
  · exact row31_alias0_coordinate_04
  · exact row31_alias0_coordinate_05
  · exact row31_alias0_coordinate_06
  · exact row31_alias0_coordinate_07
  · exact row31_alias0_coordinate_08
  · exact row31_alias0_coordinate_09
  · exact row31_alias0_coordinate_10
  · exact row31_alias0_coordinate_11
  · exact row31_alias0_coordinate_12
  · exact row31_alias0_coordinate_13
  · exact row31_alias0_coordinate_14
  · exact row31_alias0_coordinate_15
  · exact row31_alias0_coordinate_16
  · exact row31_alias0_coordinate_17
  · exact row31_alias0_coordinate_18
  · exact row31_alias0_coordinate_19
  · exact row31_alias0_coordinate_20
  · exact row31_alias0_coordinate_21
  · exact row31_alias0_coordinate_22
  · exact row31_alias0_coordinate_23
  · exact row31_alias0_coordinate_24
  · exact row31_alias0_coordinate_25
  · exact row31_alias0_coordinate_26
  · exact row31_alias0_coordinate_27
  · exact row31_alias0_coordinate_28
  · exact row31_alias0_coordinate_29
  · exact row31_alias0_coordinate_30
  · exact row31_alias0_coordinate_31
  · exact row31_alias0_coordinate_32

theorem row31_aliases_tied (g : Gap) (hg : g ∈ rowAliases 31) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 31 := by
  change g ∈ [Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false }) 1] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row31_alias0_zero, row31_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
