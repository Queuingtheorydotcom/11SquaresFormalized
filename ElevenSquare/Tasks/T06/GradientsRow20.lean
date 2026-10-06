import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row20_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 =
      ((1949 / 3200) + (-171 / 320) * u + (-1183 / 3200) * u^2 + (273 / 800) * u^3 + (699 / 3200) * u^4 + (-83 / 320) * u^5 + (43 / 640) * u^6) * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (-1*((((((1 / 2)) + (1 / 2)*(1) + (1 / 2)*(-(0))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*(constructionCos) + (((((1 / 2)) + (1 / 2)*(0) + (1 / 2)*(1)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*(constructionSin)) - 1/2) = ((1949 / 3200) + (-171 / 320) * u + (-1183 / 3200) * u^2 + (273 / 800) * u^3 + (699 / 3200) * u^4 + (-83 / 320) * u^5 + (43 / 640) * u^6) * endpointPolynomial u
        dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row20_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 = polynomialGradient 20 0 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 = pairGradientFormula constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2 0 := gapGradient_pair T constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2 0
    _ = (-1*(((((1 + (1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(constructionSin)) + ((((((1 / 2)) + (1 / 2)*(1) + (1 / 2)*(-(0))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(constructionSin)*0)) + (((((1 / 2)) + (1 / 2)*(0) + (1 / 2)*(1)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 20 0 := rfl

theorem row20_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 1 = polynomialGradient 20 1 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 1 = pairGradientFormula constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2 1 := gapGradient_pair T constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2 1
    _ = (-1*(((((0 + (1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*(constructionCos) + (((1 + (1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(constructionSin)) + ((((((1 / 2)) + (1 / 2)*(1) + (1 / 2)*(-(0))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(constructionSin)*0)) + (((((1 / 2)) + (1 / 2)*(0) + (1 / 2)*(1)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 20 1 := rfl

theorem row20_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 2 = polynomialGradient 20 2 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 2 = pairGradientFormula constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2 2 := gapGradient_pair T constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2 2
    _ = (-1*(((((0 + (1 / 2)*((-(0)*1)) + (1 / 2)*(-(((1)*1)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((1)*1)) + (1 / 2)*((-(0)*1))))-(0))*(constructionSin)) + ((((((1 / 2)) + (1 / 2)*(1) + (1 / 2)*(-(0))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(constructionSin)*0)) + (((((1 / 2)) + (1 / 2)*(0) + (1 / 2)*(1)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(39 / 80), (-81 / 80), (-71 / 80), (81 / 80), (13 / 16), (-31 / 80), (-5 / 16), (3 / 16)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 20 2 := rfl

theorem row20_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 18 = polynomialGradient 20 18 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 18 = pairGradientFormula constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2 18 := gapGradient_pair T constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2 18
    _ = (-1*(((((0 + (1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(1))*(constructionCos) + (((0 + (1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(constructionSin)) + ((((((1 / 2)) + (1 / 2)*(1) + (1 / 2)*(-(0))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(constructionSin)*0)) + (((((1 / 2)) + (1 / 2)*(0) + (1 / 2)*(1)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 20 18 := rfl

theorem row20_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 19 = polynomialGradient 20 19 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 19 = pairGradientFormula constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2 19 := gapGradient_pair T constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2 19
    _ = (-1*(((((0 + (1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(1))*(constructionSin)) + ((((((1 / 2)) + (1 / 2)*(1) + (1 / 2)*(-(0))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(constructionSin)*0)) + (((((1 / 2)) + (1 / 2)*(0) + (1 / 2)*(1)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 20 19 := rfl

theorem row20_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 20 = polynomialGradient 20 20 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 20 = pairGradientFormula constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2 20 := gapGradient_pair T constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2 20
    _ = (-1*(((((0 + (1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(constructionSin)) + ((((((1 / 2)) + (1 / 2)*(1) + (1 / 2)*(-(0))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(constructionSin)*1)) + (((((1 / 2)) + (1 / 2)*(0) + (1 / 2)*(1)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*(((constructionCos)*1))))) := rfl
    _ = polyEval ![(-11 / 20), (27 / 10), (-33 / 10), (9 / 5), (19 / 4), (17 / 10), -5, 2] u := by
      apply sub_eq_zero.mp
      calc
        (-1*(((((0 + (1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))-(0))*(constructionSin)) + ((((((1 / 2)) + (1 / 2)*(1) + (1 / 2)*(-(0))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(constructionSin)*1)) + (((((1 / 2)) + (1 / 2)*(0) + (1 / 2)*(1)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*(((constructionCos)*1))))) - polyEval ![(-11 / 20), (27 / 10), (-33 / 10), (9 / 5), (19 / 4), (17 / 10), -5, 2] u = ((-1177 / 3200) + (-183 / 320) * u + (1259 / 3200) * u^2 + (183 / 400) * u^3 + (-427 / 3200) * u^4 + (-61 / 320) * u^5 + (61 / 640) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 20 20 := rfl

theorem row20_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 3 = polynomialGradient 20 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 4 = polynomialGradient 20 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 5 = polynomialGradient 20 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 6 = polynomialGradient 20 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 7 = polynomialGradient 20 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 8 = polynomialGradient 20 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 9 = polynomialGradient 20 9 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 10 = polynomialGradient 20 10 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 11 = polynomialGradient 20 11 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 12 = polynomialGradient 20 12 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 13 = polynomialGradient 20 13 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 14 = polynomialGradient 20 14 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 15 = polynomialGradient 20 15 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 16 = polynomialGradient 20 16 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 17 = polynomialGradient 20 17 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 21 = polynomialGradient 20 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 22 = polynomialGradient 20 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 23 = polynomialGradient 20 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 24 = polynomialGradient 20 24 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 25 = polynomialGradient 20 25 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 26 = polynomialGradient 20 26 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 27 = polynomialGradient 20 27 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 28 = polynomialGradient 20 28 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 29 = polynomialGradient 20 29 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 30 = polynomialGradient 20 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 31 = polynomialGradient 20 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) 32 = polynomialGradient 20 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row20_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) = polynomialGradient 20 := by
  funext j
  fin_cases j
  · exact row20_alias0_coordinate_00
  · exact row20_alias0_coordinate_01
  · exact row20_alias0_coordinate_02
  · exact row20_alias0_coordinate_03
  · exact row20_alias0_coordinate_04
  · exact row20_alias0_coordinate_05
  · exact row20_alias0_coordinate_06
  · exact row20_alias0_coordinate_07
  · exact row20_alias0_coordinate_08
  · exact row20_alias0_coordinate_09
  · exact row20_alias0_coordinate_10
  · exact row20_alias0_coordinate_11
  · exact row20_alias0_coordinate_12
  · exact row20_alias0_coordinate_13
  · exact row20_alias0_coordinate_14
  · exact row20_alias0_coordinate_15
  · exact row20_alias0_coordinate_16
  · exact row20_alias0_coordinate_17
  · exact row20_alias0_coordinate_18
  · exact row20_alias0_coordinate_19
  · exact row20_alias0_coordinate_20
  · exact row20_alias0_coordinate_21
  · exact row20_alias0_coordinate_22
  · exact row20_alias0_coordinate_23
  · exact row20_alias0_coordinate_24
  · exact row20_alias0_coordinate_25
  · exact row20_alias0_coordinate_26
  · exact row20_alias0_coordinate_27
  · exact row20_alias0_coordinate_28
  · exact row20_alias0_coordinate_29
  · exact row20_alias0_coordinate_30
  · exact row20_alias0_coordinate_31
  · exact row20_alias0_coordinate_32

theorem row20_aliases_tied (g : Gap) (hg : g ∈ rowAliases 20) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 20 := by
  change g ∈ [Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row20_alias0_zero, row20_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
