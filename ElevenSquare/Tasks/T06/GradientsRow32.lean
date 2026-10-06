import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row32_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 0 =
      ((2353 / 3200) + (-79 / 320) * u + (-1861 / 3200) * u^2 + (23 / 400) * u^3 + (943 / 3200) * u^4 + (-41 / 320) * u^5 + (1 / 640) * u^6) * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (-1*((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(constructionSin))) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*(constructionCos)) - 1/2) = ((2353 / 3200) + (-79 / 320) * u + (-1861 / 3200) * u^2 + (23 / 400) * u^3 + (943 / 3200) * u^4 + (-41 / 320) * u^5 + (1 / 640) * u^6) * endpointPolynomial u
        dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row32_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 18 = polynomialGradient 32 18 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 18 = pairGradientFormula constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2 18 := gapGradient_pair T constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2 18
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(1))*((-(constructionSin))) + (((0 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionCos)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(((constructionCos)*0)))) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 32 18 := rfl

theorem row32_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 19 = polynomialGradient 32 19 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 19 = pairGradientFormula constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2 19 := gapGradient_pair T constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2 19
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(1))*(constructionCos)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(((constructionCos)*0)))) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 32 19 := rfl

theorem row32_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 20 = polynomialGradient 32 20 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 20 = pairGradientFormula constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2 20 := gapGradient_pair T constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2 20
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionCos)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(((constructionCos)*1)))) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*((-(constructionSin)*1))))) := rfl
    _ = polyEval ![(2 / 5), (31 / 40), (-31 / 10), (139 / 40), 5, (41 / 40), -5, (17 / 8)] u := by
      apply sub_eq_zero.mp
      calc
        (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionCos)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(((constructionCos)*1)))) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*((-(constructionSin)*1))))) - polyEval ![(2 / 5), (31 / 40), (-31 / 10), (139 / 40), 5, (41 / 40), -5, (17 / 8)] u = ((-639 / 3200) + (-29 / 40) * u + (1033 / 3200) * u^2 + (27 / 50) * u^3 + (-369 / 3200) * u^4 + (-9 / 40) * u^5 + (67 / 640) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 32 20 := rfl

theorem row32_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 21 = polynomialGradient 32 21 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 21 = pairGradientFormula constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2 21 := gapGradient_pair T constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2 21
    _ = (-1*(((((1 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionCos)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(((constructionCos)*0)))) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 32 21 := rfl

theorem row32_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 22 = polynomialGradient 32 22 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 22 = pairGradientFormula constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2 22 := gapGradient_pair T constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2 22
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*((-(constructionSin))) + (((1 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionCos)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(((constructionCos)*0)))) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 32 22 := rfl

theorem row32_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 23 = polynomialGradient 32 23 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 23 = pairGradientFormula constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2 23 := gapGradient_pair T constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2 23
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*1)) + (1 / 2)*(-(((constructionCos)*1)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((constructionCos)*1)) + (1 / 2)*((-(constructionSin)*1))))-(0))*(constructionCos)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(((constructionCos)*0)))) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      apply sub_eq_zero.mp
      calc
        (-1*(((((0 + (1 / 2)*((-(constructionSin)*1)) + (1 / 2)*(-(((constructionCos)*1)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((constructionCos)*1)) + (1 / 2)*((-(constructionSin)*1))))-(0))*(constructionCos)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)))*((-(((constructionCos)*0)))) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)))*((-(constructionSin)*0))))) - polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u = ((17 / 640) + (3 / 64) * u + (-19 / 640) * u^2 + (-3 / 80) * u^3 + (7 / 640) * u^4 + (1 / 64) * u^5 + (-1 / 128) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 32 23 := rfl

theorem row32_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 0 = polynomialGradient 32 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 1 = polynomialGradient 32 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 2 = polynomialGradient 32 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 3 = polynomialGradient 32 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 4 = polynomialGradient 32 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 5 = polynomialGradient 32 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 6 = polynomialGradient 32 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 7 = polynomialGradient 32 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 8 = polynomialGradient 32 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 9 = polynomialGradient 32 9 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 10 = polynomialGradient 32 10 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 11 = polynomialGradient 32 11 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 12 = polynomialGradient 32 12 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 13 = polynomialGradient 32 13 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 14 = polynomialGradient 32 14 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 15 = polynomialGradient 32 15 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 16 = polynomialGradient 32 16 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 17 = polynomialGradient 32 17 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 24 = polynomialGradient 32 24 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 25 = polynomialGradient 32 25 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 26 = polynomialGradient 32 26 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 27 = polynomialGradient 32 27 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 28 = polynomialGradient 32 28 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 29 = polynomialGradient 32 29 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 30 = polynomialGradient 32 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 31 = polynomialGradient 32 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) 32 = polynomialGradient 32 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row32_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2) = polynomialGradient 32 := by
  funext j
  fin_cases j
  · exact row32_alias0_coordinate_00
  · exact row32_alias0_coordinate_01
  · exact row32_alias0_coordinate_02
  · exact row32_alias0_coordinate_03
  · exact row32_alias0_coordinate_04
  · exact row32_alias0_coordinate_05
  · exact row32_alias0_coordinate_06
  · exact row32_alias0_coordinate_07
  · exact row32_alias0_coordinate_08
  · exact row32_alias0_coordinate_09
  · exact row32_alias0_coordinate_10
  · exact row32_alias0_coordinate_11
  · exact row32_alias0_coordinate_12
  · exact row32_alias0_coordinate_13
  · exact row32_alias0_coordinate_14
  · exact row32_alias0_coordinate_15
  · exact row32_alias0_coordinate_16
  · exact row32_alias0_coordinate_17
  · exact row32_alias0_coordinate_18
  · exact row32_alias0_coordinate_19
  · exact row32_alias0_coordinate_20
  · exact row32_alias0_coordinate_21
  · exact row32_alias0_coordinate_22
  · exact row32_alias0_coordinate_23
  · exact row32_alias0_coordinate_24
  · exact row32_alias0_coordinate_25
  · exact row32_alias0_coordinate_26
  · exact row32_alias0_coordinate_27
  · exact row32_alias0_coordinate_28
  · exact row32_alias0_coordinate_29
  · exact row32_alias0_coordinate_30
  · exact row32_alias0_coordinate_31
  · exact row32_alias0_coordinate_32

theorem row32_aliases_tied (g : Gap) (hg : g ∈ rowAliases 32) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 32 := by
  change g ∈ [Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true }) 2] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row32_alias0_zero, row32_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
