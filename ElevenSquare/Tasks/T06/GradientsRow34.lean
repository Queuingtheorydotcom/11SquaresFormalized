import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row34_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 =
      ((1027 / 3200) + (29 / 160) * u + (-999 / 3200) * u^2 + (-191 / 800) * u^3 + (337 / 3200) * u^4 + (9 / 80) * u^5 + (-41 / 640) * u^6) * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (-1*((((((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*(constructionCos) + (((((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(constructionSin)) - 1/2) = ((1027 / 3200) + (29 / 160) * u + (-999 / 3200) * u^2 + (-191 / 800) * u^3 + (337 / 3200) * u^4 + (9 / 80) * u^5 + (-41 / 640) * u^6) * endpointPolynomial u
        dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row34_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 18 = polynomialGradient 34 18 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 18 = pairGradientFormula constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1 18 := gapGradient_pair T constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1 18
    _ = (-1*(((((1 + (1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin)*0)) + (((((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 34 18 := rfl

theorem row34_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 19 = polynomialGradient 34 19 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 19 = pairGradientFormula constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1 19 := gapGradient_pair T constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1 19
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((1 + (1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin)*0)) + (((((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 34 19 := rfl

theorem row34_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 20 = polynomialGradient 34 20 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 20 = pairGradientFormula constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1 20 := gapGradient_pair T constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1 20
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*1)) + (-1 / 2)*(-(((constructionCos)*1)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*1)) + (-1 / 2)*((-(constructionSin)*1))))-(0))*(constructionSin)) + ((((((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin)*0)) + (((((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      apply sub_eq_zero.mp
      calc
        (-1*(((((0 + (1 / 2)*((-(constructionSin)*1)) + (-1 / 2)*(-(((constructionCos)*1)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*1)) + (-1 / 2)*((-(constructionSin)*1))))-(0))*(constructionSin)) + ((((((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin)*0)) + (((((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(((constructionCos)*0))))) - polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u = ((17 / 640) + (3 / 64) * u + (-19 / 640) * u^2 + (-3 / 80) * u^3 + (7 / 640) * u^4 + (1 / 64) * u^5 + (-1 / 128) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 34 20 := rfl

theorem row34_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 24 = polynomialGradient 34 24 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 24 = pairGradientFormula constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1 24 := gapGradient_pair T constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1 24
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(1))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin)*0)) + (((((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 34 24 := rfl

theorem row34_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 25 = polynomialGradient 34 25 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 25 = pairGradientFormula constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1 25 := gapGradient_pair T constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1 25
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(1))*(constructionSin)) + ((((((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin)*0)) + (((((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 34 25 := rfl

theorem row34_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 26 = polynomialGradient 34 26 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 26 = pairGradientFormula constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1 26 := gapGradient_pair T constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1 26
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin)*1)) + (((((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(((constructionCos)*1))))) := rfl
    _ = polyEval ![(59 / 40), (-81 / 40), (-71 / 40), (81 / 40), (13 / 8), (-31 / 40), (-5 / 8), (3 / 8)] u := by
      apply sub_eq_zero.mp
      calc
        (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin)*1)) + (((((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(((constructionCos)*1))))) - polyEval ![(59 / 40), (-81 / 40), (-71 / 40), (81 / 40), (13 / 8), (-31 / 40), (-5 / 8), (3 / 8)] u = ((219 / 3200) + (-63 / 160) * u + (357 / 3200) * u^2 + (263 / 800) * u^3 + (-151 / 3200) * u^4 + (-3 / 20) * u^5 + (43 / 640) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 34 26 := rfl

theorem row34_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 = polynomialGradient 34 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 1 = polynomialGradient 34 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 2 = polynomialGradient 34 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 3 = polynomialGradient 34 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 4 = polynomialGradient 34 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 5 = polynomialGradient 34 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 6 = polynomialGradient 34 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 7 = polynomialGradient 34 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 8 = polynomialGradient 34 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 9 = polynomialGradient 34 9 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 10 = polynomialGradient 34 10 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 11 = polynomialGradient 34 11 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 12 = polynomialGradient 34 12 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 13 = polynomialGradient 34 13 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 14 = polynomialGradient 34 14 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 15 = polynomialGradient 34 15 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 16 = polynomialGradient 34 16 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 17 = polynomialGradient 34 17 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 21 = polynomialGradient 34 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 22 = polynomialGradient 34 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 23 = polynomialGradient 34 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 27 = polynomialGradient 34 27 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 28 = polynomialGradient 34 28 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 29 = polynomialGradient 34 29 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 30 = polynomialGradient 34 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 31 = polynomialGradient 34 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 32 = polynomialGradient 34 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row34_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) = polynomialGradient 34 := by
  funext j
  fin_cases j
  · exact row34_alias0_coordinate_00
  · exact row34_alias0_coordinate_01
  · exact row34_alias0_coordinate_02
  · exact row34_alias0_coordinate_03
  · exact row34_alias0_coordinate_04
  · exact row34_alias0_coordinate_05
  · exact row34_alias0_coordinate_06
  · exact row34_alias0_coordinate_07
  · exact row34_alias0_coordinate_08
  · exact row34_alias0_coordinate_09
  · exact row34_alias0_coordinate_10
  · exact row34_alias0_coordinate_11
  · exact row34_alias0_coordinate_12
  · exact row34_alias0_coordinate_13
  · exact row34_alias0_coordinate_14
  · exact row34_alias0_coordinate_15
  · exact row34_alias0_coordinate_16
  · exact row34_alias0_coordinate_17
  · exact row34_alias0_coordinate_18
  · exact row34_alias0_coordinate_19
  · exact row34_alias0_coordinate_20
  · exact row34_alias0_coordinate_21
  · exact row34_alias0_coordinate_22
  · exact row34_alias0_coordinate_23
  · exact row34_alias0_coordinate_24
  · exact row34_alias0_coordinate_25
  · exact row34_alias0_coordinate_26
  · exact row34_alias0_coordinate_27
  · exact row34_alias0_coordinate_28
  · exact row34_alias0_coordinate_29
  · exact row34_alias0_coordinate_30
  · exact row34_alias0_coordinate_31
  · exact row34_alias0_coordinate_32

theorem row34_aliases_tied (g : Gap) (hg : g ∈ rowAliases 34) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 34 := by
  change g ∈ [Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row34_alias0_zero, row34_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
