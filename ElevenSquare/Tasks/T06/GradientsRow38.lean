import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row38_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 0 =
      ((2353 / 3200) + (-79 / 320) * u + (-1861 / 3200) * u^2 + (23 / 400) * u^3 + (943 / 3200) * u^4 + (-41 / 320) * u^5 + (1 / 640) * u^6) * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (-1*((((((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(constructionSin))) + (((((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*(constructionCos)) - 1/2) = ((2353 / 3200) + (-79 / 320) * u + (-1861 / 3200) * u^2 + (23 / 400) * u^3 + (943 / 3200) * u^4 + (-41 / 320) * u^5 + (1 / 640) * u^6) * endpointPolynomial u
        dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row38_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 24 = polynomialGradient 38 24 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 24 = pairGradientFormula constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2 24 := gapGradient_pair T constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2 24
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(1))*((-(constructionSin))) + (((0 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionCos)) + ((((((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(((constructionCos)*0)))) + (((((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 38 24 := rfl

theorem row38_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 25 = polynomialGradient 38 25 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 25 = pairGradientFormula constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2 25 := gapGradient_pair T constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2 25
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(1))*(constructionCos)) + ((((((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(((constructionCos)*0)))) + (((((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 38 25 := rfl

theorem row38_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 26 = polynomialGradient 38 26 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 26 = pairGradientFormula constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2 26 := gapGradient_pair T constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2 26
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionCos)) + ((((((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(((constructionCos)*1)))) + (((((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*((-(constructionSin)*1))))) := rfl
    _ = polyEval ![(2 / 5), (31 / 40), (-31 / 10), (139 / 40), 5, (41 / 40), -5, (17 / 8)] u := by
      apply sub_eq_zero.mp
      calc
        (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionCos)) + ((((((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(((constructionCos)*1)))) + (((((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*((-(constructionSin)*1))))) - polyEval ![(2 / 5), (31 / 40), (-31 / 10), (139 / 40), 5, (41 / 40), -5, (17 / 8)] u = ((-639 / 3200) + (-29 / 40) * u + (1033 / 3200) * u^2 + (27 / 50) * u^3 + (-369 / 3200) * u^4 + (-9 / 40) * u^5 + (67 / 640) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 38 26 := rfl

theorem row38_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 27 = polynomialGradient 38 27 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 27 = pairGradientFormula constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2 27 := gapGradient_pair T constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2 27
    _ = (-1*(((((1 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionCos)) + ((((((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(((constructionCos)*0)))) + (((((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 38 27 := rfl

theorem row38_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 28 = polynomialGradient 38 28 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 28 = pairGradientFormula constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2 28 := gapGradient_pair T constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2 28
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*((-(constructionSin))) + (((1 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionCos)) + ((((((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(((constructionCos)*0)))) + (((((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 38 28 := rfl

theorem row38_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 29 = polynomialGradient 38 29 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 29 = pairGradientFormula constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2 29 := gapGradient_pair T constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2 29
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*1)) + (1 / 2)*(-(((constructionCos)*1)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((constructionCos)*1)) + (1 / 2)*((-(constructionSin)*1))))-(0))*(constructionCos)) + ((((((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(((constructionCos)*0)))) + (((((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      apply sub_eq_zero.mp
      calc
        (-1*(((((0 + (1 / 2)*((-(constructionSin)*1)) + (1 / 2)*(-(((constructionCos)*1)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((constructionCos)*1)) + (1 / 2)*((-(constructionSin)*1))))-(0))*(constructionCos)) + ((((((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)))*((-(((constructionCos)*0)))) + (((((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)))*((-(constructionSin)*0))))) - polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u = ((17 / 640) + (3 / 64) * u + (-19 / 640) * u^2 + (-3 / 80) * u^3 + (7 / 640) * u^4 + (1 / 64) * u^5 + (-1 / 128) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 38 29 := rfl

theorem row38_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 0 = polynomialGradient 38 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 1 = polynomialGradient 38 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 2 = polynomialGradient 38 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 3 = polynomialGradient 38 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 4 = polynomialGradient 38 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 5 = polynomialGradient 38 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 6 = polynomialGradient 38 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 7 = polynomialGradient 38 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 8 = polynomialGradient 38 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 9 = polynomialGradient 38 9 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 10 = polynomialGradient 38 10 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 11 = polynomialGradient 38 11 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 12 = polynomialGradient 38 12 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 13 = polynomialGradient 38 13 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 14 = polynomialGradient 38 14 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 15 = polynomialGradient 38 15 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 16 = polynomialGradient 38 16 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 17 = polynomialGradient 38 17 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 18 = polynomialGradient 38 18 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 19 = polynomialGradient 38 19 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 20 = polynomialGradient 38 20 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 21 = polynomialGradient 38 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 22 = polynomialGradient 38 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 23 = polynomialGradient 38 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 30 = polynomialGradient 38 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 31 = polynomialGradient 38 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 32 = polynomialGradient 38 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row38_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) = polynomialGradient 38 := by
  funext j
  fin_cases j
  · exact row38_alias0_coordinate_00
  · exact row38_alias0_coordinate_01
  · exact row38_alias0_coordinate_02
  · exact row38_alias0_coordinate_03
  · exact row38_alias0_coordinate_04
  · exact row38_alias0_coordinate_05
  · exact row38_alias0_coordinate_06
  · exact row38_alias0_coordinate_07
  · exact row38_alias0_coordinate_08
  · exact row38_alias0_coordinate_09
  · exact row38_alias0_coordinate_10
  · exact row38_alias0_coordinate_11
  · exact row38_alias0_coordinate_12
  · exact row38_alias0_coordinate_13
  · exact row38_alias0_coordinate_14
  · exact row38_alias0_coordinate_15
  · exact row38_alias0_coordinate_16
  · exact row38_alias0_coordinate_17
  · exact row38_alias0_coordinate_18
  · exact row38_alias0_coordinate_19
  · exact row38_alias0_coordinate_20
  · exact row38_alias0_coordinate_21
  · exact row38_alias0_coordinate_22
  · exact row38_alias0_coordinate_23
  · exact row38_alias0_coordinate_24
  · exact row38_alias0_coordinate_25
  · exact row38_alias0_coordinate_26
  · exact row38_alias0_coordinate_27
  · exact row38_alias0_coordinate_28
  · exact row38_alias0_coordinate_29
  · exact row38_alias0_coordinate_30
  · exact row38_alias0_coordinate_31
  · exact row38_alias0_coordinate_32

theorem row38_aliases_tied (g : Gap) (hg : g ∈ rowAliases 38) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 38 := by
  change g ∈ [Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row38_alias0_zero, row38_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
