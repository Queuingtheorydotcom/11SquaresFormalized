import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row41_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 0 =
      ((2193 / 3200) + (-3 / 32) * u + (-2061 / 3200) * u^2 + (-29 / 800) * u^3 + (883 / 3200) * u^4 + (-1 / 20) * u^5 + (-19 / 640) * u^6) * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (1*((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*(constructionCos) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(constructionSin)) - 1/2) = ((2193 / 3200) + (-3 / 32) * u + (-2061 / 3200) * u^2 + (-29 / 800) * u^3 + (883 / 3200) * u^4 + (-1 / 20) * u^5 + (-19 / 640) * u^6) * endpointPolynomial u
        dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row41_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 27 = polynomialGradient 41 27 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 27 = pairGradientFormula constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3 27 := gapGradient_pair T constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3 27
    _ = (1*(((((0 + (-1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(1))*(constructionCos) + (((0 + (-1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 41 27 := rfl

theorem row41_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 28 = polynomialGradient 41 28 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 28 = pairGradientFormula constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3 28 := gapGradient_pair T constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3 28
    _ = (1*(((((0 + (-1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(1))*(constructionSin)) + ((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 41 28 := rfl

theorem row41_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 29 = polynomialGradient 41 29 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 29 = pairGradientFormula constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3 29 := gapGradient_pair T constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3 29
    _ = (1*(((((0 + (-1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*1)) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*1))))) := rfl
    _ = polyEval ![(21 / 40), (21 / 40), (-49 / 40), (159 / 40), (43 / 8), (-9 / 40), (-35 / 8), (17 / 8)] u := by
      apply sub_eq_zero.mp
      calc
        (1*(((((0 + (-1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*1)) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*1))))) - polyEval ![(21 / 40), (21 / 40), (-49 / 40), (159 / 40), (43 / 8), (-9 / 40), (-35 / 8), (17 / 8)] u = ((-149 / 3200) + (-11 / 16) * u + (393 / 3200) * u^2 + (347 / 800) * u^3 + (-79 / 3200) * u^4 + (-31 / 160) * u^5 + (47 / 640) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 41 29 := rfl

theorem row41_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 30 = polynomialGradient 41 30 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 30 = pairGradientFormula constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3 30 := gapGradient_pair T constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3 30
    _ = (1*(((((1 + (-1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 41 30 := rfl

theorem row41_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 31 = polynomialGradient 41 31 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 31 = pairGradientFormula constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3 31 := gapGradient_pair T constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3 31
    _ = (1*(((((0 + (-1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((1 + (-1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 41 31 := rfl

theorem row41_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 32 = polynomialGradient 41 32 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 32 = pairGradientFormula constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3 32 := gapGradient_pair T constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3 32
    _ = (1*(((((0 + (-1 / 2)*((-(constructionSin)*1)) + (1 / 2)*(-(((constructionCos)*1)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((constructionCos)*1)) + (1 / 2)*((-(constructionSin)*1))))-(0))*(constructionSin)) + ((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      apply sub_eq_zero.mp
      calc
        (1*(((((0 + (-1 / 2)*((-(constructionSin)*1)) + (1 / 2)*(-(((constructionCos)*1)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((constructionCos)*1)) + (1 / 2)*((-(constructionSin)*1))))-(0))*(constructionSin)) + ((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) - polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u = ((17 / 640) + (3 / 64) * u + (-19 / 640) * u^2 + (-3 / 80) * u^3 + (7 / 640) * u^4 + (1 / 64) * u^5 + (-1 / 128) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 41 32 := rfl

theorem row41_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 0 = polynomialGradient 41 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 1 = polynomialGradient 41 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 2 = polynomialGradient 41 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 3 = polynomialGradient 41 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 4 = polynomialGradient 41 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 5 = polynomialGradient 41 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 6 = polynomialGradient 41 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 7 = polynomialGradient 41 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 8 = polynomialGradient 41 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 9 = polynomialGradient 41 9 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 10 = polynomialGradient 41 10 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 11 = polynomialGradient 41 11 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 12 = polynomialGradient 41 12 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 13 = polynomialGradient 41 13 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 14 = polynomialGradient 41 14 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 15 = polynomialGradient 41 15 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 16 = polynomialGradient 41 16 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 17 = polynomialGradient 41 17 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 18 = polynomialGradient 41 18 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 19 = polynomialGradient 41 19 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 20 = polynomialGradient 41 20 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 21 = polynomialGradient 41 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 22 = polynomialGradient 41 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 23 = polynomialGradient 41 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 24 = polynomialGradient 41 24 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 25 = polynomialGradient 41 25 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) 26 = polynomialGradient 41 26 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row41_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) = polynomialGradient 41 := by
  funext j
  fin_cases j
  · exact row41_alias0_coordinate_00
  · exact row41_alias0_coordinate_01
  · exact row41_alias0_coordinate_02
  · exact row41_alias0_coordinate_03
  · exact row41_alias0_coordinate_04
  · exact row41_alias0_coordinate_05
  · exact row41_alias0_coordinate_06
  · exact row41_alias0_coordinate_07
  · exact row41_alias0_coordinate_08
  · exact row41_alias0_coordinate_09
  · exact row41_alias0_coordinate_10
  · exact row41_alias0_coordinate_11
  · exact row41_alias0_coordinate_12
  · exact row41_alias0_coordinate_13
  · exact row41_alias0_coordinate_14
  · exact row41_alias0_coordinate_15
  · exact row41_alias0_coordinate_16
  · exact row41_alias0_coordinate_17
  · exact row41_alias0_coordinate_18
  · exact row41_alias0_coordinate_19
  · exact row41_alias0_coordinate_20
  · exact row41_alias0_coordinate_21
  · exact row41_alias0_coordinate_22
  · exact row41_alias0_coordinate_23
  · exact row41_alias0_coordinate_24
  · exact row41_alias0_coordinate_25
  · exact row41_alias0_coordinate_26
  · exact row41_alias0_coordinate_27
  · exact row41_alias0_coordinate_28
  · exact row41_alias0_coordinate_29
  · exact row41_alias0_coordinate_30
  · exact row41_alias0_coordinate_31
  · exact row41_alias0_coordinate_32

theorem row41_aliases_tied (g : Gap) (hg : g ∈ rowAliases 41) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 41 := by
  change g ∈ [Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row41_alias0_zero, row41_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
