import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row40_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 =
      ((2193 / 3200) + (-3 / 32) * u + (-2061 / 3200) * u^2 + (-29 / 800) * u^3 + (883 / 3200) * u^4 + (-1 / 20) * u^5 + (-19 / 640) * u^6) * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (1*((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*(constructionCos) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(constructionSin)) - 1/2) = ((2193 / 3200) + (-3 / 32) * u + (-2061 / 3200) * u^2 + (-29 / 800) * u^3 + (883 / 3200) * u^4 + (-1 / 20) * u^5 + (-19 / 640) * u^6) * endpointPolynomial u
        dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row40_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 27 = polynomialGradient 40 27 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 27 = pairGradientFormula constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0 27 := gapGradient_pair T constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0 27
    _ = (1*(((((0 + (-1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(1))*(constructionCos) + (((0 + (-1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 40 27 := rfl

theorem row40_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 28 = polynomialGradient 40 28 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 28 = pairGradientFormula constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0 28 := gapGradient_pair T constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0 28
    _ = (1*(((((0 + (-1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(1))*(constructionSin)) + ((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 40 28 := rfl

theorem row40_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 29 = polynomialGradient 40 29 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 29 = pairGradientFormula constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0 29 := gapGradient_pair T constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0 29
    _ = (1*(((((0 + (-1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*1)) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*1))))) := rfl
    _ = polyEval ![(-19 / 40), (21 / 40), (-49 / 40), (159 / 40), (43 / 8), (-9 / 40), (-35 / 8), (17 / 8)] u := by
      apply sub_eq_zero.mp
      calc
        (1*(((((0 + (-1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*1)) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*1))))) - polyEval ![(-19 / 40), (21 / 40), (-49 / 40), (159 / 40), (43 / 8), (-9 / 40), (-35 / 8), (17 / 8)] u = ((21 / 3200) + (-19 / 32) * u + (203 / 3200) * u^2 + (287 / 800) * u^3 + (-9 / 3200) * u^4 + (-13 / 80) * u^5 + (37 / 640) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 40 29 := rfl

theorem row40_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 30 = polynomialGradient 40 30 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 30 = pairGradientFormula constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0 30 := gapGradient_pair T constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0 30
    _ = (1*(((((1 + (-1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 40 30 := rfl

theorem row40_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 31 = polynomialGradient 40 31 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 31 = pairGradientFormula constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0 31 := gapGradient_pair T constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0 31
    _ = (1*(((((0 + (-1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((1 + (-1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 40 31 := rfl

theorem row40_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 32 = polynomialGradient 40 32 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 32 = pairGradientFormula constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0 32 := gapGradient_pair T constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0 32
    _ = (1*(((((0 + (-1 / 2)*((-(constructionSin)*1)) + (-1 / 2)*(-(((constructionCos)*1)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((constructionCos)*1)) + (-1 / 2)*((-(constructionSin)*1))))-(0))*(constructionSin)) + ((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      apply sub_eq_zero.mp
      calc
        (1*(((((0 + (-1 / 2)*((-(constructionSin)*1)) + (-1 / 2)*(-(((constructionCos)*1)))))-(0))*(constructionCos) + (((0 + (-1 / 2)*(((constructionCos)*1)) + (-1 / 2)*((-(constructionSin)*1))))-(0))*(constructionSin)) + ((((((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) + (-1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) + (-1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) - polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u = ((-17 / 640) + (-3 / 64) * u + (19 / 640) * u^2 + (3 / 80) * u^3 + (-7 / 640) * u^4 + (-1 / 64) * u^5 + (1 / 128) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 40 32 := rfl

theorem row40_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 = polynomialGradient 40 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 1 = polynomialGradient 40 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 2 = polynomialGradient 40 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 3 = polynomialGradient 40 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 4 = polynomialGradient 40 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 5 = polynomialGradient 40 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 6 = polynomialGradient 40 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 7 = polynomialGradient 40 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 8 = polynomialGradient 40 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 9 = polynomialGradient 40 9 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 10 = polynomialGradient 40 10 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 11 = polynomialGradient 40 11 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 12 = polynomialGradient 40 12 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 13 = polynomialGradient 40 13 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 14 = polynomialGradient 40 14 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 15 = polynomialGradient 40 15 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 16 = polynomialGradient 40 16 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 17 = polynomialGradient 40 17 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 18 = polynomialGradient 40 18 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 19 = polynomialGradient 40 19 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 20 = polynomialGradient 40 20 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 21 = polynomialGradient 40 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 22 = polynomialGradient 40 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 23 = polynomialGradient 40 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 24 = polynomialGradient 40 24 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 25 = polynomialGradient 40 25 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) 26 = polynomialGradient 40 26 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row40_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0) = polynomialGradient 40 := by
  funext j
  fin_cases j
  · exact row40_alias0_coordinate_00
  · exact row40_alias0_coordinate_01
  · exact row40_alias0_coordinate_02
  · exact row40_alias0_coordinate_03
  · exact row40_alias0_coordinate_04
  · exact row40_alias0_coordinate_05
  · exact row40_alias0_coordinate_06
  · exact row40_alias0_coordinate_07
  · exact row40_alias0_coordinate_08
  · exact row40_alias0_coordinate_09
  · exact row40_alias0_coordinate_10
  · exact row40_alias0_coordinate_11
  · exact row40_alias0_coordinate_12
  · exact row40_alias0_coordinate_13
  · exact row40_alias0_coordinate_14
  · exact row40_alias0_coordinate_15
  · exact row40_alias0_coordinate_16
  · exact row40_alias0_coordinate_17
  · exact row40_alias0_coordinate_18
  · exact row40_alias0_coordinate_19
  · exact row40_alias0_coordinate_20
  · exact row40_alias0_coordinate_21
  · exact row40_alias0_coordinate_22
  · exact row40_alias0_coordinate_23
  · exact row40_alias0_coordinate_24
  · exact row40_alias0_coordinate_25
  · exact row40_alias0_coordinate_26
  · exact row40_alias0_coordinate_27
  · exact row40_alias0_coordinate_28
  · exact row40_alias0_coordinate_29
  · exact row40_alias0_coordinate_30
  · exact row40_alias0_coordinate_31
  · exact row40_alias0_coordinate_32

theorem row40_aliases_tied (g : Gap) (hg : g ∈ rowAliases 40) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 40 := by
  change g ∈ [Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 0] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row40_alias0_zero, row40_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
