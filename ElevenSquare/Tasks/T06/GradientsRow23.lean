import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row23_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 0 =
      ((329 / 640) + (-3 / 16) * u + (-289 / 640) * u^2 + (1 / 20) * u^3 + (163 / 640) * u^4 + (-1 / 8) * u^5 + (1 / 128) * u^6) * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (1*((((((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)))*((-(constructionSin))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)))*(constructionCos)) - 1/2) = ((329 / 640) + (-3 / 16) * u + (-289 / 640) * u^2 + (1 / 20) * u^3 + (163 / 640) * u^4 + (-1 / 8) * u^5 + (1 / 128) * u^6) * endpointPolynomial u
        dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row23_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 6 = polynomialGradient 23 6 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 6 = pairGradientFormula constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1 6 := gapGradient_pair T constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1 6
    _ = (1*(((((1 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)))*((-(((constructionCos)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 23 6 := rfl

theorem row23_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 7 = polynomialGradient 23 7 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 7 = pairGradientFormula constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1 7 := gapGradient_pair T constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1 7
    _ = (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((1 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)))*((-(((constructionCos)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 23 7 := rfl

theorem row23_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 8 = polynomialGradient 23 8 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 8 = pairGradientFormula constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1 8 := gapGradient_pair T constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1 8
    _ = (1*(((((0 + (1 / 2)*((-(0)*1)) + (-1 / 2)*(-(((1)*1)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*1)) + (-1 / 2)*((-(0)*1))))-(0))*(constructionCos)) + ((((((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)))*((-(((constructionCos)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(39 / 80), (-81 / 80), (-71 / 80), (81 / 80), (13 / 16), (-31 / 80), (-5 / 16), (3 / 16)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 23 8 := rfl

theorem row23_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 30 = polynomialGradient 23 30 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 30 = pairGradientFormula constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1 30 := gapGradient_pair T constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1 30
    _ = (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(1))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)))*((-(((constructionCos)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 23 30 := rfl

theorem row23_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 31 = polynomialGradient 23 31 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 31 = pairGradientFormula constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1 31 := gapGradient_pair T constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1 31
    _ = (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(1))*(constructionCos)) + ((((((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)))*((-(((constructionCos)*0)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)))*((-(constructionSin)*0))))) := rfl
    _ = polyEval ![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 23 31 := rfl

theorem row23_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 32 = polynomialGradient 23 32 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 32 = pairGradientFormula constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1 32 := gapGradient_pair T constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1 32
    _ = (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)))*((-(((constructionCos)*1)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)))*((-(constructionSin)*1))))) := rfl
    _ = polyEval ![(-5 / 8), (7 / 8), (-9 / 8), (25 / 8), (29 / 8), (9 / 8), (-35 / 8), (15 / 8)] u := by
      apply sub_eq_zero.mp
      calc
        (1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*((-(constructionSin))) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(constructionCos)) + ((((((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)))*((-(((constructionCos)*1)))) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (1 / 2)*(0) + (-1 / 2)*(1)))-((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)))*((-(constructionSin)*1))))) - polyEval ![(-5 / 8), (7 / 8), (-9 / 8), (25 / 8), (29 / 8), (9 / 8), (-35 / 8), (15 / 8)] u = ((-47 / 640) + (-7 / 16) * u + (71 / 640) * u^2 + (41 / 160) * u^3 + (-5 / 128) * u^4 + (-3 / 32) * u^5 + (5 / 128) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 23 32 := rfl

theorem row23_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 0 = polynomialGradient 23 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 1 = polynomialGradient 23 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 2 = polynomialGradient 23 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 3 = polynomialGradient 23 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 4 = polynomialGradient 23 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 5 = polynomialGradient 23 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 9 = polynomialGradient 23 9 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 10 = polynomialGradient 23 10 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 11 = polynomialGradient 23 11 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 12 = polynomialGradient 23 12 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 13 = polynomialGradient 23 13 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 14 = polynomialGradient 23 14 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 15 = polynomialGradient 23 15 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 16 = polynomialGradient 23 16 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 17 = polynomialGradient 23 17 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 18 = polynomialGradient 23 18 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 19 = polynomialGradient 23 19 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 20 = polynomialGradient 23 20 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 21 = polynomialGradient 23 21 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 22 = polynomialGradient 23 22 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 23 = polynomialGradient 23 23 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 24 = polynomialGradient 23 24 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 25 = polynomialGradient 23 25 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 26 = polynomialGradient 23 26 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 27 = polynomialGradient 23 27 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 28 = polynomialGradient 23 28 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) 29 = polynomialGradient 23 29 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row23_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) = polynomialGradient 23 := by
  funext j
  fin_cases j
  · exact row23_alias0_coordinate_00
  · exact row23_alias0_coordinate_01
  · exact row23_alias0_coordinate_02
  · exact row23_alias0_coordinate_03
  · exact row23_alias0_coordinate_04
  · exact row23_alias0_coordinate_05
  · exact row23_alias0_coordinate_06
  · exact row23_alias0_coordinate_07
  · exact row23_alias0_coordinate_08
  · exact row23_alias0_coordinate_09
  · exact row23_alias0_coordinate_10
  · exact row23_alias0_coordinate_11
  · exact row23_alias0_coordinate_12
  · exact row23_alias0_coordinate_13
  · exact row23_alias0_coordinate_14
  · exact row23_alias0_coordinate_15
  · exact row23_alias0_coordinate_16
  · exact row23_alias0_coordinate_17
  · exact row23_alias0_coordinate_18
  · exact row23_alias0_coordinate_19
  · exact row23_alias0_coordinate_20
  · exact row23_alias0_coordinate_21
  · exact row23_alias0_coordinate_22
  · exact row23_alias0_coordinate_23
  · exact row23_alias0_coordinate_24
  · exact row23_alias0_coordinate_25
  · exact row23_alias0_coordinate_26
  · exact row23_alias0_coordinate_27
  · exact row23_alias0_coordinate_28
  · exact row23_alias0_coordinate_29
  · exact row23_alias0_coordinate_30
  · exact row23_alias0_coordinate_31
  · exact row23_alias0_coordinate_32

theorem row23_aliases_tied (g : Gap) (hg : g ∈ rowAliases 23) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 23 := by
  change g ∈ [Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row23_alias0_zero, row23_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
