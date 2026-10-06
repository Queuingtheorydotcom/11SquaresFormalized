import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row36_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 =
      ((1027 / 3200) + (29 / 160) * u + (-999 / 3200) * u^2 + (-191 / 800) * u^3 + (337 / 3200) * u^4 + (9 / 80) * u^5 + (-41 / 640) * u^6) * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (-1*((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*(constructionCos) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(constructionSin)) - 1/2) = ((1027 / 3200) + (29 / 160) * u + (-999 / 3200) * u^2 + (-191 / 800) * u^3 + (337 / 3200) * u^4 + (9 / 80) * u^5 + (-41 / 640) * u^6) * endpointPolynomial u
        dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row36_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 21 = polynomialGradient 36 21 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 21 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1 21 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1 21
    _ = (-1*(((((1 + (1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 36 21 := rfl

theorem row36_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 22 = polynomialGradient 36 22 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 22 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1 22 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1 22
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((1 + (1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 36 22 := rfl

theorem row36_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 23 = polynomialGradient 36 23 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 23 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1 23 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1 23
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*1)) + (-1 / 2)*(-(((constructionCos)*1)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*1)) + (-1 / 2)*((-(constructionSin)*1))))-(0))*(constructionSin)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      apply sub_eq_zero.mp
      calc
        (-1*(((((0 + (1 / 2)*((-(constructionSin)*1)) + (-1 / 2)*(-(((constructionCos)*1)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*1)) + (-1 / 2)*((-(constructionSin)*1))))-(0))*(constructionSin)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) - polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u = ((17 / 640) + (3 / 64) * u + (-19 / 640) * u^2 + (-3 / 80) * u^3 + (7 / 640) * u^4 + (1 / 64) * u^5 + (-1 / 128) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 36 23 := rfl

theorem row36_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 27 = polynomialGradient 36 27 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 27 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1 27 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1 27
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(1))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 36 27 := rfl

theorem row36_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 28 = polynomialGradient 36 28 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 28 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1 28 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1 28
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(1))*(constructionSin)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 36 28 := rfl

theorem row36_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 29 = polynomialGradient 36 29 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 29 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1 29 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1 29
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*1)) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*1))))) := rfl
    _ = polyEval ![(59 / 40), (-81 / 40), (-71 / 40), (81 / 40), (13 / 8), (-31 / 40), (-5 / 8), (3 / 8)] u := by
      apply sub_eq_zero.mp
      calc
        (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (-1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*0)) + (-1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (-1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*1)) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (-1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*1))))) - polyEval ![(59 / 40), (-81 / 40), (-71 / 40), (81 / 40), (13 / 8), (-31 / 40), (-5 / 8), (3 / 8)] u = ((219 / 3200) + (-63 / 160) * u + (357 / 3200) * u^2 + (263 / 800) * u^3 + (-151 / 3200) * u^4 + (-3 / 20) * u^5 + (43 / 640) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 36 29 := rfl

theorem row36_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 = polynomialGradient 36 0 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 1 = polynomialGradient 36 1 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 2 = polynomialGradient 36 2 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 3 = polynomialGradient 36 3 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 4 = polynomialGradient 36 4 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 5 = polynomialGradient 36 5 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 6 = polynomialGradient 36 6 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 7 = polynomialGradient 36 7 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 8 = polynomialGradient 36 8 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 9 = polynomialGradient 36 9 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 10 = polynomialGradient 36 10 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 11 = polynomialGradient 36 11 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 12 = polynomialGradient 36 12 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 13 = polynomialGradient 36 13 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 14 = polynomialGradient 36 14 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 15 = polynomialGradient 36 15 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 16 = polynomialGradient 36 16 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 17 = polynomialGradient 36 17 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 18 = polynomialGradient 36 18 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 19 = polynomialGradient 36 19 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 20 = polynomialGradient 36 20 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 24 = polynomialGradient 36 24 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 25 = polynomialGradient 36 25 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 26 = polynomialGradient 36 26 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 30 = polynomialGradient 36 30 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 31 = polynomialGradient 36 31 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) 32 = polynomialGradient 36 32 := by
  apply pairGradient_polynomial_zero <;> decide

theorem row36_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) = polynomialGradient 36 := by
  funext j
  fin_cases j
  · exact row36_alias0_coordinate_00
  · exact row36_alias0_coordinate_01
  · exact row36_alias0_coordinate_02
  · exact row36_alias0_coordinate_03
  · exact row36_alias0_coordinate_04
  · exact row36_alias0_coordinate_05
  · exact row36_alias0_coordinate_06
  · exact row36_alias0_coordinate_07
  · exact row36_alias0_coordinate_08
  · exact row36_alias0_coordinate_09
  · exact row36_alias0_coordinate_10
  · exact row36_alias0_coordinate_11
  · exact row36_alias0_coordinate_12
  · exact row36_alias0_coordinate_13
  · exact row36_alias0_coordinate_14
  · exact row36_alias0_coordinate_15
  · exact row36_alias0_coordinate_16
  · exact row36_alias0_coordinate_17
  · exact row36_alias0_coordinate_18
  · exact row36_alias0_coordinate_19
  · exact row36_alias0_coordinate_20
  · exact row36_alias0_coordinate_21
  · exact row36_alias0_coordinate_22
  · exact row36_alias0_coordinate_23
  · exact row36_alias0_coordinate_24
  · exact row36_alias0_coordinate_25
  · exact row36_alias0_coordinate_26
  · exact row36_alias0_coordinate_27
  · exact row36_alias0_coordinate_28
  · exact row36_alias0_coordinate_29
  · exact row36_alias0_coordinate_30
  · exact row36_alias0_coordinate_31
  · exact row36_alias0_coordinate_32

theorem row36_aliases_tied (g : Gap) (hg : g ∈ rowAliases 36) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 36 := by
  change g ∈ [Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row36_alias0_zero, row36_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
