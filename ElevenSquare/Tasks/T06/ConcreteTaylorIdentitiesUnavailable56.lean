import ElevenSquare.Tasks.T06.ConcreteTaylorGeometry
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsPolynomial
import ElevenSquare.ConstructionData
import ElevenSquare.Tasks.T06.AnalyticPacket
import ElevenSquare.Tasks.T06.Gradients
import ElevenSquare.Tasks.T06.PolynomialBounds
import ElevenSquare.Tasks.T06.DataFeatures

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem concreteUnavailable56_A0 :
    dot (featureCenterDifference constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(3 / 80), (-127 / 80), (493 / 80), (-253 / 80), (-111 / 16), (-97 / 80), (95 / 16), (-39 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (((1411 / 3200) + (49 / 64) * u + (-1747 / 3200) * u^2 + (-533 / 800) * u^3 + (601 / 3200) * u^4 + (93 / 320) * u^5 + (-93 / 640) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable56_A1 :
    dot (featureCenterDifference constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false }))) = polyEval ![(83 / 80), (73 / 80), (-87 / 80), (-53 / 80), (9 / 16), (23 / 80), (-5 / 16), (1 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (((2657 / 3200) + (-19 / 32) * u + (-1599 / 3200) * u^2 + (279 / 800) * u^3 + (827 / 3200) * u^4 + (-21 / 80) * u^5 + (39 / 640) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable56_L0 :
    (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false })).1 = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable56_L1 :
    (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false })).2 = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable56_C0 :
    dot (cornerOffset constructionSquare 5 0) (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(-43 / 80), (-73 / 80), (87 / 80), (53 / 80), (-9 / 16), (-23 / 80), (5 / 16), (-1 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable56_C1 :
    dot (perp (cornerOffset constructionSquare 5 0)) (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(39 / 80), (-81 / 80), (-71 / 80), (81 / 80), (13 / 16), (-31 / 80), (-5 / 16), (3 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable56_value :
    gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 = polyEval ![-1, (-5 / 2), (29 / 4), (-5 / 2), (-15 / 2), (-3 / 2), (25 / 4), (-5 / 2)] u := by
  apply construction_eq_of_polynomial_multiple (((1411 / 3200) + (49 / 64) * u + (-1747 / 3200) * u^2 + (-533 / 800) * u^3 + (601 / 3200) * u^4 + (93 / 320) * u^5 + (-93 / 640) * u^6))
  norm_num [gapValue, featureGap, perturbedCorner, perturbedCenter, perturbedAxis, featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring



end
end ElevenSquare.Tasks.T06
