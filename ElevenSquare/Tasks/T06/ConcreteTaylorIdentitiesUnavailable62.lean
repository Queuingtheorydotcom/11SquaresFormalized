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

theorem concreteUnavailable62_A0 :
    dot (featureCenterDifference constructionSquare ({ owner := 7, other := 6, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 7, other := 6, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(1 / 10), (-31 / 40), (31 / 10), (-139 / 40), -5, (-41 / 40), 5, (-17 / 8)] u := by
  apply construction_eq_of_polynomial_multiple (((277 / 1600) + (217 / 320) * u + (-469 / 1600) * u^2 + (-201 / 400) * u^3 + (167 / 1600) * u^4 + (67 / 320) * u^5 + (-31 / 320) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable62_A1 :
    dot (featureCenterDifference constructionSquare ({ owner := 7, other := 6, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 7, other := 6, distinct := by decide, perpendicular := false, reverse := false }))) = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (((567 / 800) + (-47 / 160) * u + (-883 / 1600) * u^2 + (19 / 200) * u^3 + (227 / 800) * u^4 + (-23 / 160) * u^5 + (3 / 320) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable62_L0 :
    (featureNormal constructionSquare ({ owner := 7, other := 6, distinct := by decide, perpendicular := false, reverse := false })).1 = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable62_L1 :
    (featureNormal constructionSquare ({ owner := 7, other := 6, distinct := by decide, perpendicular := false, reverse := false })).2 = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable62_C0 :
    dot (cornerOffset constructionSquare 6 0) (featureNormal constructionSquare ({ owner := 7, other := 6, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (((17 / 640) + (3 / 64) * u + (-19 / 640) * u^2 + (-3 / 80) * u^3 + (7 / 640) * u^4 + (1 / 64) * u^5 + (-1 / 128) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable62_C1 :
    dot (perp (cornerOffset constructionSquare 6 0)) (featureNormal constructionSquare ({ owner := 7, other := 6, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (((-17 / 640) + (-3 / 64) * u + (19 / 640) * u^2 + (3 / 80) * u^3 + (-7 / 640) * u^4 + (-1 / 64) * u^5 + (1 / 128) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable62_value :
    gapValue T constructionSquare (Gap.pair ({ owner := 7, other := 6, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 = polyEval ![(-9 / 10), (-31 / 40), (31 / 10), (-139 / 40), -5, (-41 / 40), 5, (-17 / 8)] u := by
  apply construction_eq_of_polynomial_multiple (((639 / 3200) + (29 / 40) * u + (-1033 / 3200) * u^2 + (-27 / 50) * u^3 + (369 / 3200) * u^4 + (9 / 40) * u^5 + (-67 / 640) * u^6))
  norm_num [gapValue, featureGap, perturbedCorner, perturbedCenter, perturbedAxis, featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring



end
end ElevenSquare.Tasks.T06
