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

theorem concreteUnavailable26_A0 :
    dot (featureCenterDifference constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(11 / 80), (11 / 80), (161 / 80), (-331 / 80), (-71 / 16), (-59 / 80), (75 / 16), (-33 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (((47 / 640) + (7 / 16) * u + (-71 / 640) * u^2 + (-41 / 160) * u^3 + (5 / 128) * u^4 + (3 / 32) * u^5 + (-5 / 128) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable26_A1 :
    dot (featureCenterDifference constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := false }))) = polyEval ![(83 / 80), (73 / 80), (-87 / 80), (-53 / 80), (9 / 16), (23 / 80), (-5 / 16), (1 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (((329 / 640) + (-3 / 16) * u + (-289 / 640) * u^2 + (1 / 20) * u^3 + (163 / 640) * u^4 + (-1 / 8) * u^5 + (1 / 128) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable26_L0 :
    (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := false })).1 = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable26_L1 :
    (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := false })).2 = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable26_C0 :
    dot (cornerOffset constructionSquare 2 0) (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(-43 / 80), (-73 / 80), (87 / 80), (53 / 80), (-9 / 16), (-23 / 80), (5 / 16), (-1 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable26_C1 :
    dot (perp (cornerOffset constructionSquare 2 0)) (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(39 / 80), (-81 / 80), (-71 / 80), (81 / 80), (13 / 16), (-31 / 80), (-5 / 16), (3 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable26_value :
    gapValue T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 = polyEval ![(-9 / 10), (-31 / 40), (31 / 10), (-139 / 40), -5, (-41 / 40), 5, (-17 / 8)] u := by
  apply construction_eq_of_polynomial_multiple (((47 / 640) + (7 / 16) * u + (-71 / 640) * u^2 + (-41 / 160) * u^3 + (5 / 128) * u^4 + (3 / 32) * u^5 + (-5 / 128) * u^6))
  norm_num [gapValue, featureGap, perturbedCorner, perturbedCenter, perturbedAxis, featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring



end
end ElevenSquare.Tasks.T06
