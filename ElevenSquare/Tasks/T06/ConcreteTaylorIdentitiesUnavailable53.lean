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

theorem concreteUnavailable53_A0 :
    dot (featureCenterDifference constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(161 / 400), (771 / 400), (-1549 / 400), (729 / 400), (419 / 80), (581 / 400), (-75 / 16), (147 / 80)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable53_A1 :
    dot (featureCenterDifference constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true }))) = polyEval ![(-73 / 400), (-903 / 400), (1157 / 400), (-1697 / 400), (-467 / 80), (-33 / 400), (75 / 16), (-171 / 80)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable53_L0 :
    (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true })).1 = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable53_L1 :
    (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true })).2 = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable53_C0 :
    dot (cornerOffset constructionSquare 6 1) (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(43 / 80), (73 / 80), (-87 / 80), (-53 / 80), (9 / 16), (23 / 80), (-5 / 16), (1 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable53_C1 :
    dot (perp (cornerOffset constructionSquare 6 1)) (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(39 / 80), (-81 / 80), (-71 / 80), (81 / 80), (13 / 16), (-31 / 80), (-5 / 16), (3 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable53_value :
    gapValue T constructionSquare (Gap.pair ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 = polyEval ![(-36 / 25), (-71 / 25), (124 / 25), (-29 / 25), (-29 / 5), (-87 / 50), 5, (-19 / 10)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [gapValue, featureGap, perturbedCorner, perturbedCenter, perturbedAxis, featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring



end
end ElevenSquare.Tasks.T06
