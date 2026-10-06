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

theorem concreteUnavailable46_A0 :
    dot (featureCenterDifference constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(19 / 400), (309 / 400), (-371 / 400), (1691 / 400), (241 / 80), (-101 / 400), (-45 / 16), (113 / 80)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable46_A1 :
    dot (featureCenterDifference constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true }))) = polyEval ![(-117 / 400), (-987 / 400), (53 / 400), (87 / 400), (-63 / 80), (-757 / 400), (35 / 16), (-59 / 80)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable46_L0 :
    (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true })).1 = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable46_L1 :
    (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true })).2 = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable46_C0 :
    dot (cornerOffset constructionSquare 8 1) (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(43 / 80), (73 / 80), (-87 / 80), (-53 / 80), (9 / 16), (23 / 80), (-5 / 16), (1 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable46_C1 :
    dot (perp (cornerOffset constructionSquare 8 1)) (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(39 / 80), (-81 / 80), (-71 / 80), (81 / 80), (13 / 16), (-31 / 80), (-5 / 16), (3 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable46_value :
    gapValue T constructionSquare (Gap.pair ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 = polyEval ![(-217 / 200), (-337 / 200), (403 / 200), (-713 / 200), (-143 / 40), (-7 / 200), (25 / 8), (-59 / 40)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [gapValue, featureGap, perturbedCorner, perturbedCenter, perturbedAxis, featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring



end
end ElevenSquare.Tasks.T06
