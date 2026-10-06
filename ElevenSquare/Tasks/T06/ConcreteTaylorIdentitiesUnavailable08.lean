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

theorem concreteUnavailable08_A0 :
    dot (featureCenterDifference constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true })) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true })) = polyEval ![(371 / 400), (281 / 400), (-1539 / 400), (1519 / 400), (449 / 80), (-609 / 400), (-45 / 16), (117 / 80)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable08_A1 :
    dot (featureCenterDifference constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true }))) = polyEval ![(147 / 400), (867 / 400), (-823 / 400), (-1367 / 400), (113 / 80), (837 / 400), (-25 / 16), (19 / 80)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable08_L0 :
    (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true })).1 = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable08_L1 :
    (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true })).2 = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable08_C0 :
    dot (cornerOffset constructionSquare 9 2) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true })) = polyEval ![(43 / 80), (73 / 80), (-87 / 80), (-53 / 80), (9 / 16), (23 / 80), (-5 / 16), (1 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable08_C1 :
    dot (perp (cornerOffset constructionSquare 9 2)) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true })) = polyEval ![(39 / 80), (-81 / 80), (-71 / 80), (81 / 80), (13 / 16), (-31 / 80), (-5 / 16), (3 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable08_value :
    gapValue T constructionSquare (Gap.pair ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 0 = polyEval ![(-393 / 200), (-323 / 200), (987 / 200), (-627 / 200), (-247 / 40), (247 / 200), (25 / 8), (-61 / 40)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [gapValue, featureGap, perturbedCorner, perturbedCenter, perturbedAxis, featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring



end
end ElevenSquare.Tasks.T06
