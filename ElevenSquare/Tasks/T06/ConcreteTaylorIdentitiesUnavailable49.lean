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

theorem concreteUnavailable49_A0 :
    dot (featureCenterDifference constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(9 / 80), (19 / 80), (319 / 80), (-359 / 80), (-93 / 16), (-51 / 80), (85 / 16), (-37 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (((469 / 3200) + (101 / 160) * u + (-843 / 3200) * u^2 + (-93 / 200) * u^3 + (299 / 3200) * u^4 + (31 / 160) * u^5 + (-57 / 640) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable49_A1 :
    dot (featureCenterDifference constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := false }))) = polyEval ![(83 / 80), (73 / 80), (-87 / 80), (-53 / 80), (9 / 16), (23 / 80), (-5 / 16), (1 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (((2353 / 3200) + (-79 / 320) * u + (-1861 / 3200) * u^2 + (23 / 400) * u^3 + (943 / 3200) * u^4 + (-41 / 320) * u^5 + (1 / 640) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable49_L0 :
    (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := false })).1 = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable49_L1 :
    (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := false })).2 = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable49_C0 :
    dot (cornerOffset constructionSquare 4 0) (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(-43 / 80), (-73 / 80), (87 / 80), (53 / 80), (-9 / 16), (-23 / 80), (5 / 16), (-1 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable49_C1 :
    dot (perp (cornerOffset constructionSquare 4 0)) (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(39 / 80), (-81 / 80), (-71 / 80), (81 / 80), (13 / 16), (-31 / 80), (-5 / 16), (3 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable49_value :
    gapValue T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 = polyEval ![(-37 / 40), (-27 / 40), (203 / 40), (-153 / 40), (-51 / 8), (-37 / 40), (45 / 8), (-19 / 8)] u := by
  apply construction_eq_of_polynomial_multiple (((469 / 3200) + (101 / 160) * u + (-843 / 3200) * u^2 + (-93 / 200) * u^3 + (299 / 3200) * u^4 + (31 / 160) * u^5 + (-57 / 640) * u^6))
  norm_num [gapValue, featureGap, perturbedCorner, perturbedCenter, perturbedAxis, featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring



end
end ElevenSquare.Tasks.T06
