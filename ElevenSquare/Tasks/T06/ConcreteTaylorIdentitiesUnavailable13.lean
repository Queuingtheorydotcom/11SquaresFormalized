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

theorem concreteUnavailable13_A0 :
    dot (featureCenterDifference constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(1 / 16), (13 / 16), (-49 / 16), (-5 / 16), (31 / 16), (3 / 16), (-15 / 16), (5 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (((-857 / 3200) + (-7 / 80) * u + (809 / 3200) * u^2 + (131 / 800) * u^3 + (-267 / 3200) * u^4 + (-13 / 160) * u^5 + (31 / 640) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable13_A1 :
    dot (featureCenterDifference constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true }))) = polyEval ![(-83 / 80), (-73 / 80), (87 / 80), (53 / 80), (-9 / 16), (-23 / 80), (5 / 16), (-1 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (((-219 / 3200) + (63 / 160) * u + (-357 / 3200) * u^2 + (-263 / 800) * u^3 + (151 / 3200) * u^4 + (3 / 20) * u^5 + (-43 / 640) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable13_L0 :
    (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true })).1 = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable13_L1 :
    (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true })).2 = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable13_C0 :
    dot (cornerOffset constructionSquare 1 2) (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(43 / 80), (73 / 80), (-87 / 80), (-53 / 80), (9 / 16), (23 / 80), (-5 / 16), (1 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable13_C1 :
    dot (perp (cornerOffset constructionSquare 1 2)) (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(-39 / 80), (81 / 80), (71 / 80), (-81 / 80), (-13 / 16), (31 / 80), (5 / 16), (-3 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable13_value :
    gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 = polyEval ![(-11 / 10), (-69 / 40), (83 / 20), (39 / 40), (-5 / 2), (-19 / 40), (5 / 4), (-3 / 8)] u := by
  apply construction_eq_of_polynomial_multiple (((857 / 3200) + (7 / 80) * u + (-809 / 3200) * u^2 + (-131 / 800) * u^3 + (267 / 3200) * u^4 + (13 / 160) * u^5 + (-31 / 640) * u^6))
  norm_num [gapValue, featureGap, perturbedCorner, perturbedCenter, perturbedAxis, featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring



end
end ElevenSquare.Tasks.T06
