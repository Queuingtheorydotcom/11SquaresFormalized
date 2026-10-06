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

theorem concreteUnavailable50_A0 :
    dot (featureCenterDifference constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(9 / 80), (19 / 80), (319 / 80), (-359 / 80), (-93 / 16), (-51 / 80), (85 / 16), (-37 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (((469 / 3200) + (101 / 160) * u + (-843 / 3200) * u^2 + (-93 / 200) * u^3 + (299 / 3200) * u^4 + (31 / 160) * u^5 + (-57 / 640) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable50_A1 :
    dot (featureCenterDifference constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := true }))) = polyEval ![(83 / 80), (73 / 80), (-87 / 80), (-53 / 80), (9 / 16), (23 / 80), (-5 / 16), (1 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (((2353 / 3200) + (-79 / 320) * u + (-1861 / 3200) * u^2 + (23 / 400) * u^3 + (943 / 3200) * u^4 + (-41 / 320) * u^5 + (1 / 640) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable50_L0 :
    (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := true })).1 = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable50_L1 :
    (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := true })).2 = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable50_C0 :
    dot (cornerOffset constructionSquare 4 2) (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(43 / 80), (73 / 80), (-87 / 80), (-53 / 80), (9 / 16), (23 / 80), (-5 / 16), (1 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable50_C1 :
    dot (perp (cornerOffset constructionSquare 4 2)) (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(-39 / 80), (81 / 80), (71 / 80), (-81 / 80), (-13 / 16), (31 / 80), (5 / 16), (-3 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable50_value :
    gapValue T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 = polyEval ![(-23 / 20), (-23 / 20), (-29 / 10), (103 / 20), (21 / 4), (7 / 20), -5, (9 / 4)] u := by
  apply construction_eq_of_polynomial_multiple (((-469 / 3200) + (-101 / 160) * u + (843 / 3200) * u^2 + (93 / 200) * u^3 + (-299 / 3200) * u^4 + (-31 / 160) * u^5 + (57 / 640) * u^6))
  norm_num [gapValue, featureGap, perturbedCorner, perturbedCenter, perturbedAxis, featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring



end
end ElevenSquare.Tasks.T06
