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

theorem concreteUnavailable75_A0 :
    dot (featureCenterDifference constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![-1, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (((-471 / 1600) + (-43 / 320) * u + (113 / 400) * u^2 + (161 / 800) * u^3 + (-151 / 1600) * u^4 + (-31 / 320) * u^5 + (9 / 160) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable75_A1 :
    dot (featureCenterDifference constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := false }))) = polyEval ![(-39 / 40), (81 / 40), (71 / 40), (-81 / 40), (-13 / 8), (31 / 40), (5 / 8), (-3 / 8)] u := by
  apply construction_eq_of_polynomial_multiple (((-19 / 200) + (111 / 320) * u + (-131 / 1600) * u^2 + (-233 / 800) * u^3 + (29 / 800) * u^4 + (43 / 320) * u^5 + (-19 / 320) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable75_L0 :
    (featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := false })).1 = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable75_L1 :
    (featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := false })).2 = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable75_C0 :
    dot (cornerOffset constructionSquare 7 3) (featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (((17 / 640) + (3 / 64) * u + (-19 / 640) * u^2 + (-3 / 80) * u^3 + (7 / 640) * u^4 + (1 / 64) * u^5 + (-1 / 128) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable75_C1 :
    dot (perp (cornerOffset constructionSquare 7 3)) (featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (((17 / 640) + (3 / 64) * u + (-19 / 640) * u^2 + (-3 / 80) * u^3 + (7 / 640) * u^4 + (1 / 64) * u^5 + (-1 / 128) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteUnavailable75_value :
    gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := false }) 3) 0 = polyEval ![-2, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (((-857 / 3200) + (-7 / 80) * u + (809 / 3200) * u^2 + (131 / 800) * u^3 + (-267 / 3200) * u^4 + (-13 / 160) * u^5 + (31 / 640) * u^6))
  norm_num [gapValue, featureGap, perturbedCorner, perturbedCenter, perturbedAxis, featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring



end
end ElevenSquare.Tasks.T06
