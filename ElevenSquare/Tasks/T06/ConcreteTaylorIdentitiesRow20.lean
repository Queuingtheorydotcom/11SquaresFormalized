import ElevenSquare.Tasks.T06.ConcreteTaylorGeometry
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsPolynomial
import ElevenSquare.Tasks.T06.AnalyticPacket
import ElevenSquare.Tasks.T06.Gradients
import ElevenSquare.Tasks.T06.PolynomialBounds
import ElevenSquare.Tasks.T06.DataFeatures

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem concreteRow20Alias0_A0 :
    dot (featureCenterDifference constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(-83 / 80), (-73 / 80), (87 / 80), (53 / 80), (-9 / 16), (-23 / 80), (5 / 16), (-1 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (((-1949 / 3200) + (171 / 320) * u + (1183 / 3200) * u^2 + (-273 / 800) * u^3 + (-699 / 3200) * u^4 + (83 / 320) * u^5 + (-43 / 640) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow20Alias0_A1 :
    dot (featureCenterDifference constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }))) = polyEval ![(1 / 16), (-27 / 16), (67 / 16), (-45 / 16), (-89 / 16), (-21 / 16), (85 / 16), (-35 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (((1177 / 3200) + (183 / 320) * u + (-1259 / 3200) * u^2 + (-183 / 400) * u^3 + (427 / 3200) * u^4 + (61 / 320) * u^5 + (-61 / 640) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow20Alias0_L0 :
    (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true })).1 = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow20Alias0_L1 :
    (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true })).2 = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow20Alias0_C0 :
    dot (cornerOffset constructionSquare 0 2) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(43 / 80), (73 / 80), (-87 / 80), (-53 / 80), (9 / 16), (23 / 80), (-5 / 16), (1 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow20Alias0_C1 :
    dot (perp (cornerOffset constructionSquare 0 2)) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(-39 / 80), (81 / 80), (71 / 80), (-81 / 80), (-13 / 16), (31 / 80), (5 / 16), (-3 / 16)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


end
end ElevenSquare.Tasks.T06
