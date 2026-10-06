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

theorem concreteRow46Alias0_A0 :
    dot (featureCenterDifference constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![-1, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (((-527 / 800) + (9 / 64) * u + (983 / 1600) * u^2 + (-1 / 800) * u^3 + (-53 / 200) * u^4 + (21 / 320) * u^5 + (7 / 320) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow46Alias0_A1 :
    dot (featureCenterDifference constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true }))) = polyEval ![(-1 / 40), (-21 / 40), (49 / 40), (-159 / 40), (-43 / 8), (9 / 40), (35 / 8), (-17 / 8)] u := by
  apply construction_eq_of_polynomial_multiple (((1 / 50) + (41 / 64) * u + (-149 / 1600) * u^2 + (-317 / 800) * u^3 + (11 / 800) * u^4 + (57 / 320) * u^5 + (-21 / 320) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow46Alias0_L0 :
    (featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true })).1 = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow46Alias0_L1 :
    (featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true })).2 = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow46Alias0_C0 :
    dot (cornerOffset constructionSquare 9 1) (featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (((-17 / 640) + (-3 / 64) * u + (19 / 640) * u^2 + (3 / 80) * u^3 + (-7 / 640) * u^4 + (-1 / 64) * u^5 + (1 / 128) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow46Alias0_C1 :
    dot (perp (cornerOffset constructionSquare 9 1)) (featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (((-17 / 640) + (-3 / 64) * u + (19 / 640) * u^2 + (3 / 80) * u^3 + (-7 / 640) * u^4 + (-1 / 64) * u^5 + (1 / 128) * u^6))
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


end
end ElevenSquare.Tasks.T06
