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

theorem concreteRow24Alias0_A0 :
    dot (featureCenterDifference constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow24Alias0_A1 :
    dot (featureCenterDifference constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }))) = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow24Alias0_L0 :
    (featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false })).1 = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow24Alias0_L1 :
    (featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false })).2 = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow24Alias0_C0 :
    dot (cornerOffset constructionSquare 4 0) (featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow24Alias0_C1 :
    dot (perp (cornerOffset constructionSquare 4 0)) (featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow24Alias1_A0 :
    dot (featureCenterDifference constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![-1, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow24Alias1_A1 :
    dot (featureCenterDifference constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }))) = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow24Alias1_L0 :
    (featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true })).1 = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow24Alias1_L1 :
    (featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true })).2 = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow24Alias1_C0 :
    dot (cornerOffset constructionSquare 3 1) (featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


theorem concreteRow24Alias1_C1 :
    dot (perp (cornerOffset constructionSquare 3 1)) (featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true })) = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
  apply construction_eq_of_polynomial_multiple (0)
  norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring


end
end ElevenSquare.Tasks.T06
