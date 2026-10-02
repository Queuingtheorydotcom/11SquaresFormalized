import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianFixedFacet
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FeatureData

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.Groups.G005
noncomputable section

theorem g005_pair_01_pos_lower :
    MedianLowerBound featureA 3 (rationalDot (pairWorldQ site00 site01))
      (rationalDot (pairWorldQ site00 site01) site01) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_01_neg_lower :
    MedianLowerBound featureA 3 (rationalDot (rationalNeg (pairWorldQ site00 site01)))
      (rationalDot (rationalNeg (pairWorldQ site00 site01)) site00) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_03_pos_lower :
    MedianLowerBound featureA 3 (rationalDot (pairWorldQ site00 site03))
      (rationalDot (pairWorldQ site00 site03) site00) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_03_neg_lower :
    MedianLowerBound featureA 3 (rationalDot (rationalNeg (pairWorldQ site00 site03)))
      (rationalDot (rationalNeg (pairWorldQ site00 site03)) site03) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_04_pos_lower :
    MedianLowerBound featureA 3 (rationalDot (pairWorldQ site00 site04))
      (rationalDot (pairWorldQ site00 site04) site04) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_04_neg_lower :
    MedianLowerBound featureA 3 (rationalDot (rationalNeg (pairWorldQ site00 site04)))
      (rationalDot (rationalNeg (pairWorldQ site00 site04)) site00) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_05_pos_lower :
    MedianLowerBound featureA 3 (rationalDot (pairWorldQ site00 site05))
      (rationalDot (pairWorldQ site00 site05) site00) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_05_neg_lower :
    MedianLowerBound featureA 3 (rationalDot (rationalNeg (pairWorldQ site00 site05)))
      (rationalDot (rationalNeg (pairWorldQ site00 site05)) site05) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_13_pos_lower :
    MedianLowerBound featureA 3 (rationalDot (pairWorldQ site01 site03))
      (rationalDot (pairWorldQ site01 site03) site03) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_13_neg_lower :
    MedianLowerBound featureA 3 (rationalDot (rationalNeg (pairWorldQ site01 site03)))
      (rationalDot (rationalNeg (pairWorldQ site01 site03)) site01) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_14_pos_lower :
    MedianLowerBound featureA 3 (rationalDot (pairWorldQ site01 site04))
      (rationalDot (pairWorldQ site01 site04) site01) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_14_neg_lower :
    MedianLowerBound featureA 3 (rationalDot (rationalNeg (pairWorldQ site01 site04)))
      (rationalDot (rationalNeg (pairWorldQ site01 site04)) site04) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_15_pos_lower :
    MedianLowerBound featureA 3 (rationalDot (pairWorldQ site01 site05))
      (rationalDot (pairWorldQ site01 site05) site05) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_15_neg_lower :
    MedianLowerBound featureA 3 (rationalDot (rationalNeg (pairWorldQ site01 site05)))
      (rationalDot (rationalNeg (pairWorldQ site01 site05)) site01) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_34_pos_lower :
    MedianLowerBound featureA 3 (rationalDot (pairWorldQ site03 site04))
      (rationalDot (pairWorldQ site03 site04) site01) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_34_neg_lower :
    MedianLowerBound featureA 3 (rationalDot (rationalNeg (pairWorldQ site03 site04)))
      (rationalDot (rationalNeg (pairWorldQ site03 site04)) site01) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_35_pos_lower :
    MedianLowerBound featureA 3 (rationalDot (pairWorldQ site03 site05))
      (rationalDot (pairWorldQ site03 site05) site01) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_35_neg_lower :
    MedianLowerBound featureA 3 (rationalDot (rationalNeg (pairWorldQ site03 site05)))
      (rationalDot (rationalNeg (pairWorldQ site03 site05)) site01) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_45_pos_lower :
    MedianLowerBound featureA 3 (rationalDot (pairWorldQ site04 site05))
      (rationalDot (pairWorldQ site04 site05) site00) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g005_pair_45_neg_lower :
    MedianLowerBound featureA 3 (rationalDot (rationalNeg (pairWorldQ site04 site05)))
      (rationalDot (rationalNeg (pairWorldQ site04 site05)) site00) := by
  unfold MedianLowerBound featureA
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site03,
    site04, site05, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_01_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_01_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_03_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_03_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_04_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_04_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_05_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_05_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_13_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_13_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_14_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_14_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_15_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_15_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_34_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_34_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_35_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_35_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_45_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_pair_45_neg_lower
