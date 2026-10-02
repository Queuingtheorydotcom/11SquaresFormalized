import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianFixedFacet
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FeatureData

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.Groups.G004
noncomputable section

theorem g004_pair_01_pos_lower :
    MedianLowerBound featureSites 3 (rationalDot (pairWorldQ site00 site01))
      (rationalDot (pairWorldQ site00 site01) site04) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_01_neg_lower :
    MedianLowerBound featureSites 3 (rationalDot (rationalNeg (pairWorldQ site00 site01)))
      (rationalDot (rationalNeg (pairWorldQ site00 site01)) site04) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_02_pos_lower :
    MedianLowerBound featureSites 3 (rationalDot (pairWorldQ site00 site02))
      (rationalDot (pairWorldQ site00 site02) site00) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_02_neg_lower :
    MedianLowerBound featureSites 3 (rationalDot (rationalNeg (pairWorldQ site00 site02)))
      (rationalDot (rationalNeg (pairWorldQ site00 site02)) site02) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_03_pos_lower :
    MedianLowerBound featureSites 3 (rationalDot (pairWorldQ site00 site03))
      (rationalDot (pairWorldQ site00 site03) site03) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_03_neg_lower :
    MedianLowerBound featureSites 3 (rationalDot (rationalNeg (pairWorldQ site00 site03)))
      (rationalDot (rationalNeg (pairWorldQ site00 site03)) site00) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_04_pos_lower :
    MedianLowerBound featureSites 3 (rationalDot (pairWorldQ site00 site04))
      (rationalDot (pairWorldQ site00 site04) site02) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_04_neg_lower :
    MedianLowerBound featureSites 3 (rationalDot (rationalNeg (pairWorldQ site00 site04)))
      (rationalDot (rationalNeg (pairWorldQ site00 site04)) site02) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_12_pos_lower :
    MedianLowerBound featureSites 3 (rationalDot (pairWorldQ site01 site02))
      (rationalDot (pairWorldQ site01 site02) site03) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_12_neg_lower :
    MedianLowerBound featureSites 3 (rationalDot (rationalNeg (pairWorldQ site01 site02)))
      (rationalDot (rationalNeg (pairWorldQ site01 site02)) site03) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_13_pos_lower :
    MedianLowerBound featureSites 3 (rationalDot (pairWorldQ site01 site03))
      (rationalDot (pairWorldQ site01 site03) site03) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_13_neg_lower :
    MedianLowerBound featureSites 3 (rationalDot (rationalNeg (pairWorldQ site01 site03)))
      (rationalDot (rationalNeg (pairWorldQ site01 site03)) site01) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_14_pos_lower :
    MedianLowerBound featureSites 3 (rationalDot (pairWorldQ site01 site04))
      (rationalDot (pairWorldQ site01 site04) site01) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_14_neg_lower :
    MedianLowerBound featureSites 3 (rationalDot (rationalNeg (pairWorldQ site01 site04)))
      (rationalDot (rationalNeg (pairWorldQ site01 site04)) site04) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_23_pos_lower :
    MedianLowerBound featureSites 3 (rationalDot (pairWorldQ site02 site03))
      (rationalDot (pairWorldQ site02 site03) site02) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_23_neg_lower :
    MedianLowerBound featureSites 3 (rationalDot (rationalNeg (pairWorldQ site02 site03)))
      (rationalDot (rationalNeg (pairWorldQ site02 site03)) site03) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_24_pos_lower :
    MedianLowerBound featureSites 3 (rationalDot (pairWorldQ site02 site04))
      (rationalDot (pairWorldQ site02 site04) site00) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_24_neg_lower :
    MedianLowerBound featureSites 3 (rationalDot (rationalNeg (pairWorldQ site02 site04)))
      (rationalDot (rationalNeg (pairWorldQ site02 site04)) site00) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_34_pos_lower :
    MedianLowerBound featureSites 3 (rationalDot (pairWorldQ site03 site04))
      (rationalDot (pairWorldQ site03 site04) site04) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

theorem g004_pair_34_neg_lower :
    MedianLowerBound featureSites 3 (rationalDot (rationalNeg (pairWorldQ site03 site04)))
      (rationalDot (rationalNeg (pairWorldQ site03 site04)) site03) := by
  unfold MedianLowerBound featureSites
  norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, site00, site01, site02,
    site03, site04, physicalToUnit, rationalDot, rationalNeg, pairWorldQ]

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_01_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_01_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_02_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_02_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_03_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_03_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_04_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_04_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_12_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_12_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_13_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_13_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_14_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_14_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_23_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_23_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_24_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_24_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_34_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_34_neg_lower
