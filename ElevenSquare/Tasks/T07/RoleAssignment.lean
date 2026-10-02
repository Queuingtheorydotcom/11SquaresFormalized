import ElevenSquare.Cover
import ElevenSquare.Tasks.T07.CoordinateBridge
import ElevenSquare.Pending.S06_CandidateMasks
import ElevenSquare.Tasks.T07.RoleAssignmentFinite

/-! Exact correspondence between the eleven trace owners (in increasing cell
order) and the eleven local construction roles. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem ownerCell_image_case438 :
    Finset.univ.image ownerCell = caseMask ⟨438, by omega⟩ := by
  rw [candidate_mask_438, ownerCell_image]

theorem occupied_has_owner_order {U : ℝ} (P : Packing 11 U)
    (hocc : Occupies P (caseMask ⟨438, by omega⟩)) :
    ∃ perm : Equiv.Perm Owner, ∀ i,
      ClosedCell (ownerCell i) (normalizeCenter (P.squares (perm i)).center) := by
  obtain ⟨a, ha, him, hcell⟩ := hocc
  obtain ⟨perm, hp⟩ := image_permutation a ownerCell ha ownerCell_injective
    (him.trans ownerCell_image_case438.symm)
  refine ⟨perm, ?_⟩
  intro i
  simpa only [hp i] using hcell (perm i)

theorem relabel_centered {U S : ℝ} (P : Packing 11 U)
    (perm : Equiv.Perm Owner) (hsmall : CenteredPacking P S) :
    CenteredPacking (relabelPacking P perm) S := by
  intro i p hp
  exact hsmall (perm i) p hp

end
end ElevenSquare.Tasks.T07
