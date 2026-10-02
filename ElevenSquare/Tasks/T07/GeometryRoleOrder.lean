import ElevenSquare.Tasks.T07.RoleAssignment
import ElevenSquare.Tasks.T07.GeometryAngles

/-! Owner-to-role relabeling, independent of the global case exclusion families. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem occupied_has_role_order {U : ℝ} (P : Packing 11 U)
    (hocc : Occupies P (caseMask ⟨438, by omega⟩)) :
    ∃ perm : Equiv.Perm Owner, ∀ i,
      ClosedCell (roleCell i)
        (normalizeCenter (P.squares (perm i)).center) := by
  obtain ⟨perm, howner⟩ := occupied_has_owner_order P hocc
  refine ⟨rolePermutation.trans perm, ?_⟩
  intro i
  have h := howner (roleOwner i)
  rw [role_cell_correspondence] at h
  change ClosedCell (roleCell i)
    (normalizeCenter (P.squares (perm (roleOwner i))).center)
  exact h

end
end ElevenSquare.Tasks.T07
