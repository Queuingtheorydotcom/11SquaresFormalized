import ElevenSquare.Tasks.T07.GeometryRoleOrder
import ElevenSquare.Tasks.T07.D4Transport

/-! Reindex the actual case-438 packing by the local construction roles. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- The D4 reduction, increasing-cell owner order, and role permutation all
preserve the centered whole-square bound. -/
theorem case438_centered_role_reduction {S : ℝ} (P : Packing 11 S)
    (hST : S ≤ T) :
    ∃ Q : Packing 11 coverCap,
      CenteredPacking Q S ∧
      ∀ i, ClosedCell (roleCell i)
        (normalizeCenter (Q.squares i).center) := by
  obtain ⟨Q, hocc, hsmall⟩ := case438_centered_reduction P hST
  obtain ⟨perm, hroles⟩ := occupied_has_role_order Q hocc
  refine ⟨relabelPacking Q perm, relabel_centered Q perm hsmall, ?_⟩
  exact hroles

/-- Start with the particular cap packing supplied by the D4 reduction.
Relabel it by construction role, rotate physical squares into the `T` frame,
and choose a shallow-angle representative for each square. -/
theorem occupied_to_local_pose {S : ℝ} (Q : Packing 11 coverCap)
    (hocc : Occupies Q (caseMask ⟨438, by omega⟩))
    (hsmall : CenteredPacking Q S) (hST : S ≤ T) :
    ∃ (C : Packing 11 coverCap) (R : Packing 11 T) (h : Displacement),
      CenteredPacking C S ∧
      (∀ i, ClosedCell (roleCell i)
        (normalizeCenter (C.squares i).center)) ∧
      CenteredPacking R S ∧
      (∀ i, SameSquare (quarterSquare coverCap T (C.squares i)) (R.squares i)) ∧
      (∀ i,
        (R.squares i).center = perturbedCenter constructionSquare h i ∧
        (R.squares i).axis = perturbedAxis constructionSquare h i) := by
  obtain ⟨perm, hroles⟩ := occupied_has_role_order Q hocc
  let C : Packing 11 coverCap := relabelPacking Q perm
  have hCsmall : CenteredPacking C S := relabel_centered Q perm hsmall
  let B : Packing 11 T := quarterPacking C T_pos.le hCsmall hST
  have hBsmall : CenteredPacking B S :=
    quarterPacking_centered C T_pos.le hCsmall hST
  obtain ⟨R, h, hRsmall, hsame, hpose⟩ :=
    centered_packing_has_local_pose B hBsmall
  exact ⟨C, R, h, hCsmall, hroles, hRsmall, hsame, hpose⟩

/-- Complete physical transport and pose construction. The only remaining
local-certificate input is the focused rectangle bound on `h`. The returned
same-square relation records that the actual cap squares were quarter-turned,
then their axis representatives changed without scaling their side lengths. -/
theorem case438_to_local_pose {S : ℝ} (P : Packing 11 S)
    (hST : S ≤ T) :
    ∃ (Q : Packing 11 coverCap) (R : Packing 11 T) (h : Displacement),
      CenteredPacking Q S ∧
      (∀ i, ClosedCell (roleCell i)
        (normalizeCenter (Q.squares i).center)) ∧
      CenteredPacking R S ∧
      (∀ i, SameSquare (quarterSquare coverCap T (Q.squares i)) (R.squares i)) ∧
      (∀ i,
        (R.squares i).center = perturbedCenter constructionSquare h i ∧
        (R.squares i).axis = perturbedAxis constructionSquare h i) := by
  obtain ⟨Q, hsmall, hrole⟩ := case438_centered_role_reduction P hST
  let B : Packing 11 T := quarterPacking Q T_pos.le hsmall hST
  have hBsmall : CenteredPacking B S :=
    quarterPacking_centered Q T_pos.le hsmall hST
  obtain ⟨R, h, hRsmall, hsame, hpose⟩ :=
    centered_packing_has_local_pose B hBsmall
  exact ⟨Q, R, h, hsmall, hrole, hRsmall, hsame, hpose⟩

end
end ElevenSquare.Tasks.T07
