import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin

/-! Bounded kernel regression for the T07 owner-to-role permutation proof.

The finite maps and inverse proofs match `RoleAssignmentFinite`. An arbitrary
indexed predicate represents the geometric cell condition, so this checks the
same proof composition without loading the packing or numerical certificates.
-/
namespace T07GeometryRoles
noncomputable section

abbrev Owner := Fin 11

def ownerCell : Owner → Fin 16 := ![0,1,2,3,4,8,9,10,11,13,15]

def roleCell : Owner → Fin 16 := ![3,15,8,0,4,1,2,11,9,10,13]

def roleOwner : Owner → Owner := ![3,10,5,0,4,1,2,8,6,7,9]

def ownerRole : Owner → Owner := ![3,5,6,0,4,2,8,9,7,10,1]

theorem roleOwner_left_inverse (i : Owner) : ownerRole (roleOwner i) = i := by
  fin_cases i <;> rfl

theorem roleOwner_right_inverse (i : Owner) : roleOwner (ownerRole i) = i := by
  fin_cases i <;> rfl

theorem roleOwner_bijective : Function.Bijective roleOwner := by
  constructor
  · intro i j h
    calc i = ownerRole (roleOwner i) := (roleOwner_left_inverse i).symm
      _ = ownerRole (roleOwner j) := congrArg ownerRole h
      _ = j := roleOwner_left_inverse j
  · intro i
    exact ⟨ownerRole i, roleOwner_right_inverse i⟩

def rolePermutation : Equiv.Perm Owner := Equiv.ofBijective roleOwner roleOwner_bijective

theorem role_cell_correspondence (i : Owner) : ownerCell (roleOwner i) = roleCell i := by
  fin_cases i <;> decide

theorem occupied_has_role_order (cell : Fin 16 → Owner → Prop)
    (hocc : ∃ perm : Equiv.Perm Owner, ∀ i, cell (ownerCell i) (perm i)) :
    ∃ perm : Equiv.Perm Owner, ∀ i, cell (roleCell i) (perm i) := by
  obtain ⟨perm, howner⟩ := hocc
  refine ⟨rolePermutation.trans perm, ?_⟩
  intro i
  have h := howner (roleOwner i)
  rw [role_cell_correspondence] at h
  simpa only [Equiv.trans_apply, rolePermutation, Equiv.coe_ofBijective] using h

#print axioms roleOwner_bijective
#print axioms role_cell_correspondence
#print axioms occupied_has_role_order

end
end T07GeometryRoles
