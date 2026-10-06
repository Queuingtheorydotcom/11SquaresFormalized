import ElevenSquare.Simplified.LocalAliasCore

namespace ElevenSquare.Simplified.LocalAlias
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T06

/-- Each nonlinear row is attached to one physical contact. Wall rows do not
use this index. Repeated entries correspond to different vertices of a contact. -/
def rowContact : Fin 42 → Fin 14 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 2, 3, 4, 4, 5, 5, 6, 6, 7, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]

def featureWitnessCheck (r : Fin 512) (p : Fin 14) : Gap → Bool
  | .wall _ _ _ => true
  | .pair f _ => decide (allFeatures (rawSelections r p) = f)

theorem rawEnabled_of_witness_check (r : Fin 512) (p : Fin 14) (g : Gap)
    (h : featureWitnessCheck r p g = true) : RawEnabled r g := by
  cases g with
  | wall i v w => trivial
  | pair f v => exact ⟨p, of_decide_eq_true h⟩

def enabledWitnessCheck (r : Fin 512) (row : Fin 42) : Bool :=
  (rowAliases (branchRows (rawSelectionBranch r) row)).any
    (featureWitnessCheck r (rowContact row))

/-- A checked contact index supplies exactly the old nonlinear alias premise.
No assertion that an unchecked contact index is correct is required. -/
theorem enabled_alias_of_witness_check (r : Fin 512) (row : Fin 42)
    (h : enabledWitnessCheck r row = true) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch r) row), RawEnabled r g := by
  unfold enabledWitnessCheck at h
  obtain ⟨g, hg, he⟩ := List.any_eq_true.mp h
  exact ⟨g, hg, rawEnabled_of_witness_check r (rowContact row) g he⟩

end ElevenSquare.Simplified.LocalAlias

#print axioms ElevenSquare.Simplified.LocalAlias.rawEnabled_of_witness_check
#print axioms ElevenSquare.Simplified.LocalAlias.enabled_alias_of_witness_check
