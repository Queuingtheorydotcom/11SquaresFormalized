import ElevenSquare.Tasks.T06.BranchAliasDefinitions

namespace ElevenSquare.Simplified.LocalAlias
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T06

def rawGroupIndex (q : Fin 32) (s : Fin 16) : Fin 512 :=
  ⟨16*q.val+s.val, by have hq := q.isLt; have hs := s.isLt; omega⟩

def enabledAliasCheck (r : Fin 512) (row : Fin 42) : Bool :=
  (rowAliases (branchRows (rawSelectionBranch r) row)).any
    (fun g => decide (RawEnabled r g))

/-- Boolean search supplies an actual enabled nonlinear alias, preserving the
original membership and feature-selection propositions. -/
theorem enabled_alias_of_check (r : Fin 512) (row : Fin 42)
    (h : enabledAliasCheck r row = true) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch r) row), RawEnabled r g := by
  unfold enabledAliasCheck at h
  obtain ⟨g, hg, he⟩ := List.any_eq_true.mp h
  exact ⟨g, hg, of_decide_eq_true he⟩

end ElevenSquare.Simplified.LocalAlias

#print axioms ElevenSquare.Simplified.LocalAlias.enabled_alias_of_check
