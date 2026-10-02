import ElevenSquare.Tasks.T03.Exclusion
import ElevenSquare.Pending.S06_Exclusion
import ElevenSquare.Interop.Wand125.Families.Returned

/-! Returned-family source wiring through all 173 published owned-hull proofs.
The public initialized-terminal-trace contract is unchanged. Full native compiler
and axiom acceptance of this complete dependency path remains to be checked. -/

namespace ElevenSquare.Pending
noncomputable section

-- 173 actual returned indices, independent of the final D4 bridge.
theorem returned_certificate_exists (k : Fin 2184) (hk : k.val ∈ returnedIndices) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  exact ElevenSquare.Interop.Wand125.returned_certificate k hk

theorem returned_excluded (k : Fin 2184) (hk : k.val ∈ returnedIndices) : Excluded k := by
  obtain ⟨a, b, hroot, htrace, hterminal⟩ := returned_certificate_exists k hk
  exact ElevenSquare.Tasks.T03.excludes_of_terminal_trace
    (caseMask k) a b hroot htrace hterminal


end
end ElevenSquare.Pending

#print axioms ElevenSquare.Pending.returned_certificate_exists
#print axioms ElevenSquare.Pending.returned_excluded
