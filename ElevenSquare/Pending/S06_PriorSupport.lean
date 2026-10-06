import ElevenSquare.Tasks.T02.Exclusion
import ElevenSquare.Pending.S06_Exclusion
import ElevenSquare.Interop.Wand125.Families.Prior

/-! Prior-family source wiring through the published owned-hull proofs.
The original baseline premise remains in the public interface for compatibility.
Compiler and axiom acceptance of the complete integration remains to be checked. -/

namespace ElevenSquare.Pending
noncomputable section

-- Preserve the original baseline-exclusion premise. The imported proof is
-- independent of that premise and of S07_Bridge or the final 2180-case conclusion.
theorem prior_certificate_exists
    (hbase : ∀ k : Fin 2184, k.val ∈ baselineIndices → Excluded k)
    (k : Fin 2184) (hk : k.val ∈ priorIndices) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  exact ElevenSquare.Interop.Wand125.prior_certificate k hk

theorem prior_excluded
    (hbase : ∀ k : Fin 2184, k.val ∈ baselineIndices → Excluded k)
    (k : Fin 2184) (hk : k.val ∈ priorIndices) : Excluded k := by
  obtain ⟨a, b, hroot, htrace, hterminal⟩ := prior_certificate_exists hbase k hk
  exact ElevenSquare.Tasks.T02.excludes_of_terminal_trace
    (caseMask k) a b hroot htrace hterminal


end
end ElevenSquare.Pending

#print axioms ElevenSquare.Pending.prior_certificate_exists
#print axioms ElevenSquare.Pending.prior_excluded
