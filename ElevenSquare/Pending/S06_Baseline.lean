import ElevenSquare.Tasks.T01.Handoff.Assembly
import ElevenSquare.Tasks.T01.Exclusion
import ElevenSquare.Orientation
import ElevenSquare.Cases
import ElevenSquare.Pending.S06_Data
import ElevenSquare.Pending.S06_Exclusion
import ElevenSquare.Pending.S05_Trace

/-! Baseline source wiring through completed native groups and the published
field and generic families. The public contract is unchanged. Full compiler and
axiom acceptance of the new dependency path remains to be checked. -/

namespace ElevenSquare.Pending
noncomputable section

-- Build a root, a trace, and a terminal state for EACH actual index.
-- Initial ownership must come from geometry, including all ancestors and angle seams.
theorem baseline_certificate_exists (k : Fin 2184) (hk : k.val ∈ baselineIndices) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  exact ElevenSquare.Tasks.T01.Handoff.all_certificates k hk

theorem baseline_excluded (k : Fin 2184) (hk : k.val ∈ baselineIndices) : Excluded k := by
  obtain ⟨a, b, hroot, htrace, hterminal⟩ := baseline_certificate_exists k hk
  exact ElevenSquare.Tasks.T01.excludes_of_terminal_trace
    (caseMask k) a b hroot htrace hterminal


end
end ElevenSquare.Pending

#print axioms ElevenSquare.Pending.baseline_certificate_exists
#print axioms ElevenSquare.Pending.baseline_excluded
