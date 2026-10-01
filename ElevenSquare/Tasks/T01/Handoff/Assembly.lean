import ElevenSquare.Tasks.T01.Handoff.RootInitialization
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.Complete
import ElevenSquare.Tasks.T01.Handoff.Groups.G003.CachedComplete
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Complete
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.Complete
import ElevenSquare.Interop.Wand125.Certificates
import ElevenSquare.Interop.Wand125.Families.Baseline
namespace ElevenSquare.Tasks.T01.Handoff
open ElevenSquare.Pending
noncomputable section
/-- Preserve completed native groups and use the published baseline family for the rest.
The new family dependency path still requires full compiler and axiom replay. -/
theorem all_certificates
    (k : Fin 2184) (hk : k.val ∈ baselineIndices) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  by_cases hw : ElevenSquare.Interop.Wand125.applicable k = true
  · exact ElevenSquare.Interop.Wand125.certificate k hw
  by_cases h3 : k.val ∈ groupCases (3 : Group)
  · exact Groups.G003.Cached.certificate k h3
  by_cases h4 : k.val ∈ groupCases (4 : Group)
  · exact Groups.G004.certificate k h4
  by_cases h7 : k.val ∈ groupCases (7 : Group)
  · exact Groups.G007.certificate k h7
  exact ElevenSquare.Interop.Wand125.baseline_certificate k hk

end
end ElevenSquare.Tasks.T01.Handoff
