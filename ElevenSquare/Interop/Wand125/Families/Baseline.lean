import ElevenSquare.Interop.Wand125.Families.BaselineCore
import Sqpack.S11Opt.Simplified.SelectedFields
import Sqpack.S11Opt.Split.U2Generic

/-!
# Published exclusions for all 1,931 native baseline indices

Apply the conditional baseline bridge to the published field and generic
families. The native baseline dispatcher and final D4 bridge are not dependencies.
-/

namespace ElevenSquare.Interop.Wand125
open ElevenSquare.Pending
open SquarePacking.S11Opt
open SquarePacking.S11Opt.Split
noncomputable section

/-- The published field and generic families exclude every native baseline case. -/
theorem baseline_maskAt_excluded (k : Fin 2184) (hk : k.val ∈ baselineIndices) :
    CaseExcluded (maskAt k.val) :=
  baseline_maskAt_excluded_of SquarePacking.S11Opt.Simplified.SelectedFields.field_excluded
    SquarePacking.S11Opt.Split.generic_excluded k hk

/-- Preserve the native initialized-terminal-trace contract for the baseline family. -/
theorem baseline_certificate (k : Fin 2184) (hk : k.val ∈ baselineIndices) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b :=
  baseline_certificate_of SquarePacking.S11Opt.Simplified.SelectedFields.field_excluded
    SquarePacking.S11Opt.Split.generic_excluded k hk

end
end ElevenSquare.Interop.Wand125

#print axioms ElevenSquare.Interop.Wand125.baseline_maskAt_excluded
#print axioms ElevenSquare.Interop.Wand125.baseline_certificate
