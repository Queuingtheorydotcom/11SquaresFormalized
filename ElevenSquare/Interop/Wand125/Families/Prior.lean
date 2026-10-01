import ElevenSquare.Interop.Wand125.Families
import Sqpack.S11Opt.Split.U2Prior

/-!
# Published exclusions for all 76 native prior indices

The upstream owned-hull proofs establish this family independently of the native
baseline-exclusion premise. The public S06 interface can therefore retain that
premise while using this stronger certificate theorem.
-/

namespace ElevenSquare.Interop.Wand125
open ElevenSquare.Pending
noncomputable section

/-- Preserve the native initialized-terminal-trace contract for the prior family. -/
theorem prior_certificate (k : Fin 2184) (hk : k.val ∈ priorIndices) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b :=
  prior_certificate_of SquarePacking.S11Opt.Split.prior_excluded k hk

end
end ElevenSquare.Interop.Wand125

#print axioms ElevenSquare.Interop.Wand125.prior_certificate
