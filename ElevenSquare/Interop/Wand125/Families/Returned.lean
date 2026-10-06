import ElevenSquare.Interop.Wand125.Families
import Sqpack.S11Opt.Split.U2Returned

/-!
# Published exclusions for all 173 native returned indices

The upstream release at `8126ef4d5ce0ecc967d7223388bac65ee5ffce5e`
includes case1465 and the complete returned-family dispatcher. Transport its
exclusions through the existing case-order and geometry bridge, preserving the
native initialized-terminal-trace contract. The native baseline dispatcher,
final symmetry bridge, and global optimality are not dependencies.
-/

namespace ElevenSquare.Interop.Wand125
open ElevenSquare.Pending
noncomputable section

/-- Preserve the native initialized-terminal-trace contract for every returned case. -/
theorem returned_certificate (k : Fin 2184) (hk : k.val ∈ returnedIndices) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b :=
  returned_certificate_of SquarePacking.S11Opt.Split.returned_excluded k hk

end
end ElevenSquare.Interop.Wand125

#print axioms SquarePacking.S11Opt.Split.returned_excluded
#print axioms ElevenSquare.Interop.Wand125.returned_certificate
