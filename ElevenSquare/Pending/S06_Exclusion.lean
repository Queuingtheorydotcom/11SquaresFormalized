import ElevenSquare.Cover
import ElevenSquare.Pending.S06_Data

/-! Shared case-exclusion proposition, independent of family certificate assemblies. -/

namespace ElevenSquare.Pending
noncomputable section

def Excluded (k : Fin 2184) : Prop :=
  ∀ P : Packing 11 coverCap, ¬ Occupies P (caseMask k)

end
end ElevenSquare.Pending
