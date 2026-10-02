import ElevenSquare.Cover
import ElevenSquare.Tasks.T07.CoordinateBridge
import ElevenSquare.ConstructionData
import ElevenSquare.Pending.S06_Data
import ElevenSquare.Pending.S08_Packet

/-! The physical case438 capture contract; no global exclusion premise is needed. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def Case438NearCertificate : Prop :=
  ∀ (S : ℝ) (Q : Packing 11 coverCap),
    S ≤ T →
    Occupies Q (caseMask ⟨438, by omega⟩) →
    CenteredPacking Q S →
    ∃ R : Packing 11 T, CenteredPacking R S ∧
      ∃ h : Displacement, InRectangle focusedRadii h ∧
        ∀ i,
          (R.squares i).center = perturbedCenter constructionSquare h i ∧
          (R.squares i).axis = perturbedAxis constructionSquare h i

end
end ElevenSquare.Tasks.T07
