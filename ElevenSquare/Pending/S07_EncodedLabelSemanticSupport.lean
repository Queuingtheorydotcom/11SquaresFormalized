import ElevenSquare.Pending.S07_EncodedData
import ElevenSquare.Pending.S07_LabelData
import ElevenSquare.Pending.NatRangeCertificates

/-! Agreement between the encoded labels and the closed-cell overlay labels. -/
namespace ElevenSquare.Pending.EncodedSearch
def LabelGood (r : ℕ) : Prop := ∀ g : Fin 4, label r g.val = (recordedOverlayLabels[r]! g).val
end ElevenSquare.Pending.EncodedSearch
