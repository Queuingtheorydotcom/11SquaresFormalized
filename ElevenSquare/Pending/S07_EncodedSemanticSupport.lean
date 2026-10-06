import ElevenSquare.Pending.S07_EncodedLabelSemanticSupport
import ElevenSquare.Pending.S07_BanMembershipSupport
namespace ElevenSquare.Pending.EncodedSearch
def NeighborGood (r : ℕ) : Prop := ∀ s ∈ neighbors r, NatPairBanned r s
end ElevenSquare.Pending.EncodedSearch
