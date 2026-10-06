import ElevenSquare.Pending.S07_EncodedLabelSemanticSupport
namespace ElevenSquare.Pending.EncodedSearch
def MaskRep (k : ℕ) (m : Finset (Fin 16)) : Prop := ∀ j : Fin 16, j ∈ m ↔ j.val ∈ mask k
theorem raw_masks_eq : otherRawMasks = {{0,1,2,4,6,7,9,10,12,14,15}, {0,1,3,5,6,8,9,11,12,13,14}, {0,1,3,5,6,8,9,11,13,14,15}, {0,2,3,4,5,6,7,11,12,13,14}, {1,2,3,4,6,7,9,10,12,14,15}, {1,2,3,4,8,9,10,11,12,13,15}} := by decide
theorem mask_bounded : ∀ k : Fin 6, ∀ j ∈ mask k.val, j < 16 := by decide
theorem other_mask_rep (m : Finset (Fin 16)) (hm : m ∈ otherRawMasks) :
    ∃ k : Fin 6, MaskRep k.val m := by
  rw [raw_masks_eq] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by unfold MaskRep; decide⟩
  · exact ⟨1, by unfold MaskRep; decide⟩
  · exact ⟨2, by unfold MaskRep; decide⟩
  · exact ⟨3, by unfold MaskRep; decide⟩
  · exact ⟨4, by unfold MaskRep; decide⟩
  · exact ⟨5, by unfold MaskRep; decide⟩
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.other_mask_rep
#print axioms ElevenSquare.Pending.EncodedSearch.mask_bounded
