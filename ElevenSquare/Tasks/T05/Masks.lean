import ElevenSquare.Pending.S06_CasesExact
import ElevenSquare.Pending.S06_CandidateMasks
import ElevenSquare.Pending.S07_LabelData

/-! Finite classification of eleven-cell masks, using the frozen enumeration.
No physical quarter-turn is assumed to permute the Voronoi labels. -/
namespace ElevenSquare.Pending.T05Masks
noncomputable section

/-- The two frozen half-turn mask definitions agree. -/
theorem pending_halfTurnMask_eq (m : CellMask) :
    ElevenSquare.Pending.halfTurnMask m = ElevenSquare.halfTurnMask m := by
  unfold ElevenSquare.Pending.halfTurnMask ElevenSquare.halfTurnMask
  apply congrArg (fun f : Fin 16 → Fin 16 => m.image f)
  funext j
  apply Fin.ext
  dsimp [Fin.rev]
  omega

/-- Choose the canonical representative using only the exact half-turn. -/
theorem canonical_case (m : CellMask) (hm : m.card = 11) :
    ∃ flip : Bool, ∃ k : Fin 2184,
      caseMask k = (if flip then ElevenSquare.halfTurnMask m else m) := by
  rcases ElevenSquare.mask_or_halfTurn_canonical m hm with h | h
  · rw [← recorded_cases_exact.2] at h
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
    exact ⟨false, k, hk⟩
  · rw [← recorded_cases_exact.2] at h
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
    exact ⟨true, k, hk⟩

/-- Only the four existing candidate indices are used in this reduction. -/
theorem candidate_index_cases (k : Fin 2184) (hk : k.val ∈ candidateIndices) :
    k.val = 438 ∨ k.val = 999 ∨ k.val = 1462 ∨ k.val = 1659 := by
  have hc : candidateIndices = {438, 999, 1462, 1659} := by decide
  simpa only [hc, Finset.mem_insert, Finset.mem_singleton] using hk

/-- Excluding the target candidate leaves the three recorded other masks. -/
theorem candidate_other (k : Fin 2184) (hk : k.val ∈ candidateIndices)
    (hne : k.val ≠ 438) : caseMask k ∈ otherCandidateMasks := by
  rcases candidate_index_cases k hk with h | h | h | h
  · exact (hne h).elim
  · have he : k = ⟨999, by omega⟩ := Fin.ext h
    rw [he, candidate_mask_999]
    decide
  · have he : k = ⟨1462, by omega⟩ := Fin.ext h
    rw [he, candidate_mask_1462]
    decide
  · have he : k = ⟨1659, by omega⟩ := Fin.ext h
    rw [he, candidate_mask_1659]
    decide

/-- Return from the canonical orientation without discarding either half-turn. -/
theorem other_raw_of_canonical (m : CellMask) (flip : Bool) (k : Fin 2184)
    (he : caseMask k = (if flip then ElevenSquare.halfTurnMask m else m))
    (hk : k.val ∈ candidateIndices) (hne : k.val ≠ 438) :
    m ∈ otherRawMasks := by
  have ho := candidate_other k hk hne
  cases flip with
  | false =>
    have he' : caseMask k = m := by simpa using he
    apply Finset.mem_union.mpr
    exact Or.inl (he' ▸ ho)
  | true =>
    have he' : caseMask k = ElevenSquare.halfTurnMask m := by
      simpa using he
    apply Finset.mem_union.mpr
    refine Or.inr (Finset.mem_image.mpr ⟨caseMask k, ho, ?_⟩)
    rw [pending_halfTurnMask_eq, he', ElevenSquare.halfTurnMask_twice]

end
end ElevenSquare.Pending.T05Masks

#print axioms ElevenSquare.Pending.T05Masks.canonical_case
#print axioms ElevenSquare.Pending.T05Masks.other_raw_of_canonical
